#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
PADDOCK SCOUT  v1.13.0  —  SEVENTHWELL

NAS上の「演者フォルダ」を読み取り専用で監視して、変化があったらデスクトップ通知する。
通知をクリックすると、そのフォルダの中身をアプリ内で表示する（Explorer / Finder でも開ける）。
PowerPoint は 動画 / ハイパーリンク / COI / 自動送り / クリック無効 を自動で解析する。
「会場ボード」表示では、全会場を横に並べて受付状況を一覧できる。
受付PC用の PADDOCK SADDLE（NASへ書き込む）、会場の発表PC用の PADDOCK GATE（発表PCへコピーする）は、
このファイルを部品として読み込む別アプリ。このファイル単体（PADDOCK SCOUT）はどこにも書き込まない。

  ・Python 3.7 以上 / 標準ライブラリのみ（追加インストール不要）
  ・NAS上で行うのは「フォルダ一覧・サイズ・更新日時の取得」と「PowerPoint解析のための読み取り」だけ。
    ファイルを作る・書く・消す・名前を変える処理は一切ない。
  ・設定 / ログ / 解析結果は、このファイルの横の sw_nas_watch_data\ に保存（NAS側には置かない）

起動:
  python sw_nas_watch.py
  python sw_nas_watch.py --root "\\192.168.0.10\share\学会名" --depth 3
  python sw_nas_watch.py --port 8790 --no-browser
"""

import argparse
import base64
import errno
import fnmatch
import hashlib
import json
import os
import posixpath
import queue
import re
import secrets
import shutil
import socket
import struct
import subprocess
import sys
import threading
import time
import unicodedata
import webbrowser
import xml.etree.ElementTree as ET
import lzma
import zipfile
import zlib
from collections import deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, unquote, urlparse
from urllib.request import Request, urlopen
from urllib.error import HTTPError

APP_NAME = "PADDOCK SCOUT"
VERSION = "1.17.5"
DEFAULT_PORT = 8790
IS_WIN = sys.platform.startswith("win")
IS_MAC = sys.platform == "darwin"

DIR = "D"                 # スナップショット上のフォルダ印
MAX_GROUP_WAIT = 180.0    # 書き込みが続いていても、この秒数で途中経過を確定させる
RECENT_KEEP = 6 * 3600    # フォルダ表示で「最近の変更」印を残す時間
EVENT_KEEP = 3000
ANA_VERSION = 5   # 解析内容を変えたら上げる（保存済みの解析結果を作り直す）  3: 動画の形式チェック  4: リンク動画の解析失敗を修正  5: 全体点検の修正（音声リンク・H.264プロファイル等）
SYNC_ANALYSIS_BUDGET = 12.0  # 通知に解析結果を載せるため、確定直後に待つ最大秒数

DEFAULT_IGNORE = [
    "Thumbs.db", "desktop.ini", ".DS_Store", "._*", "~$*", "~*.tmp", "*.tmp", ".~lock.*#",
    ".TemporaryItems", ".Trashes", ".Spotlight-V100", ".fseventsd", ".apdisk",
    ".AppleDouble", ".AppleDB", ".AppleDesktop", "Network Trash Folder",
    "@eaDir", "#recycle", "#snapshot", "@Recycle", ".@__thumb", "@Recently-Snapshot",
    "$RECYCLE.BIN", "System Volume Information",
    "*.sb-*", ".smbdelete*",
]
# 現場で演者フォルダに入れる「目印」の画像（例: 00_受付済.jpg / 13_変更有.jpg / 17_会場取得.jpg / 18_発表終了.jpg）。
# ファイル名にこの文字を含む画像・テキストは、データではなく目印として扱う（全角半角・大文字小文字・空白や _ - は区別しない）。
# role: recv=受付済 / got=会場取得済 / done=発表終了 / drop=演題取り下げ / direct=会場直（データは会場で受け取る）
#       warn=注意として目立たせる / info=表示だけ
MARK_ROLES = ("recv", "got", "done", "drop", "direct", "warn", "op", "info")   # op=会場のオペが対応すること（発表者ツール・演台上げなど）
DEFAULT_MARKS = [
    {"w": "受付済", "role": "recv"}, {"w": "受付完了", "role": "recv"},
    {"w": "動画有", "role": "op"}, {"w": "音声有", "role": "op"}, {"w": "動画のみ音声不要", "role": "info"},
    {"w": "PC持込", "role": "op"}, {"w": "Win持込", "role": "op"}, {"w": "Mac持込", "role": "op"}, {"w": "持込", "role": "op"},
    {"w": "Backup", "role": "info"},
    {"w": "持込リモプレ", "role": "op"}, {"w": "リモプレ", "role": "op"}, {"w": "COIあり", "role": "info"}, {"w": "OP卓PC 発表者ツール", "role": "op"}, {"w": "発表者ツール", "role": "op"},
    {"w": "ミラーリング", "role": "op"}, {"w": "Mac PPT", "role": "op"}, {"w": "Mac Keynote", "role": "op"},
    {"w": "演台上げ", "role": "op"}, {"w": "演台持上", "role": "op"},
    # よく使われる目印画像の名前（PowerPoint の版・持込・リモート・オペ対応など）
    {"w": "Win 365", "role": "op"}, {"w": "Win 2007", "role": "op"}, {"w": "Win 2010", "role": "op"}, {"w": "Win 2013", "role": "op"},
    {"w": "Win 2016", "role": "op"}, {"w": "Win 2019", "role": "op"}, {"w": "Win 2021", "role": "op"}, {"w": "Mac 365", "role": "op"},
    {"w": "PC持込 Win", "role": "op"}, {"w": "PC持込 Mac", "role": "op"}, {"w": "ビデオ持込", "role": "op"}, {"w": "メディア持込", "role": "op"},
    {"w": "Zoom使用", "role": "op"}, {"w": "リモート登壇", "role": "op"}, {"w": "アダプター貸出", "role": "op"}, {"w": "変換アダプター貸出", "role": "op"},
    {"w": "オペ操作", "role": "op"}, {"w": "オペレーター", "role": "op"}, {"w": "記念品お渡し", "role": "info"}, {"w": "記念品お渡し済", "role": "info"},
    {"w": "データ修正", "role": "warn"}, {"w": "データなし", "role": "info"}, {"w": "読んでください", "role": "warn"}, {"w": "連絡", "role": "warn"},
    {"w": "変更有", "role": "warn"}, {"w": "演者変更", "role": "warn"},
    {"w": "演題取り下げ", "role": "drop"}, {"w": "取り下げ", "role": "drop"}, {"w": "取下げ", "role": "drop"},
    {"w": "会場直", "role": "direct"}, {"w": "会場直撃", "role": "direct"}, {"w": "事前預り", "role": "recv"},
    {"w": "会場取得", "role": "got"}, {"w": "取得済", "role": "got"}, {"w": "会場確認済", "role": "got"}, {"w": "受取済", "role": "got"},
    {"w": "受け取り済", "role": "got"}, {"w": "DL済", "role": "got"}, {"w": "ダウンロード済", "role": "got"},
    {"w": "発表終了", "role": "done"}, {"w": "発表済", "role": "done"},
]
MARKS_V = 5                       # 目印の既定を増やしたら上げる（保存済みの設定にも新しい既定を足す）
MARKS_ADDED = {2: ["PC持込", "持込"], 3: ["演台上げ"], 4: ["Mac持込", "Win持込", "リモプレ", "COIあり"],
               5: ["演台持上", "Win 365", "Win 2007", "Win 2010", "Win 2013", "Win 2016", "Win 2019", "Win 2021", "Mac 365",
                   "PC持込 Win", "PC持込 Mac", "ビデオ持込", "メディア持込", "Zoom使用", "リモート登壇", "アダプター貸出", "変換アダプター貸出",
                   "オペ操作", "オペレーター", "記念品お渡し", "記念品お渡し済", "データ修正", "データなし", "読んでください", "連絡",
                   "会場直撃", "事前預り", "会場確認済"]}
# 既定の役割を変えたもの：前の版のまま（＝利用者が変えていない）なら新しい役割にする
MARKS_ROLE_CHANGED = {3: (("PC持込", "Win持込", "Mac持込", "持込", "持込リモプレ", "OP卓PC 発表者ツール", "発表者ツール",
                           "ミラーリング", "Mac PPT", "Mac Keynote"), "info", "op"),
                      4: (("動画有", "音声有"), "info", "op")}   # 動画・音声は会場のオペが音や映像を出すので「オペが対応」に
MARK_STATUS_ROLES = ("recv", "got", "done", "drop", "direct")   # 演者の状態を決める目印
MARK_CHIP_ROLES = ("direct", "warn", "op", "info")              # 演者の行にチップで出す目印
MARK_MAX = 20 * 1024 * 1024
PRES_OPEN_EXT = (".pptx", ".ppsx", ".pptm", ".ppsm", ".ppt", ".pps", ".key", ".pdf")   # 開く対象の発表ファイル
META_DIRS = ("system-info",)       # 受付システムが演者フォルダに入れる付帯情報のフォルダ（中身は発表データに数えない）
# 設定に関係なく常に無視するもの：PADDOCK SADDLE（受付アプリ）がNASへ書き込む途中の一時ファイル
BUILTIN_IGNORE = [".swnr_*.part"]
DEFAULT_COI = ["COI", "利益相反", "ディスクロージャー", "Disclosure", "Conflict of Interest"]
NOTIFY_KINDS = ["incoming", "folder_new", "add", "mod", "rename", "del",
                "folder_rename", "folder_del", "offline", "online", "copied", "copy_err"]
SYS_KINDS = {"copied", "copy_err"}      # アプリ側の動作の知らせ（未確認数には数えない）
OP_OLD_DIR = "_差し替え前"              # コピー先で上書きした旧版の退避先（コピー先フォルダの中）
TMP_PREFIX = ".swnw_"                   # コピー途中の一時ファイル（コピー先にだけ作る）
COPY_CHUNK = 1 << 20
MAX_DESTS = 4
DEFAULT_CFG = {
    "roots": [],
    "poll_sec": 2.0,
    "settle_sec": 6.0,
    "ignore": DEFAULT_IGNORE,
    "notify": {k: True for k in NOTIFY_KINDS},
    "ui": {"sound": True, "click": "app", "sticky": False, "os_open": False},
    "report_while_stopped": True,
    "analyze": True,
    "coi_keywords": DEFAULT_COI,
    "marks": DEFAULT_MARKS,
    "max_depth": 12,
    "max_entries": 200000,
    # 会場オペレーターモード：自分の会場だけを監視し、受信が完了した演者フォルダをコピー先へコピーする
    "op": {"enabled": False, "root": "", "venue": "", "dests": [], "max_mbps": 0, "days": [], "day": "", "day_dir": True, "dsub": ""},
}

CATS = [
    ("PPT", {"ppt", "pptx", "pptm", "pps", "ppsx", "ppsm", "pot", "potx", "potm"}),
    ("KEY", {"key"}),
    ("PDF", {"pdf"}),
    ("動画", {"mp4", "mov", "m4v", "avi", "wmv", "mkv", "mpg", "mpeg", "mts", "m2ts",
             "webm", "flv", "mxf", "3gp", "asf"}),
    ("音声", {"wav", "mp3", "m4a", "aac", "aif", "aiff", "flac", "wma", "ogg"}),
    ("画像", {"jpg", "jpeg", "png", "gif", "bmp", "tif", "tiff", "heic", "webp", "psd"}),
    ("Word", {"doc", "docx"}),
    ("Excel", {"xls", "xlsx", "xlsm", "csv"}),
    ("圧縮", {"zip", "rar", "7z", "lzh", "tar", "gz"}),
]
VIDEO_EXTS = CATS[3][1]
PPT_CAT_EXTS = CATS[0][1]                     # 差し替えの判断に使う（パワーポイントが変わったときだけ）
MARK_EXTS = set(CATS[5][1]) | {"txt", ""}     # 目印として扱うファイル（画像・テキスト・拡張子なし）
AUDIO_EXTS = CATS[4][1]
PPTX_EXTS = {"pptx", "pptm", "ppsx", "ppsm", "potx", "potm"}


def ext_of(name):
    return name.rsplit(".", 1)[-1].lower() if "." in name else ""


def file_cat(name):
    ext = ext_of(name)
    for label, exts in CATS:
        if ext in exts:
            return label
    return "他"


def ana_kind(rel):
    e = ext_of(rel)
    if e in PPTX_EXTS:
        return "pptx"
    if e == "key":
        return "key"
    if e in ("ppt", "pps", "pot"):
        return "ppt"
    return None


def _err(e):
    if isinstance(e, OSError):
        msg = e.strerror or str(e)
        if getattr(e, "winerror", None):
            msg = "%s (WinError %s)" % (msg, e.winerror)
        return msg
    return str(e)


def norm_key(path):
    return os.path.normcase(os.path.normpath(os.path.abspath(path) if not path.startswith(("\\\\", "//")) else path))


def is_under(child, parent):
    c, p = norm_key(child), norm_key(parent)
    if c == p:
        return True
    return c.startswith(p.rstrip("\\/") + os.sep)


def base(rel):
    return rel.rsplit("/", 1)[-1]


def parent_of(rel):
    return rel.rsplit("/", 1)[0] if "/" in rel else ""


def group_of(rel, sig, depth):
    """rel がどの「演者フォルダ」に属するか。浅い階層のファイル等は '' に入れる。"""
    n = rel.count("/") + 1
    if n > depth:
        return "/".join(rel.split("/", depth)[:depth])
    if n == depth and sig == DIR:
        return rel
    return ""


def unit_of(rel, sig, depth):
    """受信待ち・コピー待ちのまとまり。演者フォルダはフォルダごと、
    セッションフォルダに直接置かれた発表ファイル（演者フォルダなし）は1ファイルずつ。"""
    g = group_of(rel, sig, depth)
    if g == "" and sig != DIR and rel.count("/") + 1 == depth:
        return rel
    return g


def compile_ignore(patterns):
    pats = [p.strip().lower() for p in patterns if p and p.strip()]
    if not pats:
        return None
    return re.compile("|".join("(?:%s)" % fnmatch.translate(p) for p in pats))


def is_ignored(ignore_re, rel):
    """rel のどこかの階層が無視パターンに当たるか（scan_tree と同じ判定）。"""
    return ignore_re is not None and any(ignore_re.match(x.lower()) for x in rel.split("/"))


class ScanTooLarge(Exception):
    pass


def scan_tree(root, ignore_re, max_depth, max_entries, only=None):
    """読み取り専用スキャン。os.scandir と stat だけを使う（ファイルは開かない）。
    戻り値: (entries, warnings, failed_dirs)   entries: rel -> DIR | (size, mtime_ns)
    only を指定すると、そのフォルダ（「DAY1/第1会場」のような相対パスも可）とその途中のフォルダだけを見る（会場オペレーターモード）。
    ルート自体が読めない場合は OSError をそのまま送出する。"""
    out = {}
    warns = []
    failed = []
    only_segs = only.split("/") if only else None
    stack = [("", root, 0)]
    while stack:
        rel, apath, lvl = stack.pop()
        try:
            it = os.scandir(long_path(apath))     # 深いフォルダ（260文字超）も読めるように
        except OSError as e:
            if not rel:
                raise
            failed.append(rel)
            warns.append("%s: %s" % (rel, _err(e)))
            continue
        try:
            with it:
                for de in it:
                    name = de.name
                    if only_segs is not None:
                        lv = rel.count("/") + 1 if rel else 0
                        if lv < len(only_segs) and name != only_segs[lv]:
                            continue
                    if ignore_re is not None and ignore_re.match(name.lower()):
                        continue
                    r = name if not rel else rel + "/" + name
                    try:
                        if de.is_dir(follow_symlinks=False):
                            out[r] = DIR
                            if lvl + 1 < max_depth:
                                stack.append((r, de.path, lvl + 1))
                        elif de.is_file(follow_symlinks=False):
                            st = de.stat(follow_symlinks=False)
                            out[r] = (st.st_size, st.st_mtime_ns)
                    except OSError as e:
                        warns.append("%s: %s" % (r, _err(e)))
                    if len(out) > max_entries:
                        raise ScanTooLarge("ファイル数が上限(%d)を超えました。監視フォルダを絞ってください" % max_entries)
        except OSError as e:
            if not rel:
                raise
            failed.append(rel)
            warns.append("%s: %s" % (rel, _err(e)))
    return out, warns, failed


# ---------------------------------------------------------------- PowerPoint 解析（読み取り専用）
NS_P = "http://schemas.openxmlformats.org/presentationml/2006/main"
NS_A = "http://schemas.openxmlformats.org/drawingml/2006/main"
NS_R = "http://schemas.openxmlformats.org/officeDocument/2006/relationships"
NS_PR = "http://schemas.openxmlformats.org/package/2006/relationships"
NS_P14 = "http://schemas.microsoft.com/office/powerpoint/2010/main"
T_P, T_A_P, T_A_T = "{%s}p" % NS_A, "{%s}p" % NS_A, "{%s}t" % NS_A
OLE_MAGIC = b"\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1"


def open_ro(path):
    """読み取り専用で開く。
    Windowsでは「他の人の読み取り・上書き・削除・名前変更をすべて許可する」共有モードでしか開かない。
    （この開き方ができない環境では、普通の開き方には切り替えず、解析そのものをやめる）"""
    if not IS_WIN:
        return open(path, "rb")
    try:
        import ctypes
        import msvcrt
        from ctypes import wintypes
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        fn = k32.CreateFileW
        fn.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, ctypes.c_void_p,
                       wintypes.DWORD, wintypes.DWORD, wintypes.HANDLE]
        fn.restype = wintypes.HANDLE
        k32.CloseHandle.argtypes = [wintypes.HANDLE]
    except Exception as e:
        raise UnsafeOpen("安全な開き方を使えないため解析しません（%s）" % e)
    # GENERIC_READ / FILE_SHARE_READ|WRITE|DELETE / OPEN_EXISTING / FILE_FLAG_SEQUENTIAL_SCAN
    h = fn(path, 0x80000000, 0x7, None, 3, 0x08000000, None)
    if h is None or h == ctypes.c_void_p(-1).value:
        raise ctypes.WinError(ctypes.get_last_error())
    try:
        fd = msvcrt.open_osfhandle(h, os.O_RDONLY | getattr(os, "O_BINARY", 0))
    except Exception as e:
        k32.CloseHandle(h)
        raise UnsafeOpen("安全な開き方を使えないため解析しません（%s）" % e)
    return os.fdopen(fd, "rb")


class UnsafeOpen(Exception):
    pass


def in_use_by_office(path):
    """PowerPointで開かれている間は「~$ファイル名」の鍵ファイルがある。あれば触らない（stat のみで確認）。"""
    d, n = os.path.split(path)
    for c in {"~$" + n, "~$" + n[2:] if len(n) > 2 else "", ".~lock." + n + "#"}:   # PowerPoint / LibreOffice
        if not c:
            continue
        try:
            os.stat(long_path(os.path.join(d, c)))
            return True
        except (FileNotFoundError, NotADirectoryError):
            continue
        except (OSError, ValueError):
            return True   # 確認できないとき（ネットワークの一時的な不調など）も触らない側に倒す
    return False


_MK_SEP = re.compile(r"[\s_\-\u2010-\u2015\u2212\u30fb.,\u3001\u3002()\[\]\u3010\u3011\u300c-\u300f\u3014\u3015"
                     r"\u2605\u2606\u25c6\u25c7\u25ce\u25cf\u25cb\u25a0\u25a1\u203b\u266a\u25b2\u25b3\u25bc\u25bd\u3007\u2713\u2714\u2611\u2b50\ufe0f!?#*+=~^:;'\"]+")   # ★☆◆◇◎●○■□※♪▲△▼▽〇 などの飾りも無視


_MK_CODE = r"(?:\d{4}[-_.]?\d{1,2}[-_.]?\d{1,2}|[A-Za-z]{1,3}\d{1,4}(?:[-‐]\d{1,4})?|\d{1,4}[-‐]\d{1,4}|No\.?\d{1,4})"   # 日付（2026-10-23）・演題番号（A01・S1-01・No.1）
_MK_NUM = re.compile(r"^\s*(?:(?:[(\[（【]" + _MK_CODE + r"[)\]）】][\s_\-.・]*|" + _MK_CODE + r"[\s_\-.・]+|\d{1,4}[\s_.・]+(?=\d)))*"
                     r"[(\[（【]?\d{0,4}[)\]）】]?[\s_\-.・]*")      # 先頭の番号（00_ / 17- / (3) / A01_ / S1-01_ / 2026-10-23_ など。くり返しも）
_MK_TAIL = re.compile(r"^(?:み|済|済み|有|使用)?(?:の?コピー|copy|\d)*$")            # 後ろに付いてよいもの（受付済み・「- コピー (2)」など）


# セッションのフォルダに直接置かれた、番号付きのメモ（03_はPC持ち込み.txt など）：発表ファイルの無い演者の枠として並べる
_NOTE_SLOT = re.compile(r"^\s*\d{1,3}[\s_\-.・]+.*\.txt$", re.I)


def mark_stem(name):
    """目印の照合に使う名前：拡張子と先頭の番号を除き、mark_norm でそろえたもの。"""
    stem = name.rsplit(".", 1)[0] if "." in name else name
    return mark_norm(_MK_NUM.sub("", unicodedata.normalize("NFKC", stem), count=1))


META_DIRS_N = None   # mark_norm を定義した後で作る


def mark_match(marks, name):
    """目印の文字で「始まる」ものだけを目印にする。後ろに別の言葉が続くもの（受付済の資料.png・Backup_図1.png など）は
    データとして扱う（データの画像を目印と取り違えて数えない・消さないため）。
    英字だけの目印（Backup など）は、データの画像の名前にも使われやすいので、名前全体がその言葉のときだけ（番号の付け足しも不可）。"""
    st = mark_stem(name)
    st0 = None
    for k, role, label, i in marks:          # 長いキーワードから順に
        if k.isascii() and k.isalpha():
            if st0 is None:
                stem = name.rsplit(".", 1)[0] if "." in name else name
                st0 = mark_norm(re.sub(r"^\s*[(\[（【]?\d{1,4}[)\]）】]?[\s_\-.・]*", "", unicodedata.normalize("NFKC", stem), count=1))
            if st0 == k:
                return role, label, i
            continue
        if st.startswith(k) and _MK_TAIL.match(st[len(k):]):
            return role, label, i
    return None


_MK_OKURI = (("持ち込み", "持込"), ("持込み", "持込"), ("持ち込", "持込"), ("受け付け", "受付"), ("受付け", "受付"),
             ("受け付", "受付"), ("受け取り", "受取"), ("受取り", "受取"), ("受け取", "受取"), ("取り下げ", "取下げ"),
             ("有り", "有"), ("あり", "有"), ("アリ", "有"), ("無し", "なし"),
             ("持ち上げ", "持上"), ("持上げ", "持上"), ("預かり", "預り"))   # 演台持ち上げ／演台持上、事前預かり／事前預り   # 音声あり／音声有、動画アリ／動画有 も同じ


def mark_norm(s):
    """目印の照合用：全角半角・大文字小文字をそろえ、空白・_・-・括弧（【】など）を取り除く。
    送り仮名の違い（持ち込み／持込、受け取り／受取、取り下げ／取下げ など）も同じとみなす。"""
    t = _MK_SEP.sub("", unicodedata.normalize("NFKC", str(s)).lower())
    for a, b in _MK_OKURI:
        t = t.replace(a, b)
    return t


META_DIRS_N = {mark_norm(x) for x in META_DIRS}


def compile_marks(cfg):
    out = []
    for i, m in enumerate(cfg.get("marks") or []):
        k = mark_norm(m.get("w", ""))
        if k:
            out.append((k, m.get("role") if m.get("role") in MARK_ROLES else "info", str(m.get("w")).strip(), i))
    out.sort(key=lambda x: -len(x[0]))   # 長いキーワードを優先（「OP卓PC 発表者ツール」と「発表者ツール」など）
    return out


def migrate_marks(raw):
    """v1.10 の「受付済」「会場取得済」の設定（mark_recv / mark_got）を、目印の一覧へ移す。"""
    out = [dict(m) for m in DEFAULT_MARKS]
    have = {mark_norm(m["w"]) for m in out}
    for key, role in (("mark_recv", "recv"), ("mark_got", "got")):
        v = raw.get(key)
        if isinstance(v, list):
            for w in v:
                k = mark_norm(w)
                if k and k not in have:
                    have.add(k)
                    out.append({"w": str(w).strip()[:40], "role": role})
    return out


COI_MATCH_REV = "3"   # 照合のしかたを変えたら上げる（解析結果を作り直す）


def coi_signature(words):
    return hashlib.sha1(("r" + COI_MATCH_REV + "\n" + "\n".join(words)).encode("utf-8")).hexdigest()[:12]


def compile_coi(words):
    asc, ja = [], []
    for w in words:
        w = unicodedata.normalize("NFKC", str(w)).strip()
        if not w:
            continue
        if re.fullmatch(r"[\x20-\x7e]+", w):
            if re.fullmatch(r"[A-Za-z]{2,6}", w):
                # COI などの短い略語：続けて書いたもの（COI・CoI）か、大文字の間に空白・点があるもの（「ＣＯ　Ｉ」「C.O.I」）。
                # ハイフン（「Co-I」＝共同研究者）や、段落・改行をまたぐもの（「…CO」＋改行＋「I度」）は COI としない
                spaced = "[ \t\u3000.・]*".join(re.escape(c.upper()) for c in w)
                pat = "(?:" + re.escape(w) + "|(?-i:" + spaced + "))"
            else:
                # 「Conflicts of Interest」「Conflict-of-Interest」「Conflict of<改行>Interest」も拾う（複数形・ハイフン・改行）
                ws = re.split(r"[\s\-]+", w)
                sep = r"[\s\-\u2010-\u2015_・]*" if len(ws) > 1 else ""
                pat = sep.join(re.escape(x) + ("s?" if len(ws) > 1 and x[-1:].isalpha() else "") for x in ws)
            if w[0].isalnum():
                pat = r"(?<![A-Za-z])" + pat
            if len(w) <= 4 and w[-1].isalnum():   # COI など短い略語は語の一部に一致させない（「COIs」は可）
                pat += r"s?(?![A-Za-z])"
            asc.append(pat)
        else:
            ja.append(re.escape(re.sub(r"\s+", "", w)))
    return (re.compile("|".join(asc), re.I) if asc else None,
            re.compile("|".join(ja), re.I) if ja else None)


def slide_texts(root):
    """スライドの文字：段落ごと（改行 a:br は空白）＋図形・表のセルごとに段落をつないだもの
    （「Conflict of」「Interest」や「利益」「相反」が別の行・段落に分かれていても見つけるため）"""
    br = "{%s}br" % NS_A
    out = []
    for body in list(root.iter("{%s}txBody" % NS_P)) + list(root.iter("{%s}txBody" % NS_A)):
        paras = []
        for p in body.iter(T_A_P):
            paras.append("".join(("\n" if el.tag == br else (el.text or "")) for el in p.iter() if el.tag in (T_A_T, br)))
        paras = [x for x in paras if x.strip()]
        out += paras
        if len(paras) > 1:
            out.append("\n".join(paras))
    return out


def _coi_find(coi, texts):
    a, j = coi
    for raw in texts:
        t = unicodedata.normalize("NFKC", raw or "")
        m = a.search(t) if a else None
        if not m and j:
            m = j.search(re.sub(r"\s+", "", t))
        if m:   # 判定は全角/半角をそろえて行い、表示はスライドの原文のまま
            return m.group(0), re.sub(r"\s+", " ", raw or "").strip()[:70]
    return None


def _resolve(base_dir, target):
    if target.startswith("/"):
        return target.lstrip("/")
    return posixpath.normpath(posixpath.join(base_dir, target))


def _link_status(tgt, pptx_dir):
    """リンク動画の参照先。NAS上の相対パスだけ存在確認（stat）する。(状態, 表示用, 見つかったファイルのパス or None) を返す。"""
    t = tgt.strip()
    low = t.lower()
    if re.match(r"^(https?|rtsp|rtmp|mms)://", low):
        return "online", t, None
    if low.startswith("file:"):
        t = unquote(t[5:])
        if t.startswith("///") or (t.startswith("/") and not t.startswith("//")):
            t = "/" + t.lstrip("/")          # ローカルのパス（file:///C:/… や file:///Users/…）
            if re.match(r"^/[A-Za-z]:", t):
                t = t[1:]
        # file://サーバー/共有/… はネットワーク上の場所（UNC）のまま
    else:
        t = unquote(t)
    if re.match(r"^[A-Za-z]:[\\/]", t):
        return "abs", t.replace("/", "\\"), None
    if t.startswith(("\\\\", "//")):
        return "unc", t.replace("/", "\\"), None
    if t.startswith("/"):
        return "abs", t, None
    rel = t.replace("\\", "/")
    p = os.path.normpath(os.path.join(pptx_dir, *[x for x in rel.split("/") if x]))
    try:
        ok = os.path.isfile(p)
    except OSError:
        ok = False
    return ("here" if ok else "missing"), t, (p if ok else None)


# ---------------------------------------------------------------- 動画の形式（コーデック）判定
# 動画ファイルの「箱の見出し」と、形式情報（moov）だけを読む。映像データ本体は読まない。
# 判定の根拠：PowerPoint(Windows)の推奨は H.264 + AAC の MP4。Windows標準の H.264 デコーダは
# Baseline / Main / High（8bit・4:2:0）・レベル5.1まで。HEVC は別途「HEVC拡張」が必要。ProRes は非対応。
PROBE_MOOV_MAX = 48 * 1024 * 1024     # moov（形式情報）の上限
PROBE_SEQ_MAX = 64 * 1024 * 1024      # 圧縮されたZIPメンバーを前から読むときの上限
PROBE_TOTAL_MAX = 320 * 1024 * 1024   # 1つのPowerPointで、動画の形式確認のために読む量の合計の上限
VIDEO_LIST_MAX = 2000                 # 1つのPowerPointで記録する動画・音声の数の上限（本数に制限はかけない前提の安全弁）
PRORES = {"apcn", "apch", "apcs", "apco", "ap4h", "ap4x", "aprn", "aprh"}
H264_OK = {66: "Baseline", 77: "Main", 100: "High"}
H264_NG = {110: "High 10（10bit）", 122: "High 4:2:2", 244: "High 4:4:4", 44: "CAVLC 4:4:4"}


class _ProbeStop(Exception):
    pass


class _Meter:
    """1つのPowerPointの中の動画すべてで共有する、読み取り量の残り。"""
    def __init__(self, left):
        self.left = left

    def take(self, n):
        self.left -= n
        if self.left < 0:
            raise _ProbeStop("動画が多く、読み取り量の上限に達したため省略しました。試写で確認を")


class _DirectReader:
    """ファイル（またはZIP内の無圧縮メンバー）を、必要な位置だけシークして読む。"""
    def __init__(self, f, base, size, meter=None):
        self.f, self.base, self.size, self.used, self.meter = f, base, size, 0, meter

    def read_at(self, off, n):
        if off >= self.size:
            return b""
        n = min(n, self.size - off)
        self.used += n
        if self.used > PROBE_MOOV_MAX + (1 << 20):
            raise _ProbeStop("読み取り量の上限")
        if self.meter:
            self.meter.take(n)
        self.f.seek(self.base + off)
        return self.f.read(n)


class _SeqReader:
    """ZIP内の圧縮メンバー：前から順に読むしかないので、上限までで打ち切る（直前に読んだ分だけ手元に残す）。"""
    def __init__(self, fp, size, meter=None):
        self.fp, self.size, self.meter = fp, size, meter
        self.buf, self.boff = b"", 0        # 手元にある範囲 [boff, boff+len(buf))

    def _read(self, n):
        b = self.fp.read(n)
        if self.meter and b:
            self.meter.take(len(b))
        return b

    def read_at(self, off, n):
        if off < self.boff:
            raise _ProbeStop("後戻りできません")
        if off + n > PROBE_SEQ_MAX:
            raise _ProbeStop("形式情報がファイルの後ろにあり、確認できません")
        end = self.boff + len(self.buf)
        if off >= end:
            skip = off - end
            while skip > 0:
                b = self._read(min(skip, 1 << 20))
                if not b:
                    return b""
                skip -= len(b)
            self.buf, self.boff = b"", off
        else:
            self.buf, self.boff = self.buf[off - self.boff:], off
        while len(self.buf) < n:
            b = self._read(n - len(self.buf))
            if not b:
                break
            self.buf += b
        return self.buf[:n]


def _boxes(buf, start, end):
    """メモリ上のMP4ボックスを列挙（type, payload_start, box_end）。"""
    off = start
    while off + 8 <= end:
        size, typ = struct.unpack(">I4s", buf[off:off + 8])
        hdr = 8
        if size == 1:
            if off + 16 > end:
                return
            size = struct.unpack(">Q", buf[off + 8:off + 16])[0]
            hdr = 16
        elif size == 0:
            size = end - off
        if size < hdr or off + size > end:
            return
        yield typ.decode("latin-1"), off + hdr, off + size
        off += size


def _child(buf, start, end, name):
    for t, a, b in _boxes(buf, start, end):
        if t == name:
            return a, b
    return None


def _video_entry(buf, a, b, fmt):
    """VisualSampleEntry（a=中身の先頭, b=終わり）から、形式名と判定を返す。"""
    out = {"vc": fmt}
    if a + 78 <= b:
        w, h = struct.unpack(">HH", buf[a + 24:a + 28])
        out["w"], out["h"] = w, h
    kids = (a + 78, b)
    if fmt in ("avc1", "avc3"):
        c = _child(buf, kids[0], kids[1], "avcC")
        prof = lvl = None
        if c and c[1] - c[0] >= 4:
            prof, lvl = buf[c[0] + 1], buf[c[0] + 3]
        out["name"] = "H.264" + (" %s" % (H264_OK.get(prof) or H264_NG.get(prof) or ("Extended" if prof == 88 else "profile %s" % prof))
                                 if prof else "")
        if lvl:
            out["name"] += " L%d.%d" % (lvl // 10, lvl % 10)
        if prof in H264_NG:
            out["v"], out["why"] = "bad", "Windows標準のH.264再生は8bit・4:2:0（High以下）まで。この形式は再生できない可能性が高い"
        elif prof and prof not in H264_OK:
            out["v"], out["why"] = "warn", "一般的でないH.264のプロファイル（%s）。会場PCで試写を" % (
                "Extended" if prof == 88 else prof)
        elif lvl and lvl > 51:
            out["v"], out["why"] = "warn", "Windows標準のH.264再生の対応はレベル5.1まで。試写で確認を"
    elif fmt in ("hvc1", "hev1", "dvh1", "dvhe"):
        out["name"] = "HEVC（H.265）" + (" Dolby Vision" if fmt.startswith("dvh") else "")
        out["v"], out["why"] = "bad", "Windowsは「HEVC拡張」が入っていないと再生できない（iPhone撮影の動画に多い）"
    elif fmt in PRORES:
        out["name"] = "Apple ProRes"
        out["v"], out["why"] = "bad", "Windowsでは再生できない（Macで書き出した動画に多い）"
    elif fmt == "av01":
        out["name"] = "AV1"
        out["v"], out["why"] = "warn", "Windowsに「AV1拡張」がないと再生できない場合がある"
    elif fmt in ("vp08", "vp09"):
        out["name"] = "VP8" if fmt == "vp08" else "VP9"
        out["v"], out["why"] = "warn", "MP4/MOV内のVPx。会場PCで試写を"
    elif fmt == "mp4v":
        out["name"] = "MPEG-4 Part 2"
    elif fmt in ("jpeg", "mjpa", "mjpb"):
        out["name"] = "Motion JPEG"
    elif fmt in ("h263", "s263"):
        out["name"] = "H.263"
    elif fmt in ("AVdn", "AVdh"):
        out["name"] = "Avid DNxHD/HR"
        out["v"], out["why"] = "bad", "Windows標準では再生できない"
    else:
        out["name"] = fmt.strip() or "不明"
        out["v"], out["why"] = "warn", "一般的でない形式（%s）。会場PCで試写を" % fmt.strip()
    if out.get("w") and out.get("h") and (out["w"] > 4096 or out["h"] > 2304) and not out.get("v"):
        out["v"], out["why"] = "warn", "解像度が大きい（%d×%d）。会場PCで試写を" % (out["w"], out["h"])
    return out


def _audio_entry(buf, a, b, fmt):
    if fmt == "mp4a":
        name = "AAC"
        c = _child(buf, a + 28, b, "esds")
        if c:
            body = buf[c[0] + 4:c[1]]
            i = body.find(b"\x04")
            while 0 <= i < len(body) - 2:
                j = i + 1
                while j < len(body) and body[j] & 0x80 and j - i < 4:
                    j += 1
                if j + 1 < len(body):
                    oti = body[j + 1]
                    if oti in (0x69, 0x6B):
                        name = "MP3"
                    break
                i = body.find(b"\x04", i + 1)
        return {"name": name}
    if fmt in ("lpcm", "sowt", "twos", "in24", "in32", "fl32", "fl64", "raw ", "ulaw", "alaw"):
        return {"name": "PCM"}
    if fmt == "alac":
        return {"name": "ALAC"}
    if fmt == ".mp3":
        return {"name": "MP3"}
    if fmt in ("ac-3", "ec-3"):
        return {"name": "Dolby Digital" + (" Plus" if fmt == "ec-3" else ""), "v": "warn",
                "why": "音声がDolby形式。音が出ない場合があるので試写を"}
    return {"name": fmt.strip() or "不明", "v": "warn", "why": "一般的でない音声形式（%s）。試写を" % fmt.strip()}


def _parse_moov(buf):
    vids, auds = [], []
    mv = _child(buf, 0, len(buf), "moov")
    if not mv:
        return vids, auds
    for t, a, b in _boxes(buf, mv[0], mv[1]):
        if t != "trak":
            continue
        md = _child(buf, a, b, "mdia")
        if not md:
            continue
        hd = _child(buf, md[0], md[1], "hdlr")
        handler = buf[hd[0] + 8:hd[0] + 12].decode("latin-1") if hd and hd[1] - hd[0] >= 12 else ""
        mi = _child(buf, md[0], md[1], "minf")
        st = mi and _child(buf, mi[0], mi[1], "stbl")
        sd = st and _child(buf, st[0], st[1], "stsd")
        if not sd or sd[1] - sd[0] < 16:
            continue
        e0 = sd[0] + 8
        esize, efmt = struct.unpack(">I4s", buf[e0:e0 + 8])
        efmt = efmt.decode("latin-1")
        ea, eb = e0 + 8, min(e0 + esize, sd[1])
        if handler == "vide":
            vids.append(_video_entry(buf, ea, eb, efmt))
        elif handler == "soun":
            auds.append(_audio_entry(buf, ea, eb, efmt))
    return vids, auds


def probe_video(reader, name):
    """動画の形式を判定して {container, video, audio, v(ok/warn/bad), why} を返す。"""
    head = reader.read_at(0, 16)
    if len(head) < 12:
        return {"container": "不明", "v": "warn", "why": "ファイルが短すぎます"}
    if head[:4] == b"RIFF" and head[8:12] == b"AVI ":
        return {"container": "AVI", "v": "warn", "why": "旧形式（AVI）。PowerPoint 2505以降は対応が限定的で、再生時に変換が入る。試写を"}
    if head[:16] == bytes.fromhex("3026b2758e66cf11a6d900aa0062ce6c"):
        return {"container": "WMV/ASF", "v": "warn", "why": "旧形式（WMV）。PowerPoint 2505以降は対応が限定的で、再生時に変換が入る。試写を"}
    if head[:4] in (b"\x00\x00\x01\xba", b"\x00\x00\x01\xb3"):
        return {"container": "MPEG-1/2", "v": "warn", "why": "旧形式（MPEG-2）。PowerPoint 2505以降は対応が限定的。試写を"}
    if head[:4] == b"\x1a\x45\xdf\xa3":
        return {"container": "WebM/MKV", "v": "warn", "why": "WebM/MKV。音声がVorbisなどだと拡張が必要。試写を"}
    typ = head[4:8]
    if typ not in (b"ftyp", b"moov", b"mdat", b"wide", b"free", b"skip", b"pnot", b"uuid"):
        return {"container": "不明", "v": "warn", "why": "動画の形式を判別できません。試写を"}
    container = "MOV" if (typ == b"ftyp" and head[8:12] == b"qt  ") or typ in (b"wide", b"pnot", b"mdat") \
        else ("MP4" if typ == b"ftyp" else "MP4/MOV")
    off, n = 0, 0
    while n < 10000:
        n += 1
        h = reader.read_at(off, 16)
        if len(h) < 8:
            break
        size, t = struct.unpack(">I4s", h[:8])
        if size == 1 and len(h) >= 16:
            size = struct.unpack(">Q", h[8:16])[0]
        elif size == 0:
            size = reader.size - off
        if size < 8:
            break
        if t == b"moov":
            if size > PROBE_MOOV_MAX:
                raise _ProbeStop("形式情報が大きすぎます")
            vids, auds = _parse_moov(reader.read_at(off, size))
            if not vids:
                return {"container": container, "v": "warn", "why": "映像トラックが見つかりません"}
            v = vids[0]
            out = {"container": container, "video": v["name"], "audio": auds[0]["name"] if auds else "なし"}
            if v.get("w"):
                out["res"] = "%d×%d" % (v["w"], v["h"])
            worst = [x for x in [v] + auds if x.get("v") == "bad"] or [x for x in [v] + auds if x.get("v") == "warn"]
            if worst:
                out["v"], out["why"] = worst[0]["v"], worst[0]["why"]
            else:
                out["v"] = "ok"
            return out
        off += size
    return {"container": container, "v": "warn", "why": "形式情報（moov）が見つかりません。試写を"}


def probe_zip_member(f, z, name, meter=None):
    info = z.getinfo(name)
    if info.flag_bits & 0x1:
        return {"container": "不明", "v": "warn", "why": "暗号化されています"}
    if info.compress_type == zipfile.ZIP_STORED:
        f.seek(info.header_offset)
        lh = f.read(30)
        if len(lh) < 30 or lh[:4] != b"PK\x03\x04":
            raise _ProbeStop("ZIPの構造が読めません")
        nlen, elen = struct.unpack("<HH", lh[26:30])
        return probe_video(_DirectReader(f, info.header_offset + 30 + nlen + elen, info.file_size, meter), name)
    with z.open(name) as fp:
        return probe_video(_SeqReader(fp, info.file_size, meter), name)


def probe_file(path, meter=None):
    """リンク動画（同じフォルダにある実ファイル）の形式。開き方は解析と同じ安全な読み取り専用。"""
    f = open_ro(path)
    try:
        st0 = os.fstat(f.fileno())
        r = probe_video(_DirectReader(f, 0, st0.st_size, meter), path)
        st1 = os.fstat(f.fileno())
        if (st0.st_size, st0.st_mtime_ns) != (st1.st_size, st1.st_mtime_ns):
            raise _ProbeStop("読み取り中に変更されました")
        return r
    finally:
        f.close()


def analyze_pptx(path, coi):
    def fail(msg, retry=False):
        return {"v": ANA_VERSION, "ok": False, "error": msg, "retry": retry}
    try:
        f = open_ro(path)
    except UnsafeOpen as e:
        return fail(str(e))
    except OSError as e:
        busy = getattr(e, "winerror", None) in (32, 33) or e.errno in (errno.EBUSY, errno.EAGAIN)
        return fail("開けません: " + _err(e), retry=busy or isinstance(e, (TimeoutError, ConnectionError)))
    try:
        st0 = os.fstat(f.fileno())
        try:
            z = zipfile.ZipFile(f)
        except zipfile.BadZipFile:
            f.seek(0)
            if f.read(8) == OLE_MAGIC:
                return fail("パスワード付き（暗号化）か、拡張子だけ変えた旧形式(.ppt)のため解析できません")
            return fail("PowerPointとして読めません（破損・コピー途中の可能性）", retry=True)
        with z:
            if len(z.infolist()) > 100000:
                return fail("ファイル内の部品が多すぎるため解析できません")
            res = _parse_pptx(z, path, coi, f)
        st1 = os.fstat(f.fileno())
        if (st0.st_size, st0.st_mtime_ns) != (st1.st_size, st1.st_mtime_ns):
            return fail("読み取り中にファイルが変更されました", retry=True)
        return res
    except (KeyError, ET.ParseError, ValueError, zipfile.BadZipFile, EOFError, RuntimeError,
            NotImplementedError, IndexError, zlib.error, lzma.LZMAError) as e:
        return fail("解析できません（ファイルが壊れている可能性）: %s" % e)
    except OSError as e:
        return fail("読み取りエラー: " + _err(e), retry=True)
    except Exception as e:      # 想定外でも「解析中」のまま止まらないように、結果として返す
        return fail("解析できません: %s: %s" % (type(e).__name__, e))
    finally:
        f.close()


def _parse_pptx(z, path, coi, f=None):
    names = set(z.namelist())
    budget = [200 * 1024 * 1024]

    def rd(name):
        info = z.getinfo(name)
        if info.file_size > 16 * 1024 * 1024:
            raise ValueError("XMLが大きすぎます: " + name)
        budget[0] -= info.file_size
        if budget[0] < 0:
            raise ValueError("XMLの合計が大きすぎます")
        return z.read(name)

    def rels_of(part):
        d, b = posixpath.split(part)
        rp = posixpath.join(d, "_rels", b + ".rels")
        if rp not in names:
            return []
        root = ET.fromstring(rd(rp))
        return [(r.get("Id"), r.get("Type") or "", r.get("Target") or "", r.get("TargetMode") or "")
                for r in root.iter("{%s}Relationship" % NS_PR)]

    pres_part = "ppt/presentation.xml"
    if pres_part not in names:
        for _i, typ, tgt, _m in rels_of(""):
            if typ.endswith("/officeDocument"):
                pres_part = _resolve("", tgt)
    pres = ET.fromstring(rd(pres_part))
    if pres.tag.startswith("{http://purl.oclc.org/ooxml/"):
        return {"v": ANA_VERSION, "ok": False,
                "error": "「Strict Open XML」形式のため解析できません（通常の .pptx で保存し直すと解析できます）"}
    pdir = posixpath.dirname(pres_part)
    prel = {}
    props_part = posixpath.join(pdir, "presProps.xml")
    for rid, typ, tgt, mode in rels_of(pres_part):
        prel[rid] = (typ, tgt, mode)
        if typ.endswith("/presProps"):
            props_part = _resolve(pdir, tgt)
    order = []
    lst = pres.find("{%s}sldIdLst" % NS_P)
    if lst is not None:
        for s in lst.findall("{%s}sldId" % NS_P):
            rid = s.get("{%s}id" % NS_R)
            if rid in prel:
                order.append(_resolve(pdir, prel[rid][1]))

    use_timings, loop, kiosk = True, False, False
    if props_part in names:
        sp = ET.fromstring(rd(props_part)).find("{%s}showPr" % NS_P)
        if sp is not None:
            use_timings = sp.get("useTimings", "1") not in ("0", "false")
            loop = sp.get("loop", "0") in ("1", "true")
            kiosk = sp.find("{%s}kiosk" % NS_P) is not None

    hidden, auto, noclick, coi_hits = [], [], [], []
    media, links, other = {}, {}, {}
    pptx_dir = os.path.dirname(path)
    for n, part in enumerate(order[:2000], 1):
        if part not in names:
            continue
        root = ET.fromstring(rd(part))
        if root.get("show") in ("0", "false"):
            hidden.append(n)
        tr = root.find(".//{%s}transition" % NS_P)
        if tr is not None:
            tm = tr.get("advTm")
            if tm:
                try:
                    auto.append([n, round(int(tm) / 1000.0, 1)])
                except ValueError:
                    pass
            if tr.get("advClick") in ("0", "false"):
                noclick.append(n)
        texts = slide_texts(root)
        sdir = posixpath.dirname(part)
        srels = rels_of(part)
        internal = {rid for rid, _t, _g, mode in srels if mode.lower() != "external"}
        # 動画・音声を埋め込んである図形では、a:videoFile などの「リンク」側は使われない
        # （PowerPoint 2010以降は p14:media の埋め込みを再生する）。そのリンクは外部動画として扱わない。
        unused_link = set()
        for pic in root.iter("{%s}pic" % NS_P):
            if any(el.get("{%s}embed" % NS_R) in internal for el in pic.iter("{%s}media" % NS_P14)):
                for tag in ("videoFile", "audioFile", "quickTimeFile", "wavAudioFile"):
                    for el in pic.iter("{%s}%s" % (NS_A, tag)):
                        unused_link.add(el.get("{%s}link" % NS_R))
        for rid, typ, tgt, mode in srels:
            t = typ.rsplit("/", 1)[-1]
            ext = mode.lower() == "external"
            if ext and tgt.strip().upper() in ("", "NULL"):
                continue   # 参照先が「NULL」のダミー（変換・編集ツールが残すことがある）。実体がないので無視
            if ext and rid in unused_link:
                continue
            if t in ("video", "media", "audio"):
                key = (tgt if ext else _resolve(sdir, tgt), ext)
                m = media.get(key)
                if m is None:
                    fname = unquote(tgt.replace("\\", "/")).rstrip("/").rsplit("/", 1)[-1]
                    av = t if t in ("video", "audio") else ("audio" if ext_of(fname) in AUDIO_EXTS else "video")
                    m = {"s": [], "name": fname, "av": av}
                    if ext:
                        st, disp, lp = _link_status(tgt, pptx_dir)
                        m.update(kind="online" if st == "online" else "link", st=st, target=disp)
                        if lp:
                            m["_lp"] = lp
                    else:
                        m.update(kind="embed", size=z.getinfo(key[0]).file_size if key[0] in names else None, _part=key[0])
                    media[key] = m
                elif t in ("video", "audio"):
                    m["av"] = t
                if n not in m["s"]:
                    m["s"].append(n)
            elif t == "hyperlink" and ext:
                e = links.setdefault(tgt, {"url": tgt, "s": []})
                if n not in e["s"]:
                    e["s"].append(n)
            elif ext:
                e = other.setdefault(tgt, {"type": t, "target": tgt, "s": []})
                if n not in e["s"]:
                    e["s"].append(n)
            elif t == "diagramData":   # SmartArt の文字
                dp = _resolve(sdir, tgt)
                if dp in names:
                    sa = ["".join(x.text or "" for x in p.iter(T_A_T)) for p in ET.fromstring(rd(dp)).iter(T_A_P)]
                    texts += sa + ["\n".join(x for x in sa if x.strip())]
        hit = _coi_find(coi, texts)
        if hit:
            coi_hits.append({"s": n, "kw": hit[0], "text": hit[1]})

    vids = [m for m in media.values() if m["av"] == "video"]
    auds = [m for m in media.values() if m["av"] == "audio"]
    # 動画の形式（会場PCで再生できるか）。見出しと形式情報だけを読む。失敗しても解析全体は止めない
    # 動画が何本あっても全部確認する。読む量の合計には上限があり、超えた分は「省略」と明示する。
    # 安く確認できるもの（無圧縮で埋め込まれた動画・リンク動画＝見出しと形式情報だけ読めばよい）を先に、
    # 圧縮されて埋め込まれた動画（前から順に読むしかない）を後にする
    def cost(m):
        if m["kind"] == "embed" and m.get("_part"):
            key = _resolve("", m["_part"])
            if key in names and z.getinfo(key).compress_type != zipfile.ZIP_STORED:
                return 1
        return 0
    meter = _Meter(PROBE_TOTAL_MAX)
    for m in sorted(vids[:VIDEO_LIST_MAX], key=cost):
        lp = m.pop("_lp", None)
        try:
            if m["kind"] == "embed" and f is not None:
                key = _resolve("", m.get("_part", "")) if m.get("_part") else None
                if key and key in names:
                    m["fmt"] = probe_zip_member(f, z, key, meter)
            elif lp and ext_of(lp) in VIDEO_EXTS:
                m["fmt"] = probe_file(lp, meter)
        except Exception as e:      # 1本の動画の確認に失敗しても、ほかの動画と解析全体は続ける
            m["fmt"] = {"container": "不明", "v": "unk", "why": "形式を確認できません（%s）" % (str(e) or type(e).__name__)}
    for m in list(media.values()):
        m.pop("_lp", None)
        m.pop("_part", None)
    return {"v": ANA_VERSION, "ok": True, "slides": len(order), "hidden": hidden[:1000],
            "video": vids[:VIDEO_LIST_MAX], "audio": auds[:VIDEO_LIST_MAX], "n_video": len(vids), "n_audio": len(auds),
            "links": list(links.values())[:80],
            "other": list(other.values())[:40], "coi": coi_hits[:10], "auto": auto[:2000],
            "noclick": noclick[:2000], "use_timings": use_timings, "loop": loop, "kiosk": kiosk,
            "n_links": len(links), "n_other": len(other)}


def ana_sum(r):
    if not r.get("ok"):
        return {"err": r.get("error") or "解析できません"}
    v = r["video"]
    return {"slides": r["slides"], "video": r.get("n_video", len(v)),
            "vlink": sum(1 for x in v if x["kind"] != "embed"),
            "vbad": sum(1 for x in v if x.get("st") in ("missing", "abs")),
            "vfbad": sum(1 for x in v if (x.get("fmt") or {}).get("v") == "bad"),
            "vfwarn": sum(1 for x in v if (x.get("fmt") or {}).get("v") == "warn"),
            "abad": sum(1 for x in (r.get("audio") or []) if x.get("kind") != "embed" and x.get("st") in ("missing", "abs")),
            "links": r.get("n_links", len(r["links"])), "other": r.get("n_other", len(r["other"])),
            "coi": bool(r["coi"]),
            "auto": len(r["auto"]) if r["use_timings"] else 0,
            "auto_off": len(r["auto"]) if not r["use_timings"] else 0,
            "noclick": len(r["noclick"]), "kiosk": bool(r["kiosk"])}


def ana_text(s):
    if s.get("err"):
        return "解析不可（%s）" % s["err"]
    parts = [
        "動画なし" if not s["video"] else "動画あり(%d%s)" % (s["video"], "・外部%d" % s["vlink"] if s["vlink"] else "")
        + ("・再生できない形式%d" % s["vfbad"] if s.get("vfbad") else "") + ("・形式要確認%d" % s["vfwarn"] if s.get("vfwarn") else "")
        + ("・音声リンク切れ%d" % s["abad"] if s.get("abad") else ""),
        "リンクなし" if not s["links"] else "リンクあり(%d)" % s["links"],
        "COIあり" if s["coi"] else "COIなし",
        "自動送りなし" if not s["auto"] else "自動送りあり(%d枚)" % s["auto"],
        "クリック無効あり(自動プレゼン)" if s["kiosk"] else ("クリック無効あり(%d枚)" % s["noclick"] if s["noclick"] else "クリック無効なし"),
    ]
    return " / ".join(parts)


def ana_warn(s):
    return bool(s.get("err") or s.get("vlink") or not s.get("coi") or s.get("noclick") or s.get("kiosk")
                or s.get("vfbad") or s.get("vfwarn") or s.get("abad"))


# ---------------------------------------------------------------- local storage
def json_bytes(obj):
    """JSONをUTF-8のバイト列に。ファイル名に不正な文字（Mac/Linuxの壊れた名前など）があっても落ちないように。"""
    try:
        return json.dumps(obj, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    except UnicodeEncodeError:
        return json.dumps(obj, ensure_ascii=True, separators=(",", ":")).encode("ascii")


class LocalStore:
    """設定・ログ・スナップショットはすべてローカルのデータフォルダへ。NAS配下には絶対に書かない。"""

    def __init__(self, data_dir):
        self.dir = data_dir
        self.roots = []
        self.lock = threading.Lock()

    def path(self, name):
        return os.path.join(self.dir, name)

    def guard(self, target):
        for r in self.roots:
            if is_under(target, r):
                raise RuntimeError("監視フォルダ配下への書き込みは禁止: %s" % target)

    def write_json(self, name, obj):
        p = self.path(name)
        self.guard(p)
        tmp = p + ".tmp"
        with self.lock:
            with open(tmp, "wb") as f:
                f.write(json_bytes(obj))
            os.replace(tmp, p)

    def read_json(self, name, default=None):
        try:
            with open(self.path(name), "r", encoding="utf-8") as f:
                return json.load(f)
        except (OSError, ValueError):
            return default

    def append_line(self, name, obj):
        p = self.path(name)
        self.guard(p)
        with self.lock:
            with open(p, "ab") as f:
                f.write(json_bytes(obj) + b"\n")


def is_remote_path(p):
    """ネットワーク上の場所（UNC・ネットワークドライブ）か。アプリの保存先をNAS上に作らないための確認。"""
    ap = os.path.abspath(p)
    if ap.startswith(("\\\\", "//")):
        return True
    if IS_WIN:
        try:
            import ctypes
            return ctypes.windll.kernel32.GetDriveTypeW(ap[:3]) == 4       # DRIVE_REMOTE
        except Exception:
            return False
    return False


OP_DEST_NAME = "講演資料"


def desktop_dir():
    """このPCのユーザーのデスクトップ（場所を移していても実際の場所）。"""
    if IS_WIN:
        try:
            import ctypes
            buf = ctypes.create_unicode_buffer(520)
            if ctypes.windll.shell32.SHGetFolderPathW(None, 0x10, None, 0, buf) == 0 and buf.value:   # CSIDL_DESKTOPDIRECTORY
                return buf.value
        except Exception:
            pass
    return os.path.join(os.path.expanduser("~"), "Desktop")


def default_op_dest():
    """発表PCのコピー先の初期値：デスクトップ\講演資料（無ければコピーのときに自動で作る）。"""
    return os.path.join(desktop_dir(), OP_DEST_NAME)


def data_dir_candidates(home_env, folder, hidden):
    """保存先の候補：exe の横（ネットワーク上なら使わない）→ ローカルのアプリ用フォルダ → ホーム。"""
    home = os.environ.get(home_env, "")
    here = home if home and os.path.isdir(home) else os.path.dirname(os.path.abspath(__file__))
    cands = []
    if not is_remote_path(here):
        cands.append(os.path.join(here, folder))
    la = os.environ.get("LOCALAPPDATA", "")
    if la and not is_remote_path(la):
        cands.append(os.path.join(la, "SEVENTHWELL", folder))
    cands.append(os.path.join(os.path.expanduser("~"), hidden))
    return cands


def carry_over_renamed(data_dir, home_env, folder, old_top):
    """アプリ名の変更（SW_NAS_* → PADDOCK_*）で展開先のフォルダ名が変わったとき、
    同じ場所にある前の名前のフォルダから設定・記録を引き継ぐ（初回だけ。前のフォルダは読むだけで変更しない）。
    戻り値: 引き継ぎ元のフォルダ or None"""
    if os.path.exists(os.path.join(data_dir, "config.json")):
        return None
    home = os.environ.get(home_env, "")
    if not home or not os.path.isdir(home):
        return None
    par = os.path.dirname(os.path.abspath(home))
    cands = []
    for base in (par, os.path.dirname(par)):
        if not base or is_remote_path(base):
            continue
        try:
            names = sorted(e.name for e in os.scandir(base) if e.is_dir() and e.name.upper().startswith(old_top))
        except OSError:
            continue
        for n in names[:20]:
            cands += [os.path.join(base, n, folder), os.path.join(base, n, old_top, folder)]
    found = []
    me = os.path.normcase(os.path.abspath(data_dir))
    for d in cands:
        try:
            if os.path.normcase(os.path.abspath(d)) != me:
                found.append((os.stat(os.path.join(d, "config.json")).st_mtime, d))
        except OSError:
            pass
    if not found:
        return None
    src = max(found)[1]
    for e in os.scandir(src):
        try:
            if e.is_file() and not e.name.startswith(".probe"):
                shutil.copy2(e.path, os.path.join(data_dir, e.name))
            elif e.is_dir():
                shutil.copytree(e.path, os.path.join(data_dir, e.name), dirs_exist_ok=True)
        except OSError:
            pass
    return src


def pick_data_dir():
    # PADDOCK_SCOUT.exe から起動したときは exe の横に保存する（ランチャーが場所を渡す）。
    # exe をNAS上に置いて起動した場合は、NASに書かないようローカルのアプリ用フォルダへ保存する
    cands = data_dir_candidates("SW_NAS_WATCH_HOME", "sw_nas_watch_data", ".sw_nas_watch")
    for d in cands:
        try:
            os.makedirs(d, exist_ok=True)
            probe = os.path.join(d, ".probe")
            with open(probe, "w") as f:
                f.write("ok")
            os.remove(probe)
            return d
        except OSError:
            continue
    raise SystemExit("データ保存先を作れません")


# ---------------------------------------------------------------- config
def startup_config(store, data_dir, raw):
    """起動時の設定の読み込み。問題があっても全部を初期化せず、問題のある監視フォルダだけ外す。
    元の設定ファイルは config.bad-日時.json として残す。戻り値: (cfg, 知らせる文 or None)"""
    try:
        return validate_cfg(raw or {}, data_dir), None
    except ValueError as e:
        first_err = str(e)
    bad = "config.bad-%s.json" % time.strftime("%Y%m%d-%H%M%S")
    try:
        store.write_json(bad, raw)
    except Exception:
        bad = ""
    raw = raw if isinstance(raw, dict) else {}
    keep, dropped = [], []
    for r in raw.get("roots") or []:
        try:
            validate_cfg(dict(raw, roots=[r], op={}), data_dir)
            keep.append(r)
        except (ValueError, TypeError, AttributeError):
            dropped.append(str(r.get("path") if isinstance(r, dict) else r))
    cfg = None
    for cand in (dict(raw, roots=keep), dict(raw, roots=keep, op={})):
        try:
            cfg = validate_cfg(cand, data_dir)
            break
        except (ValueError, TypeError, AttributeError):
            continue
    if cfg is None:
        cfg = validate_cfg({}, data_dir)
    msg = "設定ファイルに問題がありました（%s）。" % first_err
    if dropped:
        msg += "次の監視フォルダを外して起動します: %s。" % "、".join(dropped)
    if bad:
        msg += "元の設定は %s に残しています。" % bad
    return cfg, msg


def validate_cfg(raw, data_dir, old=None):
    old = old or DEFAULT_CFG
    cfg = json.loads(json.dumps(DEFAULT_CFG))
    if not isinstance(raw, dict):
        raise ValueError("設定の形式が不正です")
    roots = []
    seen_paths = set()
    raw_roots = raw.get("roots", old.get("roots", []))
    if raw_roots is None:
        raw_roots = []
    if not isinstance(raw_roots, list):
        raise ValueError("監視フォルダの設定の形式が不正です")
    for r in raw_roots:
        if not isinstance(r, dict):
            continue
        p = str(r.get("path", "")).strip().strip('"')
        if not p:
            continue
        if len(p) > 1024:
            raise ValueError("パスが長すぎます")
        k = norm_key(p)
        if k in seen_paths:
            raise ValueError("同じフォルダが2回登録されています: %s" % p)
        seen_paths.add(k)
        if is_under(data_dir, p):
            raise ValueError("このアプリの保存先を含むフォルダは監視できません: %s" % p)
        try:
            depth = int(r.get("depth", 3))
        except (TypeError, ValueError):
            depth = 3
        rid = str(r.get("id") or "")
        if not re.fullmatch(r"r[0-9a-f]{8}", rid) or any(x["id"] == rid for x in roots):
            rid = "r" + secrets.token_hex(4)      # 同じIDが2つあると、監視が二重に動いて止められなくなる
        roots.append({
            "id": rid,
            "path": p,
            "label": str(r.get("label") or "").strip()[:60],
            "depth": max(1, min(6, depth)),
            "enabled": bool(r.get("enabled", True)),
        })
    cfg["roots"] = roots

    def num(key, lo, hi):
        v = raw.get(key, old.get(key, DEFAULT_CFG[key]))
        try:
            v = float(v)
        except (TypeError, ValueError):
            v = DEFAULT_CFG[key]
        return max(lo, min(hi, v))

    cfg["poll_sec"] = num("poll_sec", 1, 60)
    cfg["settle_sec"] = num("settle_sec", 0, 300)
    cfg["max_depth"] = int(num("max_depth", 1, 40))
    cfg["max_entries"] = int(num("max_entries", 1000, 2000000))

    def strlist(key, limit):
        v = raw.get(key, old.get(key, DEFAULT_CFG[key]))
        if isinstance(v, str):
            v = v.splitlines()
        if not isinstance(v, (list, tuple)):
            v = DEFAULT_CFG[key]
        return [str(x).strip() for x in v if str(x).strip()][:limit]

    cfg["ignore"] = strlist("ignore", 300)
    cfg["coi_keywords"] = strlist("coi_keywords", 60)
    mv = raw.get("marks")
    if mv is None:
        mv = migrate_marks(raw) if ("mark_recv" in raw or "mark_got" in raw) else old.get("marks", DEFAULT_MARKS)
    marks, seen_mk = [], set()
    for x in (mv if isinstance(mv, list) else DEFAULT_MARKS):
        if isinstance(x, str):
            x = {"w": x}
        if not isinstance(x, dict):
            continue
        w = str(x.get("w", "")).strip()[:40]
        k = mark_norm(w)
        if not k or k in seen_mk:
            continue
        seen_mk.add(k)
        marks.append({"w": w, "role": x.get("role") if x.get("role") in MARK_ROLES else "info"})
    try:
        mver = int(raw.get("marks_v", old.get("marks_v", 1 if (raw.get("marks") or old.get("marks")) else MARKS_V)))
    except (TypeError, ValueError):
        mver = 1
    for v in range(mver + 1, MARKS_V + 1):    # 前の版で保存した設定にも、新しく増やした既定の目印を足す
        rc = MARKS_ROLE_CHANGED.get(v)
        if rc:
            ws = {mark_norm(w) for w in rc[0]}
            for m in marks:
                if mark_norm(m["w"]) in ws and m["role"] == rc[1]:
                    m["role"] = rc[2]
        for w in MARKS_ADDED.get(v, []):
            if mark_norm(w) not in seen_mk:
                seen_mk.add(mark_norm(w))
                marks.append({"w": w, "role": next((m["role"] for m in DEFAULT_MARKS if m["w"] == w), "info")})
    cfg["marks"] = marks[:100]
    cfg["marks_v"] = MARKS_V
    nt = raw.get("notify", old.get("notify", {}))
    nt = nt if isinstance(nt, dict) else {}
    cfg["notify"] = {k: bool(nt.get(k, True)) for k in NOTIFY_KINDS}
    ui = raw.get("ui", old.get("ui", {}))
    ui = ui if isinstance(ui, dict) else {}
    cfg["ui"] = {
        "sound": bool(ui.get("sound", True)),
        "click": ui.get("click") if ui.get("click") in ("app", "both") else "app",
        "sticky": bool(ui.get("sticky", False)),
        "os_open": bool(ui.get("os_open", False)),
    }
    if not cfg["ui"]["os_open"]:
        cfg["ui"]["click"] = "app"
    cfg["report_while_stopped"] = bool(raw.get("report_while_stopped", old.get("report_while_stopped", True)))
    cfg["analyze"] = bool(raw.get("analyze", old.get("analyze", True)))
    cfg["op"] = validate_op(raw.get("op", old.get("op", {})), roots, data_dir)
    return cfg


def unc_server(p):
    """\\\\server\\share\\… → server（小文字）。\\\\?\\UNC\\server\\… も同じ。ローカル（C:\\・\\\\?\\C:\\）は ""。"""
    x = str(p or "").replace("/", "\\")
    if x.lower().startswith("\\\\?\\unc\\"):
        x = "\\\\" + x[8:]
    elif x.startswith("\\\\?\\") or x.startswith("\\\\.\\"):
        return ""
    if not x.startswith("\\\\"):
        return ""
    return x[2:].split("\\")[0].lower()


def same_unc_host(a, b):
    ha = unc_server(a)
    return bool(ha) and ha == unc_server(b)


def validate_op(op, roots, data_dir):
    """会場オペレーターモードの設定。コピー先はNAS（監視フォルダ）の外だけ。"""
    op = op if isinstance(op, dict) else {}
    out = {"enabled": bool(op.get("enabled", False)), "root": "", "venue": "", "dests": [], "max_mbps": 0,
           "days": [], "day": "", "day_dir": bool(op.get("day_dir", True)), "dsub": ""}
    rid = str(op.get("root") or "")
    if any(r["id"] == rid for r in roots):
        out["root"] = rid
    elif len(roots) == 1:
        out["root"] = roots[0]["id"]          # 監視フォルダが1つだけなら、それを使う（保存前の新しいフォルダでも）
    venue = check_venue(op.get("venue"))
    # 日ごとに分かれている学会（学会 → DAY1 → 会場 …）：日ごとに「この日はこのフォルダ」を指定し、いまの日を選ぶ
    raw_days = op.get("days") or []
    if not isinstance(raw_days, list):
        raise ValueError("日ごとの設定の形式が不正です")
    names = set()
    for x in raw_days[:MAX_DAYS]:
        if not isinstance(x, dict):
            continue
        lab = str(x.get("label") or "").strip()[:40]
        v = check_venue(x.get("venue"))
        if not lab and not v:
            continue
        lab = lab or v.split("/")[0]
        if "/" not in v:
            raise ValueError("日ごとの会場：「%s」の会場を選んでください" % lab)
        if lab in names:
            raise ValueError("日の名前が重なっています: %s" % lab)
        names.add(lab)
        out["days"].append({"label": lab, "venue": v})
    if out["days"]:
        want = str(op.get("day") or "")
        if want and not any(x["label"] == want for x in out["days"]):
            raise ValueError("「いまの日」（%s）が日ごとの会場にありません" % want)
        cur = next((x for x in out["days"] if x["label"] == want), out["days"][0])
        out["day"] = cur["label"]
        venue = cur["venue"]
        if out["day_dir"]:
            out["dsub"] = safe_dirname(cur["label"])
    out["venue"] = venue
    try:
        out["max_mbps"] = max(0, min(1000, int(float(op.get("max_mbps") or 0))))
    except (TypeError, ValueError):
        out["max_mbps"] = 0
    raw_d = op.get("dests") or []
    if not isinstance(raw_d, list):
        raise ValueError("コピー先の設定の形式が不正です")
    seen = []
    for i, d in enumerate(raw_d):
        if not isinstance(d, dict):
            continue
        p = str(d.get("path", "")).strip().strip('"')
        if not p:
            continue
        if len(p) > 1024:
            raise ValueError("コピー先のパスが長すぎます")
        if len(out["dests"]) >= MAX_DESTS:
            raise ValueError("コピー先は%dか所までです" % MAX_DESTS)
        for r in roots:
            if overlaps(p, r["path"]):     # ネットワークドライブ（Z:）など別の書き方で同じNASを指していないかも確かめる
                raise ValueError("コピー先にNAS（監視フォルダ）の中や、監視フォルダを含む場所は指定できません: %s" % p)
            if same_unc_host(p, r["path"]):   # 同じNASの別の共有（\\NAS\backup など）にも書かない
                raise ValueError("コピー先に NAS（監視している学会フォルダと同じサーバー）は指定できません。このアプリは NAS に書き込みません: %s" % p)
        if overlaps(p, data_dir):
            raise ValueError("コピー先にこのアプリの保存先は指定できません: %s" % p)
        for q in seen:
            if is_under(p, q) or is_under(q, p):
                raise ValueError("コピー先が重なっています: %s / %s" % (q, p))
        seen.append(p)
        did = str(d.get("id") or "")
        if not re.fullmatch(r"d[0-9a-f]{8}", did):
            did = "d" + secrets.token_hex(4)
        out["dests"].append({"id": did, "path": p, "enabled": bool(d.get("enabled", True)),
                             "label": str(d.get("label") or "").strip()[:30] or ("コピー先%d" % (len(out["dests"]) + 1))})
    if out["enabled"]:
        if not out["root"]:
            raise ValueError("会場オペレーターモード: 監視フォルダを選んでください")
        if not any(d["enabled"] for d in out["dests"]):
            raise ValueError("会場オペレーターモード: コピー先を1つ以上設定してください")
    return out


MAX_DAYS = 10


def check_venue(v):
    """会場フォルダ（監視フォルダからの相対。日ごとに分かれているときは「DAY1/第1会場」のように2段まで）"""
    v = str(v or "").strip().replace("\\", "/").strip("/")
    if not v:
        return ""
    segs = v.split("/")
    if len(v) > 400 or len(segs) > 3 or any(not x.strip() or x in (".", "..") or ":" in x for x in segs):
        raise ValueError("会場フォルダ名が不正です: %s" % v)
    return "/".join(segs)


def safe_dirname(name):
    """コピー先に作る日のフォルダ名（Windowsで使えない文字は「_」に）"""
    t = re.sub(r'[\\/:*?"<>|\x00-\x1f]', "_", name).strip().rstrip(".")
    return t[:60] or "DAY"


def op_sub(op, rel):
    """NAS上の rel（監視フォルダからの相対）→ コピー先での相対パス（会場フォルダまでを除き、日のフォルダを前に付ける）"""
    prefix = (op["venue"] + "/") if op["venue"] else ""
    if prefix and not rel.startswith(prefix):
        sub = ""
    else:
        sub = rel[len(prefix):]
    ds = op.get("dsub") or ""
    return (ds + "/" + sub) if ds and sub else (ds or sub)


def unc_host(p):
    m = re.match(r"^[\\/]{2}([^\\/]+)", p or "")
    return m.group(1).lower() if m else ""


_DINGNUM = {}
for _base, _n0, _cnt in ((0x2776, 1, 10), (0x2780, 1, 10), (0x278A, 1, 10), (0x24EB, 11, 10), (0x24F5, 1, 10), (0x24FF, 0, 1)):
    for _i in range(_cnt):
        _DINGNUM[chr(_base + _i)] = str(_n0 + _i)


def nat_key(name):
    """画面と同じ並び（①〜⑳・全角数字などを数字に読み替え、数字は数値として比べる）。"""
    t = unicodedata.normalize("NFKC", str(name))
    t = "".join(_DINGNUM.get(c, c) for c in t).lower()
    return [(0, int(x), "") if x.isdigit() else (1, 0, x) for x in re.split(r"(\d+)", t) if x], str(name)


def default_label(path):
    p = path.rstrip("\\/")
    return re.split(r"[\\/]", p)[-1] or p


# ---------------------------------------------------------------- analyzer (background)
class Analyzer(threading.Thread):
    """PowerPoint解析。結果はローカルにキャッシュ（ファイルのサイズ+更新日時が同じなら読み直さない）。"""

    def __init__(self, mgr):
        super().__init__(daemon=True, name="analyzer")
        self.mgr = mgr
        self.lock = threading.Lock()
        self.cv = threading.Condition()
        self.q = deque()
        self.qset = set()
        self.cache = {}
        self.by_sig = {}
        self.dirty = False
        self.last_save = 0.0
        self.stop_ev = threading.Event()
        self.busy = {}          # PowerPointで開かれているため後回しにしているファイル
        self.last_cost = 0.0
        self.last_retry = time.time()
        self.cs = coi_signature(mgr.cfg["coi_keywords"])
        d = mgr.store.read_json("analysis.json") or {}
        if d.get("cs") == self.cs and d.get("v") == ANA_VERSION:
            for k, e in (d.get("entries") or {}).items():
                self.cache[k] = e
                self._index(k, e)

    def _index(self, k, e):
        self.by_sig[(k.split("|", 1)[0], e["sig"][0], e["sig"][1])] = k

    @staticmethod
    def key(w, rel):
        return w.snap_name + "|" + rel

    def get(self, w, rel, sig):
        e = self.cache.get(self.key(w, rel))
        if e and e["sig"][0] == sig[0] and e["sig"][1] == sig[1]:
            return e["res"]
        return None

    def _put(self, k, sig, res, cs=None):
        if cs is not None and cs != self.cs:
            return                  # 解析中にCOIの文字が変わった：古い設定での結果は使わない
        e = {"sig": [sig[0], sig[1]], "res": res, "at": time.time()}
        self.cache[k] = e
        if res.get("ok"):
            self._index(k, e)
        self.dirty = True

    @staticmethod
    def _has_links(res):
        return any(m.get("kind") != "embed" for m in (res.get("video") or []) + (res.get("audio") or []))

    def lookup(self, w, rel, sig):
        with self.lock:
            r = self.get(w, rel, sig)
            if r is not None:
                return r
            alt = self.by_sig.get((w.snap_name, sig[0], sig[1]))   # 名前変更・移動しただけなら再利用
            e = self.cache.get(alt) if alt else None
            if e and e["sig"][0] == sig[0] and e["sig"][1] == sig[1] and e["res"].get("ok"):
                r = e["res"]
                # リンク動画の有無はフォルダによって変わるので、別のフォルダへ移ったときは解析し直す
                if self._has_links(r) and parent_of(alt.split("|", 1)[1]) != parent_of(rel):
                    return None
                self._put(self.key(w, rel), sig, r)
                return r
        return None

    def recheck_links(self, w, group):
        """演者フォルダに変化があったとき、リンク動画・音声を含むPowerPointを解析し直す
        （PowerPointの後から動画が届いた・動画を差し替えた、などを反映するため）。"""
        pre = group + "/" if group else ""
        with self.lock:
            todo = []
            for k, e in list(self.cache.items()):
                kw, _, rel = k.partition("|")
                if kw == w.snap_name and rel.startswith(pre) and e["res"].get("ok") and self._has_links(e["res"]):
                    del self.cache[k]
                    todo.append(rel)
                    self.dirty = True
        com = w.committed or {}
        for rel in todo:
            sig = com.get(rel)
            if sig and sig != DIR:
                self.enqueue(w, rel, sig)

    def analyze_file(self, w, rel, sig, attempt=0):
        r = self.lookup(w, rel, sig)
        if r is not None:
            return r
        path = os.path.join(w.path, *rel.split("/"))
        k = self.key(w, rel)
        if in_use_by_office(path):
            self.busy[k] = time.time()
            self.enqueue(w, rel, sig, delay=60, attempt=attempt)
            return None
        self.busy.pop(k, None)
        t0 = time.monotonic()
        cs = self.cs
        res = analyze_pptx(path, self.mgr.coi)
        self.last_cost = time.monotonic() - t0
        if res.get("retry") and attempt < 3:
            self.enqueue(w, rel, sig, delay=5 * (attempt + 1), attempt=attempt + 1)
            return None
        transient = not res.get("ok") and (res.get("retry") or str(res.get("error", "")).startswith(("開けません", "読み取りエラー")))
        res.pop("retry", None)
        if transient:
            res["transient"] = True     # ネットワークの一時的な不調など：保存せず、あとで解析し直す
        res["sum"] = ana_sum(res)
        with self.lock:
            self._put(self.key(w, rel), sig, res, cs)
        return res

    def is_busy(self, w, rel):
        return self.key(w, rel) in self.busy

    def enqueue(self, w, rel, sig, delay=0.0, attempt=0):
        k = self.key(w, rel)
        with self.cv:
            if k in self.qset:
                # すでに待ち行列にある：新しい版なら差し替える（古い版のまま捨てられて解析されないのを防ぐ）
                for i, it in enumerate(self.q):
                    if it[0] is w and it[1] == rel and it[2] != tuple(sig):
                        self.q[i] = (w, rel, tuple(sig), it[3], it[4])
                        break
                return
            self.qset.add(k)
            self.q.append((w, rel, tuple(sig), time.time() + delay, attempt))
            self.cv.notify()

    def enqueue_all(self, w):
        com = w.committed or {}
        for rel, sig in list(com.items()):
            if sig == DIR or ana_kind(rel) != "pptx":
                continue
            r = self.get(w, rel, sig)
            if r is None or r.get("transient"):
                self.enqueue(w, rel, sig)

    def reset(self, cs):
        with self.lock:
            self.cache.clear()
            self.by_sig.clear()
            self.cs = cs
            self.dirty = True
        for w in list(self.mgr.watchers.values()):
            self.enqueue_all(w)

    def run(self):
        while not self.stop_ev.is_set():
            item = None
            with self.cv:
                if not self.q:
                    self.cv.wait(2.0)
                if self.q:
                    item = self.q.popleft()
            if item:
                w, rel, sig, not_before, attempt = item
                if not_before > time.time():
                    with self.cv:
                        self.q.append(item)
                    self.stop_ev.wait(0.3)
                    continue
                with self.cv:
                    self.qset.discard(self.key(w, rel))
                now_sig = (w.committed or {}).get(rel)
                if now_sig and now_sig != DIR and now_sig != sig and ana_kind(rel) == "pptx" and not w.stop_ev.is_set():
                    sig = tuple(now_sig)    # 待っている間に新しい版になった：新しい版を解析する
                if self.mgr.cfg["analyze"] and not w.stop_ev.is_set() and (w.committed or {}).get(rel) == sig:
                    try:
                        if self.analyze_file(w, rel, sig, attempt) is not None:
                            w.ver += 1
                            self.mgr.poke()
                    except Exception as e:
                        self.mgr.log("analyze error %s: %r" % (rel, e))
                    self.stop_ev.wait(max(0.3, self.last_cost * 3))   # NASを使う時間は最大でも1/4
                    self.last_cost = 0.0
            if self.dirty and time.time() - self.last_save > 10:
                self.save()
            if time.time() - self.last_retry > 300:
                self.last_retry = time.time()
                for w in list(self.mgr.watchers.values()):   # 一時的に読めなかったものを解析し直す
                    if w.online:
                        self.enqueue_all(w)
        self.save()

    def save(self):
        with self.lock:
            items = [(k, e) for k, e in self.cache.items() if not e["res"].get("transient")][-20000:]
            data = {"v": ANA_VERSION, "cs": self.cs, "entries": dict(items)}
            self.dirty = False
        try:
            self.mgr.store.write_json("analysis.json", data)
        except Exception as e:
            self.mgr.log("analysis save failed: %s" % e)
        self.last_save = time.time()


# ---------------------------------------------------------------- watcher
class Watcher(threading.Thread):
    def __init__(self, mgr, rc):
        super().__init__(daemon=True, name="watch-" + rc["id"])
        self.mgr = mgr
        self.id = rc["id"]
        self.path = rc["path"]
        self.label = rc["label"] or default_label(rc["path"])
        self.depth = rc["depth"]
        self.scope = mgr.op_scope(rc["id"])   # 会場オペレーターモードでは、その会場フォルダだけを見る
        self.stop_ev = threading.Event()
        self.lock = threading.Lock()
        self.committed = None
        self.current = {}
        self.pending = {}          # rel -> [sig, last_change, first_seen]
        self.notified_pending = set()
        self.recent = {}           # rel -> (op, ts)
        self.groups = []
        self.sdirs = []
        self.mk_gen = mgr.mk_gen
        self.online = None
        self.error = ""
        self.warns = []
        self.last_scan = 0.0
        self.scan_ms = 0
        self.scanning = False
        self.ver = 0
        self.rebaseline = False
        self.reignore = None       # 無視パターンを変えたとき：変更前のパターン（基準を作り直さずに差し替える）
        self.absorb = set()        # 最初の基準作りで読めなかったフォルダ。読めるようになったら通知せずに基準へ入れる
        self.fail_count = 0
        self.dirty = False
        self.last_save = 0.0
        self.snap_name = "snap_%s.json" % hashlib.sha1(norm_key(self.path).encode("utf-8")).hexdigest()[:16]
        self.saved = self._load_snapshot()

    def root_title(self):
        return "%s（%s）" % (self.label, "直下" if self.depth == 1 else "演者フォルダより上")

    # ---- snapshot (local)
    def _ignore_sig(self):
        key = "\n".join(sorted(self.mgr.cfg["ignore"])) + "\n#scope=" + (self.scope or "")
        return hashlib.sha1(key.encode("utf-8")).hexdigest()

    def _load_snapshot(self):
        d = self.mgr.store.read_json(self.snap_name)
        if not d or d.get("ignore_sig") != self._ignore_sig():
            return None
        snap = {}
        for row in d.get("entries", []):
            if len(row) == 2 and row[1] == DIR:
                snap[row[0]] = DIR
            elif len(row) == 3:
                snap[row[0]] = (int(row[1]), int(row[2]))
        return snap

    def save_snapshot(self):
        if self.committed is None:
            return
        with self.lock:
            rows = [[k, DIR] if v == DIR else [k, v[0], v[1]] for k, v in self.committed.items()]
        try:
            self.mgr.store.write_json(self.snap_name, {
                "path": self.path, "ignore_sig": self._ignore_sig(), "saved": time.time(), "entries": rows})
            self.dirty = False
            self.last_save = time.time()
        except Exception as e:
            self.mgr.log("snapshot save failed: %s" % e)

    # ---- loop
    def stop_now(self):
        self.stop_ev.set()

    def run(self):
        while not self.stop_ev.is_set():
            t0 = time.monotonic()
            try:
                self.step()
            except Exception as e:
                self.mgr.log("watcher %s error: %r" % (self.id, e))
            took = time.monotonic() - t0
            wait = max(0.3, self.mgr.cfg["poll_sec"] - took, took * 2)
            self.stop_ev.wait(wait)
        if self.dirty:
            self.save_snapshot()

    def _pend_sig(self):
        return frozenset((k, v[0]) for k, v in self.pending.items())

    def step(self):
        cfg = self.mgr.cfg
        now = time.time()
        t0 = time.monotonic()
        self.scanning = True
        cur, err, warns, failed = None, None, [], []
        try:
            cur, warns, failed = scan_tree(self.path, self.mgr.ignore_re, cfg["max_depth"], cfg["max_entries"],
                                           only=self.scope)
            ref = self.committed if self.committed is not None else self.saved
            if self.scope is not None and cur.get(self.scope) != DIR:
                err = "会場フォルダ「%s」が見つかりません" % self.scope
                cur = None
            elif not cur and ref and len(ref) >= 3 and not self.rebaseline:
                err = "フォルダが空に見えます（NAS未接続・未マウントの可能性）"
                cur = None
        except ScanTooLarge as e:
            err = str(e)
        except OSError as e:
            err = _err(e)
        finally:
            self.scanning = False
        self.scan_ms = int((time.monotonic() - t0) * 1000)
        self.last_scan = now
        if self.stop_ev.is_set():
            return
        if err:
            self.fail_count += 1
            if self.fail_count >= 2 or self.online is None:
                self._set_offline(err)
            return
        self.fail_count = 0
        self._set_online()

        # 一時的に読めなかったフォルダは、前の状態のままとみなす（消えた・新しく入ったと誤って知らせない）
        ref = self.committed if self.committed is not None else self.saved
        if failed and ref is not None:
            pre = tuple(f + "/" for f in failed)
            for k in [k for k in cur if k.startswith(pre)]:
                del cur[k]
            for k, v in ref.items():
                if k.startswith(pre):
                    cur[k] = v
        elif failed and ref is None:
            self.absorb.update(failed)          # 最初の基準：読めなかったところは、読めたときに基準へ入れる

        flag = False
        first = self.committed is None
        if first:
            if self.saved is not None and cfg["report_while_stopped"] and not self.rebaseline:
                self.committed = dict(self.saved)
                flag = True
            else:
                self.committed = dict(cur)
                self.dirty = True
            self.saved = None
        if self.rebaseline:
            with self.lock:
                self.committed = dict(cur)
                self.pending.clear()
                self.recent.clear()
                self.notified_pending = set()
            self.rebaseline = False
            self.dirty = True
            flag = False
            first = True
            self.absorb = set(failed)
        if self.absorb:
            ok = [a for a in self.absorb if a not in failed]
            if ok:
                pre = tuple(a + "/" for a in ok)
                with self.lock:
                    for k, v in cur.items():
                        if (k in ok or k.startswith(pre)) and k not in self.committed:
                            self.committed[k] = v
                self.absorb.difference_update(ok)
                self.dirty = True
        if self.reignore is not None:
            # 無視パターンの変更：新しく無視するものは基準から外し、無視しなくなったものは今の状態を基準に入れる。
            # 受信中のもの（pending）はそのまま続ける
            old_re, self.reignore = self.reignore[0], None
            new_re = self.mgr.ignore_re
            with self.lock:
                com = self.committed
                for k in [k for k in com if is_ignored(new_re, k)]:
                    del com[k]
                    self.pending.pop(k, None)
                for k, v in cur.items():
                    if k not in com and is_ignored(old_re, k):
                        com[k] = v
            self.dirty = True

        before = self._pend_sig()
        # 停止中に起きた変化は、次の確認（数秒後）で変わっていなければすぐ確定して「停止中の変化」として知らせる。
        # いま書き込み中かもしれないもの（更新日時が新しい・次の確認で変わった）は、普段どおり落ち着くのを待つ
        changes, quick_groups = self._process(cur, now, cfg["settle_sec"], quick=flag)
        events = self._make_events(changes, now, False, quick_groups) if changes else []
        incoming = self._incoming() if not flag else []
        mk_gen = self.mgr.mk_gen
        with self.lock:
            self.current = cur
            self.warns = warns[:100]
            self.groups = self._summarize(cur)
            self.sdirs = self._sessions(cur)
        if events or before != self._pend_sig() or mk_gen != self.mk_gen:
            self.mk_gen = mk_gen
            self.ver += 1
        if events or first or before != self._pend_sig():
            self.mgr.copier.kick()
        for inc in incoming:
            self.mgr.transient("incoming", inc)
        if events and cfg["analyze"]:
            for ev in events:   # 動画などが届いた・消えた → リンク動画のあるPowerPointの結果を作り直す
                g = ev.get("group")
                if g is not None and any(ana_kind(it.get("to") or it.get("path") or "") != "pptx" for it in ev.get("items", [])):
                    self.mgr.analyzer.recheck_links(self, g)
            self._attach_analysis(events)
        for ev in events:
            self.mgr.emit(ev)
        if first and cfg["analyze"]:
            self.mgr.analyzer.enqueue_all(self)
        if events:
            self.dirty = True
        if self.dirty and time.time() - self.last_save > 3:
            self.save_snapshot()
        self.mgr.poke()

    def _set_offline(self, err):
        was = self.online
        self.online = False
        if self.committed is None and not self.current and self.saved:
            # 起動したときに NAS が見えない：前回の一覧を出しておく（コピー先にある分は開けるように。コピーはしない）
            try:
                cur = dict(self.saved)
                with self.lock:
                    self.current = cur
                    self.groups = self._summarize(cur)
                    self.sdirs = self._sessions(cur)
                self.ver += 1
            except Exception as e:
                self.mgr.log("offline list failed: %r" % (e,))
        if err != self.error:
            self.ver += 1
        self.error = err
        if was is not False:
            self.ver += 1
            self.mgr.emit({"kind": "offline", "kinds": ["offline"], "root": self.id, "root_label": self.label,
                           "group": None, "where": "", "title": self.label, "summary": "接続できません",
                           "detail": err, "items": [], "n_items": 0, "while_stopped": False})
        self.mgr.poke()

    def _set_online(self):
        was = self.online
        self.online = True
        self.error = ""
        if was is not True:
            self.ver += 1
        if was is False:
            if self.mgr.cfg["analyze"] and self.committed is not None:
                self.mgr.analyzer.enqueue_all(self)     # 接続が切れていた間に失敗した解析をやり直す
            self.mgr.emit({"kind": "online", "kinds": ["online"], "root": self.id, "root_label": self.label,
                           "group": None, "where": "", "title": self.label, "summary": "接続が復帰しました",
                           "detail": self.path, "items": [], "n_items": 0, "while_stopped": False})

    # ---- diff / settle
    QUICK_SETTLE = 1.0

    def _process(self, cur, now, settle, quick=False):
        com = self.committed
        changed = set(k for k, v in cur.items() if com.get(k) != v)
        changed.update(k for k in com if k not in cur)
        with self.lock:
            for k in list(self.pending):
                if k not in changed:
                    del self.pending[k]
            for k in changed:
                sig = cur.get(k)
                p = self.pending.get(k)
                if p is None:
                    # 起動直後に見つかった「停止中の変化」：更新日時が古いものは次の確認で変わらなければすぐ確定する
                    q = bool(quick) and (sig is None or sig == DIR or now - sig[1] / 1e9 >= settle + 2)
                    self.pending[k] = [sig, now, now, q]
                elif p[0] != sig:
                    p[0] = sig
                    p[1] = now
                    if len(p) > 3:
                        p[3] = False          # まだ変わり続けている＝書き込み中
            if not self.pending:
                return {}, set()
            groups = {}
            for k, (sig, _t, _f, *_q) in self.pending.items():
                g = unit_of(k, sig if sig is not None else com.get(k), self.depth)
                groups.setdefault(g, []).append(k)
            ready = {}
            def need(k):
                p = self.pending[k]
                return self.QUICK_SETTLE if len(p) > 3 and p[3] else settle
            for g, keys in groups.items():
                quiet = all(now - self.pending[k][1] >= need(k) for k in keys)
                if quiet:
                    ready[g] = keys
                elif now - min(self.pending[k][2] for k in keys) >= MAX_GROUP_WAIT:
                    rk = [k for k in keys if now - self.pending[k][1] >= need(k)]
                    if rk:
                        ready[g] = rk
            changes = {}
            quick_groups = set()
            notq = set()
            for u, keys in ready.items():
                for k in keys:
                    p = self.pending.pop(k)
                    new = p[0]
                    old = com.get(k)
                    g = group_of(k, new if new is not None else old, self.depth)
                    changes.setdefault(g, []).append((k, old, new))
                    if not (len(p) > 3 and p[3]):
                        notq.add(g)
                    if new is None:
                        com.pop(k, None)
                    else:
                        com[k] = new
            quick_groups = set(changes) - notq
        return changes, quick_groups

    def _incoming(self):
        """コピーが始まった（まだ確定していない）フォルダを、確定を待たずに知らせる。"""
        com = self.committed
        groups = {}
        mo = self.mgr.marker_of
        with self.lock:
            for k, (sig, _t, _f, *_q) in self.pending.items():
                old = com.get(k)
                if mo(k, sig if sig is not None else old):
                    continue      # 目印画像（受付済・動画有 など）の出し入れは「受信中」にしない
                g = group_of(k, sig if sig is not None else old, self.depth)
                groups.setdefault(g, []).append((k, old, sig))
        new = [g for g in groups if g not in self.notified_pending]
        self.notified_pending = set(groups)
        out = []
        for g in new:
            items = groups[g]
            adds = [k for k, o, n in items if o is None and n not in (None, DIR)]
            mods = [k for k, o, n in items if o not in (None, DIR) and n not in (None, DIR)]
            dels = [k for k, o, n in items if n is None and o not in (None, DIR)]
            new_folder = bool(g) and any(k == g and o is None and n == DIR for k, o, n in items)
            if adds or mods:
                summary = "受信中 %d件（NASへの書き込み完了を待っています）" % (len(adds) + len(mods))
            elif dels:
                summary = "削除を確認中 %d件" % len(dels)
            else:
                summary = "フォルダの変化を確認中"
            if new_folder:
                summary = "新しい演者フォルダ・" + summary
            names = [base(k) for k in sorted(adds + mods + dels)]
            detail = "、".join(names[:3]) + (" ほか%d件" % (len(names) - 3) if len(names) > 3 else "")
            out.append({"root": self.id, "root_label": self.label, "group": g,
                        "where": parent_of(g) if g else "", "title": base(g) if g else self.root_title(),
                        "summary": summary, "detail": detail})
        return out

    def _attach_analysis(self, events):
        """確定したPowerPointをその場で解析し、通知に結果を載せる（時間がかかる分は後回し）。"""
        an = self.mgr.analyzer
        limit = time.monotonic() + SYNC_ANALYSIS_BUDGET
        for ev in events:
            g = ev.get("group") or ""
            prefix = g + "/" if g else ""
            out = []
            for it in ev.get("items", []):
                if it["op"] not in ("add", "mod", "rename"):
                    continue
                sub = it["to"] if it["op"] == "rename" else it["path"]
                rel = prefix + sub
                kind = ana_kind(rel)
                if kind == "key":
                    out.append({"file": sub, "na": "Keynoteは解析対象外"})
                    continue
                if kind == "ppt":
                    out.append({"file": sub, "na": "旧形式(.ppt)は解析対象外"})
                    continue
                if kind != "pptx":
                    continue
                sig = self.committed.get(rel)
                if not sig or sig == DIR:
                    continue
                res = None
                if time.monotonic() < limit:
                    try:
                        res = an.analyze_file(self, rel, sig)
                    except Exception as e:
                        self.mgr.log("analyze error %s: %r" % (rel, e))
                else:
                    an.enqueue(self, rel, sig)
                if res:
                    s = res["sum"]
                    out.append({"file": sub, "text": ana_text(s), "warn": ana_warn(s), "sum": s})
                elif an.is_busy(self, rel):
                    out.append({"file": sub, "na": "PowerPointで開かれているため解析は後で行います"})
                else:
                    out.append({"file": sub, "pending": True})
            if out:
                ev["ana"] = out[:10]

    def _content_sig(self, g, ch, old_side):
        out = []
        for rel, old, new in ch:
            if rel == g:
                continue
            s = old if old_side else new
            if s is None:
                return None
            out.append((rel[len(g) + 1:], s if s == DIR else tuple(s)))
        return tuple(sorted(out, key=lambda x: x[0]))

    def _make_events(self, changes, now, flag, stopped_groups=()):
        evs = []
        dels, news = {}, {}
        for g, ch in changes.items():
            if not g:
                continue
            for rel, old, new in ch:
                if rel == g and old == DIR and new is None:
                    dels[g] = self._content_sig(g, ch, True)
                elif rel == g and old is None and new == DIR:
                    news[g] = self._content_sig(g, ch, False)
        used = set()
        for dg, dsig in dels.items():
            if dsig is None:
                continue
            # 中身が同じフォルダが複数あるときは、同じ名前（移動）→ 同じ親（名前変更）の順に組み合わせる
            cands = sorted(news.items(), key=lambda x: (base(x[0]) != base(dg), parent_of(x[0]) != parent_of(dg), x[0]))
            for ng, nsig in cands:
                if ng in used or nsig is None or dsig != nsig:
                    continue
                if not dsig and parent_of(dg) != parent_of(ng):
                    continue
                used.add(ng)
                nfiles = sum(1 for x in nsig if x[1] != DIR)
                frm = base(dg) if parent_of(dg) == parent_of(ng) else dg
                evs.append(self._ev("folder_rename", ["folder_rename"], ng, base(ng),
                                    "フォルダ名変更", "%s → %s" % (frm, base(ng)) + (" (%dファイル)" % nfiles if nfiles else ""),
                                    [{"op": "folder_rename", "path": dg, "to": ng}], flag or (dg in stopped_groups and ng in stopped_groups),
                                    {"from_group": dg}))
                for rel in list(self.recent):
                    if rel == dg or rel.startswith(dg + "/"):
                        op, ts = self.recent.pop(rel)
                        self.recent[ng + rel[len(dg):]] = (op, ts)
                changes.pop(dg, None)
                changes.pop(ng, None)
                break
        for g, ch in changes.items():
            ev = self._group_event(g, ch, now, flag or g in stopped_groups)
            if ev:
                evs.append(ev)
        cut = now - RECENT_KEEP
        for rel in [r for r, (_o, ts) in self.recent.items() if ts < cut]:
            del self.recent[rel]
        return evs

    def _group_event(self, g, ch, now, flag):
        adds, mods, dels, dadd, ddel = [], [], [], [], []
        new_folder = del_folder = False
        for rel, old, new in ch:
            if g and rel == g:
                if old is None and new == DIR:
                    new_folder = True
                elif old == DIR and new is None:
                    del_folder = True
                continue
            sub = rel[len(g) + 1:] if g else rel
            if old == DIR and new == DIR:
                continue
            if old == DIR:
                ddel.append(sub)
                old = None
            if new == DIR:
                dadd.append(sub)
                new = None
            if old is None and new is None:
                continue
            if old is None:
                adds.append([sub, new])
            elif new is None:
                dels.append([sub, old])
            else:
                mods.append([sub, old, new])
        renames = []
        if dels and adds:
            remaining = list(adds)
            for d in list(dels):
                cand = [a for a in remaining if tuple(a[1]) == tuple(d[1])]
                if not cand:
                    continue
                same = [a for a in cand if parent_of(a[0]) == parent_of(d[0])]
                a = (same or cand)[0]
                renames.append([d[0], a[0], a[1]])
                remaining.remove(a)
                dels.remove(d)
            adds = remaining

        kinds = []
        if new_folder:
            kinds.append("folder_new")
        if del_folder:
            kinds.append("folder_del")
        if adds or (dadd and not new_folder):
            kinds.append("add")
        if mods:
            kinds.append("mod")
        if renames:
            kinds.append("rename")
        if (dels or ddel) and not del_folder:
            kinds.append("del")
        if not kinds:
            return None

        prefix = (g + "/") if g else ""
        for sub, _s in adds:
            self.recent[prefix + sub] = ("add", now)
        for sub, _o, _n in mods:
            self.recent[prefix + sub] = ("mod", now)
        for _f, t, _s in renames:
            self.recent[prefix + t] = ("ren", now)
        for sub, _s in dels:
            self.recent.pop(prefix + sub, None)

        items = []
        items += [{"op": "dir_add", "path": s} for s in sorted(dadd)]
        items += [{"op": "add", "path": s, "size": sig[0]} for s, sig in sorted(adds)]
        items += [{"op": "mod", "path": s, "size": n[0], "old_size": o[0]} for s, o, n in sorted(mods)]
        items += [{"op": "rename", "path": f, "to": t, "size": sig[0]} for f, t, sig in sorted(renames)]
        items += [{"op": "del", "path": s, "size": sig[0]} for s, sig in sorted(dels)]
        items += [{"op": "dir_del", "path": s} for s in sorted(ddel)]

        mo = self.mgr.marker_of
        mk_add = [m for m in (mo(prefix + sub, sig) for sub, sig in adds) if m]
        parts = []
        if mk_add:
            rs = {m[0] for m in mk_add}
            for r, txt in (("drop", "演題取り下げ"), ("done", "発表終了"), ("got", "会場取得済"), ("recv", "受付済（目印）"), ("direct", "会場直")):
                if r in rs:
                    parts.append(txt)
            lab = sorted({(m[2], m[1]) for m in mk_add if m[0] in ("warn", "op", "info")})
            if lab:
                parts.append("目印 " + "・".join(x[1] for x in lab[:4]) + (" ほか%d" % (len(lab) - 4) if len(lab) > 4 else ""))
        if new_folder:
            parts.append("新しい演者フォルダ")
        if del_folder:
            parts.append("フォルダ削除")
        if adds:
            parts.append("追加 %d" % len(adds))
        if dadd and not new_folder:
            parts.append("フォルダ追加 %d" % len(dadd))
        if mods:
            parts.append("更新 %d" % len(mods))
        if renames:
            parts.append("名前変更 %d" % len(renames))
        if dels and not del_folder:
            parts.append("削除 %d" % len(dels))
        if ddel and not del_folder:
            parts.append("フォルダ削除 %d" % len(ddel))
        show = (lambda x: x) if not g else base   # 上位フォルダの変化はパスごと見せる
        if del_folder:
            detail = ("%dファイルを含む" % len(dels)) if dels else ""
        else:
            names = [show(x[0]) for x in sorted(adds)] + [show(x[0]) for x in sorted(mods)] + \
                    ["%s→%s" % (base(f), base(t)) for f, t, _s in renames] + [show(x[0]) for x in sorted(dels)]
            if not names:
                names = [show(x) for x in sorted(dadd + ddel)]
            detail = "、".join(names[:3]) + (" ほか%d件" % (len(names) - 3) if len(names) > 3 else "")
        title = base(g) if g else self.root_title()
        extra = None
        if g and (adds or mods or renames or dels):
            # 受付・差し替えの判定用：この変化の前後の「データ」の数（目印は除く）と、パワーポイントの数
            pre = g + "/"
            now_data = [k for k, v in self.committed.items() if v != DIR and k.startswith(pre) and not mo(k, v)]
            isd = lambda sub, sig: not mo(prefix + sub, sig)
            isp = lambda sub: ext_of(base(sub)) in PPT_CAT_EXTS
            fa = len(now_data)
            fb = fa - sum(1 for sub, sig in adds if isd(sub, sig)) + sum(1 for sub, sig in dels if isd(sub, sig))
            pa = sum(1 for k in now_data if isp(k))
            pb = pa - sum(1 for sub, _s in adds if isp(sub)) + sum(1 for sub, _s in dels if isp(sub)) \
                - sum(1 for f, t, _s in renames if isp(t) and not isp(f)) + sum(1 for f, t, _s in renames if isp(f) and not isp(t))
            # 差し替え＝新しいパワーポイントが入った・中身が変わったときだけ（名前変更・移動・削除は数えない）
            pchg = any(isp(x[0]) for x in adds) or any(isp(x[0]) for x in mods)
            extra = {"fchg": True, "fa": fa, "fb": fb, "pchg": bool(pchg), "pa": pa, "pb": pb}
        return self._ev(kinds[0], kinds, g, title, " / ".join(parts), detail, items, flag, extra)

    def _ev(self, kind, kinds, g, title, summary, detail, items, flag, extra=None):
        ev = {"kind": kind, "kinds": kinds, "root": self.id, "root_label": self.label, "group": g,
              "where": parent_of(g) if g else "", "title": title, "summary": summary, "detail": detail,
              "items": items[:300], "n_items": len(items), "while_stopped": bool(flag)}
        if extra:
            ev.update(extra)
        return ev

    # ---- views
    def _sessions(self, cur):
        """セッションのフォルダ（演者フォルダの1つ上）と、そこに直接置かれたファイル。
        演者フォルダがまだ無いセッションも一覧に出せるように、またセッション直下の発表ファイルも開けるように。"""
        if self.depth < 2:
            return []
        out = {}
        for k, sig in cur.items():
            n = k.count("/") + 1
            if n == self.depth - 1 and sig == DIR:
                out.setdefault(k, [])
            elif n == self.depth and sig != DIR:
                parent = k.rsplit("/", 1)[0]
                if self.mgr.marker_of(k, sig) or (file_cat(k) == "他" and not _NOTE_SLOT.match(k.rsplit("/", 1)[1])):
                    continue
                out.setdefault(parent, []).append([k.rsplit("/", 1)[1], sig[0], sig[1] / 1e9])
        pend = {}
        for k in self.pending:     # NASへ受信中のセッション直下のファイル（開けるのは受信が終わってから）
            if k.count("/") + 1 == self.depth and k.rsplit("/", 1)[0] in out:
                pend.setdefault(k.rsplit("/", 1)[0], []).append(k.rsplit("/", 1)[1])
        return [dict({"key": k, "loose": sorted(v)}, **({"pend": sorted(pend[k])} if k in pend else {}))
                for k, v in sorted(out.items())]

    def _summarize(self, cur):
        g = {}

        def new_sum(key):
            return {"key": key, "files": 0, "dirs": 0, "size": 0, "mtime": 0, "pending": 0, "cats": {}, "px": []}

        for k, sig in cur.items():
            key = group_of(k, sig, self.depth)
            s = g.get(key)
            if s is None:
                s = g[key] = new_sum(key)
            if k == key:
                continue
            if sig == DIR:
                s["dirs"] += 1
            else:
                mk = self.mgr.marker_of(k, sig)
                if mk:   # 目印（受付済・会場取得・動画有 など）はデータとして数えない
                    if mk[0] in MARK_STATUS_ROLES:
                        s["mk_" + mk[0]] = 1
                    if mk[0] in MARK_CHIP_ROLES:
                        s.setdefault("fl", {})[mk[1]] = (mk[2], mk[0])
                    continue
                s["files"] += 1
                s["size"] += sig[0]
                if sig[1] > s["mtime"]:
                    s["mtime"] = sig[1]
                c = file_cat(k)
                s["cats"][c] = s["cats"].get(c, 0) + 1
                if ana_kind(k):
                    s["px"].append((k, sig))
        for k, (sig, _t, _f, *_q) in self.pending.items():
            s0 = sig if sig is not None else (self.committed or {}).get(k)
            if self.mgr.marker_of(k, s0):
                continue          # 目印画像の出し入れでは「コピー中」にしない
            key = group_of(k, s0, self.depth)
            if key in g:
                s = g[key]
                s["pending"] += 1
                if sig is not None and sig != DIR:
                    s["pbytes"] = s.get("pbytes", 0) + sig[0]   # 受信中のファイルの今のサイズ（進み具合の表示用）
                s["pstart"] = min(s.get("pstart", _f), _f)
        out = []
        for key, s in g.items():
            if key == "" and s["files"] == 0 and s["pending"] == 0:
                continue
            s["mtime"] = s["mtime"] / 1e9 if s["mtime"] else 0
            if "fl" in s:
                s["fl"] = [[lb, r] for lb, (_i, r) in sorted(s["fl"].items(), key=lambda x: x[1][0])]
            out.append(s)
        return out

    def status(self):
        return {"online": self.online, "error": self.error, "last_scan": self.last_scan,
                "scan_ms": self.scan_ms, "scanning": self.scanning, "count": len(self.current),
                "pending": len(self.pending), "warns": self.warns[:20], "n_warns": len(self.warns)}

    def folder(self, group, analyzer, analyze_on):
        with self.lock:
            cur = self.current
            pend = dict(self.pending)
            recent = dict(self.recent)
        prefix = group + "/" if group else ""
        items = []
        for k, sig in cur.items():
            if group:
                if not k.startswith(prefix):
                    continue
                rel = k[len(prefix):]
            else:
                if group_of(k, sig, self.depth) != "":
                    continue
                rel = k
            it = {"p": rel, "d": sig == DIR}
            if sig != DIR:
                mk = self.mgr.marker_of(k, sig)
                if mk:
                    it["mk"], it["ml"] = mk[0], mk[1]
                it["s"] = sig[0]
                it["m"] = sig[1] / 1e9
                it["c"] = file_cat(rel)
                kind = ana_kind(rel)
                if kind and analyze_on:
                    if kind == "key":
                        it["a"] = {"na": "Keynoteは解析対象外"}
                    elif kind == "ppt":
                        it["a"] = {"na": "旧形式(.ppt)は解析対象外"}
                    elif k in pend:
                        it["a"] = {"pending": True, "copying": True}
                    else:
                        res = analyzer.get(self, k, sig)
                        it["a"] = res if res is not None else {"pending": True, "inuse": analyzer.is_busy(self, k)}
            if k in pend:
                it["st"] = "pending"
            elif k in recent:
                it["st"], it["ct"] = recent[k]
            items.append(it)
            if len(items) >= 5000:
                break
        return items


# ---------------------------------------------------------------- 会場オペレーターモード（コピー）
CP_ORDER = ["err", "off", "busy", "copying", "todo", "wait", "srcbusy", "old", "edited", "ok"]
CP_PROBLEM = {"err", "off", "busy", "srcbusy", "edited"}


def long_path(p):
    """Windowsで260文字を超えるパスでも読み書きできるようにする（コピー処理だけで使う）。"""
    if not IS_WIN or len(p) < 240 or p.startswith("\\\\?\\"):
        return p
    p = os.path.normpath(p)        # 「/」区切りのままだと \\?\ 付きのパスとして無効になる
    if p.startswith("\\\\"):
        return "\\\\?\\UNC\\" + p[2:]
    return "\\\\?\\" + os.path.abspath(p)


def _bg_io_priority():
    """コピー用スレッドを「バックグラウンド優先度」にする（Windows）。PC上の再生・操作を邪魔しにくくする。"""
    if not IS_WIN:
        return
    try:
        import ctypes
        from ctypes import wintypes
        k32 = ctypes.WinDLL("kernel32")
        k32.GetCurrentThread.restype = wintypes.HANDLE
        k32.SetThreadPriority.argtypes = [wintypes.HANDLE, ctypes.c_int]
        k32.SetThreadPriority(k32.GetCurrentThread(), 0x00010000)   # THREAD_MODE_BACKGROUND_BEGIN
    except Exception:
        pass


def _hide(path):
    """コピー途中の一時ファイルを隠しファイルにする（Windows。オペレーターの目に触れないように）。"""
    if not IS_WIN:
        return
    try:
        import ctypes
        ctypes.WinDLL("kernel32").SetFileAttributesW(long_path(path), 0x2)   # FILE_ATTRIBUTE_HIDDEN
    except Exception:
        pass


def _unhide(path):
    """隠し属性を外す。Windowsでは名前を変えても属性はそのまま残るので、隠しにした一時ファイルを
    本来の名前に置き換える直前と直後に必ず呼ぶ（呼ばないと、置いたファイルが隠しファイルになってしまう）。"""
    if not IS_WIN:
        return
    try:
        import ctypes
        from ctypes import wintypes
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        k32.GetFileAttributesW.argtypes = [wintypes.LPCWSTR]
        k32.GetFileAttributesW.restype = wintypes.DWORD
        k32.SetFileAttributesW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD]
        k32.SetFileAttributesW.restype = wintypes.BOOL
        p = long_path(path)
        a = k32.GetFileAttributesW(p)
        if a != 0xFFFFFFFF and a & 0x2:
            k32.SetFileAttributesW(p, (a & ~0x2) or 0x80)   # 0x80 = FILE_ATTRIBUTE_NORMAL
    except Exception:
        pass


def _canon(p):
    try:
        return os.path.realpath(p)
    except (OSError, ValueError):
        return p


def overlaps(a, b):
    """a と b が同じ場所か、どちらかがもう一方の中にあるか。書き方の違い（ネットワークドライブ Z: と \\\\NAS\\share、
    シンボリックリンクなど）も、実在する部分を stat して確かめる（読むだけ・書き込みはしない）。"""
    if is_under(a, b) or is_under(b, a):
        return True
    ca, cb = _canon(a), _canon(b)
    if is_under(ca, cb) or is_under(cb, ca):
        return True

    def anc_hits(child, parent):
        try:
            sp = os.stat(parent)
        except OSError:
            return False
        x = child
        for _ in range(64):
            try:
                sx = os.stat(x)
                if sx.st_ino and sp.st_ino and os.path.samestat(sx, sp):
                    return True
            except OSError:
                pass
            nx = os.path.dirname(x.rstrip("\\/"))
            if not nx or nx == x:
                break
            x = nx
        return False
    return anc_hits(a, b) or anc_hits(b, a)


def dest_locked(path):
    """（Windows）コピー先のファイルを他のアプリ（動画プレーヤー・PDFビューアなど）が開いていて、置き換えられない状態か。
    「削除」の権限で開けるかを試して、すぐ閉じるだけ（読み書きはしない）。NASのファイルには使わない。"""
    if not IS_WIN:
        return False
    try:
        import ctypes
        from ctypes import wintypes
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        fn = k32.CreateFileW
        fn.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, ctypes.c_void_p,
                       wintypes.DWORD, wintypes.DWORD, wintypes.HANDLE]
        fn.restype = wintypes.HANDLE
        k32.CloseHandle.argtypes = [wintypes.HANDLE]
        h = fn(long_path(path), 0x00010000, 0x7, None, 3, 0x80, None)   # DELETE / 共有すべて許可 / OPEN_EXISTING
        if h is None or h == ctypes.c_void_p(-1).value:
            return ctypes.get_last_error() in (32, 33)                  # 共有違反＝ほかのアプリが開いている
        k32.CloseHandle(h)
        return False
    except Exception:
        return False


class Copier(threading.Thread):
    """会場オペレーターモード：受信が完了した演者フォルダを、コピー先（メインPC・バックアップPCなど）へコピーする。
    ・NASは読むだけ。Windowsでは他の人の読み取り・上書き・削除・名前変更を妨げない開き方で読む。NASには何も書かない。
    ・受信中（確定していない）の演者フォルダはコピーしない。NAS上で開かれているファイルにも触れない。
    ・コピー先へは一時ファイルに書いてから置き換える（書きかけのファイルが見えない）。内容はハッシュで照合する。
    ・コピー先で開かれているファイル（発表中など）は上書きしない。閉じられてから差し替える。
    ・上書きする前の版はコピー先の「_差し替え前」へ退避する。コピー先のファイルを消すことはない。
    ・コピー先で誰かが編集したファイルは、NAS側が更新されない限り上書きしない。"""

    def __init__(self, mgr):
        super().__init__(daemon=True, name="copier")
        self.mgr = mgr
        self.stop_ev = threading.Event()
        self.wake = threading.Event()
        self.lock = threading.Lock()
        self.ver = 0
        self.gen = 0
        self.dest = {}          # did -> {"online": bool|None, "error": str}
        self.fst = {}           # did -> {rel: [state, msg]}
        self.gagg = {}          # did -> {group: state}
        self.pagg = {}          # did -> {group: 発表ファイルのうち いちばん良い状態}
        self.man = {}           # did -> {rel: [src_size, src_mtime_ns, dst_size, dst_mtime_ns, copied_at]}
        self.mnames = {}
        self.man_dirty = set()
        self.cleaned = set()
        self.active = None
        self.queue_n = 0
        self.last_sig = None
        self.last_full = 0.0
        self.last_save = 0.0
        self.last_prog = 0.0
        self.touched = {}       # group -> set(rel)  今回コピーを試みたファイル（完了の知らせ用）
        self.alias_cache = {}   # コピー先がNASの別名でないかの確認結果
        self.backoff = {}       # (did, rel) -> [NAS側の版, 次に試す時刻, 待ち秒数]  失敗したコピーをすぐ繰り返さない
        self.reported = {}      # group -> 最後に知らせた内容（同じ内容を何度も知らせない）
        self.depth = 3

    # ---- control
    def kick(self):
        self.wake.set()

    def reconfigure(self):
        self.gen += 1
        self.last_sig = None
        self.wake.set()

    def stop_now(self):
        self.stop_ev.set()
        self.wake.set()

    def _bump(self):
        self.ver += 1
        self.mgr.poke()

    def run(self):
        _bg_io_priority()
        while not self.stop_ev.is_set():
            self.wake.wait(5.0)
            self.wake.clear()
            if self.stop_ev.is_set():
                break
            try:
                self.cycle()
            except Exception as e:
                self.mgr.log("copier error: %r" % e)
            if self.man_dirty and time.time() - self.last_save > 5:
                self.save()
        self.save()

    # ---- manifest (local)
    def _mname(self, op, d):
        rpath = next((r["path"] for r in self.mgr.cfg["roots"] if r["id"] == op["root"]), "")
        key = "%s|%s|%s" % (norm_key(d["path"]), norm_key(rpath) if rpath else "", op["venue"])
        return "copy_%s.json" % hashlib.sha1(key.encode("utf-8")).hexdigest()[:16]

    def _sync_dests(self, op, dests):
        want = {d["id"]: d for d in dests}
        with self.lock:
            for did in [x for x in self.mnames if x not in want]:
                if did in self.man_dirty:
                    self._save_one(did)
                for dct in (self.man, self.mnames, self.fst, self.gagg, self.pagg, self.dest):
                    dct.pop(did, None)
                self.man_dirty.discard(did)
            for did, d in want.items():
                name = self._mname(op, d)
                if self.mnames.get(did) != name:
                    if did in self.man_dirty:
                        self._save_one(did)
                    data = self.mgr.store.read_json(name) or {}
                    ent = data.get("entries") if isinstance(data.get("entries"), dict) else {}
                    self.man[did] = {k: v for k, v in ent.items() if isinstance(v, list) and len(v) == 5}
                    self.mnames[did] = name
                    self.fst[did] = {}
                    self.gagg[did] = {}
                    self.pagg[did] = {}
                    self.dest[did] = {"online": None, "error": ""}
                    self.man_dirty.discard(did)

    def _save_one(self, did):
        try:
            self.mgr.store.write_json(self.mnames[did], {"saved": time.time(), "entries": self.man.get(did, {})})
        except Exception as e:
            self.mgr.log("copy manifest save failed: %s" % e)

    def save(self):
        with self.lock:
            for did in list(self.man_dirty):
                if did in self.mnames:
                    self._save_one(did)
            self.man_dirty.clear()
        self.last_save = time.time()

    # ---- helpers
    def _dpath(self, root, prefix, rel):
        sub = rel[len(prefix):]
        ds = getattr(self, "dsub", "")
        if ds:
            sub = ds + "/" + sub if sub else ds
        return os.path.join(root, *sub.split("/"))

    def _dest_is_nas(self, dpath, roots):
        key = (dpath, tuple(roots))
        v = self.alias_cache.get(key)
        if v is None or time.time() - v[1] > 300:
            v = (any(overlaps(dpath, r) for r in roots), time.time())
            self.alias_cache[key] = v
        return v[0]

    def _set(self, did, rel, state, msg=""):
        with self.lock:
            self.fst.setdefault(did, {})[rel] = [state, msg]

    def _dest_online(self, d):
        did, p = d["id"], d["path"]
        err = ""
        roots = [r["path"] for r in self.mgr.cfg.get("roots") or []]
        try:
            if self._dest_is_nas(p, roots) or any(same_unc_host(p, r) for r in roots):   # NAS（監視フォルダと同じサーバー）には、フォルダも作らない
                raise OSError("コピー先が NAS（監視フォルダ）の中を指しています。コピーしません")
            os.makedirs(long_path(p), exist_ok=True)
            if not os.path.isdir(long_path(p)):
                err = "フォルダではありません"
        except OSError as e:
            err = _err(e)
        st = self.dest.setdefault(did, {"online": None, "error": ""})
        was = st["online"]
        st["online"], st["error"] = (not err), err
        if err and was is not False:
            self.mgr.emit({"kind": "copy_err", "kinds": ["copy_err"], "root": self.mgr.cfg["op"]["root"],
                           "root_label": d["label"], "group": None, "where": "", "title": d["label"],
                           "summary": "コピー先に接続できません（つながったら自動でコピーします）",
                           "detail": "%s: %s" % (p, err), "items": [], "n_items": 0, "while_stopped": False, "sys": True})
        elif not err and was is False:
            self.mgr.log("COPY  %s に再接続しました: %s" % (d["label"], p))
        if not err and did not in self.cleaned:
            self.cleaned.add(did)
            self._clean_tmp(p)
        return not err

    def _clean_tmp(self, root):
        """前回の異常終了（コピー中にウィンドウを閉じた等）で残った一時ファイル（.swnw_xxxx.part）だけを片付ける。
        コピー先の中だけ。書き込み中なら更新日時が新しいので、2分以上前のものに限る。"""
        pat = re.compile(r"^%s[0-9a-f]{12}\.part$" % re.escape(TMP_PREFIX))
        cut = time.time() - 120
        n = 0
        for dp, dns, fns in os.walk(long_path(root)):
            dns[:] = [x for x in dns if x != OP_OLD_DIR]
            for fn in fns:
                if pat.match(fn):
                    fp = os.path.join(dp, fn)
                    try:
                        if os.stat(fp).st_mtime < cut:
                            os.remove(fp)
                    except OSError:
                        pass
            n += 1
            if n > 20000:
                break

    def _need(self, did, root, prefix, rel, sig):
        dp = self._dpath(root, prefix, rel)
        m = self.man.get(did, {}).get(rel)
        try:
            st = os.stat(long_path(dp))
        except FileNotFoundError:
            st = None
        except OSError as e:
            return ["err", _err(e)]
        if st is not None and not os.path.isfile(long_path(dp)):
            return ["err", "コピー先に同じ名前のフォルダがあります"]
        tol = 2_000_000_000
        if m and m[0] == sig[0] and m[1] == sig[1]:
            if st is None:
                return ["todo", "コピー先にないため、もう一度コピーします"]
            if st.st_size == m[2] and abs(st.st_mtime_ns - m[3]) <= tol:
                return ["ok", ""]
            return ["edited", "コピー先で変更されています（NAS側が更新されない限り上書きしません）"]
        if st is not None and st.st_size == sig[0] and abs(st.st_mtime_ns - sig[1]) <= tol:
            with self.lock:   # 同じファイルが既にある（手作業でコピー済みなど）→ そのまま使う
                self.man.setdefault(did, {})[rel] = [sig[0], sig[1], st.st_size, st.st_mtime_ns, time.time()]
                self.man_dirty.add(did)
            return ["ok", ""]
        return ["todo", ""]

    def _aggregate(self, files):
        agg, pagg = {}, {}
        with self.lock:
            for did, fs in self.fst.items():
                a, pa = {}, {}
                for rel, fsig in files.items():
                    if self.mgr.marker_of(rel, fsig):   # 目印・付帯情報のコピーの状態は、演者の状態に入れない
                        continue
                    s = (fs.get(rel) or ["todo"])[0]
                    g = group_of(rel, (0, 0), self.depth)
                    cur = a.get(g)
                    if cur is None or CP_ORDER.index(s) < CP_ORDER.index(cur):
                        a[g] = s
                    if rel.lower().endswith(PRES_OPEN_EXT):   # 発表ファイルだけの状態（大きな動画のコピー中でもスライドは開けるように）
                        if s not in ("ok", "edited", "old", "off") and rel in (self.man.get(did) or {}):
                            s = "old"   # 新しい版はまだだが、前にコピーした版がこのPCにある → 開ける
                        cur = pa.get(g)
                        if cur is None or CP_ORDER.index(s) > CP_ORDER.index(cur):   # どれか1つでも開ければ開ける
                            pa[g] = s
                agg[did] = a
                pagg[did] = pa
            self.gagg = agg
            self.pagg = pagg

    # ---- main cycle
    def cycle(self):
        op = self.mgr.cfg["op"]
        gen = self.gen
        if not op["enabled"]:
            if self.fst or self.dest:
                with self.lock:
                    self.fst, self.gagg, self.pagg, self.dest = {}, {}, {}, {}
                    self.man, self.mnames = {}, {}
                self.active = None
                self._bump()
            return
        dests = [d for d in op["dests"] if d["enabled"]]
        self._sync_dests(op, dests)
        w = self.mgr.watchers.get(op["root"])
        if not w or w.committed is None or w.online is not True:
            return
        self.depth = w.depth
        prefix = (op["venue"] + "/") if op["venue"] else ""
        self.dsub = op.get("dsub") or ""
        with w.lock:
            com = dict(w.committed)
            pend = list(w.pending.items())
        mko = self.mgr.marker_of
        # 目印・付帯情報（受付済.jpg・system-info など）の出し入れでは「受信中」にしない（受付が目印を置いても、開けなくならないように）
        pend_groups = set(unit_of(k, s if s is not None else com.get(k), w.depth) for k, (s, _t, _f, *_q) in pend
                          if not mko(k, s if s is not None else com.get(k)))
        files, dirs = {}, []
        for rel, sig in com.items():
            if prefix and not rel.startswith(prefix):
                continue
            if sig == DIR:
                dirs.append(rel)
            else:
                files[rel] = sig
        with self.lock:
            outstanding = any(st[0] != "ok" and st[0] != "edited" for fs in self.fst.values() for st in fs.values()) \
                or any(not x.get("online") for x in self.dest.values())
        sig_now = (gen, hash(frozenset(files.items())), frozenset(pend_groups),
                   tuple((d["id"], d["path"]) for d in dests))
        if sig_now == self.last_sig and not outstanding and time.time() - self.last_full < 60:
            return
        self.last_sig = sig_now
        self.last_full = time.time()

        work = {}
        for d in dests:
            did = d["id"]
            if not self._dest_online(d):
                with self.lock:
                    self.fst[did] = {rel: ["off", self.dest[did]["error"]] for rel in files}
                continue
            for rel in dirs:   # 演者フォルダなどのフォルダ構成もコピー先に作る（受信中のものは除く）
                if rel[len(prefix):] and group_of(rel, DIR, w.depth) not in pend_groups:
                    try:
                        os.makedirs(long_path(self._dpath(d["path"], prefix, rel)), exist_ok=True)
                    except OSError:
                        pass
            new = {}
            for rel, sig in files.items():
                if unit_of(rel, sig, w.depth) in pend_groups:
                    # 受信中の演者：もうコピー済みのファイルはそのまま開けるように（会場が開けなくならないように）。
                    # 差し替え中のファイルも、コピー先に前の版があれば「前の版」として開ける。コピーは受信が終わってから
                    st = self._need(did, d["path"], prefix, rel, sig)
                    if st[0] in ("ok", "edited"):
                        new[rel] = st
                    elif rel in (self.man.get(did) or {}) and os.path.isfile(long_path(self._dpath(d["path"], prefix, rel))):
                        new[rel] = ["old", "NASで新しい版を受信中です（いまは前の版。受信が終わったら差し替えます）"]
                    else:
                        new[rel] = ["wait", "NASへの受信が終わるのを待っています"]
                    continue
                st = self._need(did, d["path"], prefix, rel, sig)
                if st[0] == "todo":
                    bo = self.backoff.get((did, rel))
                    if bo and bo[0] == sig and time.time() < bo[1]:
                        # 直前に失敗した（コピー先で使用中など）。NASからの読み直しを繰り返さないよう、少し待ってから
                        prev = (self.fst.get(did) or {}).get(rel)
                        st = prev if prev and prev[0] in ("busy", "err") else ["busy", "少し待ってから、もう一度コピーします"]
                    else:
                        work.setdefault(rel, []).append(did)
                new[rel] = st
            with self.lock:
                self.fst[did] = new
        self._aggregate(files)
        self._bump()
        for key in [k for k, v in self.backoff.items() if files.get(k[1]) != v[0]]:
            del self.backoff[key]

        gnew = {}
        for rel, sig in files.items():
            g = group_of(rel, sig, w.depth)
            gnew[g] = max(gnew.get(g, 0), sig[1])
        order = sorted(work, key=lambda r: (-gnew[group_of(r, files[r], w.depth)], files[r][0], r))
        self.queue_n = len(order)
        for rel in order:
            if self.stop_ev.is_set() or self.gen != gen or not self.mgr.cfg["op"]["enabled"]:
                break
            with w.lock:
                cur = (w.committed or {}).get(rel)
                g = unit_of(rel, files[rel], w.depth)
                busy_g = any(unit_of(k, s if s is not None else w.committed.get(k), w.depth) == g
                             and not self.mgr.marker_of(k, s if s is not None else w.committed.get(k))   # 目印の出し入れは待たない
                             for k, (s, _t, _f, *_q) in w.pending.items())
            if cur != files[rel] or busy_g:
                for did in work[rel]:
                    self._set(did, rel, "wait", "NASへの受信が終わるのを待っています")
                self.queue_n -= 1
                continue
            try:
                self._copy(w, op, prefix, rel, files[rel], [d for d in dests if d["id"] in work[rel]], gen)
            except Exception as e:   # 1つのファイルの失敗で、ほかのファイルのコピーを止めない
                self.active = None
                for did in work[rel]:
                    self._set(did, rel, "err", "コピーに失敗しました（あとで再試行）: " + _err(e))
            now = time.time()
            for did in work[rel]:
                st0 = ((self.fst.get(did) or {}).get(rel) or ["todo"])[0]
                key = (did, rel)
                if st0 in ("busy", "err"):
                    bo = self.backoff.get(key)
                    delay = min(300, bo[2] * 2) if bo and bo[0] == files[rel] else 30
                    self.backoff[key] = [files[rel], now + delay, delay]
                else:
                    self.backoff.pop(key, None)
            self.queue_n -= 1
            self._aggregate(files)
            self._bump()
        self.queue_n = 0
        self._aggregate(files)
        self._report(w, op, prefix, files, dests)
        self._bump()

    # ---- copy one file to one or more destinations (NASからは1回だけ読む)
    def _copy(self, w, op, prefix, rel, sig, dlist, gen):
        src = os.path.join(w.path, *rel.split("/"))
        g = group_of(rel, sig, w.depth)
        if in_use_by_office(src):
            for d in dlist:
                self._set(d["id"], rel, "srcbusy", "NAS上で開かれているため、閉じられてからコピーします")
            return
        self.touched.setdefault(g, set()).add(rel)
        roots = [r["path"] for r in self.mgr.cfg["roots"]]
        targets = []
        vol_need = {}
        for d in dlist:
            did = d["id"]
            dp = self._dpath(d["path"], prefix, rel)
            if any(is_under(dp, r) for r in roots) or self._dest_is_nas(d["path"], roots):
                self._set(did, rel, "err", "NAS（監視フォルダ）の中には書き込みません")
                continue
            if in_use_by_office(dp):
                self._set(did, rel, "busy", "コピー先で開かれているため、閉じられてから差し替えます")
                continue
            if dest_locked(dp):      # 動画プレーヤー・PDFビューアなどで開かれている（NASを読む前に確かめる）
                self._set(did, rel, "busy", "コピー先でほかのアプリが開いているため、閉じられてから差し替えます")
                continue
            try:
                ddir = os.path.dirname(dp)
                os.makedirs(long_path(ddir), exist_ok=True)
                try:
                    old_size = os.stat(long_path(dp)).st_size     # 旧版を「_差し替え前」に残す分も要る
                except OSError:
                    old_size = 0
                try:
                    vol = os.stat(long_path(ddir)).st_dev
                except OSError:
                    vol = ddir
                vol_need[vol] = vol_need.get(vol, 0) + sig[0] + old_size
                free = shutil.disk_usage(long_path(ddir)).free
                need = vol_need[vol] + 64 * 1024 * 1024
                if free < need:
                    vol_need[vol] -= sig[0] + old_size
                    raise OSError(errno.ENOSPC, "空き容量が足りません（必要 %.1fGB / 空き %.1fGB）"
                                  % (need / 1e9, free / 1e9))
                tmp = os.path.join(ddir, TMP_PREFIX + secrets.token_hex(6) + ".part")
                f = open(long_path(tmp), "xb")
                _hide(tmp)
            except OSError as e:
                self._set(did, rel, "err", "コピー先に書き込めません: " + _err(e))
                continue
            targets.append({"d": d, "dp": dp, "tmp": tmp, "f": f, "err": None})
            self._set(did, rel, "copying", "")
        if not targets:
            return
        self.active = {"rel": rel, "dests": [t["d"]["id"] for t in targets], "done": 0, "total": sig[0]}
        self._bump()
        h = hashlib.sha256()
        n = 0
        abort = None
        limit = op["max_mbps"] * 1024 * 1024
        t0 = time.monotonic()
        try:
            try:
                fsrc = open_ro(long_path(src))
            except (OSError, UnsafeOpen) as e:
                abort = ["todo", "NAS上のファイルを読めません（あとで再試行）: " + _err(e)]
            else:
                with fsrc:
                    while True:
                        if self.stop_ev.is_set() or self.gen != gen:
                            abort = ["todo", "中断しました（あとで再開します）"]
                            break
                        try:
                            b = fsrc.read(COPY_CHUNK)
                        except OSError as e:   # NAS が途中で切れた・読めなくなった：このファイルだけあとで再試行
                            abort = ["err", "NAS上のファイルを読めませんでした（あとで再試行）: " + _err(e)]
                            break
                        if not b:
                            break
                        h.update(b)
                        n += len(b)
                        for t in targets:
                            if t["err"] is None:
                                try:
                                    t["f"].write(b)
                                except OSError as e:
                                    t["err"] = _err(e)
                        if all(t["err"] for t in targets):
                            break
                        self.active["done"] = n
                        now = time.monotonic()
                        if now - self.last_prog > 1.0:
                            self.last_prog = now
                            self._bump()
                        if limit:
                            ahead = n / limit - (now - t0)
                            if ahead > 0:
                                self.stop_ev.wait(min(ahead, 5))
            if abort is None and not all(t["err"] for t in targets):
                try:
                    st = os.stat(long_path(src))
                    now_sig = (st.st_size, st.st_mtime_ns)
                except OSError:
                    now_sig = None
                if now_sig != (sig[0], sig[1]) or n != sig[0]:
                    abort = ["wait", "コピー中にNAS側のファイルが変わったため、受信完了後にやり直します"]
            digest = h.digest()
            for t in targets:
                did = t["d"]["id"]
                try:
                    if t["err"] is None:
                        t["f"].flush()
                        os.fsync(t["f"].fileno())
                except OSError as e:
                    t["err"] = _err(e)
                try:
                    t["f"].close()
                except OSError as e:
                    t["err"] = t["err"] or _err(e)
                if abort:
                    self._set(did, rel, abort[0], abort[1])
                    continue
                if t["err"]:
                    self._set(did, rel, "err", "コピー先に書き込めません: " + t["err"])
                    continue
                try:
                    if self._hash(t["tmp"]) != digest:
                        self._set(did, rel, "err", "書き込んだ内容が元のファイルと一致しません（コピー先の障害の可能性）")
                        continue
                except OSError as e:
                    self._set(did, rel, "err", "書き込んだファイルを確認できません: " + _err(e))
                    continue
                if in_use_by_office(t["dp"]):
                    self._set(did, rel, "busy", "コピー先で開かれているため、閉じられてから差し替えます")
                    continue
                try:
                    self._replace(t, prefix, rel, sig)
                except PermissionError as e:
                    self._set(did, rel, "busy", "コピー先で使用中のため、あとで差し替えます（%s）" % _err(e))
                except OSError as e:
                    self._set(did, rel, "err", "コピー先に置けません: " + _err(e))
        finally:
            for t in targets:
                try:
                    t["f"].close()
                except OSError:
                    pass
                try:
                    if os.path.exists(long_path(t["tmp"])):
                        os.remove(long_path(t["tmp"]))
                except OSError:
                    pass
            self.active = None

    @staticmethod
    def _hash(path):
        h = hashlib.sha256()
        with open(long_path(path), "rb") as f:
            while True:
                b = f.read(COPY_CHUNK)
                if not b:
                    break
                h.update(b)
        return h.digest()

    @staticmethod
    def _plain_copy(src, dst):
        """コピー先の中での複製（旧版の退避用）。OSの特殊なコピー機能は使わず、読んで書くだけ。"""
        st = os.stat(long_path(src))
        # 途中で止まっても（アプリの終了・電源断）壊れた旧版が残らないよう、隠しの一時ファイルに書いてから名前を付ける
        tmp = os.path.join(os.path.dirname(dst), ".swnw_bk_%s.part" % secrets.token_hex(4))
        try:
            with open(long_path(src), "rb") as fi, open(long_path(tmp), "xb") as fo:
                while True:
                    b = fi.read(COPY_CHUNK)
                    if not b:
                        break
                    fo.write(b)
            os.utime(long_path(tmp), ns=(st.st_atime_ns, st.st_mtime_ns))
            if os.path.exists(long_path(dst)):
                raise FileExistsError(errno.EEXIST, "already exists", dst)
            os.rename(long_path(tmp), long_path(dst))
        except OSError:
            try:
                os.remove(long_path(tmp))
            except OSError:
                pass
            raise

    def _replace(self, t, prefix, rel, sig):
        d, dp = t["d"], t["dp"]
        did = d["id"]
        backup = None
        if os.path.exists(long_path(dp)):
            # 置き換える直前まで元のファイルはそのまま。旧版は「_差し替え前」に複製してから差し替える
            backup = os.path.join(d["path"], OP_OLD_DIR, time.strftime("%Y%m%d-%H%M%S"),
                                  *os.path.relpath(dp, d["path"]).replace("\\", "/").split("/"))
            if os.path.exists(long_path(backup)):
                base_, ext_ = os.path.splitext(backup)
                backup = "%s_%s%s" % (base_, secrets.token_hex(2), ext_)
            os.makedirs(long_path(os.path.dirname(backup)), exist_ok=True)
            self._plain_copy(dp, backup)
        try:
            _unhide(t["tmp"])
            os.replace(long_path(t["tmp"]), long_path(dp))
            _unhide(dp)
        except OSError:
            if backup:
                try:
                    os.remove(long_path(backup))
                except OSError:
                    pass
                # 置き換えられなかったときは、作った「_差し替え前\日時\…」の空フォルダも片付ける
                stop = os.path.normcase(os.path.join(d["path"], OP_OLD_DIR))
                x = os.path.dirname(backup)
                while os.path.normcase(x) != stop and len(x) > len(stop):
                    try:
                        os.rmdir(long_path(x))
                    except OSError:
                        break
                    x = os.path.dirname(x)
            raise
        try:
            os.utime(long_path(dp), ns=(time.time_ns(), sig[1]))   # 更新日時はNAS上の元ファイルに合わせる
        except OSError:
            pass
        st = os.stat(long_path(dp))
        with self.lock:
            self.man.setdefault(did, {})[rel] = [sig[0], sig[1], st.st_size, st.st_mtime_ns, time.time()]
            self.man_dirty.add(did)
            self.fst.setdefault(did, {})[rel] = ["ok", "差し替え（旧版は %s に退避）" % OP_OLD_DIR if backup else ""]
        self.mgr.log("COPY  %s → %s%s" % (rel, d["label"], "（旧版を退避）" if backup else ""))

    # ---- 知らせ（演者フォルダごとに1回）
    def _report(self, w, op, prefix, files, dests):
        labels = {d["id"]: d["label"] for d in dests}
        for g in list(self.touched):
            rels = [r for r in self.touched[g] if r in files]
            if not rels:
                self.touched.pop(g, None)
                continue
            with self.lock:
                states = {did: [self.fst.get(did, {}).get(r, ["todo", ""]) for r in rels] for did in labels}
            if any(s[0] in ("todo", "copying") for ss in states.values() for s in ss):
                continue   # まだ途中（次の周回で知らせる）
            self.touched.pop(g, None)
            okd = [did for did, ss in states.items() if all(s[0] == "ok" for s in ss)]
            bad = []
            for did, ss in states.items():
                probs = [s for s in ss if s[0] != "ok"]
                if probs:
                    bad.append("%s: %s" % (labels[did], probs[0][1] or probs[0][0]))
            names = sorted(base(r) for r in rels)
            detail = "、".join(names[:3]) + (" ほか%d件" % (len(names) - 3) if len(names) > 3 else "")
            if not bad:
                kind, summary = "copied", "コピー完了 → %s（%dファイル）" % ("・".join(labels[x] for x in okd), len(rels))
            else:
                kind = "copy_err"
                summary = ("%sにコピー済み / " % "・".join(labels[x] for x in okd) if okd else "") + " / ".join(bad)
            if self.reported.get(g) == summary:
                continue
            self.reported[g] = summary
            items = [{"op": "copy", "path": r[len(g) + 1:] if g else r[len(prefix):], "size": files[r][0]} for r in sorted(rels)]
            self.mgr.emit({"kind": kind, "kinds": [kind], "root": w.id, "root_label": w.label, "group": g,
                           "where": parent_of(g) if g else "", "title": base(g) if g else w.root_title(),
                           "summary": summary, "detail": detail, "items": items[:300], "n_items": len(items),
                           "while_stopped": False, "sys": True})

    # ---- API views
    def summary(self):
        op = self.mgr.cfg["op"]
        if not op["enabled"]:
            return {"enabled": False}
        out = []
        with self.lock:
            for d in op["dests"]:
                did = d["id"]
                fs = self.fst.get(did, {})
                cnt = {}
                for st in fs.values():
                    cnt[st[0]] = cnt.get(st[0], 0) + 1
                ds = self.dest.get(did, {})
                out.append({"id": did, "label": d["label"], "path": d["path"], "enabled": d["enabled"],
                            "online": ds.get("online"), "error": ds.get("error", ""), "count": cnt, "total": len(fs)})
        a0 = self.active
        act = dict(a0) if a0 else None
        return {"enabled": True, "root": op["root"], "venue": op["venue"], "dests": out,
                "day": op.get("day", ""), "days": [x["label"] for x in op.get("days") or []],
                "queue": self.queue_n, "active": act, "max_mbps": op["max_mbps"]}

    def group_states(self, group):
        with self.lock:
            return {did: a.get(group) for did, a in self.gagg.items() if a.get(group)}

    def pres_states(self, group):
        with self.lock:
            return {did: a.get(group) for did, a in self.pagg.items() if a.get(group)}

    def file_states(self, rels):
        with self.lock:
            return {rel: {did: fs[rel] for did, fs in self.fst.items() if rel in fs} for rel in rels}


# ---------------------------------------------------------------- manager
class NullCopier:
    """コピーをしないアプリ（PADDOCK SCOUT・PADDOCK SADDLE）用の空のコピー係。
    コピー（会場PCへの書き込み）は PADDOCK GATE だけが行う。"""
    ver = 0
    active = None

    def __init__(self, mgr=None):
        pass

    def start(self):
        pass

    def stop_now(self):
        pass

    def join(self, timeout=None):
        pass

    def kick(self):
        pass

    def reconfigure(self):
        pass

    def summary(self):
        return {"enabled": False}

    def group_states(self, group):
        return {}

    def file_states(self, rels):
        return {}


MEMO_MAX = 32 * 1024     # メモ（.txt）として表示する大きさの上限（これより後ろは省略）
MEMO_FILES = 5


def decode_text(b):
    """テキストファイルの文字コードを推定して読む（UTF-8 / BOM付き / UTF-16 / Shift_JIS（Windowsのメモ帳の古い既定））"""
    if b.startswith(b"\xef\xbb\xbf"):
        return b[3:].decode("utf-8", "replace")
    if b.startswith((b"\xff\xfe", b"\xfe\xff")):
        return b.decode("utf-16", "replace")
    for enc in ("utf-8", "cp932"):
        try:
            return b.decode(enc)
        except UnicodeDecodeError:
            continue
    return b.decode("utf-8", "replace")


def read_memo(path, size):
    """演者フォルダの .txt をメモとして読む（NASは読むだけ。他の人の書き込み・削除を妨げない開き方）"""
    with open_ro(long_path(path)) as f:
        b = f.read(MEMO_MAX + 4)
    trunc = size > MEMO_MAX or len(b) > MEMO_MAX
    if trunc:
        b = b[:MEMO_MAX]
        if b[:2] in (b"\xff\xfe", b"\xfe\xff"):
            b = b[:len(b) // 2 * 2]
    t = decode_text(b)
    if trunc and not b.startswith((b"\xff\xfe", b"\xfe\xff")):
        t = t.rstrip("\ufffd")
    return t.replace("\r\n", "\n").replace("\r", "\n").replace("\x00", ""), trunc


class Manager:
    COPIER_CLASS = None      # PADDOCK GATE だけが Copier を使う（WATCH・RECEPTION はコピーしない）
    def __init__(self, store, cfg):
        self.store = store
        self.cfg = cfg
        self.ignore_re = compile_ignore(list(cfg["ignore"]) + BUILTIN_IGNORE)
        self.coi = compile_coi(cfg["coi_keywords"])
        self.marks = compile_marks(cfg)
        self.cfg_lock = threading.Lock()
        self._mk_cache = {}
        self.mk_gen = 0          # 目印の設定を変えたら増やす（演者の状態を作り直して画面へ知らせる）
        self.watchers = {}
        self.cond = threading.Condition()
        self.events = deque(maxlen=EVENT_KEEP)
        self.trans = deque(maxlen=300)
        self.tseq = 0
        self.ver = 0
        self.boot = secrets.token_hex(6)
        st = store.read_json("state.json", {}) or {}
        self.seen = {k: int(v) for k, v in (st.get("seen") or {}).items()}
        self.seen_lock = threading.Lock()
        self.seen_floor = int(st.get("seen_floor", 0))
        # 演者フォルダごとの受付時刻と、受付後の変更（差し替え）回数。"root|group" -> {"recv","n","last","sum"}
        tr = store.read_json("track.json", {}) or {}
        self.track = {k: v for k, v in tr.items() if isinstance(v, dict)} if isinstance(tr, dict) else {}
        self.next_id = 1
        self._load_events()
        store.roots = [r["path"] for r in cfg["roots"]]
        self.logq = queue.Queue(maxsize=2000)
        threading.Thread(target=self._log_loop, daemon=True, name="log").start()
        self.analyzer = Analyzer(self)
        if self.COPIER_CLASS is None:
            # このアプリはコピーしない：オペレーター設定が残っていても使わない（会場PCへは何も書かない）
            self.op_moved = bool(cfg.get("op", {}).get("enabled"))
            cfg["op"] = dict(cfg.get("op") or {}, enabled=False)
        else:
            self.op_moved = False
        self.copier = (self.COPIER_CLASS or NullCopier)(self)

    def log(self, msg):
        # 監視スレッドはここで待たない（コンソールが止まっても監視は止めない）
        try:
            self.logq.put_nowait("[%s] %s" % (time.strftime("%H:%M:%S"), msg))
        except Exception:
            pass

    def _log_loop(self):
        while True:
            line = self.logq.get()
            try:
                print(line, flush=True)
            except Exception:
                pass

    def _load_events(self):
        p = self.store.path("events.jsonl")
        try:
            with open(p, "r", encoding="utf-8") as f:
                lines = f.readlines()
        except OSError:
            return
        for ln in lines[-EVENT_KEEP:]:
            try:
                ev = json.loads(ln)
                self.events.append(ev)
                self.next_id = max(self.next_id, int(ev["id"]) + 1)
            except (ValueError, KeyError, TypeError):
                continue
        if len(lines) > EVENT_KEEP * 2:
            try:
                self.store.guard(p)
                with open(p + ".tmp", "w", encoding="utf-8") as f:
                    f.writelines(lines[-EVENT_KEEP:])
                os.replace(p + ".tmp", p)
            except OSError:
                pass

    def start(self):
        self.analyzer.start()
        self.copier.start()
        for rc in self.watch_roots(self.cfg):
            self._start_watcher(rc)

    def watch_roots(self, cfg):
        """監視する（NASを見に行く）フォルダ。PADDOCK GATE は自分の会場の監視フォルダだけ（OpManager で差し替え）"""
        return [r for r in cfg["roots"] if r["enabled"]]

    def _start_watcher(self, rc):
        w = Watcher(self, rc)
        self.watchers[rc["id"]] = w
        w.start()

    def stop(self):
        for w in list(self.watchers.values()):
            w.stop_now()
        self.analyzer.stop_ev.set()
        self.copier.stop_now()
        for w in list(self.watchers.values()):
            w.join(timeout=3)
            if w.dirty:
                w.save_snapshot()
        self.analyzer.join(timeout=3)
        self.copier.join(timeout=5)

    def marker_of(self, rel, sig):
        """目印ファイル（00_受付済.jpg など）なら (role, 表示名, 設定での順番) を返す。ファイル名だけで判断し、中身は読まない。
        受付システムが入れる付帯情報のフォルダ（system-info など）の中は、目印として読めなくても「データ」には数えない（role="meta"）。"""
        if sig is None or sig == DIR:
            return None
        lr = rel.lower()
        meta = "/" in rel and "info" in lr and any(mark_norm(x) in META_DIRS_N for x in rel.split("/")[:-1])
        if sig[0] > MARK_MAX:
            return ("meta", "付帯情報", 10 ** 6) if meta else None
        name = base(rel)
        if meta:
            return mark_match(self.marks, name) or ("meta", "付帯情報", 10 ** 6)
        if ext_of(name) not in MARK_EXTS:
            return None
        cache = self._mk_cache
        r = cache.get(name, False)
        if r is False:
            r = mark_match(self.marks, name)
            if len(cache) > 50000:
                cache.clear()
            cache[name] = r
        return r

    def poke(self):
        with self.cond:
            self.cond.notify_all()

    def op_scope(self, rid):
        op = self.cfg.get("op") or {}
        if op.get("enabled") and op.get("root") == rid and op.get("venue"):
            return op["venue"]
        return None

    def total_ver(self):
        return self.ver + self.copier.ver + sum(w.ver for w in list(self.watchers.values()))

    def _track(self, ev):
        """受付（初めてファイルが入った）と、その後の変更（差し替え）を数える。cond を持った状態で呼ぶ。"""
        g = ev.get("group")
        if not g or ev.get("sys"):
            return False
        key = "%s|%s" % (ev.get("root"), g)
        kinds = ev.get("kinds") or [ev.get("kind")]
        if ev.get("kind") == "folder_rename" and ev.get("from_group"):
            old = self.track.pop("%s|%s" % (ev.get("root"), ev["from_group"]), None)
            if old is not None:
                self.track[key] = old
                return True
            return False
        if "folder_del" in kinds:
            return self.track.pop(key, None) is not None
        if not ev.get("fchg"):
            return False
        rec = self.track.get(key)
        changed = False
        if ev.get("fb", 0) == 0 and ev.get("fa", 0) > 0 and not (rec and rec.get("recv")):
            rec = rec or {"recv": None, "n": 0}     # はじめてデータが入った＝受付
            rec["recv"] = ev["ts"]
            ev["recv"] = True
            changed = True
        if ev.get("pchg") and ev.get("pb", 0) > 0:
            rec = rec or {"recv": None, "n": 0}     # パワーポイントがあった所でパワーポイントが変わった＝差し替え
            rec["n"] = int(rec.get("n", 0)) + 1
            rec["last"] = ev["ts"]
            rec["sum"] = ev.get("summary", "")[:80]
            ev["repl"] = rec["n"]
            changed = True
        if changed:
            self.track[key] = rec
        return changed

    def emit(self, ev):
        with self.cond:
            ev["id"] = self.next_id
            self.next_id += 1
            ev["ts"] = time.time()
            if self._track(ev):
                try:
                    self.store.write_json("track.json", self.track)
                except Exception as e:
                    self.log("track save failed: %s" % e)
            self.events.append(ev)
            self.cond.notify_all()
        try:
            self.store.append_line("events.jsonl", ev)
        except Exception as e:
            self.log("event log write failed: %s" % e)
        g = "" if ev.get("group") is None else ev["group"]
        self.log("%s  %s / %s  %s %s%s" % (ev["kind"].upper(), ev.get("root_label", ""), g, ev.get("summary", ""),
                                           ev.get("detail", ""), "  [差し替え %d回目]" % ev["repl"] if ev.get("repl") else ""))
        for a in ev.get("ana") or []:
            self.log("      %s: %s" % (a["file"], a.get("text") or a.get("na") or "解析待ち"))
        return ev["id"]

    def transient(self, kind, payload):
        with self.cond:
            self.tseq += 1
            payload.update(kind=kind, tid=self.tseq, ts=time.time())
            self.trans.append(payload)
            self.cond.notify_all()

    def wait_events(self, after, tafter, timeout):
        with self.cond:
            if not any(e["id"] > after for e in self.events) and not any(t["tid"] > tafter for t in self.trans):
                self.cond.wait(timeout)
            return ([e for e in self.events if e["id"] > after],
                    [t for t in self.trans if t["tid"] > tafter])

    def _save_state(self):
        try:
            self.store.write_json("state.json", {"seen": dict(self.seen), "seen_floor": self.seen_floor})
        except Exception as e:
            self.log("state save failed: %s" % e)

    def mark_seen(self, root, group):
        with self.seen_lock:
            last = self.next_id - 1
            if root is None:
                self.seen_floor = last
                self.seen = {}
            else:
                self.seen["%s|%s" % (root, group)] = last
            self.ver += 1
            self._save_state()
        self.poke()

    def is_unread(self, ev):
        if ev.get("group") is None or ev.get("sys"):
            return False
        key = "%s|%s" % (ev.get("root"), ev.get("group"))
        return ev["id"] > max(self.seen_floor, self.seen.get(key, 0))

    def apply_config(self, new):
        with self.cfg_lock:          # 保存の2度押しなどで同時に走らないように
            self._apply_config(new)

    def _apply_config(self, new):
        if self.COPIER_CLASS is None:
            new["op"] = dict(new.get("op") or {}, enabled=False)
        old = self.cfg
        ignore_changed = old["ignore"] != new["ignore"]
        coi_changed = old["coi_keywords"] != new["coi_keywords"]
        analyze_on = new["analyze"] and not old["analyze"]
        op_changed = old.get("op") != new.get("op") or [r["path"] for r in old["roots"]] != [r["path"] for r in new["roots"]]
        old_ignore_re = self.ignore_re
        old_roots = self.store.roots
        self.store.roots = [r["path"] for r in new["roots"]]
        try:
            self.store.write_json("config.json", new)     # 先に保存（保存できなければ何も変えない）
        except Exception:
            self.store.roots = old_roots
            raise
        self.cfg = new
        self.ignore_re = compile_ignore(list(new["ignore"]) + BUILTIN_IGNORE)
        self.coi = compile_coi(new["coi_keywords"])
        if old.get("marks") != new.get("marks"):
            self.marks = compile_marks(new)
            self._mk_cache = {}
            self.mk_gen += 1
        want = {r["id"]: r for r in self.watch_roots(new)}
        for rid, w in list(self.watchers.items()):
            r = want.get(rid)
            if r is None or norm_key(r["path"]) != norm_key(w.path) or r["depth"] != w.depth \
                    or self.op_scope(rid) != w.scope:
                w.stop_now()
                del self.watchers[rid]
                if w.dirty:
                    w.save_snapshot()
            else:
                w.label = r["label"] or default_label(r["path"])
                if ignore_changed:
                    w.reignore = (old_ignore_re,)
        for rid, r in want.items():
            if rid not in self.watchers:
                self._start_watcher(r)
        if coi_changed:
            self.analyzer.reset(coi_signature(new["coi_keywords"]))
        elif analyze_on:
            for w in list(self.watchers.values()):
                self.analyzer.enqueue_all(w)
        if op_changed:
            self.copier.reconfigure()
        self.ver += 1
        self.poke()

    # ---- API views
    def status_payload(self):
        roots = []
        for rc in self.cfg["roots"]:
            w = self.watchers.get(rc["id"])
            d = {"id": rc["id"]}
            if w:
                d.update(w.status())
            else:
                d.update({"online": None, "error": "停止中" if not rc["enabled"] else "", "count": 0, "pending": 0})
            d.pop("warns", None)
            roots.append(d)
        return {"ver": self.total_ver(), "boot": self.boot, "now": time.time(), "roots": roots}

    def group_ana(self, w, px):
        a = {"n": 0, "done": 0, "video": 0, "vwarn": 0, "vfbad": 0, "vfwarn": 0, "abad": 0, "links": 0, "coi": 0, "auto": 0,
             "noclick": 0, "err": 0, "na": 0}
        for rel, sig in px:
            if ana_kind(rel) != "pptx":
                a["na"] += 1
                continue
            a["n"] += 1
            res = self.analyzer.get(w, rel, sig)
            if res is None:
                continue
            a["done"] += 1
            s = res.get("sum") or {}
            if s.get("err"):
                a["err"] += 1
                continue
            a["video"] += s["video"]
            a["vwarn"] += s["vlink"]
            a["vfbad"] += s.get("vfbad", 0)
            a["vfwarn"] += s.get("vfwarn", 0)
            a["abad"] += s.get("abad", 0)
            a["links"] += s["links"]
            a["coi"] += 1 if s["coi"] else 0
            a["auto"] += s["auto"]
            a["noclick"] += s["noclick"] + (1 if s["kiosk"] else 0)
        return a

    def state_payload(self, local):
        with self.cond:          # 一覧と「最後の通知番号」を同時に取る（その間に起きた通知を取りこぼさない）
            evs = list(self.events)
            last_id = self.next_id - 1
        unread = {}
        for e in evs:
            if self.is_unread(e):
                k = "%s|%s" % (e["root"], e["group"])
                unread[k] = unread.get(k, 0) + 1
        last_by = {}
        for e in evs:
            if e.get("group") is not None and not e.get("sys"):
                last_by["%s|%s" % (e["root"], e["group"])] = e
        roots = []
        analyze_on = self.cfg["analyze"]
        op_on = self.cfg["op"]["enabled"]
        for rc in self.cfg["roots"]:
            w = self.watchers.get(rc["id"])
            d = {"id": rc["id"], "label": rc["label"] or default_label(rc["path"]), "path": rc["path"],
                 "depth": rc["depth"], "enabled": rc["enabled"]}
            if w:
                d.update(w.status())
                with w.lock:
                    groups = [dict(x) for x in w.groups]
                    sdirs = [dict(x, loose=[list(f) for f in x["loose"]]) for x in w.sdirs]
                if op_on and rc["id"] == self.cfg["op"]["root"]:   # セッション直下のファイルのコピーの状態
                    rels = [x["key"] + "/" + f[0] for x in sdirs for f in x["loose"]]
                    fs = self.copier.file_states(rels) if rels else {}
                    for x in sdirs:
                        for f in x["loose"]:
                            st = fs.get(x["key"] + "/" + f[0])
                            if st:
                                f.append({did: v[0] for did, v in st.items()})
                d["sdirs"] = sdirs
                for gsum in groups:
                    px = gsum.pop("px", [])
                    if analyze_on and px:
                        gsum["ana"] = self.group_ana(w, px)
                    k = "%s|%s" % (rc["id"], gsum["key"])
                    gsum["unread"] = unread.get(k, 0)
                    if op_on and rc["id"] == self.cfg["op"]["root"]:
                        cp = self.copier.group_states(gsum["key"])
                        if cp:
                            gsum["cp"] = cp
                        cpp = self.copier.pres_states(gsum["key"])
                        if cpp:
                            gsum["cpp"] = cpp
                    le = last_by.get(k)
                    if le:
                        gsum["last_ts"] = le["ts"]
                        gsum["last_kind"] = le["kind"]
                    tr = self.track.get(k)
                    if tr:
                        if tr.get("recv"):
                            gsum["recv_ts"] = tr["recv"]
                        if tr.get("n"):
                            gsum["repl"], gsum["repl_ts"], gsum["repl_sum"] = tr["n"], tr.get("last"), tr.get("sum", "")
                d["groups"] = groups
            else:
                d.update({"online": None, "error": "", "groups": [], "count": 0, "pending": 0, "warns": []})
            roots.append(d)
        out_evs = []
        for e in evs[-300:]:
            x = dict(e)
            x["items"] = e.get("items", [])[:12]
            x["u"] = self.is_unread(e)
            out_evs.append(x)
        return {"app": APP_NAME, "version": VERSION, "boot": self.boot, "now": time.time(),
                "last_event_id": last_id, "ver": self.total_ver(), "roots": roots,
                "events": out_evs, "ui": self.cfg["ui"], "notify": self.cfg["notify"], "local": local,
                "analyze": analyze_on, "os": "win" if IS_WIN else ("mac" if IS_MAC else "other"),
                "unread_total": sum(unread.values()), "op": self.copier.summary(), "op_moved": self.op_moved}

    def folder_payload(self, rid, group):
        w = self.watchers.get(rid)
        if not w:
            raise KeyError("監視フォルダが見つかりません")
        # セッションのフォルダに直接置かれたファイル1つを、演者1人として見せるとき（PADDOCK GATE）：
        # そのファイルだけを、親（セッションのフォルダ）の中の1件として返す
        with w.lock:
            fsig = (w.current or {}).get(group) if group else None
        if fsig is not None and fsig != DIR and "/" in group:
            parent, name = group.rsplit("/", 1)
            items = [it for it in w.folder(parent, self.analyzer, self.cfg["analyze"]) if it["p"] == name]
            full = os.path.join(w.path, *parent.split("/"))
            out = {"root": rid, "group": group, "label": w.label, "path": full, "items": items, "events": [],
                   "exists": True, "now": time.time(), "track": None, "memo": [], "file": name}
            op = self.cfg["op"]
            if op["enabled"] and op["root"] == rid:
                st = self.copier.file_states([group]).get(group) or {}
                for it in items:
                    if st:
                        it["cp"] = st
                sub = op_sub(op, parent)
                out["op"] = {"dests": [{"id": d["id"], "label": d["label"], "enabled": d["enabled"],
                                        "state": (st.get(d["id"]) or [None])[0],
                                        "path": os.path.join(d["path"], *sub.split("/")) if sub else d["path"]}
                                       for d in op["dests"]]}
            return out
        items = w.folder(group, self.analyzer, self.cfg["analyze"])
        evs = [dict(e) for e in list(self.events) if e.get("root") == rid and e.get("group") == group][-20:]
        evs.reverse()
        for e in evs:
            e["u"] = self.is_unread(e)
        full = os.path.join(w.path, *group.split("/")) if group else w.path
        out = {"root": rid, "group": group, "label": w.label, "path": full, "items": items,
               "events": evs, "exists": group == "" or group in w.current, "now": time.time(),
               "track": self.track.get("%s|%s" % (rid, group))}
        out["memo"] = self.folder_memos(full, items)
        op = self.cfg["op"]
        if op["enabled"] and op["root"] == rid:
            pre = group + "/" if group else ""
            fs = self.copier.file_states([pre + it["p"] for it in items if not it["d"]])
            for it in items:
                if not it["d"]:
                    st = fs.get(pre + it["p"])
                    if st:
                        it["cp"] = st
            gs = self.copier.group_states(group)
            dl = []
            for d in op["dests"]:
                sub = op_sub(op, group)
                dl.append({"id": d["id"], "label": d["label"], "enabled": d["enabled"], "state": gs.get(d["id"]),
                           "path": os.path.join(d["path"], *sub.split("/")) if sub else d["path"]})
            out["op"] = {"dests": dl}
        return out

    def folder_memos(self, full, items):
        """演者フォルダの中の .txt（演者・受付からのメモ）。受信中のものは読まない。内容は大きさ・更新日時が変わるまで覚えておく"""
        cache = self.__dict__.setdefault("_memo_cache", {})
        out = []
        txt = [it for it in items if not it["d"] and not it.get("mk") and it["p"].lower().endswith(".txt")]
        txt.sort(key=lambda it: (it["p"].count("/"), nat_key(it["p"])))
        for it in txt[:MEMO_FILES]:
            m = {"p": it["p"], "s": it.get("s", 0), "m": it.get("m", 0)}
            if it.get("st") == "pending":
                m["pending"] = True
                out.append(m)
                continue
            path = os.path.join(full, *it["p"].split("/"))
            key = (path, it.get("s"), it.get("m"))
            hit = cache.get(path)
            if hit and hit[0] == key:
                m.update(hit[1])
            else:
                try:
                    t, tr = read_memo(path, it.get("s") or 0)
                    r = {"text": t, "trunc": tr}
                except (OSError, UnsafeOpen) as e:
                    r = {"error": _err(e) if isinstance(e, OSError) else str(e)}
                if "error" not in r:   # 読めなかったとき（一時的なネットワークの不調など）は覚えずに、次に読み直す
                    if len(cache) > 300:
                        cache.clear()
                    cache[path] = (key, r)
                m.update(r)
            out.append(m)
        if len(txt) > MEMO_FILES:
            out.append({"more": len(txt) - MEMO_FILES})
        return out

    def list_venues(self, rid, path=None):
        """会場オペレーター用の設定：監視フォルダ直下のフォルダ名（一覧の取得のみ）。保存前のパスでも見られる。"""
        if path:
            target = str(path).strip().strip('"')
        else:
            rc = next((r for r in self.cfg["roots"] if r["id"] == rid), None)
            if not rc:
                raise KeyError("監視フォルダが見つかりません")
            target = rc["path"]
        out = []
        try:
            with os.scandir(long_path(target)) as it:
                for de in it:
                    if self.ignore_re is not None and self.ignore_re.match(de.name.lower()):
                        continue
                    try:
                        if de.is_dir(follow_symlinks=False):
                            out.append(de.name)
                    except OSError:
                        continue
        except OSError as e:
            raise KeyError("フォルダを開けません: %s" % _err(e))
        return sorted(out, key=nat_key)[:500]

    def resolve(self, rid, rel):
        w = self.watchers.get(rid)
        if not w:
            raise KeyError("監視フォルダが見つかりません")
        parts = [p for p in (rel or "").split("/") if p]
        for p in parts:
            if p in (".", "..") or "\\" in p or ":" in p:
                raise ValueError("不正なパス")
        return os.path.join(w.path, *parts) if parts else w.path


# ---------------------------------------------------------------- OS helpers
def reveal(path):
    """Explorer / Finder で表示する（このアプリ自体は何も書き込まない）。"""
    isdir = os.path.isdir(path)
    if IS_WIN:
        if isdir:
            os.startfile(path)  # noqa
        else:
            subprocess.Popen('explorer /select,"%s"' % path)
    elif IS_MAC:
        subprocess.Popen(["open", path] if isdir else ["open", "-R", path])
    else:
        subprocess.Popen(["xdg-open", path if isdir else os.path.dirname(path)])


def pick_folder(dest=False):
    title = "コピー先のフォルダを選択" if dest else "監視するフォルダを選択"
    if IS_MAC:
        r = subprocess.run(["osascript", "-e", 'POSIX path of (choose folder with prompt "%s")' % title],
                           capture_output=True, text=True)
        return r.stdout.strip() or None
    if IS_WIN:
        # Windows標準のフォルダ選択。監視フォルダ選択では「新しいフォルダー」ボタンを出さない＝NASに何も作らせない
        # ダイアログがブラウザの裏に出ないように：見えない小さな最前面ウィンドウを作り、
        # 前面にあるウィンドウ（ブラウザ）の入力に一時的につないでから前面に出し、それを親にしてダイアログを開く
        ps = ("Add-Type -AssemblyName System.Windows.Forms;"
              "Add-Type -Namespace SW -Name U -MemberDefinition '"
              "[DllImport(\"user32.dll\")] public static extern IntPtr GetForegroundWindow();"
              "[DllImport(\"user32.dll\")] public static extern uint GetWindowThreadProcessId(IntPtr h, IntPtr p);"
              "[DllImport(\"kernel32.dll\")] public static extern uint GetCurrentThreadId();"
              "[DllImport(\"user32.dll\")] public static extern bool AttachThreadInput(uint a, uint b, bool f);"
              "[DllImport(\"user32.dll\")] public static extern bool SetForegroundWindow(IntPtr h);"
              "[DllImport(\"user32.dll\")] public static extern bool BringWindowToTop(IntPtr h);"
              "[DllImport(\"user32.dll\")] public static extern void keybd_event(byte k, byte s, uint f, UIntPtr e);';"
              "$f=New-Object System.Windows.Forms.Form -Property @{TopMost=$true;ShowInTaskbar=$false;"
              "FormBorderStyle='None';StartPosition='CenterScreen';Width=1;Height=1;Opacity=0};"
              "$f.Show();"
              "try{$fg=[SW.U]::GetForegroundWindow();$a=[SW.U]::GetWindowThreadProcessId($fg,[IntPtr]::Zero);"
              "$b=[SW.U]::GetCurrentThreadId();$j=($a -ne 0 -and $a -ne $b);"
              "if($j){[void][SW.U]::AttachThreadInput($b,$a,$true)};"
              "[SW.U]::keybd_event(0x12,0,0,[UIntPtr]::Zero);[SW.U]::keybd_event(0x12,0,2,[UIntPtr]::Zero);"
              "[void][SW.U]::SetForegroundWindow($f.Handle);[void][SW.U]::BringWindowToTop($f.Handle);$f.Activate();"
              "if($j){[void][SW.U]::AttachThreadInput($b,$a,$false)}}catch{};"
              "$d=New-Object System.Windows.Forms.FolderBrowserDialog;"
              "$d.Description='%s（ネットワーク上のフォルダも選べます）';"
              "$d.ShowNewFolderButton=$%s;" % (title, "true" if dest else "false") +
              "[Console]::OutputEncoding=[System.Text.Encoding]::UTF8;"
              "$r=$d.ShowDialog($f);$f.Close();"
              "if($r -eq [System.Windows.Forms.DialogResult]::OK){[Console]::Out.Write($d.SelectedPath)}")
        try:
            r = subprocess.run(["powershell", "-NoProfile", "-STA", "-Command", ps], capture_output=True,
                               text=True, encoding="utf-8", errors="replace", creationflags=0x08000000)
            if r.returncode == 0:
                return r.stdout.lstrip("\ufeff").strip() or None
        except OSError:
            pass
        try:
            import tkinter as tk
            from tkinter import filedialog
        except ImportError:
            raise RuntimeError("フォルダ選択ダイアログを開けませんでした。パスを直接入力してください")
        root = tk.Tk()
        root.withdraw()
        root.attributes("-topmost", True)
        root.lift()
        root.focus_force()
        p = filedialog.askdirectory(parent=root, title=title, mustexist=True)
        root.destroy()
        return os.path.normpath(p) if p else None
    if shutil.which("zenity"):
        r = subprocess.run(["zenity", "--file-selection", "--directory"], capture_output=True, text=True)
        return r.stdout.strip() or None
    raise RuntimeError("この環境ではフォルダ選択ダイアログを使えません。パスを直接入力してください")


def find_browser():
    cands = []
    if IS_WIN:
        for env in ("PROGRAMFILES", "PROGRAMFILES(X86)", "LOCALAPPDATA"):
            b = os.environ.get(env)
            if b:
                cands.append(os.path.join(b, "Google", "Chrome", "Application", "chrome.exe"))
        for env in ("PROGRAMFILES(X86)", "PROGRAMFILES"):
            b = os.environ.get(env)
            if b:
                cands.append(os.path.join(b, "Microsoft", "Edge", "Application", "msedge.exe"))
    elif IS_MAC:
        for d in ("/Applications", os.path.expanduser("~/Applications")):
            cands.append(os.path.join(d, "Google Chrome.app", "Contents", "MacOS", "Google Chrome"))
            cands.append(os.path.join(d, "Microsoft Edge.app", "Contents", "MacOS", "Microsoft Edge"))
    else:
        for n in ("google-chrome", "chromium", "chromium-browser", "microsoft-edge"):
            p = shutil.which(n)
            if p:
                cands.append(p)
    for c in cands:
        if c and os.path.isfile(c):
            return c
    return None


def open_ui(url, data_dir, mode):
    if mode == "none":
        return
    exe = find_browser() if mode == "app" else None
    if exe:
        prof = os.path.join(data_dir, "browser_profile")
        args = [exe, "--app=" + url, "--user-data-dir=" + prof, "--no-first-run", "--no-default-browser-check",
                "--autoplay-policy=no-user-gesture-required", "--window-size=1400,900"]
        try:
            subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            return
        except OSError:
            pass
    webbrowser.open(url)


# ---------------------------------------------------------------- HTTP
class Handler(BaseHTTPRequestHandler):
    server_version = "SWNasWatch/" + VERSION

    def log_message(self, fmt, *args):
        pass

    @property
    def M(self):
        return self.server.mgr

    def is_local(self):
        return self.client_address[0] in ("127.0.0.1", "::1", "::ffff:127.0.0.1")

    def host_ok(self):
        h = (self.headers.get("Host") or "").lower()
        if h in self.server.allowed_hosts:
            return True
        return self.server.lan and not self.is_local()

    def send_json(self, obj, code=200):
        body = json_bytes(obj)
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.wfile.write(body)

    def deny(self, code, msg):
        self.send_json({"error": msg}, code)

    def do_GET(self):
        if not self.host_ok():
            return self.deny(403, "host not allowed")
        u = urlparse(self.path)
        q = parse_qs(u.query)
        try:
            if u.path in ("/", "/index.html"):
                body = (getattr(self.server, "page", None) or HTML).replace("__TOKEN__", self.server.token).replace("__VERSION__", VERSION).replace(
                    "__APPKIND__", getattr(self.server, "appkind", "watch")).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Cache-Control", "no-store")
                self.send_header("X-Content-Type-Options", "nosniff")
                self.send_header("Referrer-Policy", "no-referrer")
                self.send_header("Content-Security-Policy",
                                 "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; "
                                 "img-src 'self' data:; connect-src 'self' http://ipc.localhost ipc:; frame-ancestors 'none'; base-uri 'none'")   # ipc：Tauri 版の窓とのやりとり
                self.end_headers()
                self.wfile.write(body)
            elif u.path == "/api/ping":
                self.send_json({"app": APP_NAME, "version": VERSION, "ppid": os.getppid()})
            elif u.path == "/api/state":
                self.send_json(self.M.state_payload(self.is_local()))
            elif u.path == "/api/folder":
                rid = (q.get("root") or [""])[0]
                group = (q.get("group") or [""])[0]
                self.send_json(self.M.folder_payload(rid, group))
            elif u.path == "/api/config":
                self.send_json({"config": self.M.cfg, "defaults": {"ignore": DEFAULT_IGNORE, "coi": DEFAULT_COI,
                                                                   "marks": DEFAULT_MARKS,
                                                                   "op_dest": default_op_dest() if self.is_local() else ""},
                                "data_dir": self.M.store.dir if self.is_local() else ""})
            elif u.path == "/api/venues":
                path = (q.get("path") or [""])[0] if self.is_local() else ""
                self.send_json({"venues": self.M.list_venues((q.get("root") or [""])[0], path)})
            elif u.path == "/api/stream":
                self.stream(q)
            else:
                self.deny(404, "not found")
        except KeyError as e:
            self.deny(404, str(e).strip("'\""))
        except OSError:
            pass  # ブラウザ側が切断（SSE含む）
        except Exception as e:
            try:
                self.deny(500, "%s: %s" % (type(e).__name__, e))
            except OSError:
                pass

    def stream(self, q):
        try:
            last = int(self.headers.get("Last-Event-ID") or (q.get("since") or ["0"])[0])
        except ValueError:
            last = 0
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Accel-Buffering", "no")
        self.end_headers()
        M = self.M
        tlast = M.tseq
        srv = self.server
        lk = getattr(srv, "clients_lock", None) or threading.Lock()
        with lk:
            srv.clients = getattr(srv, "clients", 0) + 1
            srv.ever_client = True
            srv.last_client = time.time()
        try:
            self._stream(M, last, tlast)
        finally:
            with lk:
                srv.clients -= 1
                srv.last_client = time.time()

    def _stream(self, M, last, tlast):
        self.wfile.write(b"retry: 2000\n\n")
        last_status = None
        last_beat = 0.0
        while not self.server.stopping:
            evs, trs = M.wait_events(last, tlast, 2.0)
            out = []
            for t in trs:
                tlast = t["tid"]
                out.append("event: incoming\ndata: %s\n\n" % json_bytes(t).decode("utf-8"))
            for ev in evs:
                last = ev["id"]
                x = dict(ev)
                x["u"] = M.is_unread(ev)
                out.append("id: %d\nevent: ev\ndata: %s\n\n" % (ev["id"], json_bytes(x).decode("utf-8")))
            st = M.status_payload()
            sig = (st["ver"], tuple((r["id"], r.get("online"), r.get("scanning"), int(r.get("last_scan") or 0)) for r in st["roots"]))
            now = time.time()
            if sig != last_status or now - last_beat > 10:
                out.append("event: status\ndata: %s\n\n" % json_bytes(st).decode("utf-8"))
                last_status = sig
                last_beat = now
            if out:
                self.wfile.write("".join(out).encode("utf-8"))
                self.wfile.flush()
        try:   # 終了するとき：画面に知らせる（タスクバーの［終了］・新しい版の起動でも、画面に「終了しました」を出す）
            self.wfile.write(b"event: bye\ndata: {}\n\n")
            self.wfile.flush()
        except OSError:
            pass

    def do_POST(self):
        if not self.is_local() or (self.headers.get("Host") or "").lower() not in self.server.allowed_hosts:
            return self.deny(403, "この操作はアプリを動かしているPCからのみ可能です")
        if urlparse(self.path).path == "/api/shell/quit":   # Tauri 版の窓（タスクバーのアイコンの［終了］）から。鍵はこのPCのファイルにだけある
            key = SHELL_KEY[0]
            if not key or not secrets.compare_digest((self.headers.get("X-SW-Shell") or "").encode("utf-8", "replace"), key.encode("ascii")):
                return self.deny(403, "shell")
            block = getattr(self.server, "quit_block", None)
            msg = block() if block else ""
            if msg:
                return self.deny(409, msg)
            self.send_json({"ok": True})
            request_quit(self.server, "タスクバーのアイコンの［終了］で終了します")
            return
        if urlparse(self.path).path == "/api/handover":   # 別の版を起動したとき：この版を終わらせる（専用ヘッダーが要るので、ほかのサイトからは送れない）
            v = (self.headers.get("X-SW-Handover") or "").strip()
            mine = getattr(self.server, "version", VERSION)
            if not v or v == mine:
                return self.deny(400, "same version")
            if ver_tuple(v) and ver_tuple(mine) and ver_tuple(v) < ver_tuple(mine):   # 古い版には譲らない（古いショートカットを押しても、新しい版を止めない）
                return self.deny(409, "新しい版（v%s）が動いています。古い版（v%s）は使えません" % (mine, v))
            block = getattr(self.server, "quit_block", None)
            msg = block() if block else ""
            if msg:
                return self.deny(409, msg)
            self.send_json({"ok": True})
            request_quit(self.server, "新しい版（v%s）が起動されたため、この版（v%s）を終了します" % (v, mine))
            return
        if self.headers.get("X-SW-Token") != self.server.token:
            return self.deny(403, "token")
        try:
            n = int(self.headers.get("Content-Length") or 0)
            if n > 1_000_000:
                return self.deny(413, "too large")
            body = json.loads(self.rfile.read(n).decode("utf-8") or "{}") if n else {}
        except (ValueError, UnicodeDecodeError):
            return self.deny(400, "bad json")
        path = urlparse(self.path).path
        M = self.M
        try:
            if path == "/api/quit":
                block = getattr(self.server, "quit_block", None)
                msg = block() if block else ""
                if msg:
                    return self.deny(409, msg)
                self.send_json({"ok": True})
                request_quit(self.server, "画面の［終了］で終了します")
                return
            if path == "/api/seen":
                if body.get("all"):
                    M.mark_seen(None, None)
                else:
                    M.mark_seen(str(body.get("root")), str(body.get("group") or ""))
                self.send_json({"ok": True})
            elif path == "/api/open":
                if not M.cfg["ui"].get("os_open"):
                    return self.deny(403, "「Explorer / Finder で開く」は設定でオフになっています")
                p = M.resolve(str(body.get("root")), str(body.get("rel") or ""))
                if not os.path.exists(p):
                    return self.deny(404, "見つかりません（削除・移動された可能性）: %s" % p)
                reveal(p)
                self.send_json({"ok": True, "path": p})
            elif path == "/api/pick":
                p = pick_folder(dest=bool(body.get("dest")))
                self.send_json({"ok": True, "path": p})
            elif path == "/api/rebaseline":
                w = M.watchers.get(str(body.get("root")))
                if not w:
                    return self.deny(404, "監視フォルダが見つかりません")
                w.rebaseline = True
                self.send_json({"ok": True})
            elif path == "/api/opday":
                # 会場オペレーター：日ごとに分かれている学会で「いまの日」を切り替える（その日の会場フォルダを監視・コピー）
                with M.cfg_lock:
                    raw = json.loads(json.dumps(M.cfg))
                op = raw.get("op") or {}
                day = str(body.get("day") or "")
                if not op.get("enabled") or day not in [x["label"] for x in op.get("days") or []]:
                    return self.deny(400, "その日は設定されていません")
                op["day"] = day
                cfg = validate_cfg(raw, M.store.dir, M.cfg)
                M.apply_config(cfg)
                self.send_json({"ok": True, "day": cfg["op"]["day"], "venue": cfg["op"]["venue"]})
            elif path == "/api/config":
                cfg = validate_cfg(body, M.store.dir, M.cfg)
                warns = []
                for r in cfg["roots"]:
                    if r["enabled"] and not os.path.isdir(r["path"]):
                        warns.append("いま開けません（NAS未接続・パス違いの可能性）: %s" % r["path"])
                op = cfg["op"]
                if op["enabled"]:
                    hosts = {unc_host(r["path"]) for r in cfg["roots"]} - {""}
                    for d in op["dests"]:
                        if d["enabled"] and unc_host(d["path"]) in hosts:
                            warns.append("コピー先「%s」がNASと同じサーバーです。NASに書き込むことになるため、通常はPCのフォルダを指定してください" % d["label"])
                M.apply_config(cfg)
                self.send_json({"ok": True, "warnings": warns, "config": cfg})
            else:
                self.deny(404, "not found")
        except (ValueError, KeyError, RuntimeError) as e:
            self.deny(400, str(e).strip("'\""))
        except Exception as e:
            self.deny(500, "%s: %s" % (type(e).__name__, e))


# ---------------------------------------------------------------- 起動・終了（コンソールを出さない起動のとき）
# 起動用の exe はコンソール（黒い画面）を出さずに動かす（SW_NAS_AUTOQUIT=1）。そのときは
#  ・画面のウィンドウを閉じて、しばらく（20秒）どの画面ともつながっていなければ終了する
#  ・画面の［終了］でも終了できる
AUTOQUIT = os.environ.get("SW_NAS_AUTOQUIT") == "1"
STOP_HINT = ("画面のウィンドウを閉じると止まります（画面の［終了］でも止められます）" if AUTOQUIT
             else "このウィンドウを閉じると止まります（Ctrl+C で終了）")


def _open_quiet(fn):
    try:
        fn()
        return True
    except Exception:
        return False


def handover(url, version):
    """裏で動いている別の版に終わってもらう。(ok, 理由)"""
    req = Request(url + "api/handover", data=b"{}", method="POST",
                  headers={"Content-Type": "application/json", "X-SW-Handover": version})
    try:
        with urlopen(req, timeout=5) as r:
            return bool(json.loads(r.read().decode("utf-8")).get("ok")), ""
    except HTTPError as e:
        try:
            msg = json.loads(e.read().decode("utf-8")).get("error") or str(e)
        except Exception:
            msg = str(e)
        if e.code == 404 or (e.code == 403 and msg == "token"):   # 引き継ぎに対応していない古い版
            return False, "old"
        return False, msg
    except Exception as e:
        return False, str(e)


def claim_port(host, port, url, app_name, open_fn=None, version=None):
    """ポートが使えるか。同じアプリが動いていれば画面を開いて False（このまま終わる）。
    裏で動いているのが別の版（更新した直後など）なら、そちらに終わってもらってから、この版で起動する。
    終了したばかりで後片付け中（ポートはまだ使用中・応答なし）のときは、空くまで少し待つ"""
    asked = False
    for i in range(40):
        if port_free(host, port):
            return True
        try:
            with urlopen(url + "api/ping", timeout=2) as r:
                j = json.loads(r.read().decode("utf-8"))
            if j.get("app") == app_name:
                old = str(j.get("version") or "")
                if version and old and old != version and not asked:
                    ok, why = handover(url, version)
                    if ok:
                        print("裏で動いていた %s v%s を終了して、v%s で起動します" % (app_name, old, version), flush=True)
                        asked = True
                        time.sleep(1)
                        continue
                    opened = bool(open_fn) and _open_quiet(open_fn)
                    if why == "old":
                        raise SystemExit("%s の別の版（v%s）が裏で動いています。\n%s［終了］（電源のボタン）で終了してから、もう一度起動してください。"
                                         % (app_name, old, "開いた画面の" if opened else "その画面を開き、"))
                    raise SystemExit("%s の別の版（v%s）が動いているため、v%s を起動できませんでした。\n%s" % (app_name, old, version, why))
                if asked:   # 終わるのを待っている
                    time.sleep(1)
                    continue
                print("%s はすでに起動しています。画面を開きます: %s" % (app_name, url))
                if open_fn:
                    open_fn()
                return False
        except SystemExit:
            raise
        except Exception:
            pass
        time.sleep(1)
    raise SystemExit("ポート %d が使用中です。ほかのアプリが使っている可能性があります（--port で別の番号を指定できます）" % port)


def use_legacy(flag):
    global LEGACY_UI
    if flag:
        LEGACY_UI = True


# ---------------------------------------------------------------- タスクバー右下（通知領域）のアイコン（Windows）
class Tray:
    """動いている間、タスクバー右下にアイコンを出す。クリックで画面を開く、右クリックで［画面を開く］［終了］。
    Windows 以外・失敗したときは何もしない（アプリの動作には関係しない）"""
    WM_TRAY = 0x8000 + 1      # WM_APP + 1
    ID_OPEN, ID_QUIT = 1, 2

    def __init__(self, srv, app_name, version, exe_name, open_fn, quit_confirm=None, status_fn=None):
        self.srv, self.app, self.ver, self.exe = srv, app_name, version, exe_name
        self.open_fn, self.quit_confirm, self.status_fn = open_fn, quit_confirm, status_fn
        self.hwnd = None
        self.ok = False
        self._quit = threading.Event()
        self._post = None
        self.mac = False
        self._last_open = 0.0

    def start(self):
        if os.environ.get("SW_NAS_TRAY", "1") == "0":
            return self
        if IS_MAC:   # Mac はメインスレッドで動かす（serve() から _mac_loop を呼ぶ）
            self.mac = True
            return self
        if not IS_WIN:
            return self
        threading.Thread(target=self._run, daemon=True, name="tray").start()
        return self

    def stop(self):
        self._quit.set()
        try:
            if self.hwnd and self._post:
                self._post(self.hwnd, 0x0010, 0, 0)   # WM_CLOSE
                for _ in range(20):
                    if not self.hwnd:
                        break
                    time.sleep(0.05)
        except Exception:
            pass

    def _icon_path(self):
        c = []
        if os.path.basename(sys.executable).lower().endswith("_core.exe"):   # アプリ名のついた Python 本体（アイコン入り）
            c.append(os.path.abspath(sys.executable))
        for k in ("SW_NAS_WATCH_HOME", "SW_NAS_RECEPTION_HOME", "SW_NAS_OPERATOR_HOME"):
            if os.environ.get(k):
                c.append(os.path.join(os.environ[k], self.exe))
        c.append(os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(sys.executable)))), self.exe))
        for x in c:
            if os.path.isfile(x):
                return x
        return None

    def _tip(self):
        t = "%s v%s" % (self.app, self.ver)
        try:
            st = self.status_fn() if self.status_fn else ""
        except Exception:
            st = ""
        t += "\n" + (st or "動作中（ウィンドウを閉じても動いています）")
        return t.encode("utf-16-le")[:254].decode("utf-16-le", "ignore")   # 127文字まで（絵文字などは2文字分）

    def _run(self):
        try:
            self._loop()
        except Exception as e:
            print("タスクバーのアイコンを出せませんでした: %s" % e, flush=True)
        finally:
            self.hwnd = None

    def _loop(self):
        import ctypes
        from ctypes import wintypes as W
        u32 = ctypes.WinDLL("user32", use_last_error=True)
        sh = ctypes.WinDLL("shell32", use_last_error=True)
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        LRESULT = ctypes.c_ssize_t
        WNDPROC = ctypes.WINFUNCTYPE(LRESULT, W.HWND, W.UINT, W.WPARAM, W.LPARAM)

        class WNDCLASSEXW(ctypes.Structure):
            _fields_ = [("cbSize", W.UINT), ("style", W.UINT), ("lpfnWndProc", WNDPROC), ("cbClsExtra", ctypes.c_int),
                        ("cbWndExtra", ctypes.c_int), ("hInstance", W.HINSTANCE), ("hIcon", W.HICON), ("hCursor", W.HANDLE),
                        ("hbrBackground", W.HBRUSH), ("lpszMenuName", W.LPCWSTR), ("lpszClassName", W.LPCWSTR), ("hIconSm", W.HICON)]

        class GUID(ctypes.Structure):
            _fields_ = [("a", W.DWORD), ("b", W.WORD), ("c", W.WORD), ("d", ctypes.c_ubyte * 8)]

        class NOTIFYICONDATAW(ctypes.Structure):
            _fields_ = [("cbSize", W.DWORD), ("hWnd", W.HWND), ("uID", W.UINT), ("uFlags", W.UINT), ("uCallbackMessage", W.UINT),
                        ("hIcon", W.HICON), ("szTip", ctypes.c_wchar * 128), ("dwState", W.DWORD), ("dwStateMask", W.DWORD),
                        ("szInfo", ctypes.c_wchar * 256), ("uVersion", W.UINT), ("szInfoTitle", ctypes.c_wchar * 64),
                        ("dwInfoFlags", W.DWORD), ("guidItem", GUID), ("hBalloonIcon", W.HICON)]

        class POINT(ctypes.Structure):
            _fields_ = [("x", W.LONG), ("y", W.LONG)]

        class MSG(ctypes.Structure):
            _fields_ = [("hwnd", W.HWND), ("message", W.UINT), ("wParam", W.WPARAM), ("lParam", W.LPARAM),
                        ("time", W.DWORD), ("pt", POINT)]

        u32.DefWindowProcW.argtypes = [W.HWND, W.UINT, W.WPARAM, W.LPARAM]
        u32.DefWindowProcW.restype = LRESULT
        u32.RegisterClassExW.argtypes = [ctypes.POINTER(WNDCLASSEXW)]
        u32.RegisterClassExW.restype = W.ATOM
        u32.CreateWindowExW.argtypes = [W.DWORD, W.LPCWSTR, W.LPCWSTR, W.DWORD, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
                                        W.HWND, W.HMENU, W.HINSTANCE, W.LPVOID]
        u32.CreateWindowExW.restype = W.HWND
        u32.GetMessageW.argtypes = [ctypes.POINTER(MSG), W.HWND, W.UINT, W.UINT]
        u32.TranslateMessage.argtypes = [ctypes.POINTER(MSG)]
        u32.DispatchMessageW.argtypes = [ctypes.POINTER(MSG)]
        u32.DispatchMessageW.restype = LRESULT
        u32.CreatePopupMenu.restype = W.HMENU
        u32.AppendMenuW.argtypes = [W.HMENU, W.UINT, ctypes.c_size_t, W.LPCWSTR]
        u32.TrackPopupMenu.argtypes = [W.HMENU, W.UINT, ctypes.c_int, ctypes.c_int, ctypes.c_int, W.HWND, W.LPVOID]
        u32.DestroyMenu.argtypes = [W.HMENU]
        u32.SetForegroundWindow.argtypes = [W.HWND]
        u32.PostMessageW.argtypes = [W.HWND, W.UINT, W.WPARAM, W.LPARAM]
        u32.GetCursorPos.argtypes = [ctypes.POINTER(POINT)]
        u32.DestroyWindow.argtypes = [W.HWND]
        u32.SetTimer.argtypes = [W.HWND, ctypes.c_size_t, W.UINT, W.LPVOID]
        u32.KillTimer.argtypes = [W.HWND, ctypes.c_size_t]
        u32.MessageBoxW.argtypes = [W.HWND, W.LPCWSTR, W.LPCWSTR, W.UINT]
        u32.LoadIconW.argtypes = [W.HINSTANCE, W.LPVOID]
        u32.LoadIconW.restype = W.HICON
        u32.DestroyIcon.argtypes = [W.HICON]
        u32.RegisterWindowMessageW.argtypes = [W.LPCWSTR]
        u32.RegisterWindowMessageW.restype = W.UINT
        sh.Shell_NotifyIconW.argtypes = [W.DWORD, ctypes.POINTER(NOTIFYICONDATAW)]
        sh.Shell_NotifyIconW.restype = W.BOOL
        sh.ExtractIconExW.argtypes = [W.LPCWSTR, ctypes.c_int, ctypes.POINTER(W.HICON), ctypes.POINTER(W.HICON), W.UINT]
        k32.GetModuleHandleW.argtypes = [W.LPCWSTR]
        k32.GetModuleHandleW.restype = W.HMODULE

        NIM_ADD, NIM_MODIFY, NIM_DELETE = 0, 1, 2
        NIF_MESSAGE, NIF_ICON, NIF_TIP = 1, 2, 4
        WM_CLOSE, WM_DESTROY, WM_TIMER, WM_NULL = 0x0010, 0x0002, 0x0113, 0
        WM_LBUTTONUP, WM_LBUTTONDBLCLK, WM_RBUTTONUP, WM_CONTEXTMENU = 0x0202, 0x0203, 0x0205, 0x007B
        MF_STRING, MF_GRAYED, MF_SEPARATOR = 0, 1, 0x800
        TPM_RIGHTBUTTON, TPM_RETURNCMD, TPM_NONOTIFY, TPM_BOTTOMALIGN = 2, 0x100, 0x80, 0x20
        MB_YESNO, MB_ICONQUESTION, MB_ICONINFORMATION, MB_TOPMOST, MB_SETFOREGROUND, IDYES = 4, 0x20, 0x40, 0x40000, 0x10000, 6

        hinst = k32.GetModuleHandleW(None)
        big, small = W.HICON(), W.HICON()
        ip = self._icon_path()
        own = False
        if ip and sh.ExtractIconExW(ip, 0, ctypes.byref(big), ctypes.byref(small), 1) and (small.value or big.value):
            hicon = big.value or small.value   # 表示の拡大（125%など）では大きい方を縮めたほうがきれい
            if big.value and small.value:
                u32.DestroyIcon(small.value)
            own = True
        else:
            hicon = u32.LoadIconW(None, ctypes.c_void_p(32512))   # IDI_APPLICATION
        taskbar_created = u32.RegisterWindowMessageW("TaskbarCreated")
        nid = NOTIFYICONDATAW()
        nid.cbSize = ctypes.sizeof(NOTIFYICONDATAW)
        nid.uID = 1
        nid.uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP
        nid.uCallbackMessage = self.WM_TRAY
        nid.hIcon = hicon
        last_tip = [""]
        added = [False]
        busy = [False]

        def set_tip(add=False):
            t = self._tip()
            if not add and added[0] and t == last_tip[0]:
                return
            nid.szTip = t
            ok = sh.Shell_NotifyIconW(NIM_MODIFY if (added[0] and not add) else NIM_ADD, ctypes.byref(nid))
            if not ok and added[0] and not add:   # アイコンが消えていたら出し直す
                ok = sh.Shell_NotifyIconW(NIM_ADD, ctypes.byref(nid))
            if ok:   # 失敗したら次のタイマーでもう一度（起動直後でエクスプローラーが忙しいときなど）
                added[0] = True
                last_tip[0] = t

        def bg(f):
            threading.Thread(target=f, daemon=True).start()

        WNDENUMPROC = ctypes.WINFUNCTYPE(W.BOOL, W.HWND, W.LPARAM)
        u32.EnumWindows.argtypes = [WNDENUMPROC, W.LPARAM]
        u32.GetClassNameW.argtypes = [W.HWND, W.LPWSTR, ctypes.c_int]
        u32.GetWindowTextW.argtypes = [W.HWND, W.LPWSTR, ctypes.c_int]
        u32.IsWindowVisible.argtypes = [W.HWND]
        u32.IsIconic.argtypes = [W.HWND]
        u32.ShowWindow.argtypes = [W.HWND, ctypes.c_int]
        last_open = [0.0]

        def show():
            """開いている画面があれば前に出す。なければ開く（続けてクリックしても何枚も開かない）"""
            found = []
            if getattr(self.srv, "clients", 0) > 0:
                def cb(h, _):
                    try:
                        if not u32.IsWindowVisible(h):
                            return True
                        b = ctypes.create_unicode_buffer(64)
                        u32.GetClassNameW(h, b, 64)
                        if not b.value.startswith("Chrome_WidgetWin"):
                            return True
                        t = ctypes.create_unicode_buffer(256)
                        u32.GetWindowTextW(h, t, 256)
                        if self.app in t.value:
                            found.append(h)
                            return False
                    except Exception:
                        pass
                    return True
                u32.EnumWindows(WNDENUMPROC(cb), 0)
            if found:
                h = found[0]
                if u32.IsIconic(h):
                    u32.ShowWindow(h, 9)   # SW_RESTORE
                u32.SetForegroundWindow(h)
                return
            if time.time() - last_open[0] < 4:
                return
            last_open[0] = time.time()
            bg(self.open_fn)

        def do_quit(hwnd):
            block = getattr(self.srv, "quit_block", None)
            msg = ""
            try:
                msg = block() if block else ""
            except Exception:
                msg = ""
            busy[0] = True   # 確認を出している間に、もう1つ確認を重ねない
            try:
                if msg:
                    u32.MessageBoxW(hwnd, msg, self.app, MB_ICONINFORMATION | MB_TOPMOST | MB_SETFOREGROUND)
                    return
                if self.quit_confirm and u32.MessageBoxW(hwnd, self.quit_confirm, self.app, MB_YESNO | MB_ICONQUESTION | MB_TOPMOST | MB_SETFOREGROUND) != IDYES:
                    return
            finally:
                busy[0] = False
            request_quit(self.srv, "タスクバーのアイコンの［終了］で終了します")

        def menu(hwnd):
            if busy[0]:
                return
            m = u32.CreatePopupMenu()
            u32.AppendMenuW(m, MF_STRING | MF_GRAYED, 0, "%s v%s（動作中）" % (self.app, self.ver))
            u32.AppendMenuW(m, MF_SEPARATOR, 0, None)
            u32.AppendMenuW(m, MF_STRING, self.ID_OPEN, "画面を開く")
            u32.AppendMenuW(m, MF_STRING, self.ID_QUIT, "終了")
            pt = POINT()
            u32.GetCursorPos(ctypes.byref(pt))
            u32.SetForegroundWindow(hwnd)   # これがないとメニューの外をクリックしても閉じない
            cmd = u32.TrackPopupMenu(m, TPM_RIGHTBUTTON | TPM_RETURNCMD | TPM_NONOTIFY | TPM_BOTTOMALIGN, pt.x, pt.y, 0, hwnd, None)
            u32.PostMessageW(hwnd, WM_NULL, 0, 0)
            u32.DestroyMenu(m)
            if cmd == self.ID_OPEN:
                show()
            elif cmd == self.ID_QUIT:
                do_quit(hwnd)

        def proc(hwnd, msg, wp, lp):
            try:
                if msg == self.WM_TRAY:
                    ev = lp & 0xFFFF
                    if ev in (WM_LBUTTONUP, WM_LBUTTONDBLCLK):
                        if ev == WM_LBUTTONUP:
                            show()
                    elif ev in (WM_RBUTTONUP, WM_CONTEXTMENU):
                        menu(hwnd)
                    return 0
                if msg == WM_TIMER:
                    set_tip()
                    if self.srv.stopping:
                        u32.PostMessageW(hwnd, WM_CLOSE, 0, 0)
                    return 0
                if taskbar_created and msg == taskbar_created:   # エクスプローラーが再起動したら出し直す
                    added[0] = False
                    set_tip(True)
                    return 0
                if msg == 0x0016 and wp:   # WM_ENDSESSION：Windows のシャットダウン・サインアウト。後片付けしてから終わる
                    request_quit(self.srv, "Windows の終了のため終了します")
                    for _ in range(40):
                        if getattr(self.srv, "closed", False):
                            break
                        time.sleep(0.05)
                    return 0
                if msg == WM_CLOSE:
                    u32.KillTimer(hwnd, 1)
                    sh.Shell_NotifyIconW(NIM_DELETE, ctypes.byref(nid))
                    u32.DestroyWindow(hwnd)
                    return 0
                if msg == WM_DESTROY:
                    u32.PostQuitMessage(0)
                    return 0
            except Exception as e:
                print("tray: %s" % e, flush=True)
            return u32.DefWindowProcW(hwnd, msg, wp, lp)

        self._proc = WNDPROC(proc)   # 参照を持っておく（消えると落ちる）
        cls = "PADDOCK_TRAY_%d" % os.getpid()
        wc = WNDCLASSEXW()
        wc.cbSize = ctypes.sizeof(WNDCLASSEXW)
        wc.lpfnWndProc = self._proc
        wc.hInstance = hinst
        wc.lpszClassName = cls
        if not u32.RegisterClassExW(ctypes.byref(wc)):
            raise ctypes.WinError(ctypes.get_last_error())
        hwnd = u32.CreateWindowExW(0, cls, self.app, 0, 0, 0, 0, 0, None, None, hinst, None)
        if not hwnd:
            raise ctypes.WinError(ctypes.get_last_error())
        nid.hWnd = hwnd
        self._post = u32.PostMessageW
        self.hwnd = hwnd
        if self._quit.is_set() or getattr(self.srv, "stopping", False):   # 出す前に終了が始まっていたら出さない
            u32.DestroyWindow(hwnd)
        else:
            set_tip(True)
            self.ok = True
        u32.SetTimer(hwnd, 1, 3000, None)
        m = MSG()
        while u32.GetMessageW(ctypes.byref(m), None, 0, 0) > 0:
            u32.TranslateMessage(ctypes.byref(m))
            u32.DispatchMessageW(ctypes.byref(m))
        if own:
            u32.DestroyIcon(hicon)


    # ---------------------------------------------------------------- Mac：メニューバーのアイコン
    def _show_mac(self):
        if time.time() - self._last_open < 4:   # 続けて押しても何枚も開かない
            return
        self._last_open = time.time()
        threading.Thread(target=self.open_fn, daemon=True).start()

    def _mac_loop(self, done):
        """メニューバーにアイコンを出し、done() が真になるまでイベントを回す（メインスレッドで呼ぶ）"""
        import ctypes
        from ctypes import c_void_p, c_char_p, c_double, c_long, c_ulong, c_bool
        objc = ctypes.CDLL("/usr/lib/libobjc.A.dylib")
        ctypes.CDLL("/System/Library/Frameworks/Foundation.framework/Foundation")
        appkit = ctypes.CDLL("/System/Library/Frameworks/AppKit.framework/AppKit")
        objc.objc_getClass.restype = c_void_p
        objc.objc_getClass.argtypes = [c_char_p]
        objc.sel_registerName.restype = c_void_p
        objc.sel_registerName.argtypes = [c_char_p]
        objc.objc_allocateClassPair.restype = c_void_p
        objc.objc_allocateClassPair.argtypes = [c_void_p, c_char_p, ctypes.c_size_t]
        objc.objc_registerClassPair.argtypes = [c_void_p]
        objc.class_addMethod.restype = c_bool
        objc.class_addMethod.argtypes = [c_void_p, c_void_p, c_void_p, c_char_p]
        fns = {}

        def send(restype, obj, sel, *args):
            """objc_msgSend を、引数の型どおりの関数として呼ぶ（arm64 では型を合わせないと壊れる）"""
            types = tuple(a[0] for a in args)
            key = (restype, types)
            f = fns.get(key)
            if f is None:
                f = fns[key] = ctypes.CFUNCTYPE(restype, c_void_p, c_void_p, *types)(("objc_msgSend", objc))
            return f(obj, objc.sel_registerName(sel.encode()), *[a[1] for a in args])

        C = lambda n: objc.objc_getClass(n.encode())   # noqa: E731
        idt = lambda v: (c_void_p, v)                  # noqa: E731

        def nsstr(t):
            return send(c_void_p, C("NSString"), "stringWithUTF8String:", (c_char_p, t.encode("utf-8")))

        def tip():
            return self._tip()

        pool0 = send(c_void_p, send(c_void_p, C("NSAutoreleasePool"), "alloc"), "init")
        app = send(c_void_p, C("NSApplication"), "sharedApplication")
        send(c_bool, app, "setActivationPolicy:", (c_long, 1))   # メニューバーだけ（Dock に出さない）
        # メニューの項目を押したときに呼ばれるもの
        IMP = ctypes.CFUNCTYPE(None, c_void_p, c_void_p, c_void_p)
        quit_req = [False]

        def on_open(_s, _c, _x):
            try:
                self._show_mac()
            except Exception as e:
                print("tray: %s" % e, flush=True)

        def on_quit(_s, _c, _x):
            quit_req[0] = True

        IMP2 = ctypes.CFUNCTYPE(None, c_void_p, c_void_p, c_void_p, c_void_p)

        def on_reopen(_s, _c, _e, _r):   # Finder・Dock からもう一度開かれたとき：画面を開く
            on_open(None, None, None)

        self._imps = [IMP(on_open), IMP(on_quit), IMP2(on_reopen)]
        cname = ("PaddockTrayTarget%d" % os.getpid()).encode()
        cls = objc.objc_allocateClassPair(C("NSObject"), cname, 0)
        objc.class_addMethod(cls, objc.sel_registerName(b"openUI:"), ctypes.cast(self._imps[0], c_void_p), b"v@:@")
        objc.class_addMethod(cls, objc.sel_registerName(b"quitApp:"), ctypes.cast(self._imps[1], c_void_p), b"v@:@")
        objc.class_addMethod(cls, objc.sel_registerName(b"handleReopen:withReplyEvent:"), ctypes.cast(self._imps[2], c_void_p), b"v@:@@")
        objc.objc_registerClassPair(cls)
        target = send(c_void_p, send(c_void_p, cls, "alloc"), "init")

        bar = send(c_void_p, C("NSStatusBar"), "systemStatusBar")
        item = send(c_void_p, bar, "statusItemWithLength:", (c_double, -1.0))   # NSVariableStatusItemLength
        send(c_void_p, item, "retain")
        button = send(c_void_p, item, "button")
        icon = os.environ.get("SW_NAS_MENUBAR_ICON", "")
        img = None
        if icon and os.path.isfile(icon):
            img = send(c_void_p, send(c_void_p, C("NSImage"), "alloc"), "initWithContentsOfFile:", idt(nsstr(icon)))
        if img:
            class NSSize(ctypes.Structure):
                _fields_ = [("w", c_double), ("h", c_double)]
            send(None, img, "setSize:", (NSSize, NSSize(18.0, 18.0)))
            send(None, img, "setTemplate:", (c_bool, True))   # ライト・ダークで色が自動で変わる
            send(None, button, "setImage:", idt(img))
        else:
            send(None, button, "setTitle:", idt(nsstr(self.app.split()[-1])))
        last_tip = [tip()]
        send(None, button, "setToolTip:", idt(nsstr(last_tip[0])))

        menu = send(c_void_p, send(c_void_p, C("NSMenu"), "alloc"), "initWithTitle:", idt(nsstr("")))
        send(None, menu, "setAutoenablesItems:", (c_bool, False))

        def add(title, sel=None):
            mi = send(c_void_p, send(c_void_p, C("NSMenuItem"), "alloc"), "initWithTitle:action:keyEquivalent:",
                      idt(nsstr(title)), (c_void_p, objc.sel_registerName(sel.encode()) if sel else None), idt(nsstr("")))
            if sel:
                send(None, mi, "setTarget:", idt(target))
            else:
                send(None, mi, "setEnabled:", (c_bool, False))
            send(None, menu, "addItem:", idt(mi))
        add("%s v%s（動作中）" % (self.app, self.ver))
        send(None, menu, "addItem:", idt(send(c_void_p, C("NSMenuItem"), "separatorItem")))
        add("画面を開く", "openUI:")
        add("終了", "quitApp:")
        send(None, item, "setMenu:", idt(menu))
        send(None, app, "finishLaunching")
        aem = send(c_void_p, C("NSAppleEventManager"), "sharedAppleEventManager")   # finishLaunching のあとに（上書きされないように）
        send(None, aem, "setEventHandler:andSelector:forEventClass:andEventID:", idt(target),
             (c_void_p, objc.sel_registerName(b"handleReopen:withReplyEvent:")),
             (ctypes.c_uint32, 0x61657674), (ctypes.c_uint32, 0x72617070))   # kCoreEventClass, kAEReopenApplication
        self.ok = True
        print("メニューバーにアイコンを出しました", flush=True)

        def confirm(text, two):
            alert = send(c_void_p, send(c_void_p, C("NSAlert"), "alloc"), "init")
            lines = text.split("\n", 1)
            send(None, alert, "setMessageText:", idt(nsstr(lines[0])))
            if len(lines) > 1:
                send(None, alert, "setInformativeText:", idt(nsstr(lines[1])))
            send(c_void_p, alert, "addButtonWithTitle:", idt(nsstr("終了" if two else "OK")))
            if two:
                send(c_void_p, alert, "addButtonWithTitle:", idt(nsstr("キャンセル")))
            send(None, app, "activateIgnoringOtherApps:", (c_bool, True))
            r = send(c_long, alert, "runModal")
            return r == 1000   # NSAlertFirstButtonReturn

        mode = c_void_p.in_dll(appkit, "NSDefaultRunLoopMode").value
        NSDate = C("NSDate")
        n = 0
        try:
            while not done():
                pool = send(c_void_p, send(c_void_p, C("NSAutoreleasePool"), "alloc"), "init")
                try:
                    until = send(c_void_p, NSDate, "dateWithTimeIntervalSinceNow:", (c_double, 0.3))
                    ev = send(c_void_p, app, "nextEventMatchingMask:untilDate:inMode:dequeue:",
                              (c_ulong, 0xFFFFFFFFFFFFFFFF), idt(until), idt(mode), (c_bool, True))
                    if ev:
                        send(None, app, "sendEvent:", idt(ev))
                    if quit_req[0]:
                        quit_req[0] = False
                        block = getattr(self.srv, "quit_block", None)
                        msg = ""
                        try:
                            msg = block() if block else ""
                        except Exception:
                            msg = ""
                        if msg:
                            confirm(msg, False)
                        elif not self.quit_confirm or confirm(self.quit_confirm, True):
                            request_quit(self.srv, "メニューバーのアイコンの［終了］で終了します")
                    n += 1
                    if n % 10 == 0:
                        t = tip()
                        if t != last_tip[0]:
                            last_tip[0] = t
                            send(None, button, "setToolTip:", idt(nsstr(t)))
                finally:
                    send(None, pool, "drain")
        finally:
            try:
                send(None, bar, "removeStatusItem:", idt(item))
                send(None, pool0, "drain")
            except Exception:
                pass


SHELL_KEY = [""]


def write_shell_key():
    """Tauri 版の窓から終了を頼むための鍵を作り、窓が決めたファイル（SW_NAS_SHELL_KEYFILE）に書く"""
    path = os.environ.get("SW_NAS_SHELL_KEYFILE", "")
    if not path:
        return
    SHELL_KEY[0] = secrets.token_urlsafe(24)
    try:
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="ascii") as f:
            f.write(SHELL_KEY[0])
        os.replace(tmp, path)
    except OSError as e:
        print("終了用の鍵を書けませんでした: %s" % e, flush=True)
        SHELL_KEY[0] = ""


def remove_shell_key():
    """きちんと終わるしるし：鍵のファイルを消す（窓は、鍵が残ったまま止まったら「異常終了」とみなして起動し直す）。
    終わると決めた時点（request_quit）で消す。消すのは自分が書いた鍵だけ（入れ替わった新しいエンジンの鍵は消さない）"""
    path = os.environ.get("SW_NAS_SHELL_KEYFILE", "")
    if not path or not SHELL_KEY[0]:
        return
    try:
        with open(path, encoding="ascii") as f:
            if f.read().strip() != SHELL_KEY[0]:
                return
        os.remove(path)
    except (OSError, ValueError):
        pass


def ver_tuple(v):
    try:
        return tuple(int(x) for x in str(v).split("."))
    except ValueError:
        return ()


def request_quit(srv, why=""):
    if getattr(srv, "stopping", False):
        return
    srv.stopping = True
    if why:
        print(why, flush=True)
    remove_shell_key()

    def stop():
        if getattr(srv, "clients", 0) > 0:   # 開いている画面に「終了しました」を届けてから止める
            time.sleep(2.3)
        srv.shutdown()
    threading.Thread(target=stop, daemon=True).start()



def serve(srv, tray=None):
    """サーバーを動かす。Mac でメニューバーのアイコンを出すときは、サーバーを別スレッドにしてメインスレッドでアイコンを動かす"""
    if IS_MAC and tray is not None and getattr(tray, "mac", False):
        t = threading.Thread(target=srv.serve_forever, kwargs={"poll_interval": 0.5}, daemon=True, name="http")
        t.start()
        try:
            import signal
            signal.signal(signal.SIGINT, lambda *_: request_quit(srv, "終了します…"))
            signal.signal(signal.SIGTERM, lambda *_: request_quit(srv, "終了します…"))
        except (ValueError, OSError):
            pass
        try:
            tray._mac_loop(lambda: not t.is_alive())
        except Exception as e:
            print("メニューバーのアイコンを出せませんでした: %s" % e, flush=True)
        while t.is_alive():
            t.join(0.5)
        return
    srv.serve_forever(poll_interval=0.5)


def start_autoquit(srv, idle=20.0, grace=90.0, enabled=True):
    """enabled=False：画面を閉じても止めない（OPERATOR はコピーを、RECEPTION は書き込みを裏で続けるため）。
    一度も画面がつながっていないとき（ブラウザが開けなかったなど）は止めない（もう一度起動すると画面が開く）"""
    srv.clients = 0
    srv.ever_client = False
    srv.clients_lock = threading.Lock()
    srv.last_client = time.time()
    if not AUTOQUIT or not enabled:
        return
    try:   # テスト用に短くできる
        idle = float(os.environ.get("SW_NAS_AUTOQUIT_IDLE") or idle)
        grace = float(os.environ.get("SW_NAS_AUTOQUIT_GRACE") or grace)
    except ValueError:
        pass
    t0 = time.time()

    def loop():
        while not srv.stopping:
            time.sleep(2)
            now = time.time()
            if srv.ever_client and srv.clients <= 0 and now - t0 > grace and now - srv.last_client > idle:
                request_quit(srv, "画面が閉じられたため終了します")
                return
    threading.Thread(target=loop, daemon=True, name="autoquit").start()


class Server(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 64   # 既定の5だと同時接続が多いと取りこぼす
    allow_reuse_address = not IS_WIN   # WindowsのSO_REUSEADDRは二重起動を許してしまうため使わない


def port_free(host, port):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        if not IS_WIN:
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        s.bind((host, port))
        return True
    except OSError:
        return False
    finally:
        s.close()


def disable_quick_edit():
    """Windowsのコンソールで誤って文字を選択すると処理が止まる「簡易編集モード」を、このウィンドウだけ無効にする。"""
    if not IS_WIN:
        return
    try:
        import ctypes
        from ctypes import wintypes
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        h = k32.GetStdHandle(-10)
        mode = wintypes.DWORD()
        if k32.GetConsoleMode(h, ctypes.byref(mode)):
            k32.SetConsoleMode(h, (mode.value & ~0x0040) | 0x0080)
    except Exception:
        pass


def main():
    for _s in (sys.stdout, sys.stderr):   # 出力先がファイル/パイプでも表示できない文字で落ちないように
        try:
            _s.reconfigure(errors="replace")
        except Exception:
            pass
    ap = argparse.ArgumentParser(description="%s — NAS演者フォルダの読み取り専用監視" % APP_NAME)
    ap.add_argument("--root", action="append", default=[], help="監視フォルダを追加（複数可）")
    ap.add_argument("--label", default="", help="--root の表示名")
    ap.add_argument("--depth", type=int, default=3, help="演者フォルダの階層（学会/会場/セッション/演者 なら 3）")
    ap.add_argument("--port", type=int, default=DEFAULT_PORT)
    ap.add_argument("--no-browser", action="store_true", help="画面を自動で開かない")
    ap.add_argument("--browser", choices=["app", "default"], default="app", help="app=専用ウィンドウ / default=既定のブラウザ")
    ap.add_argument("--lan", action="store_true", help="同じLANの他端末から閲覧のみ許可（操作はこのPCのみ）")
    ap.add_argument("--data-dir", default="", help="設定・ログの保存先（既定: このファイルの横）")
    ap.add_argument("--legacy-ui", action="store_true", help="旧画面（v1.13 まで）で表示する")
    a = ap.parse_args()
    use_legacy(a.legacy_ui)
    disable_quick_edit()

    data_dir = a.data_dir or pick_data_dir()
    os.makedirs(data_dir, exist_ok=True)
    moved = None if a.data_dir else carry_over_renamed(data_dir, "SW_NAS_WATCH_HOME", "sw_nas_watch_data", "SW_NAS_WATCH")
    if moved:
        print("前の名前（SW NAS WATCH）のフォルダから設定を引き継ぎました: %s" % moved)
    store = LocalStore(data_dir)
    raw = store.read_json("config.json", None)
    cfg, cfg_msg = startup_config(store, data_dir, raw)
    if cfg_msg:
        print(cfg_msg)
    for p in a.root:
        if not any(norm_key(r["path"]) == norm_key(p) for r in cfg["roots"]):
            cfg["roots"].append({"path": p, "label": a.label, "depth": a.depth, "enabled": True})
    try:
        cfg = validate_cfg(cfg, data_dir)
    except ValueError as e:
        raise SystemExit(str(e))
    if cfg["op"].get("enabled"):
        print("※ 会場オペレーターモード（発表PCへのコピー）は PADDOCK GATE に分かれました。このアプリではコピーしません。")

    host = "0.0.0.0" if a.lan else "127.0.0.1"
    url = "http://127.0.0.1:%d/" % a.port
    if not claim_port(host, a.port, url, APP_NAME, None if a.no_browser else (lambda: open_ui(url, data_dir, a.browser)), VERSION):
        return
    store.roots = [r["path"] for r in cfg["roots"]]
    store.write_json("config.json", cfg)      # 2つ目の起動（すでに起動中）では設定ファイルに触れない
    write_shell_key()

    mgr = Manager(store, cfg)
    srv = Server((host, a.port), Handler)
    srv.mgr = mgr
    srv.token = secrets.token_urlsafe(24)
    srv.version = VERSION
    srv.lan = a.lan
    srv.stopping = False
    srv.allowed_hosts = {"127.0.0.1:%d" % a.port, "localhost:%d" % a.port, "[::1]:%d" % a.port}
    srv.page = page_html()
    mgr.start()
    start_autoquit(srv, enabled=not a.no_browser)   # 画面を自動で開かないときは、閉じたかどうか分からないので自動で止めない
    tray = Tray(srv, APP_NAME, VERSION, "PADDOCK_SCOUT.exe", lambda: open_ui(url, data_dir, a.browser if a.browser != "none" else "app"),
                status_fn=lambda: "監視中 %d か所" % sum(1 for r in mgr.cfg["roots"] if r["enabled"])).start()

    print("=" * 64)
    print(" %s v%s   (読み取り専用モニター)" % (APP_NAME, VERSION))
    print(" 画面: %s" % url)
    print(" 保存先: %s" % data_dir)
    for r in cfg["roots"]:
        print(" 監視: [%s] %s  (階層%d)%s" % (r["label"] or default_label(r["path"]), r["path"], r["depth"],
                                          "" if r["enabled"] else "  ※停止中"))
    if not cfg["roots"]:
        print(" 監視フォルダ未設定 → 画面の［設定］から追加してください")
    print(" " + (STOP_HINT if not a.no_browser else "Ctrl+C で終了（画面の［終了］でも止められます）"))
    print("=" * 64, flush=True)

    if not a.no_browser:
        threading.Timer(0.6, open_ui, args=(url, data_dir, a.browser)).start()
    try:
        serve(srv, tray)
    except KeyboardInterrupt:
        print("\n終了します…")
    finally:
        srv.stopping = True
        tray.stop()
        mgr.stop()
        srv.server_close()
        srv.closed = True


# ---------------------------------------------------------------- UI
# 画面（React でビルドした1つのHTMLを圧縮して埋め込む。dev/embed_ui.py が書き込む）。
# 旧画面（下の HTML）は --legacy-ui（または環境変数 SW_NAS_LEGACY_UI=1）で使える
LEGACY_UI = os.environ.get("SW_NAS_LEGACY_UI") == "1"
UI_PACK = (
    "eNrcvWt327iyKPj9/AqZk9EVtyFFsp2XZEYn8SPtTvzo2El34u3rQ4uQRIciFZLyI7bOb5+qwpuSnfS+e9aaOb06Fog3CoVCoVBV"
    "2FyJskF5O+W1cTlJXv/HJv7UkjAdBd5l6GEEDyP4mfAyrA3GYV7wMvBm5bD50lPRaTjhgXcV8+tplpdebZClJU8h23UcleMg4lfx"
    "gDfpg8VpXMZh0iwGYcKDDtZRxmXCXx+92d4+3Hq/+VR8/sdmMcjjafn6Ok6j7Lp1/Of528PDk+CuzL7xtOudn58cvt85OD/32DfI"
    "gRFvjo7e7x1sY9RFWHCM+rzz8XjvEHPNe5tPZY3/UavJyms48sCbZNEs4dDvPCuKLI9Hcfq6MZylgzLO0oZ/B+MpyloaAKhmExhY"
    "a5DzsOQ7CcevhpfE6TfPb+U8+RAXZS8eNtJ6PW0VsynCo7DDDdnYFDJnYeT5fs7LWZ72hlneEO0ktWxY0019n/H89pgnfFBm+Zsk"
    "afwvbO0UigeVqs7+F1TWSPxeyq9r+7MyxN4fXhQ8v+IQH7y+M23E2EbiQ0/jFsEgCLzBOE4iHIDnm4wZZoxbYRTx6CCLeOFnrTIc"
    "HeCMQ5kPewfvvXo9w7Hjt9ujej1vZP7cb2WiFw01KnanG+uutFkxuyhzziE493sK7rUSxiJBHwd3854AVC1pxYBdozwub+t16L7+"
    "CqwUnyXQpSHPc54fZUk8EHndqKCaB0sRDhwSDuCAZgVvwmxH0GnA2sLrxy3rM/DidJDMIu51F0qGaZbeTrLZYplsEpdetxJZAESb"
    "Avc8Fs81FHBG72CekhafKlzBcLDS7ingIKR6Q14OxpBtDGNisT+f+w2/dxXmtSgK7vgNYV/3bj5nvycATTasxP6BIH76j3/8R+0f"
    "tf8EYPC04LWPPByUGJNjoDXNYXqpW61JnLYuC0jC1K1segs9H5e1xsCv7YYDfpFl31htLx20amEa1eKyqIXDYZzEsGyKlix2Mo6L"
    "WpHN8gEHkhHxGnzKlqPaLI14XivHvLa/d6Kia8NshtWlmIBVfNjb2jk43qlB1VxG1/IsK2tRnNOKuUX8La2GENGwA08RNNd5cHw7"
    "uciSFmK8J0bJxbL2fHYzXpKMIAsTSB0tSx3m4UiWvlqWXpR5PCjPYZ1wyHK7tIE8w+HkkH75QPpVHFH6t2XpRH1vsAfXS3uY5ddh"
    "Hp0DmkCWg6WdnBVTBDekHy9Ln/BJBmlby9KS8MctpF0MVFpc8jyEmTALe2fc4P6dXM5IRtJZktzfIx2CyeIrsEIuLmH2vD4mdBs8"
    "uBjU6/z0YnB2f89Pvf/8T1Wnd8ZUKVhxqgGvz7tY0p/jHE8B0eNiHxCn5FHXouqiAyudOeMpUNkZ380AQT5NI8BRO59O/8inCeD2"
    "cflQhmNeLibO2TgKDmlArbAo4lHKJhEuNg2PraLBWcpK/w4RFed3WgSc0YeczCAVnzBpRTCJxMeMupoH5f39NJpvUckyQ4C04oKW"
    "7lY2mWYpbsXQnpOhkF0NdFehC0RoFqehXrfiNJBhRlZo5vxynGfXtZ08RyxQFTdarZbfrZXhNw5rP62JunA1Fphcg6mJw4sEEsus"
    "JkZSy/JaWNNguR7Hg3FNzNLjVbQ8v2dDpFWZjwYmMoSx7p7nVwAyNJNvwUROSaVeC1FU1Z5VHuvWo7iJEAluItNUYLdrMk7DfwcW"
    "IMaPw2AaWu0hP3AT9cZhizaMfIaEEbL0xlFjHDK7Oz7mioujWc4rCATbDda9PQje5Hl4C5nol400chtYjsPi8Do9ghHwvLxlkzC4"
    "G8xgm01LWpdzdgUL4Bu/xb0fxoI/5+cFT1SIKDVyAwY6t5GCDvYiZ7SHxYR/LKMfYrskRiI9ynE/SBFWK0FwlcVRrQ08AOTFKJ+l"
    "LeiAnRIHnrdKsZDoj6IWMKhJI2W5X6+vXEWVQTUwupGc5mdBCn/EThsGYT4iBqdoJTwdlePmGnYrBBrX8YFDQKYHwBCUPZ7AbgZJ"
    "nc3QJ74My0vYNkKfRUG7F22GvWh11R+cRmem5tNode2sZ1U2mEM9HJZjK+LDcJaU2MfCwCAM3BQW+tRva+z0HdI4xHq7e/JErPnu"
    "dU4ktssZTlhM85Uxws5uws6z65Tn3QmglpjgueFcjsaCpjxYI3GeVG1K1XKcGVk1FwtANcBbImBVfxNau4i1C2iiBeSJsAEhoxqH"
    "QV/npo43tBMh6NPgzgu8rhe0PQY/EFjzFMvpPfFWsW9E/RtPT4Pu2dMR00Si1L1IT8uzudh1DgfB038+XX06ssh8bMPjp10m9MSP"
    "PvTSwx4ganbTVpkdAxORjhrrz30zlDQRC4TB2hBDAr5QNtED5EZeFliqYZzyyLu/pwjg0hIeph6iMhcrh/A4C1Y6iLdqb/YzXP6E"
    "ssV1jGxmDJw5HLG8gnridekjnU0ugC3pUu4LYAe+9SheDq8ry5rZEJUAF0blazdjKjpHfM4krwt94bDYE4hgPMix117fa3mrAM2M"
    "tf1uzrYHwP72G3Dc9JjckmA8ZWCm7HDAvCf1p56/6sEfBqBKCFRQQM9ipCcmmvt+N9EVAZ4ltNYDQOiElauNlQSn4v4+w4MPhKBT"
    "FNP3vC7OFH34D7S+yn0kPtNZAbVBkACdBUAIrdF181VAQRwZ5FbUIQSSEG5ySVl6IVCGuzjgp+FZTxCPHIESw/LuZasBDDKmQQ4A"
    "H+aK3AwCYr4U1zSwuSZqiAcDQfggEza4AqjDWylsPg3fb0WwF/T8OIhbV2Ey48y0CZ1h1VY1kSNkk1gguYU0kEgM7UjOQWwjsNPn"
    "vJYCCw9NAHkKIUKcQ2pE8WoNOgN0a95qg85Zp5ItEMXPAH4yArBtXIOZKGp33qrco/ATmmxdZnHa8FgNJ2XudVP48Vu1vWHtNpvV"
    "JrAmSmRLgKDhISSE00mCB3BcZwg1SXlZDU6HyJiESLWB1BYlDyNkRhTumuV5kqv9S6wrWlaKBab5y4PTM8D0tipMCzpHHLXRNDbE"
    "RsxTyWKWAPTnPrMI2wcibNhU6xyZpVkBoGp2FK2D2JwXsCH00gCYVMBHODilDZukOSXbwHe7FSHF0DEdpisMSn/O/tV61tx6fOZm"
    "dvK2rbypP68MtaNhqzKpLbAn8E/HE7V+y6scSgkMRpmHaRHjQGTkxTi4E2yRyLsdF9MQSBpsUG85s1PeYvRWlg7jUbdMnKRDuWNa"
    "zM0l8ogOFw3ZiYHGIzGuBSk+4nT2Ncfw2sUMULFApKQmAPfmf7S2FGdwNwmn3ZOcwcLeCQfjrs3rIyoSUlpnlbQVTqfJreBpNcMB"
    "E4qTOsATVNdmjQUuaYRdqG11FaYwhdIZsTVO2aVlzOaYzv37+9OzOcvSxC0IE71CW7977BDDVyNvYbEav5nCogWY0VIe8PgKVmut"
    "AKqTSNFGTZ71xZK2Vi6fz3sASM39bhXwuSvP9sFoDF9H8pge3NIXcMwmO/DWf7SO6ai/Dyf94AqzHMtTdXCAX+fnxztbH3dOzvcO"
    "TnY+Hrz5cHy+fXh+cHhy/ul45/zw4/mXw0/nf+59+HD+dud8d+/jznZwgeWg18FlBIFBAm1JEWRQnVmLyCwBk11UntNOxgAbOeO1"
    "yawoaxdcE14JJQboVhKFnMJBFuAKTMmqh1AT9AuOE3gWFpybD7SMWBYWB4KxywLFxdmsOnZ1gUuPBZcORQxnuYRlTyyWXXCTyDjR"
    "EcRhhcXuuSRFSF3poGBx/IPlHD9GN/LTAXL8A5t9DnWf+iGkdDFZcIGDBw4EA0Gilh8IBv5dKA8CA7+ndn9xIBjQgSBcciCwKgvn"
    "v8ByJ8Ryx5LdzhWjnRHiC/n2ljx1Llm3QC915d/G7FzO0WfkCuCo4HyvYQRgIeyNW0RD2uxIirCIrjJop4ChyK9zOUGiLhE1SrKL"
    "MEGhs6TEvKWqsDpyiR0Rfe5yzKMqDrgZlFoxt5GO2g1JUhgs0rbbqHURp1GDesE1dUiFzBzWmqn3Ix8GC8Ild1PBzFL65uTmS85I"
    "YyaYj66gRHHxGbkh1fkbpC8oaXu0ki2AxzS8RVF8907ujd1mh8mdD2F0jtcx3Q9jagTFehV5ULXK47E6DQ6A2AGn1k31QhDSupSq"
    "gsby8kTvn0tAWyYts7/2nC8UVpX57R1vwPkmTmFR3t65GUQjM2C4UP5zrmki8GNbkP0iHHxbOhDY6BU5sfNSlrks/zDSVwqLjJAu"
    "S27zi9mIsNZGBJ1IFw1RJf2hyp3spomd4RB2tF8ZmshpD2wvWsTPSqE94ENU7skURaywZf4WplHCF3aY5RVUSsnMqk7Y/HKs49eH"
    "USlij+dDCDtR+etV2fntevYfwvpKecxnl/vIgQkD2vJLgJGZXXgsJwILJYdm/qsi2wfKCKGnKXWbDnZuSp7DUjoGSveLk7lQzO39"
    "stX9QE0mq8CvK54XWM7rvGyttzpebxi15F1U8AcxE28CE/WTW6nmZXHTzGFfiSf8f94N1fY4eMMOx49eU+395CLqZPxTEe3uONge"
    "/ws8aWvhZMN+jP+ubPfbz2W75YKktvyZCPchyW/PCIf9k7Ej5f0x/pmU93FJa1qVtKbLJa3pUknr4fgXJK27YyNp/T0xR5K9cQ8+"
    "YSkE3yIZKjAYmZX1e0JLqwhMHLuu3AJ/5Qj7g0rscfTo5XABJ2C89s//Zy2/hk1njZy1ccL2Baa+D06UMO5ECPT2/R7vIjr02pvv"
    "eyJXxoP3zc7r1687bMKDk9OMnyEatTeTxoRDVT5FBfvs5PT9WQBR74OMi+MAyVDxLGrpRJyYs7NsHOUqgvc6OW2f2ZoDJ3S6svMp"
    "sQgtKuzdfoCFGA5lmk0bhOHvYdnAEDEheC8HJEfSpjHICtlhDv3FkfUyvnmYywFflsHaPxoZX+34wGwex9DCZXnGvgGPVq522F4O"
    "Ed9KAYTXSeM4Zu99/1u5OYGVhRF7ORTy+w0BF/ii7MF7Bu1/K/2uTIByVLFIuCyNuNGt672CcLWmCowlZPYNABN3qgtYD3uAdDfN"
    "fRNWRwKEWbv/vnvSiiNIj6O5uUoFUgIgnITpwBH2L6a20uzakchKOb6VpccN24u5F7feGGuBfZZkvgIDg21YVSwMMpH08zpkxmY4"
    "l8fY0zMW4Z9h0GFTQZknwTq7CVY67Bb/HOCfa3XjUPDyBLZj4Leca3kTLc51Y5V/kPAwX1bCThBlZlYbe5MJj5BibHozql1HdMWu"
    "IXKm4VU8QnUBzFav68+WJFxxOrI2imXJcP7aS6ez8gjOZH87tzxCLsloKTtd4mJVC20/KBuR39uXt0E9Wsb7tFXR0UaJjzGTQvp9"
    "eeYCWG0GJ5TGLDwN9pHmxzkphWEmljYGbN+3FkFPNGtRmy1JQWhysYds5RZ1xkqg4rJvPsx+m12kjWNR1d2S/tfrt2Vji1k9bJ7Y"
    "zRyLdSbwCPZIam7cOPLZEYqIEcvE5fP7YEIHQ4TTJRBbQEXsSm+qG2qsNKaVgb7e9+/vT2B3/9zwfUOTpxqcPbNSM+4uP5NJ4fwU"
    "9rg4QxWzD/yKCxoKJDHjC+1uAg0FkLprraGvXiauxorV0oR3pzDFJQmccvjLcKziCien4VIaEhg1cJJwATWWt3SKDNMsXJbuNFyW"
    "1jwADLFYR1G/w1yfuPUyf0/LXFCCEU7NlUjByWG7wTO2BwGDyZ+Nak2jOvjm3uaudWcJB0TCrys1DOr4yQLMenvBidytYISIAfvB"
    "VQPw7sQICPb7cFCGzcHqoaSB1Gnq/Yxbcz1zpto9tM8aCZ6e1NqSJfZ5UYQjvjUO05QnSExEh69KUrFwk9kFD66EtthaTwY6rSyd"
    "iFxBwpnb5gWcXrKilLU07AG4Ga+hc6xt65jA8oOFehWcsNH9PUKgzRAYFqRh5mmNHQXXtmLrycIM+XOGuGZi9+AYfyRRHubaTlHE"
    "Vid37OQP2bVO2LATDnArS3Taup0mhOpAGgWKWSmfCp6/TbLBN0jUZdfsHAPcH5NF+Q+A5sRdx3OnWAZHx3TGd274YFY9zt7e398A"
    "SA2R852ypPQDPPiEf3QO5tBk+/XJ/X1n7dnmSR+1brKEt7iQwbuFlIZUDSY/RskJcKkofC+vOU9rbeKOoRpWw2Iw9toQS9Zy5JNr"
    "Y+CpiQkOU8xUG06LhRsjz+/uBm3oxn5YjlvDJIM+dPj60xO/+8wZzIirg9yRTeKWsAeTarndOC9KBXlUE15SiGiWXS51xGwAMqkf"
    "MJFqAR2hFbAmfta7ggCsS80Cec7q7geTudobJsE+UQfFIFvyQyBjc6f1aYhSsmVz7mTL+fcZL8qjMLZvWaqZZumfcTnWaGkGhWtO"
    "DuvkgWHRz4b4edZ1B3cSrFuDO7EHt//Y4NSJbMliYPvAEatNcIHQyr5KgvfeZlffSyLdb7wP3sMxNwlv4dhg5ZTqH8B4b77vA/v/"
    "vptxv4unGWbGLvdL2DCMggjAAqLWntlKIwAKiOu0X6y/2Oi8XFu3kzYoiW9UMAEin/F1tZPB1/tVYHNOgrs46g5XV5kiAd195uzh"
    "3ROmN8Tue+bu4lAr00xUt9mZs/evMw6HE4u1eg+8VARjZIjigdpsT2gPj1CAcNBvGHame4DEhLbi902AkI8nGqs2yZpBdYvEx2cn"
    "7jyPs1kSfYl5EgWf7YTrPJwupYRiEU3UscXC6IcW0QN3wg7uobL5MfAaB0bacBzRjv12HBz8siQvyib/8yR4H1GC9zsP3o7Nhn1I"
    "IgXJ7aeBNy7LadF9+pTAcFm0snz0NMoGxVPaMpoRx67nLbTN6ccp6b2iec0qZ2XQ6ZWb1VvGXrm66qergVeHlOL0DLOmWMenj3v6"
    "lrphbhBLLY7y9uM0HsYAHHn1ix2o/V9009urXcWwR9W81XTVw/2IQDEEbK9JrgY1eFEnBuPTLG1OVGURv6rx9CrOkQGC/Q0LU0Gq"
    "v6AJDKOIZMRhUhvzZArJteswT2HPK1oekcGtiBitY16yMndUqD8Jkf7dmFSpfYa/q95WOIUxcQ+F9jqrzELgL/NTfhakjAfAOG+m"
    "CnocoLcVodFLI4UM4i73UxqsKMIobJJeAweo1dalmZKycHkszb2JxJw+y7Ofymj3x8HT/33afdP8eh42f/xz1m5vtZv4s/2c/r6k"
    "j1362KWPtd1d+Lv+grKtv9imv7vw0dnFlDWooUk/2/iXsq11XmLKVps+dnfgY73d7sDH9gsss/uKUna3t/Bje5c+dne3z/6/2rF/"
    "Nlvt5its+u0LbKYt2nxOzazvUjMb7bN/PHnK9gYo/DwZuJhlGyvkmZAXnwwY9/sr7a6K2BMRne7+uAXUB28F+ycDRC7IBKkixFY6"
    "FiJ+HiuNTaF3r49ppTLJUuK6lU5lY06l+qU+vwgFzIJuAbyuLNUW6pdKy7OrBoH9VK31V8pWOBjwaVm8FfkKNLjgrTIDBp7nW1BD"
    "w28VSBwbbfbMRxXLwIvCMmxKhVUPyVHT8/VGrA0rzFjfu2NNq0YfqVgvFkh8PQjInxtAWJDyFVAIXpLFWFfNp4pZUCJPaBPKS+ZC"
    "CcuKg/Cgkfoi+nk1Gjj41+lcj0cP5yM3yrYsZpnU2a8AMsAm1+7v8Wdd/GwInf2wLPP4YlZysqPLl0QWU9jhgkSkoD4OnH8UJQhK"
    "pk0E8JsqkZYCQuFfhIsQbS1/ANH/EMTKcmCSXfGdybS8FfqXQUbE7Rrl/j1PqZDUojAd8TybFcktUNs9ONDmv53sf6jZuhnqY2vM"
    "B99IM03lwrNHDjvClrAD3QG6jlzJn4Ka6+TfbiPBaOmE8jbhXquYJnHZ8Gqe35Kaa44o/poT0YaNgKYBVxXaduB5EUK4xPze6akn"
    "JmNLWKx6TH43pQmrd8ZOvUESFgVCD5IpTLG4y+5muUc2HTKmnO58n8VXEIfhJqePs7Ol/ZMqlqftsx50NdVdTVmHunraOav21hu4"
    "kIJ2ADSjkQwXU54kBGb4IM1b7+xXQLNG7blLeaHpcFZmHzleyWJTXF74fuSClyk+4lhzOEYiOAazQnYJJxBNOt8k03H4d3pTad8D"
    "6pld70LcMeyKgHlhcZsOatipXWyOQkdw1iCj4jxLCoV2+AvcWxRTlyIVOIoHuOfvpTKg4j8C5pcca0KeGBmQyUFGSjV4CB/HUQSN"
    "w+F4CozLPlmxQkCnw0JLa1MoXOylSZxyZFijQ1QyzCV8IEAwjGrFAHLDDw8nCWA5MKZ8coxxfxez139l+gZi9cGUTAAo8ZRmZzIr"
    "Kaogu2EInv1ie+3FleQNFBflAROTClPjX6luY+nCBFRPCqgrz67xpwD6RBgOG9Qv1fp8ea1Q3THWAVXhWe7X6nr2cwCT0DMMnp7+"
    "s9k9a5wCf3Pm20YdV7YVCi5tqO3TdKpqmxPZScvmmNPZBfBpRBxwEy3UCZPCPLyIB01EyJqKbBbjeFjWAPKq4CCJp81pWI5FKEf8"
    "BEjC4QBtnvNplhAlXRbXhIMLfBYyTZqXyi+hZYbEFw5fcKSze8ZTXDhNXC+jnA5FUDBpZrA1wdlZfFBHUKgUNalCGdZ5YNE2h+Ek"
    "TmQY59uEmmF0ibqmIgKOTbCdq4/bRGaUxx3xcS3AMUpup+Mm+h2QQTjOA1TFeMfw8QMyw0FiMfEK9YkGeMbAXNCBq+aNDAvra/iM"
    "J3CWsUCT8BIA2MQ9mT6xCxCQI56E+TdIhdwqOIl1kLCxBntuTvMqhHxoRqBiYFsefEuRTkxRxgSdwDMpoHJW8GanNs1oLptAXOCg"
    "VtN9oikGoBTjcGp3tSizqewXBdVEoKHON466wLPR2HTDjTZ9gfjsG29GIdRPxg1WRDYcwgaqYnAQgKf2JxpXqO8JmuomMfyoGKtH"
    "+EleIWqoSdcM08EYD5UYxiOvYA7EtxkhHdpdYJooM4JZGuOBt3kRR7H+yJGtwa+yaE4RqpPaVTPELeyCA1bAxxhyYCtXzTji2SgP"
    "p2OKn8DS4/CHUOeKjv1NTrpkNcQowqNbEdRoZH/d1q5hZjUKXecxYRDagdduJglw3Tfo16F2Ixf8T/cKZcihrIxGIbsK/eUcR3XP"
    "paa6cLyf4d4mv/IB7K7qywrChF/LIHnmUOHbX9jQ/lYnibXqPn16fX3dul4nGUjn1atXT6k9zyb2ALAuUimg9hhEbyUySGyzd/b/"
    "Smf+2v+AHXr5NFX8udMpYNxIgIe8pPEE8WsbUefnG9E1bxEgfsv5UBX0dIwnqpAzO6aYn8GTjqPQ8SIfYGZRJhTnSeJ9J2/Ex//p"
    "EKChtm979rgNzWkQZyUJrqvSDjh89WlmxE1+I1Hn1YSOOKht0c3v71caa1psA6e1FJhuPJFmeM0vw4cexnconFK8CB+Q2SMcTLEj"
    "CSmANUpxrmRQcyKPqP1PkEOkyQguT1Fv1HkN0rtkUW/FMFJR87tJ9fDW56eJc3I7C3TNiTr4r+MR3fO6ZReOyol7MmR5NYZwkT3e"
    "v0YSiNohXyLOo/izUa9juZU22i5il1ned4dycNzISTlvcYgwPl/Ixr6kwcd/RX2Q7T7ugONL+ZgDjnfl43qPl+FPHXAk2eMOOHai"
    "xx1wHEWPOuD4Fv7UAUecPe6AI3ss/Twhdz3sOnzYS8df6cNeOt4s6z7u73QWgwy7j7jxuCj+rhuPXXLjsfsvufEoeMWJxk5suvKx"
    "kKZhO7FWtvTxEsM2fvLng5DERdoEARUhBt9agBGTht+aUOrTf6aN2j8aYVnz+/5Tvwc1poJo3N97npQF/dd//NfqTrzKqWdHMcqV"
    "jE15rF1prPD7+6NYyq48r4c5hSZLGVCfAJU4WlEcYz9OcljGvQfi5aDoZgYFaD5J0azrG3ekTMJKGHwbomqky3iEz6ZwBLuDVd19"
    "sKK5Vlj5yId4mLSvBGWUcSsBpaF/C9FAK07PFPgjqeYbRPPFjBwyorSetFiwLmnlahXGglyq7VqOK0yRZXOuyuGIdAyAMKrXc62J"
    "Fwl8gBFKs3ZzR5MEMlFyPIAAsHSDfDEyAzorTb06LAxi/dHrbAYZXo4GYb2enGa4CcVovO2HzSYpJVs5elmzySAep9nKS33O4KNz"
    "f49WZx0/ylBBReZm7dch0HU7v1DfQ3zFaM37eDVAcNy7YafHoGX52IriAiUduLPU64OW9HBVNLxN7dLqNe2dg2BgKrQTmVOJ77PB"
    "/HoMFLVhBuiLy9v5XF8k0jJiD6F/KVceyqb7TvVoUowcGWxffp8IAYSMqPZPkt9r1wNlOJKCYi0DxjJCgiykwJ3nVor3gSilTFm3"
    "U441kZapr5alCodqIkfbufrv6B7wAImG2J6BJ2NcVthZkqElTkJOvqX1tDHdFckDXAxgwkyZiLvW6MqXyjKK7C9DEjUBwGYtFlUr"
    "SZu6q5mQs/BO902psntiUF90wpHY70V0kulotUuLhMtQJRi7W5kU6zJ6ykRCtpBAszV3h6AcFzzkvuIo6ircdMHibSlGYNXTtoiy"
    "6R2rkDJafKS0snaUpb+FXXOaQXTQqzdw+sCgHvTs4dacyulCfxkB3eB4fW9XGyY26LLXB37QxHka2a5Dc6FSGS9x+6li1NMuYphY"
    "WNAWmk/J3v+VdskFgbRNxE60yBDR1jvAwrDNSQJ+p/WzSX9LI/EfY/tkRw6Vliz1NXUJ5G3BKUbNvlqujfTXp63TNoX+/rR1Xqp+"
    "bPMxXX7wqIL29ppP1VrnwQMLDmaw0vnGr86naO7FA6tPk6bKLZq7GBU59D5mmSqpiKd3gkCoUlSYVXXZ9tK+mLsM+/a67XrW8l1b"
    "U1Ueas5U1rv2ADFY6+iFTYL3Cvmu0gFNuV06IOt6pkeUk/BmnyR7qmjXpuydFy6F39CU3pCUdBlBfWCFVghqukhQ0+XrYlZau56i"
    "ZfLSWN8HO057Ft35GHdBGiVdfz469pFd5kO0sEDNRt5KYZaJRSC7fVt0gJ5dYlSiBzZT+Hmhi46L7MYTN6leHkYxnG9MU79ZtICa"
    "7evLka68NYPDr2SMR7y0pA3bXPiDRQc4tpM0i11OfTh4oxum05RMV1aWSCw0J1kKSwP1ha0Fjus8nVK4KUoeQkWAwaQMirgv5+lR"
    "koJuUofxaJajwB4N7UYuT69dpwqXMeMYnXo4fH+GDDIML2OxycQyOgA80i5PkThSq3Bu1x9Q6A66IEz4F/uRU+OVVN0DSCyzKS42"
    "1PW1i8M2QfNIaTwXOsIRT3jJazgvqIim0eFHjuhQKYIEslIJoY2FRheRcjPCjdaBdptjFyU0SI2igjjYpS018oZAGb03o/sIiZmA"
    "ZQI1+x6gGhK8YQjnF6/LhWclcnZFqhZlH7YaBS30lgSMXdfWRbhNNB+H9F+dZaSuEVnGqI+uPBnr0zbpHtl8n7UBc3Q1El8pNSXc"
    "dC6y6FbuxzoTxZneDISN9J2ChRymggEs7bs5Io6rOyA7xhzXDzLuyv6Q1XXLPoCQtBwBGcncuSUdS8sa59aM/hi4fbJbkcyK53Xd"
    "eJg53Xnphk1/m6yysV4ZAMFNxdTp3KLjJXkxsnsa3Lld7ebKKbYYd8nkVXdCTRn3zIb+6UhBBPuVrnadrlizsx0JSKRmcCxVns5I"
    "Kmvuk1NXW2kmJ1ZWIZHdDNsniBGBFyo64kwRGMXgPolQ20jqrwToYXEgWsm+lsIZlEgj8WlXp9F3NVnbZ1ArxewC/Srf39MXqicA"
    "D3a3KAyVW4E68M7TKh1XGfpDGrKUmqLnvWpGG2HwRGwXIMjYGcjtm4Su0vSqIpJ2OscrCcHKSjWvNTdvB5bfnwfHg3jz+AiUZMbM"
    "40ojXzGwrdfpS8AWq1Ozo63hdAzNvvJXndLGuXy9itVWik1dTi9RaTHRKS4fZ8Gmc3Tth/wRKwkxCFzCBb1n5TaQe5xSLNRSWpAV"
    "M4qQRYdFGpXv75Hqtsgke1sSV7SI4/KiQMrhnX7/BARdN7uN8tVqSil13y9cX6xGBhkXjrodslrZFFMKsfpRwVFLttq9ZLNUqq/o"
    "Si49RY+X5WlyhkqLlLOEXKXxPYjqxUmwiE7oKPO0PNN7GIaVDgqMiDDbjgsSnyUkghPxcqTHKhnvjUiuJ/oAY4dlhZb/YusXfed2"
    "32m40HNNYmDq6LswdTLRXrK0PU0WVpRAW+SUakaAmqjblZz5OgcyqHb1tmnjNNPCYFi/y5XqlnhRPmy86vj+wqbpbIXL9kqlv9f9"
    "CbLZu+PHyu5IjRAND4yHLrGVS7eHaWUPZaXty2v5cNZ8Mi3fL2D6KF9H41w16zpkLYMSbdnToIR/Gsq0wKEr84d2VAEMwhFrEg4j"
    "e4TulrVIpnul5UOUrsSQQEh6ZG1B5IBikZWwvEOohbxkFQMQWL5I7fUSz60J2h84Ryg4Vku9yp4gmQ9PMxBkSdssXDWU1TSxF9lC"
    "UuXb9WqkznhLrpLX2u32U8wizoSoH/FIbro3RwM0+rP/waueGR+6q0ZlTPs8Oc4cFz1cL1Lc9B+tpA+DxIva5Rn1cABWmAMIDo9H"
    "6aG8wXq86q64CHqbs5NomXceZT96/GY6FSdDCrb4DR98SotwyD9kcOjalSX7xiGi8uf7aP7G4gmL66Kw1KF7jQU372Kzo6vjTx/3"
    "Vh4Hyv29p7V7IVTjPiKajAjSnqbRb/PgLRyyHnooJYqvYAW/za3C3iY08BrdthBaHg4bvvFw7K96m08pHYgOFBuSnSHSoR63P3zF"
    "5tFnw04T/l56aSU7rpg0EtntNDzwmn20yA35VvTDaRhJo7hCh10olLGowY+SjRN5me/fiW/Jv6gdZu4sZqBqWP8fRXAXpvGEVJ/2"
    "6H4UAsJvHuxcYYEuLT9iJH5ekLbYHqqrHc5KPNC7kceotl+J+xMVrkTczW7Cb6zgO9icpvL7MI/wYkZHDbJkNjEdEZ8FBoeykqGo"
    "4VqFj6RBq/o+HueonCK/DvgotFMPsYMkusjj6A2gjQp/FDXK4E4aWV+o8ml/orKd+t6iHrpfVmkRYVcgY1QdqG74J+li4Rdql20l"
    "4WSqPn7TSVKhjYJqEFk+HYcCPGV4cRz/oHFex1F2TZE/hD0hhrJsQs3FSXJoaiI1SusbRSLOJyrPbSv1PDdKKOiZuH2tg2fiFupS"
    "aDFnX8bBqfcnv/gWo9r8BLV097Mf8PfQO+vZfpT/KJZrfX0ZL0aLQ+cqyj3C/E3ZaPuuoiykwCFDyB8bHZ/9UaBWFvzl6FHdWpK7"
    "UcVpWVo1JbEcm0tRoYfn+9LkWLEY+VS4Jf6jqDKzyMtT+3306Z36Uk2gm6560xvrgvGH5C6QySatVc1al8LJ1LIzWanPWiXQQkAF"
    "oHtes+mh3BPwK4BRlgzdyQMH3ytpQ0qykIShwJQMimKXPn2lrmMqBpLfRV46SITHhnfjAPlHoL8zVESnGb4L5fqiZ7LwN5drGn84"
    "QIaWyZhi48mIflAYiwGY+hFP5TKg5YxvgOHvNMxDwmXt5IuVKCkj1Kcm7ImcZDZthb/vxgBsYqYVp7kiZ/ZnrHOFg+ysv2Bc8Js/"
    "KykYc7e9Sm3P26IqhTwP16gE46iW5p2fE2tAb1A8UKLa7+fA88+pQ4RHij3UDcvYiid1XRpYbPt5hMza6g2KEYY1tXtsXXdcmLuF"
    "yh2tF6ZpJrWnb5DboUhHmVzGSW3vwcJ3E3UMq3GzPF6IIzdH5UI0sioychIX6MG5SZrd2tStUzU+a0t/JdJ/nAbLgaOvj/x0mI84"
    "STehj1rWKSw2GV4G5DlwSRl58vlUKFaGHkx4MBWlEDYDAGsU1RnSEl0jSGbxKpMO7grxGxaVnn4aaLnuFoqy7cd5rjL7JZ4KIqy9"
    "RIxV5wV6Kgfb7aV0hEpjWG7sCq9mdZJ0nsxSB4Pe0qEgK/oh/i8cnHG/Cx2FddqFfnPrEBkJTy5ZIegaD7ICWLawoOdPikCNkgYF"
    "7YinBhaMbiFZGNxap5/IZfgb9rnlEz2ugw1+cJWwPkeWROxD7Ntssd/7ECs/MsqZgsqutVGoPgbj0WKAUAVRxoMNMxy03dU8t8+Z"
    "NujFaXpRzUKK22LYD3pSjrmQpwxyvHLi6vkMZfsJXCFwd9/kspBfyuJZRW5ns4uEuxmtuGr2/Qx9z2bX6WLM0qz7wHIvxizN+mla"
    "/V6abQetHbwugGIl10IXn7QYJJJCCj1M4l3MyjLDPZ6by0L5IaQx6gu5bNzxPB+vVVbynvT5pmkGRwdBuNIWdGDMTd1jC269g8gj"
    "Mxq5jXhb4Fa9pvIpJZVE8upZoAhu+b3adsE89K8OvLFHt2j2DditeCDFZ9KkPIyiHbQMwftqDttKw0PrY49BJduFziWtPh/OKC91"
    "qKsGn7+PXStXFrKBwO5ICh6t98TwpCFuDrVbAbbu94QOn3QhwSKljzeUFrNZKoA49AW9/q0gV2OJoBbfEvqSlPKvcXAn8zsvAmCZ"
    "NpZBV9m6878v7bxb//ex7NlfY8e1harj69I6YCp/Hy/3isF+Kyj9t0LB6TLpOW0Kh04VfuXVS0Cab0BjGjjiNo7Y8cP2ubQkQAxI"
    "C/khbYUJ2WqW3JdHXClu99NAh+lkjofOKKPCcNZNwlFR32i/eikU3mVOXBq6lNDW4/7cODwPR7STSVfmxrA70g+NiCyddSOrQg1k"
    "OPpEJJnqWXbfcvvUA2DckqVWC+LFyUqFMMKiUQo0yxUgPqvdk2BHovkK0F++tG99zx1FIt0xecUrbNapKqbGsKw+7SAeGxRqz7BJ"
    "quNAQLeKvZ655JfgRiVPVavwaSP8PiZuR+LAksjm9HopFkdBooyHvaKn/FnNhYIlPR1KDC6UjkVI6LVi/QMhxRAeBmMSl8shfMZX"
    "lZhuN3fjoc9QWRFfoK+u+TLIIvWUHYTu5QrLyiABIMRGYqTem2Kh7k4ouhMK6T1SPKaK6TGF1CeRmKOdvE4Mg1B3DGcvE6MN1eCX"
    "Vx9jLQ9VH2P7D1ZfHf0rZApo+Hr2EALVfK/aCkqwcFZQTPQIQpWGmVD+f7H7qCFvqbpGDm9LKK1XVv8PTK2s3j+qq/cZMsIi+Nzo"
    "bApujUv4ceOWUqwXqkW+6eEu0x4diiW07HVKtD4Kfn/EZxV7P3DSXfdu7MnYLW08IcEB1kmyXXixAXfSUmDyUzf7A27Q2HHoZFvw"
    "fse+uONZ5rCOXSdOHtcVHivdnlge9Ng7t3LbKx/7Krez47RyhCgmcnqPU83IHOPjOFvZZBKXu/EFz1F1z9FAwh17WabG14RxJi+a"
    "Gsa/u9hPOmsv8WSJP1pjk3x9pQH5nRskP9bX+ibYjScsn4i0JBuxRIY/HKxZ15gTG6Ffv36Nrz6Ru2OoYL3TbOSY4WkyuW/7921q"
    "72MePN9g+3mw0Xm1sd7esM5ThX3HUW9y7ZNMNtBRzsjk91rFgchGRW/xZVW5sfNcqkXqKtZlHc+VIuDaS6kg+Oy59PjWUbqC7TWZ"
    "aa29IXPBJi2zvey8Uvmer7+UGdfXXjyXOZ8/e7Yus3bWO+0XMvPa87XOhvItt7ax9vKlamzj5bMXz1V7r150nuk+8zqCbm2jLYcv"
    "4Ci7sf7y5fO2quT5ixcv1jqylvX1Z882NtZlw89fdNqQdcNU2llvt9fWoV6li7mx1oHiGpo6Qs7C85cb6882nmng6gipoLr+/OWL"
    "9iutAWoilKKu9Bynu2BiKrICx8H2QeKe4abCh++HMOWFOsZpL9pteYBr01tHwigr4hFlpmePplBUfWdBWVeDeNaTdhxt0VIYZPX/"
    "TnohOZHOA0DV0O824nqQsXiFdGYaFBujwR1xkFjbfycsMyUyv1vNq86UVocllW6LK8G8Xl9ppHX5vmFeb+bod7/eTFnyOoiFiWDn"
    "OXrWV0jhU6cNgccW6hvY5j30qPMc+SPeQmt7fGVLDp1a9NUuohLFGSGtA8/S3gSutQxgSU9QVAzg7GxuAtt9H6AoE/MAdLTyoJ6s"
    "bCImq2JT4HpYNA6AVtHFoFzDaumqBfv/u2Warj7j6//GJdrsVBdmZR1Wlt3yVdasCuKatheocGJcr2khibtq8sqqwYXlemSUK8te"
    "l+3NWDl2ljgU4+uVgEMZGwRo+NQbkNiz31hphPXSv78P6/Jph+wsADQKUfbVHWyirV9Dtii7cB+EPoOl+N+hNZJvWUWMaPen3tRw"
    "eUb8Vxv4NKCAGlh9C25t67wdNZT07KO26PiYb24GHbbS+JjrNQh9pH0OuDtLbzV2nQqenjHU2lnvvC6FO0AlwdOHFIvq6dcp3ZHc"
    "ByktXj3tBB13yuglRmvKAjQ8wllDcYOYsNSsbDK2Ly190cnD9Lb+38BAOjHoqu+nzTN3/upUaDIrhReg0I516RTGpVUCJUm8PR7N"
    "D1cQE/Cw1Ic7MeISrQQBD5Neepqc4Suv+NNEL1DitwTEim2X66ELD7eHMB+9pWS0pxrOTcNERPNeUk/v+Wl+VifUhsA9KtVhu+qG"
    "CLBEt/+Xc4aoB03OOpu8vwH/uNm++kBSDCnY6Ar32r9HbCdkXyN2HrEnEbumY90nete0FJb1rJC/ufxNcuE6O5yy2AS/EvbOJoGH"
    "9oQc3Q7VKDSb1spsNhiLs4AIo98VCghXK+HsZoCizVp0kYiAdKEiy8gvqlOGoVb0toUV4a+oJ8qzaQ0fOZNORjDV+hSZvvFbqgh+"
    "yaMZBqA2kkWS3xJ6BwDKTW9rAwhMw6LkNdGtwZickUgjIryfq5FiZU0qW1q+Ncz0/DlYtuMJz1xxqu9N4CublV5Xgt1+jFmMtNQm"
    "H/id8BDluMViboI6+qpRty/0jVXni5klOK3sKgYLJHlLqOqj2a6I34t8u/woK/Vc2aLhJCsWEuKltdlKX4Utu1tip44KMKTfjusa"
    "7WX7sKzuLvDExqPDtJuyKJtQIr07WDIiAMe3MIOTXTzzdHNm1dCNmbhKQn0OOGryvOjCGp8zW00Qb3JS34raCdHGjcHBvCEpjNXA"
    "fZATParWy5IVo0CsrvYSX76Rq9+WhloNOKKJ/Tx45SpBo4+SNpQBgK8smSnClDdJC3+UeiLlLpbmtvBHsW+UO1+a20EgJQLTs6v2"
    "LUAkWCaNmEE9EB5h2JfWh6ZSU+sStFJuHu3qgQCZeuNH613iEZJeaZPykDdlQ02aKxaRVP1ziUZwtiNLIV8kSRDJF1GISlHvI1J3"
    "1fl4SyMobFZPUNVJ+bK2n979isXmvtE0kory5IkS1ZMWpEmuyLUVF8ZC0W21NKJguxaFnHvpMBMuW1Tbc6fPjvip0KYrJosrQsI7"
    "Pc3RLK4EPDio+0MF3QO82rSXLltcWQydwzCHAvjOJd2d0DHXqeqmDjao0jYQk75H8VJxlKEjT9lFMudDMQiVbuQ+kzfR8hkPpboC"
    "9KBcoAfMgTcDGKQtcgjXUAL5FYtr/EMr/xM4cXYVZbQV2Sf4cgTtyKXxNAslSjK7KJXnm8JJLCix0G5xnMScEnOVCEtRaf38MfBx"
    "NVmflqqpdL9sjzGQbLeLJ8BA3N83rkkG+5igsPGIRG048W0pf5ZX3vJK9MYA/cInXuf0NNenXOkm30H8p5ywxbzFK5xu60zEXkvu"
    "C/KW+BivPTgy/KoMDrcqRB8D0T1BcZ0p2BN01YH8nqCeDsBTB97I3pG+/tfU7mEefBUaRT/vXE++YaYroKuir7RqSnfiKLsP5A/w"
    "eDGpXv9qcJd8URTBl7T1wFPp7DghgwOtPT+p+ol6B+z0oLBfjnW+Am3E9g7OTEfGzZS+138XJMwtYnPf4/+TBjf+hQatEiSnTVS7"
    "B5lOcK6HPpF3GdiJthJY8oz4wdxYQsE2rzcr30f3JNkUb5bDUSi2Bp1TlmQpSm+anc3ZRLMSqGtCCJC4kv4YyVVC/Yk1Ov4e4WE7"
    "tjvMYj37le5igrriSgAQhpFZ0lVBKnUNRBJKeU+8lVT1ejIHkDIdDqIHIVJfTpuyuQ3xl13ocVGnfvUnoGtPcqwlN2SOG3JqVaOv"
    "SLhF3eVGIvfwv7fXLly4po/vsna7dOtIV6tiVcq6ABbCA6BBu3S4RN9fHJCUepelMjIABpxrtS99XNEx01sVnCnVLXUKU4cMeRaz"
    "zhxwnrK+hNNW9Z1N7ZPMknMNfQqNDxW+Qle98ksey8wXHc7M52xqH2esrPKQqU4veFrT4ZmGAdrpuwccB3TWCdON0RXjVIvjn4og"
    "izodRp+40iCfc7JfFx/iYCg+rHOwHWPAas7EMuIK9Zvddp0PoTQD6OHE6lOsnm73DLwYbbpgRc6m6EdZxl9wNK+4SGbqnBgOATzW"
    "t8hgT7CViO9GCDcQTkcJO2R4HBZjJ3GaTWkZOUN1PuRgnLsgQk0HZ91zM7+Jy8VjtP6unpsnRlvKnKOXHrMlwlgF7JP0A4ftAh14"
    "GmQYjbReJqGCVdn1mGusoabtgVGEPRTZkp1HRslczv2YJ58C8bS+GnCeUjB/HFbu2r5Elcu160QIlstJ9VLtXbR401O5x+k8ny/G"
    "0HbxRHKUb0IpfqpuH+VQ6C/mmqTnQjsPKGfwJkSjM/XoKb5PLE1q4xRq7j9Rpt4QsAw6WKw9gfWMumOJvuQ4PgmcwA8pPfaE4Lps"
    "iov2HJjLnPxkAbfWzEXWGAK9HDPr7kHt4lUGlNDl/U4zV+b91gN7ia3VApRvC7URpckVauLjNxn09OUFv4gSt6zCFKqzTlsK7IBo"
    "PJVSUqet4tj62ib6HaDY9T635dmfc/MUoBX928BEWyfoc17hzauvK5yTe0J67EA+gHAuDlt7QInUUwlkGC8fVLDOb+r9A1EgyMSX"
    "3I9PRKTACMnihzVp5lRR3A+FhS8/Dc+oDvgNyj5KCrrkcE0rbGD9uLPL16DpBMqjoBGbF6JlnHQYsJjQjaXWjDQvhMOb3/+cd38b"
    "MFm9xS8dA/s0hQZk4tzYjtpO/+6monLZL9fvH1RZ7YLxV1iFaA91oNEXpl1fvxrR8Lva1Yk1lpXAm6XfUtwhqRZ7mOjY7CHofc59"
    "4R3EGni38obVg12tlOuXiyyn6azYWd/OLi6Shd7aaWjv+8hsUIen+Nx94QB7ziC7iEbZ4ed8DnwokaqdIrij4R6N0TijzS6onQJC"
    "ol1yttJm+Nw98I+TaXeJwSFv6eT7e3z8V74JzBZQrA0dOclnBYXn7EMYwDrcKXx2nAfC7ninYHdXMb/uoskxsJ8J5PPZZIIZj4G1"
    "3o7ZYcxOCnaeyBLHObsTG/RfUEiEvmD/E3TD/pcOYRwAjP8lfylPmSfv+S2Ww1OjCIaJDKCliQjBgt3PInxcSti9di9CJhSCCWQY"
    "QJDlAC8YmljhyyHlZNHeQ/u8NcyziVToJ/s+Yx/QR2dFMtx1MnYr9c0ZbrsTGvZi655OFDSYt0xucuR1UgDC4R+uPX4YTqLf2Mab"
    "UAnp5kmhgjAfOv6Lif/idyEByrRhtgKOM+eb/n15rH9fqv37AlWhGvKXAaLBeeKzm4mc/fOE3eHzQCd44h3ynNBlROhyM/HZ1cTC"
    "End6MONejBmvIOPtxEJAbRJJsvg2g3JT4NzphT5AHmDaIz0hWM0ltXcL1Xyzq8G3Ey6yMI9gTYTLBuxkUIN2S0mdaieSNLKpyW/Q"
    "5IHdJIKCuvSOQHUA6ceT4G6nGHQ9+BNOuceO0Qr3Isy7Xs1jH/iw7Hpv8jy7xqDHPk3l56epxz6S1aH4prDHUDtfxpDqPtvmSdfb"
    "Jhmgx/6MIfHw2GP7cGTrKu90+OGxN9NpUYk6Jiay64nfDxk+ObOf/TjKgeFDyoOrz/uUxhFAmp528+ZsC8bzsuu9DQffpFv0V13v"
    "JLzwWGcNqscnvCG4DuMlFpJ1nkP9uLoh+EK0D43BB1TyJsFYKH9EBy621u7iM26F6MnaCwO09TUC1/o65h2hfQFb3xBhAYb1Z9hi"
    "BAFo77cMX/lZf+FAdv2lBdn1Vy5YN9oOUDegNmA0gAmA8HMD3w6OcbeDAejJ7hoGoBu76xiAMrsbGIACu88wAB3YfY4BaHr3BQag"
    "2d2XCCpob/cVBjpYYRtDVDXWvYZ1d7DyDaj8YDYR8Ohgr+ypWluD5H2gkjAtOzAtAM6uJ8inxySgu54ksogTgJyepKow+TgpXU9R"
    "Xs9Spz+aGE5yYX/VQosqVe4vRjXorivYmaCdT39lBblhx5/VRWjM2I/E265vbJoBXKyzcun6ACJV746hZvxGJ9P4q25gXKxd8J9n"
    "KKyWFyBPTBw0k9ytROCusE4nur8lOWYUmnWdOuj8T+q0Jm429fpbsn9YCn1KO91C17UMn6oAqpZkA8Hg/PqumPMpD0tZltiEZfuk"
    "4vIf4BwWwEAwQO5A9vqn5R4auh43VnY9jgfjv9eFv90IkN0PRJbfANm9sHcofe3XJbPscgy/4uUN3E+w0VlObBYKEVL0qHFkRcYJ"
    "sTH4i0xLeY3sHZQTlaLZHzFWQDUnYX5L5P87kf8L6Me2jc1CaFNQS7gJnuhvIb+ITMSS+V6KF0umHJ34ERy2of09e3uyXyL4hX31"
    "hGrZg1p2nf2eJ2W4lMMRKWonlfmEAGLbSmrylhWH6EFZvzxY5Renyi92lV+WVOlkWJKuW/xKbC4E9gUG+ewHDXkXhvx2Epy+go0M"
    "tiHYfc7Ydhh8Sut1b8uIuYgeYv3SgPSLtOqkfMorxr48dKtv4PEgn/aZYWcTwoGPE9EQulSttFCvr3wpWDGkDI2V7fD+/gvwiy83"
    "8W+n8zr4Arz8X4MAt8rfB46NZD5cqksi5aNyMb411wKpWlioAyrVBY2oVe8BMhPkWVt71Vsmga1KXY1cV7tSfOQpyWRYUb0TpxK2"
    "6LEZQW6xccSJaeuD76UDjP2lqqQLYk2lgjBUbmytsWkIEGVDi441+fIBAr4NsyCLWCJVy9cvdo82mr8G9frvA2k9VJVxVRz6fZpo"
    "K+/v2nRHuAt0e35/D7hRr8s5x50NRV4oCHsTBko8RjBh0kqkagUupeG2hWQFAOQvLm1JooRm+4JkYUjSLHJCJzOgqorIoM3wwxyQ"
    "dlOE1A2sBitGCpt+ArBKWLYZqyzzhd4+MKHFEHsjdk3kFb5l8tUKMS/LZwHR6DMwWWQKj04OUMStfvEAjmFPfTSpdk94WMBjNHpO"
    "AI6MfLEIdxTCiUJR4FNRGKbnqsihArDQA8pY8kT83JAzBtXKLKfoa87R24LFt321nUfhOVK53LXDruvdnuWXWV6yAJ/2GdkWXGNn"
    "3dQxqrVu14fmDu5thNduabCT4Fs4WbolpPE+MxobwvyQX9c+hA2Tg6lLCXnhh/eJXKg0CblIt2SJNGItuulc+sJ7p8zo84pk971g"
    "XLFrtmT0iSUZ/VpK+6ULvNzTq8gyrDKrTLriFIPRPCRJDIfGzpcqPontr90Y6FIqwGnRfjIw3I1FnvNB8KjnpN75wH2DR9fIPGlK"
    "iG+2xIGkhZBdZrAtfOYncbAbiyvDEzKbh66fxLh9LN2D7u9fbS7fnCxwokz3HUor3hVEkJXmC/RQsRhqXgdDH6dJzphVyWCo+Xnn"
    "adtAydvr9SdoXuyriTs96wHOpVAb44w8O/jsc9R4P8EnRCwNmYnWbhauvcSlYr+BvWbYD+xPCSF8V+knXZcexPSeBX2CWizp9sQ8"
    "qxAs3KlJi3Sxx5oP2gwVOokxmhq/VLGPblKt3Laez7tKZscsvoK3laLfJ1XXakItZ4Uc5HSe0iHoKT6KzMVFM6ktCWcWqUI5adNO"
    "7kTMQz46tvt9YpbmwHjXuhKOyZxHnxcfEhLDcL392KlpUFUeEwJh22kRef2zI6QqniRKZKvq7DxSBS0P2r3c+MnMlcpPEpSnufAI"
    "rh4DT1kCQFrBMZ0mZww1v/XIOks0uPhMae73iCw7nspcf2OLtCmdOQrjWFUPr5rURUZOquE0QtcnGdkG8dXSvrNSd1ycDCHy14Hy"
    "bn2HZYHyStdSaZPPoZV8zrui36YNqOxYGHyiEp0TofwuzDHeOESBTyFznVP/HdeNs6GLk4B0fcIBfHxd72En1qtp+FiTGynqsBr0"
    "u57UpCi0iE9+i6fckEmA3Mqz65FkGGAXbDyYiO7fO8/RNbcjzYjwYlHNBQ/ksSANbhPYaNNajJfo6YDwvIU+gfZ2cyB5kuz3xHtK"
    "8lZDueqRb0X/KeSQSkrQwgf8jA8faYRZSs8WJSq3uCWFnovQxaH+cE3cDd9k6VOH/zojoVz4a4f+5tBOT2XYp3jB6jhRwPM438Ds"
    "ON+KZSIXxw5vgrkqT2tTOrpctyjfX5ZwCyeMkZc/pPA8wqkgqyRNyj8iEVVSJfQQgiqXjivgen2Ga8GJ08CVc8ukH9Rcq0ABhGVc"
    "Kh6WQjU/CAGfSucC5WS5QV6RzdZCHusQkUu/bLmx+BK8idpJI2FkO4mR3Jbi2lpRO633xAPSRXZ6b1w6+pbX6s8xv7Z8JY249KQL"
    "bQl/aHZMQ5xl0e3BEooTm56psaMGkxi+uZWJu1Y2BAxqj6MhDtQV1evx61xYMpLRfkzuhQG6jZLF6pqdvnK/BwDPCBOJySa/huJd"
    "Ld4S79AeiENsQshtog+JAlKCIIaYRLgiC2S6AMXq/JnM7ws3TJLBI2TClzKRsaM5a4gWmaof2V/pwzxJKHsB+WGkfXQBEkWiBtIa"
    "FmBoiB4w3aDfFU8I7CxJY04dvlRLJfsbOCKS/b4hnOg40yKtxtjgjqvrL5bg9QXdPqFQGj5YmU11xEk2nQvtUn3TSlCqvI4hIhtK"
    "j9VRYwXsRy1Wrp6JtJpCJ5zYYjUNWkXlcWhb2ClJccrD8hgUnCxledlf0nDpWDql+S7PHVuZI04oZ4rlVF7+xCohpw2myq6zKb/q"
    "Y4Sz7npb2f39X6Viev5CRAJSnaNHpDz4q1xGBnIiJbnfz4M7WkndvEIWGGCJHQmIMUeXS7CmKnQsrxKxxYXvV1Y5LL07s4KgGfPB"
    "7CWkU8Qn02uom5v1xKw1pOLFF4pU4bwBPOT3ghE8YCpw3cOJ8zjDI6foEx05c3PkTK0jp8yhgCiPnDhtlSNnah056apeKZL8VTr6"
    "5e8dD2B3c60NclrZGs9Qt9R5KrfUPjdX+VngXctwignofpNiJxiAKIHGpeUqFmcUWvfeqAgYlQ7jLRicudRnrNzKPlxCe561ywlk"
    "erCMQECfGVVn1akTHQP5zQd1a85+xAApNhwivEiKCcFHj8HCEaI9PlcmCrggH4X5vWzZEDIfbEkGDZbHsxEUzKfvjKjaEVPegYr1"
    "ZRn38VgeHX/EeDkmcYc+6Hzxe2lFc+nhjyJZKWjqYw5Hgaxi8nDoVEzE1BwrsM7pMICeeDbgYFbHldjYwpBJJa2QmHAj4p2hQ/Ro"
    "qC09i1nghReZsNvcEnaRwk4Tfo6S8Fb9nogn6pXtJGokK9NJvLg2JpaoeEl/dqQ5J93ZidBNLNI/oN4ihQ6vZNqxMfqMZtLpsjDQ"
    "5JNpGfOoxtNBfjstKRThX/TTUxtlcAKgWx/pzk4af0qFZDQI3ZYWokfKQvTTtIbv3tEfTvoDMojXsZH6FD1C28dKAxPlkk+E0OOe"
    "CB1CuyKAo5oIL3vS5pT0l2uouUx/8A36qarWtovdtuxiqWYZxrpVEGuXYaw/z0Y0MtRqljAThqxCk7kmdJjpB5sF5MCXbaSZa01a"
    "c9dQkvmJlISFNe+WZeK7o0x8BUyEIrNsSuzwNaHvKnJRv69DwDhoTui6LjWmHZeCWo+GZPhHb3x9osdq0QWlOrS9jYEHeRtvFjPF"
    "hbyN1eH/YxwUs9O38Rn7Ogk+xhWSfo5xp+2ziqdjyCcUNzt+D7rwdYKblbd6PvHn8Dkd4qdLujHb2I23CDSmTtxUSYoxxejes4o/"
    "SJGspGGYuksq1FZ8RqLFLH2L2tcUf0MNVWh4b1w0XAeO7NSoODNLvfnMyUvr8Od5Jf7rmi1daOboQVdL6PofK/GpXCJ9lnRGAqem"
    "gCEXt2X2PZvWqjI+C9dU7ZrR0BXZZt/K+Fy15la/aAL/Cw2+JQV6cckE46/cejBzacOs2ygm73gMUKyLTSpWsYfXo3nADt5c9C3p"
    "olW5QFe2YFvwb2tAEBa3BWGR8K82QXc/hdq8YJOays0Kf0u5WamdZPArO4nYAiKzG0zs3UDAYxkVt8nvQJPfRwmvobgSCLZpiKKc"
    "9njZkwlt2cdAJj21QdMerPY52tAcWmyXRyHMICwbnwvfor955ZAkJDr390rbtknMt9fjFUXtkn0dN3IoKZ2RoYLOEl1uw5ZfDdWz"
    "Z420vkEujCxbzoWXjVR38JiZoARCKDmhYFidAnq8K03i5Lvs5MXc+DPMzbPf7c0gw+e8laen/DQ7Y4MgbCnZH4vgw+k+OU2GSNUc"
    "G6B/gno9Wapk3PB95dAWIJqwkEVoaTcQNzzYpwzGmOlDUC+T7yT9Ul/Yv6Ej5A7xm/KYyYPLrOLa1ZJn/+68RnR6kZ31Slv4JSMV"
    "OvrKP8uqd34uVKW9Xoncrzgk3+L9EGdr9F52ibIOiLcf14ldHGyTm+z8PtjwGZRFNwU53iZh6p954AkjBOFFFxfJKsmjYDuMson9"
    "csn6c1/u8msWxs9y/bbk6Z/5GT5NBT+oHLAVLb6ZAJ2it8mq9B46+GRCQ0RPRjACtBHHVSCCuCDQ+F+ZfTgSBnxnzJUwpPpKJcXO"
    "4ANXqlNQ30Lj2JTrJ/zWuvZVNj+4GrQ3LiH2m04sXx+1jW4SjFWMul1PgqNwXgZJ6wKOTw11GCdbZ4kAbOU2g44iVCz7NvnOkTFz"
    "khGC94MRJaSmn/eTFUu/e8F3MrZ1J31EqKt4fKEkmeOlwNLs+BjnL1T6KzXZjy1Ko1fprUMQGvHcKBCwji+8tq354j0+YbvapXuY"
    "nrzXce7BeoomleGIHM/htcj9Pf5saKr0kJlpT3pDRQ/oNiq9rNdDSzRoGfbKFjZ8QXqU69de5loTD4JMdagxED0aUDFAb0x7oD9s"
    "IDozqHRmUO2MGnwGdUlfFASi0HSDevqmbIQ+yyoggyTZQWrwmejcc3yjNgZ6rpzswpEZ6aN1mTXP9Yjnn6NGxTglCmI2RJvk0mdT"
    "vL+W+8gkgEMIehwRiggTjVKi2E3wIWS3Ae8t6moZ3Rt8tJfeD9FUeLkxLGp3QYX2cjSGtrfyattjN8FevJCFtLQgD5ljLmR5zK6z"
    "mlfaA9OlobDXgK6vuV1/3Ip4qfFu1cbSNfV92OLSsWu+Cb4Mqj6THjRd/teNQpcbPt8EI2dqfs3Q1xq3bfh7Exw6ZHc6FPaVY/k7"
    "GUKWSyfLDUadOF1QlqU3wcSJl3akN8EPJ3qpRbhUH7sJrif/qs+nv29x/fcMaC0z7Zvg+4D2/APDMrLrYOWgXhe3lAIibBwc9CfK"
    "w/Jk1dNvGpDy2KR3gGtcsYWzIGKXvZmhP5fBjGjzVnDpPhZxqdwx1+tbxn3UZbDFxuZzK8jzxoyNfbalnoo5EFLrCOO32KUP/7Fr"
    "SZZnwUzRpfbmgRGIC87+pjFht0rlagjEyZF/Tyz598Fc+rfGPegF7PJAwpBkBcY8iWAqdU5sMAPBsDIZvRT7eD6p15HpGeHl3C25"
    "SLdMhO7vS9vaCrcKIN+oVXh7+jk9M/wnbio39/cTnwY4NLcvw/6wSzHu2639iXu1MZEkXVyVS5sfdtNf3iVtDAYDjIBO3/apV4QE"
    "7NbM2DV6nLj1KQoauZWev2GWVfC5T8MWrxp1GzeCPb4NgJG+wasfcT98APSJbQUVMco4qMhgZhLSHmtUwbxkcrDlA0B7UbErQRkH"
    "C2KYmS4Nx8Pr4Eatge7XsnHjs8vg1o6BQQs8O2hssdmqJ6giuxHINlHXKdcQdO3xLqE7wnS7bAxxd4uom6KqMVYl6C8gL1V1oKq6"
    "hKBb1TVUdYB93WI3AHE/FborB8ENjO8WBtSGXh/0LnuXwR9lAxbPbHWV1u4lpGwF495WbwtTtnz/UqbA4W7WvOz5BxgPdc+aTRV/"
    "2Zz1/DHGwwK9VPGYQU5hEIzv781ypgjrSQeByWlPVS2rmh9YDj9EuHejK0lmjSmbAFgP6LxjUO/azXIN4Dpg9FStWr1RH6Yp8jWq"
    "BxNLw2PygIYHZLNfW7mxlTwmWj+DXojykdAdB39OtJ7B10Fj4uNlRTj0j4N3IuHuOPhtQkRxFPwxoWE27L4Alt64fXAUSybLnkuf"
    "VJ5LR0w/Dr5MiNU6po9j4LcjoJZ32RDAc0y4pNWVRvX6CNIneJytKv81RtA55wVWqH3UMi+424CQj87RQ+ETpj4B58VztHPJ3Y2q"
    "k7Hg5hFhNwKqN3pYuwW69lcZjPCiOlK31P5yfg5SIddfD3h/FLsq3m+33U2+6gjG5bc0o7QlnI4h2hmo9pZ7HMGnVSa+lWMp86rr"
    "ErqHOIvbIZyAHlHel+wQ5j8Klgkfew7jWdUSr5ZBaeiDJZSrk2ohKYTUaHWk1N5oQXwv+6ScT5vasvak4qmCCGpJSFOLgEwtlhRT"
    "1wBH6MRtiCUcDXeI/Q771xF+LinXPwqCJf2o17+jxcoVGRDAHvUkDYboWOOXfGKghUEbmJIRXtNH7Agv50eGFzkiwv5u0Dhi/EFm"
    "5MhiRkZzn131j0hJP7jqQq8S8kR2ZTZdlUjMEGT4OOmTsUfpdz+JX4R4JDpUEZ1j9yLTvaHqXlXC7jisebDjQ6vjEXR8qHs2v0Ky"
    "k/r2u9xR7j50eadkdKhkI+vppswR1nVLSy6zk1S9baeGQWU5nT7dIzk6ikKvJYYXTQwjalx+NRJSrqLnztCp14r24TVLha836ntM"
    "3jJlvtTJp7hUmUk4jJbM6aKb9z9KS6V64X20KKuZ0urlIrKYF8yVVkPkwpenZUk0s6UsCkxxkFquRliGcDLe9zCU95TUpCThqXnG"
    "CKWnDiM/0AUH9KKMIG2hgWpkoBoCoU76jQECDBXWUNgqkjIbsNAmCwFmXXwvamlmBV2VE9WolI+NeWYUndsIpYfUXLK5IK/8Jnj6"
    "z/yfaf/piKUYnrXhv/t/znZ3d7efjqzHOmbGLqthGWNJhdQ+p0fpfejHNAnRbc0N+6//+C/znd4wz1bK/CO3nvBLA6gecWgmXnPC"
    "90wq7+VsrD2zBbtHiXoacEcKmY+qb0G+WXhL3FUdpS07g6NePEXuxijgyudCzeCWJ+o3Zn/2dKhtsvbI+6La5+8DOVrizVGBCOJV"
    "xEypDRecfJdnrilI30RL50GsvFFFBmi4v6yQnaCKZTNV7AjOZ3HBnRIyTmUudBvfZ3zG92M4TZdh8c0p4yYpzyzZDB9Q7y8xG87w"
    "eFtkyRUnybHfKscc01vixbn8xp93P2TW7dMN+cDTAGg4vnDoosImx59j52KC4VVBlOmXvGw1d7Jgsd8jR2fseGliSyx98hKYCLM/"
    "euH36RNPS2/b6CDVriLxGeplape+ebMpn5LD3fuJJyiT96SvQyuAeDmcU6CRuaCKpd+jOiwKWBrLgxXp/RBvDGwl/uo1gnrHrSOU"
    "rdeN1DelcYnlKswtybci9E7qZVOfRKjvueVo9I513aKpQ0gUhlRSc34VA/4riBsfwe0e76n37W1oa4f6ZM4nPTRSz0rds1L17E52"
    "qm2UrVINb9lZWIerq/MlnVl45+qoCH7hkogdpIF3LjYeenPpibd6VLBhrmPxwq0QsZ9NXu0MWaRcZDqF7hhkgeRGR6tbB5kSm5Tf"
    "oIMJF/EWlbQfHzw9SM/EXad+AcZ+zMNSFZYWIWlQomQGgItFhZFIkFpbpqSY+plVa6t1UuTzMaEwcHFk+KXol37TuCezGSsG8hjm"
    "9G/5q4H00K5lW4zVwkaAI2ArXL6NJiQ2KvjcBNFTmgqv69f/tCVm+StvrVnsg7u9ra/bu1sa2x09HeK9nUa4beRZ2HmJRtrmue3S"
    "lLiTTGPXfvnoK6a3X5+X+NiqfmRuOzs9L8+Y+BH76HnZbNpmY4IunperqyqbLm7u5aWhWIRasewND6A7EZDFzxRCWcVuGUSl1d3C"
    "fQeDHhmVZ05c1PQY04o2eY5K/U6Hw3/lyG1K9N5LCeeSfel99VM6gY2FR0RgpRMcZDC1B8CHCu4vFJOWDejWi9ZDXCNzjOQ0RgXL"
    "WCtY5vLhS/vl5b/Tu/Th/IudIusHSzeZV+zmB1ZeAimTe4Ap8waZqK+Nz9xnXxtvbIPPwczizt7oaQbMj6qMWec5PmT4HXLhKeA7"
    "1EYPLauaLodVLRBnBslUYqGnkhsgL/32mJ1XejU9wCu5SsaG8ead4GTlPkm0E6FBWx1B+yX7A+UK5K5FeILDc0vPONmDqRdun9Ww"
    "PiQOuN1p95FQPDSRHE5yzkTe30clrg8DZkbQ5BKan3U8PU5gtA1mj0J2ZeFJyuevYEwlOgeQk7ILNea/3lE4PlrIojrpd0Wkmnns"
    "jHLxXtIz2+/dx7u/kR2w9iHehxA6CTrULxhZJufExGEtbUbFTBLOMalavI/rdfOuwN37WDk15EEbGJR3PWNjdyi2s3dBB1112i+T"
    "KzsO1MWGEydgVGOl7cvjpr6Fnzvjkm8dJ4qfPLSeAoGMMB7pwHO1A2e036LGcchuSlq02nl4KoAzX+AqnpRko4PvHV1IZ9fbCXw8"
    "4RQPnBD7IW1VdtOgw34Ay+AZGB9L3dcnMKJidfUs2E6YDl8kWCfHCi0LwGu9UJ/wU55ixt2U6fAPO1xi41zS5F18B/RHKonk+hq+"
    "T5T7sDnl9eC/G/g6EpxQV4OOfPVWZEj9VXqCe729Gau3vZJm8n8/68UBkHUslkEdNjcFTFT++nWQsaQJf3DUm5umsvsSGrrPERDx"
    "KhfMnMgTW0nWhr1HFo/cPGIrp45ABzsWwaPD2va+fBIahhrQ9wI4FIAkALbZ5MWZgPCZnq1l8T1d+AewUABFACpkAgaEoCsLQ0+X"
    "xu8ujxceT4RfcPZO/j7BpTetvhl6MLQ33jJtPJNWMfgHML5UtlXEWnvbOx92Tna2PWa9BkJWhwJq6HmcXLQknMSw2tk6Gq/p2EAY"
    "dA3FozdoRSuXur1PRDPXQwuyTlLF6FnXZhOM/wpjCCxM+0r35gCn9IGLDen8Q7/Mgd21xwew5AhIOEClln22TwpBK9K7sX67MjUP"
    "mxETj0cIPAnZ3Vv/1SZpIuxmOuvd5SN+uVhlCVilPu7iqAsLGC//hkl23f2RzsWNZeX97eDOPLYNlZU555Led2HL40A98W2yrnnT"
    "bs4IcTovHcx5GEMkKwI8+rIxPuIK6NB6ha+BzikjXu/48hFM7r5Ma+2Le5nkxJ+oc807wWro0z1tjxLhKCe1VBU4dZCvSREHXLt3"
    "Sfa+c9QllLX0YV3lKHNW/QpU/5ob7Vcv7tfEckQA+OK9nseb/WktcwtOQ+1gwJKUmifXl5xq1u1TjfBCIItR3cbbhVJoxNq+c+My"
    "AQH4RHFg1D52rc2kTwaCcEM86SMevyadtsBIbeVL8OS1GPAaRRpjHkZKte8ii24hvIIyPJHJYC2tMXw1nup4xxen8BiNvF2AEtlN"
    "e76kfywVa9ueV1R6EEOxH7snuXRlyaA8Wy0z3rKXDyF29S369c4LnNKuniKrVfZ3ZRpKjCQEGHeCSLkyHX0FlT4gRVqx5ElAp6Sg"
    "w6piLhepfFoKvr7zPrVj1PbsFu0noWwW9dh1jwDrEI2MF3tssXVFgwb13drFTOou7b9TvctMBes4NawjCe5vHnmExmyFu4V1xuEk"
    "Qh8ys2ws/yS27fKC1xLpGeOcNE6kwEJ9ysrVG/CdKmK0X/mKnFjkc76Ue994gcy25LLwIV+Ut+vN0BIfwzCqg6BI1wibolrnQsL9"
    "EVODuE+RXcAtLSzN1F1IgklFTylS9qXpYwjH3y7+CbI5S+36Yrzwcv28SHF6ZWRrLzfEW8YrGoqVDK+EzvOiyPCLNMhVmufS8Yt2"
    "iK65R+m5xVCF9Y646z8Vsygd25x5fTmtNWBDxmgjUtTuvFXXoUzrMovThsdqnr/qzb0ut1nE6cz2yX8ep7FxoApYfz4Nb9GYwiqx"
    "Nax4xh+zmcBJUc9lMDa8VO9Sc1hjm8OanbGxzWFdihUxszW5S13zCnfu2ITuiha6iR4w1CgrpAR2qTgtF/Vh6bEy+bSqmSG8FJkc"
    "kw0eRUGZrvok54MPNDa2BNmiJZUQDMRQYMhUARyGxqq0IBtW2RizsktTWpa5ZLzfuLSVctilZqQug0vZt8vNGYJagnYNO38J27wT"
    "Y3/LR50h1jrGNsa2jxurSf2SklWhb/c+FL1nW7qCmVbonykZZb8xC/6KG5cABWSSIDNTyoABwqkL6UkDgeDGW/Ie04xQ5Ll0eO1j"
    "aPNd2R+KXOS+q9BXYaiKSB56uzNzipo554ggONbXZMf2ddixLnHcevJE5EAfibC3w0I6Rs5uRj3x+40tMQbRus+2iKYBERfTS99y"
    "ZFsw4q1gmDTEKET3VEnBsBpIPVqPdT75hYnYwOADiu2QfOnGuJnjyVQAjExuKLcbhZP8+69Msp6Y+/vTswdnfKjGw44fGdELbPWw"
    "tFqF7H8XuaZqBZrdYGYuV+t1RBvP3KPOzN2qrzsG6A373Ux1o9JYz61Zo9dMi4XksXKmsUyeLXdzdbq6RIQRyMYknVqCMNDwpUEY"
    "SpmJKNmXS/n0jXYmSbP2YMcp819pV+gJz9wNAwG3BX3SmwYUxy11vwDCfn9/gT8GRDBNphkmXm102voiCPbyu5FJlQIo2PUJGILD"
    "M2C+tCfw0p3Ay8UJVOtcHFkFUYP5xOYqleq5u6zO3eUjc4ddRCrTN4Ssq72CWpNhMkbLMsJEaIp3KeaCCcAcQ/NmGrbUNFyKabj0"
    "lw/ULDKhn0czcPnADNzYK9IAZcuG9JYL6a1FSI9hR0NLk0v1tm2IWIHAxnp7br0a2FtVYG89DGzVwpaEJQ33skufqtEBNUotVmbg"
    "V0pHldJyfYyCLXd9KIiNoDYzOcdqcrbE5Gz5D8JmqBoy8zPDyV06P7dmhagjzbHgNiTTcRXM2FGAisa7ggUyampHm5dK3HxE4mbB"
    "Xbw+6jd2gysoSe13Iay5IKx/L0Dsu2KXp0dncqns6TdsrwzzcBXsylPfHPiLq3p9bwmLgWzdFXJacWMPBnKEanoS/sfBXnekOag9"
    "hv+gToQjagleVpz1lqKmJ7BrYxBqOsauXemuEUNZGfNVgORMjsTW4MMOXS106Mrq0BUkXOnrGLtZ4cYhyKlD1RZ3gxuoGDLqVndN"
    "qwCnXQMkHX+lXtfdtfHzqEufAni7C33dtfq6Cwm7RikNa1yw/Pysd1yck8/+3IWlQbmDKlEmWmMt4mPnRqxyYnzWFueqy+BYnH9w"
    "85JTVM3a8c2N2Sg4Xo7QbA9QIRXXa2YCV/ZaUZZyBLmV4Zdx/LPE8T2hUirR/PMvofnnx9H888JMfbZm6jPDfxLNxRj+HoI/MPA9"
    "QnQzHLbn4vovLL5fwPUHG1c4v7wD3KENi2i/56L9nkH7v9Pt5WifcAfv4fNBxL82iP8T9gBCSgH/XYkfpv9kU1U9rfjsX2Y2pARP"
    "HZCQRRwFs97I0VYZKQ5DvPgrD1JMnKBkDiFdfOHf4cA1DBHMSWPEFntscXFjaFCJ9/RztKN/22FrJA5bj3ZM9EdywKMKR2v3jyrR"
    "C5aesBUxo0DXPbdmT501qudLffS4lNjoNPdvOuuNA7Pv43ld8y1y1kdixm37PoD8TM72yKcPMbEbcPB46BgYLBwD3czumS9YPAaK"
    "uZm5c/Poqc+eErp5EMKT6rxAjCWEmT922IQaF0FleOeR5p3FMh49xDsrcms4K3LTbieZHbDKPP+9gwiKdOjAYWQUarqe9xvLQboE"
    "00olGvvrMeD4DMHid0vnvHVNwulREWwNUbmA7Qwp1PHZYYJqUuLEtidv+1PpefJHWLnBfYsPKGFsEci8hmx+tLz4HiZKbaT3tXGY"
    "4K3GuYwQLzFad/8nmRKFK2VR224AVUv0lkE3O/JKDy8Gi3pKN619J/IeVWjNrpO7SQCaBxJlZUuKkLi2lFqllj2BpQ8jdcr2ULdB"
    "AEg+Eo53NHhBy9NBLPSg9NWYuNxV2kV6l2wlojcQ/iQegXSzVn3bC1VlLfW14YwA+4FeCbhP9wx3Us2ty5m6VKJ8eJGL0TSjOP1q"
    "R0LuRD8QX71AoDvKAga8lziDDO5oBN02s7vdVZsGwqYgniEwdwhCp7ys4Ns+4dSHUu37EMI7lw/lorrOkeUqRNxTpC3zkrB2b55o"
    "Eba4WA1KBo0gVqiIhH5YIpPRI6dVD+R/n9Lz9pb6m/AwfydnDjCmp67PDOqSE0Uzy6XOSy6h2ZLbU3SJ62K1UyNzaqsgbKVKRbb0"
    "0+/WjY95t+b31NGV+iSVVITR2R+oMx/cXQC5FU8/Ve8laa7fhoV0tSfuI5NwMa4YhzmPundSbUFEWiBWJQmF5owPh/iGdrfyPM0b"
    "qUyCo7R6CLNl91e8Wp8+PAYdXui/XHQmpjoYnG4nXQ6Mt0RA95y3ZMhW+v+Y2hYiwkqG3sbiNHTUhghH9Hop7V0CKHiSuggH38SX"
    "WbLWjUNZVcyzht5bdOBSU7I1VGSU/f5SX1NrKFfKJQvrR9xfB2lX3mRX1k2K2n2yLGqakVdwvR1hxdaMM7MqVbW4KnPhXvqh2u1V"
    "aVowkEgcI5/UxRKzdjBJDrxR1jc6rzbWNtqk6eErIKZisaJSmda2obXGyvsgZzIZSMNWKDphejF231BwOrGwt9kbE0DIzluSjZcm"
    "bbRkAi0XDcoFZC31qUKakmSBhWRlS4cFugl6RDhHVELjHT6nQCGDfGVLBS0U7MVqDhN0Y9ONg1jMVcbUWw3KVkT1zC2SmiKp2Cgo"
    "tlfaCzZ/ZMEuUJtYrci8uiJzvSKZS9+UeA/V+qvLWx3z+wvAhr5zhbfVYg6rk1T3KHd5CgIsVBWThRnN8NF3t0t4NS6GptcpGr3r"
    "qa+mStEguUgKWRQMqNe9gew8YpW+ZI+DqJuJhAhiB1Rs6O5pBl+HwdDB1xC+q51FT/VkjChbGC7AMeqGqsVq8WDgE/Me68GRQ2H0"
    "6KUwopcFwHIEMCz5YFMQKzuqCXqaQwS/gYBGfeIn8/oET58T4D/d4VBHrDVzI1ZKmxZJ6CyScHGRhMsWia+cMt3C/nwQhP8Pd2/a"
    "HMeWHYh9n19BlJ4wmY0EWFVYCGYxWUGCIPke10dwR0PoZFUWkERWZjErCygQVQotEXKPl5iwWiFZo/bY88HhiZmxwxGWHbLU9vyX"
    "bnW39Ul/weecu52bmQXivW6NHe6FqLx58+737IsKujSEgzMF+PGUWR620GX9PHiqm5aMxTm3pXAvRsG5ELBNvZE3NPY3UG65kV9b"
    "98+lYde5Muza2txcvzFrtbdFjWa5x2FQ12fX6tA/h2piR1R3I5m+kY9H9ND28Yg353OzOnrNxQbZFnazYGsDmk/UdcWuJMRQRcF+"
    "eOAPBT0YwhEhyDGt2bfhb7Bv3kAjqH4wCKZeLxi5vj4kUy+bBUMVWpEQVchJ6Oo1Ne8FUwHnE4qG4tshu47lKx8MvdpLPZfAFS3H"
    "0ZbMiKFwqB67JUHPS6oXr9rRAO3UVFccWRt7d0BEaLEOk0/E7UoknpbG6xi+LpVbEpsR6VYF2oQRvwA8mnmSfqZftpnoiGHU4cQy"
    "nUr12dC/JOvFvbvQ0i01oThTHoozFaE41bbj8iVLbPfMK9Ew5vOS9yK5TAR+s0WOHIm4LcAwiBQRuzk68+ykyHbv5q43ytWvY/XL"
    "0OAfuH/6bsUu68aG8RRhpkmvQ8ue+ZNznAv/mFEuPDt2Ug87jJhRr4oEcu2mCN/VavkY0xSzR9rZZVwk/cJhRPm4X7342j/ORDzF"
    "RsMtBV2MKCbTdpdnSEJWEw3+WAtSIRYJE01yjU8DbBXGNH8Pg5VD5u6lp2NyH8J372Fa+O+x5SNDJkywfMe59mCRYSuhcCc1bi2F"
    "7EpIHzsy845jLVZhZWIQhoC6XclksMEIU8CUHNCabDfvJ8pYVnLrndSS6KXM9lOaC9sXgYg9xvYFBbMA9QqTwUyEf1BWluxxqeGa"
    "3IJKhqv7vYm2eZatK3CQp1GYPMv7Uc4iB9JHxgi6pkXLwfJCPitJFZ4BWaTjHc6lYamMTyStZrWQ314n2Y4OL2oKbOsy7EZSdLop"
    "PQj5g8YyXuBh+yamMGs6XWNoGZU2O9GtNzF35nmDmQ/WDs+y/ORrTJFAAZRfR/kYvpY5m8VE9GdBkzrKkrLh6L0YLgjc3yj3vo0v"
    "sSr17hYBpu0U0Gkg/07l388UDfftGP8d5lCxN8UQxVrLF2mfdC3Yabf4cf821Kn0qknw7FDHJv1mKewxmv1RzroCc9YVLGddjeHu"
    "w9DEzvBi6hhmGNMMvdKFkPJKi4aXRRK5eJmWRQYmxV8ZwSib3ql/PMXsRA7G7YBVg96FMz4Mgq1he/NWEFfkYajHjFeCFq79YPHQ"
    "2ICGpjOJv6FLvAiszl1oBJrTt34gWA35LDZfdFhYW55WxtesRRbvQhlAFMBVTvGrZR2aKat4kuqKF9bqCWmEYdL0I01aPH4yPxnP"
    "qGwpDGtV3hh4BRQc/pUSQ5grs1BMhSPeIAo4V4BLwdgUy2K+OnIBtHAFBe0iYPPiMflyLCpPG/WL1w3vXtRRDhbRArFpC7cBa3qV"
    "dRyUZWpmTQdcVGXWVhYLnuuTKvokZByGfP0uCzzXm8LMg3IrnImy7La4ApRC+4zZfRgbsTTuk4fY7JMSQxWLVgcvkeChX6BAGcjE"
    "F1F/0oty7fM3iIheM/OOMeejYX9jTrwlFruYKfpUypGEvMFTkoo5azXASESFTWPblKGSSeUBk0p0hMW6jAsjGdG+YUSBPSXIRKzn"
    "3WKZAg8OXBPMB+h1yY5fSHYzpPX0+2vih3ccjnfDIxkSDoqtZy/ir8wDZ0JhxKWvuryqHwFAUr2J3H2S1xYjGvzWR9TpafYqBOZ9"
    "5GVB7vp6IUYA+pW4fOAhrzCY92EKTKZkYh3hr9g1LUJTvmwn9AAH5WUUgqHcpZ6ljFywruGbMvkkjkfPs0+p/GIu/Tk4wxQxhilC"
    "hilW/JKZV0zzius4qMhV4rCy9gBZJ3El90tDh8H1JflwwED9P9WVNL15ibmMKKGs0q/mBhVVsRRcULUAtE6RE3uZOooexttmi4N2"
    "zQlQ9SlUuvqmxtY2GjEw2+nYrd3cWILG/djL2ap+QEcj83jP9nJFMS+tNTDLmFwxQEIoL+1WQkx7TKpHe7SJJ6eBUEbA9Qeh83LA"
    "4tgjoQSMCmYW8igYwV4ajsbHGZEIs1k8m00N9TAtwX+k/Jdb0lNIeQE0N7a9o9y56X1d7idBPlKGWhI649NFeG4D/YsAwq03Z7Nn"
    "mO4AcxdrBQDztNS+38xNd317A9EjmwzwjSLsXzEHeqgoKX2M/gCB1LjYJUmA1DcVGRDhEhPaHxJBKd6jYhGVgIEq0OxUl1fxteqR"
    "kchfM92jjE4YwHz5XgAsuY9uoMvLn+1YAi8Hdiy+a1a0KOsb9tX9Adf5sn5IPU0jYLEHUp0wl6hw1FCIHL6a+DYtf2Ytk06l5XaM"
    "tmSaUs6LlrfKcwpMmd/RiensGgvVxry/0A3RcasXk99AIo6upCD0FOQxCscSlPKnuVe5zH6ELmN0oaSqVLUTDKb80FMsjAp4jdj9"
    "P8rN7uugHBcobIw8kWPQx2x/4yLPzv0Cfo3Gfm7p23+rx9nUDxRJJ8+1ecPPdk19TNgpVDZeochu+S4v9YABFs1S3EVQKNcAgZ69"
    "aoxuryhC6NgUGgJgjlr7dMAqt2b4iYQ+ucncS+buXPgzjsvNh3Qqg8pHnXKmnUFUIhjLNDkBasBDckOZpQkwyrmHL9BD+KJm/Dii"
    "GBMEK/ORK803tmwNjiYWJQ4Lub1+s7m1ueVtY1xTVvNBaNWENSG4Xq72YlCutuG1S3We1NTZKNV5NdBigjr2wDXRgTAlMXo6MzCX"
    "CgOkuWSpuH5afmB4eOs7EwPKVoO/rkDVoFhS2juZMYoAvrhSYkKvBlZ2GBgi1yd/Ci00/8hC83S+0iAtna9U00f2GVIxm4znLD9F"
    "qZfvtw7cbr7fPECzFPtg7EO3Bx5HIW/+Uw1F7MWXB/RtefWBDGi3ug4gH0CLSJsVwac+NqXp34LoX4zqZZAAUW8U1kCXkWqI1Wh5"
    "2kTKHhTfucmUr8+DzgM8C6hm2rhddAsfTjKpTcT6fBuzDKod6wmzyCJSjchwDpaZBdMpPLtqzg7jwytCxf7Utt0IVc4WxQvmivMq"
    "SiwX5mgyTyUpi/cOUbr7ANNVFSYXexEwkylmLiAA5kvY6c40lVmqgM77JEi4nBs3DOoGDITubzJanC8bcMIY0LhsL6EURkJnGGvp"
    "XmzKXXqR1nEvnhYUuIpUyko1BbIPg9jJcOmQe7GZW4w7kTCmVvCYoZe5KhORbYVmGF0pgUi0+ZksELyqJ1nWpGx+lmjkISg4fQTn"
    "ej8Tvp8UUvklxdOv20y+m+8smtIsNIthW0QiQ5aEFFTCMI6EQ2/HAYogm9oKTglnioXGQza1QRnnNW/IQPCAqf6Mrc73ttKhHKxw"
    "XIFIU3HG/Cz1JuNoR6mDn0b0KF+KJ0mNiYevhyNKl3oaiRiXqjgdRznFNeeVH4fn2aSwijDkmfyp6FX1NJC/xD0Rv+9FHyZHwmZT"
    "FQwiQIF9XmZyqKpOJhTCfy+b5D1Vae887e1ORdy1PaQp1cj79AMjgsMnh/H4aXT2IkKcCTx3Dpd37o2ml66ZiaDLiIaTCuAjxFHG"
    "UoBI5nzFRdNyxY4mtSvO+7sqygfCCY/PenN7EeKv7FfttKx2iCKq2/2FnypSS58Eu6a4QJylqkHs3qVoec5PVnmlxMWx2y9MzrkC"
    "IBO0X5ZJMHEnho387TFqUQ2fls69vJ5P69fwaXmVT1N3icd1rrKqaButI5dWWFOxilL6Pyndw09h9R7WBJGuuQCiWXZbSyndogA4"
    "a6I1gggIMDPWCZ96hBSaV9c88K1qBWwIwPqZ18OC+pOCoiqxbCLElZQaSq1wKZhUEyMPwSV0XB10ikQRVxYZ5dT1vMwZFZJpu5Dy"
    "IM+SEmmlUiJPTewBz2QJzADzM4HZ5UIvrFtUhF7FXELKyobh4sB2nUZrcR8OUzyIo/x5Hg3iacdEBSswoiEFLyww4CAFKjSxC107"
    "8OAKdB80/MZKutJ40VhB3n2Yr6x4zVtoppCuBI2HUGp9AiNYwU9UWOneFOrrRvJy9RV4oc9WWSgzvxwVHF+OCh4NFgLzB2EtMH89"
    "qAOgLwYVcPxkoIHmmwEHcg9jdeXvDsy1ZTslp/owdqa5AL3f4TYb6blasm+RTq2o7iL3i5dbDAAuticarOXMCIzXXOEPg/qLe28g"
    "j+bDweU7N/z/3s69u+LOvfst7ZxWG3crAN//3rv67v/NXTWGHf1Uy2MoZYm0yRIB7C5SaaKZutJFybw0Nh0YsDhy0V6DZ0mmZ7Tk"
    "MDSDiYZuBNQZE4lXYtgVZPRAfiqF2gFfjgjzvlS4ec9m9SypJ6NGZAjgHJBDPH6STVIMjFfFxRQIz448PHa7r5F7RQsiuh5RSuhj"
    "D3CLfQqVsqLahJQgELeVSGY4Dl6kZN/RiZWtKRqJq4wqTmyMC9HVKCD/Dcxcw10UpNSdGLs4Eb+BdVNjfCHSnPzWxonGYC3vn268"
    "9zM46tJG36Z3Fw22EIM1EoYXyMzmrkwi1PbSJWNcaqw19QBpJNUB5pRjSAyQeGFzfU4n3AgJ+Hke3tzEWFcajjUgPiYYrHo4wrxe"
    "hbSh5fYRC+o4OTWPYWlV5Dg0wjNh5OLx80keCdsv9Wl3qZfTAsxm+AvNpHxuQvW2FPh8qQVr1i9IIcsi3Zf0NDF32FbCkW4cwO7E"
    "KKAIHkXAEHTvFz4LF57bTY49jKEc5FKI26Vg+4nr9+m0YKC2VCQVqhAaYlVZLEH1rJgdUeBbZlXQE9ByVvTXtHyCgA7+TYPjJ98p"
    "OD7MjkHC84mBhHqanknqo/b0TZwkAMwjQKgykq8dMnFhRUcI8FSDr57u3bm/e3jldr9UXzRvtgOOZx6v1YAeJ1W1vJKH6ues6vfC"
    "E4GRv3yA3l1jgX3L6nGK/4hm0+ST2FG5tPhRvvQMJ6qqOstx7Vk21ejYxq67cEjYPfAd96Ic1kmU3c+zIa2Yx8bC9Z4SJ8YIdRa0"
    "y/ZxUeu8Ue1tnnAdsMgfVwVBrHbdphO+rI04mqxdXnE2c1KV28275Bt7PepqOK735TGWm1lY0RFAX45s4blN1G5I7o7ctAqBNL60"
    "T2wS9+J+zfCMK4uUE7F7cS69xo2mvoHZ88ipolgJ3hwDP+iZpO8qJYAKxFrILAAxGhb96J8RG33tCBPwAFmeHl2DkQMhf+1HKzEM"
    "fjwOj6KVH/0zfKIXkmiTXHTkjQUFmnris8Trx0fRuOJg+iAu5Q4sfy901OQn2O0K8zfZkHhkbd3NzPzh5o2zJFqLSBiQqrylYobF"
    "5dm0irkU5k519q83UXjyJBxZGFiW+RgqVI/hG40qC6QqVlt4O4Wj9LqnnR+DCxnlRCoplMRZWFpo92pNerAhPsFkek9QHu49QLs2"
    "T8567hUsQ84lo9DpZ4gcqAELtPEsMFNue4gpb3hpFaKnVOWrgJLAYdVOQ416rjQxBoDLr+Ny5N/Yuhs7JLSz78alXelMLDZMcjKt"
    "RoBfSFEAje7sF8fx+MD1s2It7PcdfJIBizOBc3snHSysDkmdNe9Cv9qj45sp7JH5jcYc4wWxDftYSYAygiu3E/aObS/rC+uVyIc+"
    "lfdXjr2TU0BaMo+Shn5kxoUhgxPOeekvPPMFksDHISBp1KomYu7I032wJISCq0pl3jrPMl46IeMdaZ5qBU8XnigyWrqN/kTYdMk6"
    "GxcUWeYLza3OcMZCZsgkmtoFuDba3ZmVPdNIpigIf5c5B25urm9p1hDmicpiXPmuXcU3n7Ta2542dGutt5o32up5OVjdbG83Nz0V"
    "JqFFJ7Qc5asrXrduYKxqcVdbtLbEiAC7gZq1FqXGVMpteC/Dgx9VwoM/o1jdqMVmoRfuRdygTKQw0P3vomRCWeS5/tGYvJeoUilR"
    "0FNrHUWmTpStawIKyCq1A5MxnSdAN8z/ghi7IkAXARa5ZOlV1C3FVCjHYFAL2m5urqsNWg5+P/HeCMaUUtB/BZBieflr1H+qT2Ct"
    "PDl5UlTKybM57Vlz4nb2UkdcWNGD60mxpaIHWBMIREvywe5aQXAizI2BaFFftSudp1qbeAQwmlTsHQ4knZeLeUYYIqqQ+QaEUJkc"
    "WZAPodg4GBgqFSHgmYeU2nfh9qyyanlLOkJM4iojpdh22lIxAeQcPNKEycPr94DrdTI4JygVotDsom91XfUOaamO2ZoIo1+jQdIX"
    "B2027HBQ3rAle8Oi6uCBp41rRghv6KJAN1bOkxwWna0KxW7QOTrojutYOsL8Qc9MQA75qVeZ+ouMjd1M6asSe20PR3iTqgBi8eXO"
    "J4Qs6Cige95x3O9HgLMpYViqso64ZekkBUR4LNVqPUQsz7MsEaSXsUFRNoKfnPHYewck67toFhTaP2XJKZZNYhXX2FsZzn9N9zPD"
    "hCxquVIWbSYwTXiXDDP68jBrPKWskYu70/nN1iKvnZ1f2F3l0o9Rh2SHz/ha1HqhuT46BtvtKCgkQVoisDCtnjlN0chK/0pA2WGA"
    "R+ev5LGjRKIFyuiu7+dmq23gaLt580Zrs80t/fhhlnfvEaZutblgTc4hE5yiqEahhqKCGvJ/QtSQL0YNRT1q2CmjBpqdmupSs/MY"
    "0zAod3SRSUbNLWUyJAmeeiLJufeWDKcQ6H3OHNU8TB0aVLZUNg7KAtaaFwYll9pOJgUeoYzEkSmxg9cnoF0RavS5UEMRWd0+CjP6"
    "sFj9um2Etmj/+pIMHkDTCwUWI8U2DWrlBdlVpAudEav/JaFSrZghW7tSfSB0MZRIPpuh11QfrsD5BCYKKA0m65kYKsOK90kmmfkh"
    "svhIYWS4k71yPU82P4Q/vdnM5ECczb5Ju07dUgnpDh6OAR6USpOu54TBN+lsdjqhWiF0PvR6uDtd50sLt1gwk31ZMHNJTXsC2aXi"
    "mOyq4pjsMnEMa+5LYpO0LDZBI/bv/bFXuoNBxQ0s6Lmeuphoxj2WsTL05Qz6qH/4zUaBknhpDWEDCRnNrAos4BqnKkppykOtdkO/"
    "nzrinReasffhMpfokSGDMD0bwqj96HEIo5wRuz2EMD2Ycq8WwvQEhOlJCDO9BMJ0nIECMdPvD2Lc/7QQZiRBAIcwPQlhvAp08Wqh"
    "S0dE+ylDItb8+UIIM62HMFOEMOc1EKbPIUyfIMw5DHg2g0PXdQZfWDyx3FdZtmrNhXCmuocVQKPVYDhW7wpDvAq8sRpdAHXqWmN3"
    "ln11haPJP201kZ5eACjqFg9Dc5S4oOXloVVIe4xy9u8wvt+8E5rJFWDneR3sPGews4c+x/8/WhIByCWl/CSzqGLmN5PZkSwkpS/F"
    "klYEFQq8QLnXgIjOFDOGkYLFdUYrQEkgx+jJxJHH0dS4wSj/c313i4US4yXLe5/coaR8iJmDMt5fE/lZV8V3CSzhkzD/1JS5eCms"
    "bVGX5kvqPRR1yjalQgPDZtys4ZXSEbdRNyJojfGkDrYrkoiXSisFlKZVnlFUwcufgALF5wpr4uqLoEp2/Gy217t1MkvMKOjdD52E"
    "cTHtzS2Pyff0HHFSrzI7I6pgYk1SVCE90nlRm8xg4TVLWPqdGG+Wo230BbFGanA/JdeuOcMeZYsEYjdDgXQYcJ61NuTKUst3kuW2"
    "ENp4YdehhNuGTWy1byqpbl3kFiVLQvE4CVo/ORiHbLnl6niN6jJ9nTmpiHlVsulisZcDnlLTOO53tTCmG/FYSl0lEtn21S8jDzFF"
    "Qq/oOxkXDOGZH6hQczHKGKRIMFYCFljfCyzxlVzIUx/72dxbcnKYJVNyo22Okcs00YCHC8ky14+DDD1Zck/ZsUYY857sYGRBbER5"
    "TKoX6yhMkb7csfpV2lY4h0X1er/KUDj/Fh3KMpEYJKlq+c0+YMA8tg86oKXaylPheIRTCUmqQl6ZGJODrWmmFjTRslMKxMfyf/QW"
    "LrDZKGVQvORktN4mtFUiNk00nduLn9uL3/NSljFRHoccpakJUj0A/SYf8KLfpwCNifW43NrY2m42twDthMYoBz5FQIqmDM9QJpux"
    "PTTZ/Nh+5vyn2k+9i4C3UYrKz15Ut78Yg0FdXdpqnwGbzBKSXQJ4MuYqN557cem0ZJ51lK2I779f1B2ufK6lVmqvo0AfWy8Xcmu5"
    "2acxlkf1u+16TPJKARmk25Bbv4JWrEGKycZ22vhZO3z/96MDJtXacllQAbYftaGucmbkZTv4pni5F84wxUi3dBvU3U+rWbKZ1dKD"
    "qlO7cRG9j7GZvSruJ80jXXIbdbB0IpHJXVk7P6Y4kJecmeChWsO1KZNlQKddh0kVN2/Abj+IHe2G0G6jLk7OB/UeiOjrcIihavSk"
    "uNZQXloLxCQKxOSXLj47XjAVtQHy4iYwqPLF5Uct/tK9Vad1ebm6I5m7GExntWA6FulwmfZBLrheQRm7GX0heVhBCpUpg7fI3Mpo"
    "nMMeqfoY1deuoFLztf7RWAuc8wAAWmBSZ990XbGVqEiTLiZ8H+cUWRWgMocPggh5BSR7KEd0GmkffR0RM1tezWS4yw0/CdoybqUI"
    "fLkFJdu8ZGtDhsRsb4sfcObEj81WW74CrkC+a27IWhvNm7LaduumqoeRTcTP9faNLVlTKKlFBVJXyaa22q0NWXuzvdHe3ladUZpX"
    "1R/J+WWXJGiSn2yvb29vNdU3Wzdu3Gi35Efr65ubGxvr8qutG60mVMWVWLeWAka1faN5EyYJa7S1vbG+ubG5VYrxmQTNeRIkCCjH"
    "kzElgZB5CDK328Sg3MLXGv/QURa0K5kS66cgEfHbE3JTzcl2GB1htAqy57jla90qXWsdWobHvuw69h0uX/DgnmUngfZewszzBQ4t"
    "SNWtR2TCCHFPpD63TjeQnmh+SqnoR2kFL3wV7UfpyspBcB/qqN+f+e/Cu49MTdz3PuPf7DTKB0l25n0uhCUzAdacwVLD+MJJs4Ix"
    "PJ+YmDpWTgo75LyVCMXko8CMLDo2ph0DIa6qkCrxMYJ6dSea5N8FoHkW5v0xehUSq6ndBvUjVM5F4OYmuQP6QJ2GceIX9OcJgthk"
    "DnB4jTUnwaRsQYbHX6s2SVQxNopJzNewvaCQP7DhgDPv49EXlbwsNqqHeAHbQcCoLBgMsY/UA2efcuB48gAI+FnbwjImeiDPE6M5"
    "rMhH54xIx06NrPCxzGinnktaXqaDgf5sRnWlY7+6dS/tMK6RHcZVOGRWw7gS56XDgYu0PrWBXKNyIFdeoBtg5kNROYirPqhk3q2C"
    "uC4HLRwH8YK5RdG5dVSHmK/EDYlADA0YNp2tBq15oQljkX2hU5gsLQEzEmJXnqL9sqjXAQUbLjQDgmblhj5MdAcKSEnQk5hPvMIi"
    "OwHixAAS0Lgf48S4DHQ3PqiroYdPTre1nXQS+xgBEv/SfIxZUqJyeRnWytO/MFJ2gN1GczHUpuRSSqMtsqOoOI7yhq9mJKz8KRGk"
    "wPwltFO3jcZgpSQ1kprcC4uy52w/M/KS7gWVAs1TsbgrKY9EzjKK2NmQ7AxQLgU6kaIBD40wuDmFW07Lwh0i1F2UV66SR3NdcNbl"
    "2MsWyID96CHLH1nQzLAdGINB0Zvm0rKzHpnDaA5mfZusJfvgLtyocx1QRF7GlCVEWPfTEUpwUKhmUSn+Y4ySZtFwPpr3i4jey8uk"
    "9uevN/zXofFWqCbKs9tq+goBkAHuoRIKJmVdnbSw/eQ8A3RmJ+JyywXq3sg+1n2iVcuiKU24KhK5amvZFVDO4JblllvHuOhzxk5b"
    "V0v8/LpWokCfcI8ZMcmd9AUfUP3OmthNMbHyMScqnWM2otXVNDXq7fCJUPjVyhIxqVFSJgESgeJZIgUZtkxCT3vosEcy9Di/g4LI"
    "VhT5ul8yHWt62hhsbhvQKV/Ekfco85KRF486+Siw/d1M+GyF0QsLFCtL1E2M4S4zBgJuD0d40cjnyGGZvFhsH6y8RNkgixI0KGwU"
    "XtA1rqLwwmBggcCLWgRelBE4L5Db2RGGp4S/izL+Vm84NJnPO48ybhA+7yT2ytmuRBXzQTwT3NuKtCR22H9lAoszkbCmkIg/TkeT"
    "ogGMTS8TLEkufqEzIwaDZ3hrHCWoMoe6wnk18aQ7hEBaFGpXvMkrb8ptIUwJ4RFbG+meR9WeFQrUHihZupPEmEmlRnWbq7cVr5Qs"
    "7VH5cyB6h5lwpyTFVEdl4YNt76MPcEL2iDnamT87w6D2oygvzh20vElqC/f7B9L/Dz7sB5Ql8zyJpC9CGGAFaj7D5kM3LLeSoeSt"
    "oDhhF2h3v58dBI2GNN3Cs9zoh+lRlGeTcXK+FxVfpwC5H7588ljaRzUU4a2ex5PRCCPxE/+WFrv9mFyo34R5KrJ3WrUeEoiFlSq9"
    "DydFdj/rTcbku1CzIN0YxoxbRYKimNKhCtGekMfIRNe0qrmKEJXjaogsMd01+O3VrjQaZYQYHnpJ3rRQLnF5jbElAVnk6i7VLO9s"
    "1oMm68prlt1sVc/t1W1VCBXRUAL+VPcNS+XO4Ru9QqifECtToIY+6AnoRVNZtLtdjI7d7a0dHh4Xw0TeJS8Mwm5YKusph2AUmfco"
    "CJi9HT3X9akvfVS6yhZmiWV1ZWUymyuN326r0VjpQWu/lYNWf64cPR8ac5bu9fIsSaD+N05jLH6j+CIWSu2eWuSac4h5tIrKgsjT"
    "40nIiBHLS3acfdc2jwAoHddBZcRgeamqUVN+HuuwBEtfuRLyRpoDlyBYqmN84YgSJyzPhDAC1lgyrUko7kiBScpYLU29aIrAt2lS"
    "Dop7sJzhaBz1G35RHkFeZv+KuhHkZWYv15EmkMmlQdQMSfy2xuXbqgamrt2LauO1McGBLpPEvWYdPEwakQuLg9RVU9N6MsYQFiq3"
    "03iWMALOy2eLtFTi1cAuS4zIIGE6OLrx2P1v1DXrcVFH2oeIf4dR4bjsGGM2Mw+v6WXyH0U0vJQmyoZN0ZJe+XfTl8nVVFol+ntD"
    "ymiVZNm3ci9tKDJzL6LmNSHaUi84f3MncVyvXFNTqratCOZN8t47ryP89w78ixltjLZyRxlAYNYrabtTflmpLclpS0mvDpxSzj/M"
    "0d3awAR/oUZ/LR7f00zO8vKSwzQ9btkSxxuxqA7fZM4I1kAKX1E8/Eh6EpYXZ9N/hPsm/fBKWaJEnCphWFmJR4CLKBFvMmLCUE+Z"
    "5JP9/het8o0XRi4zGlXMz0vc/daWyd5ipiOkbaWMVrTW6HnIN15NSft+2VSzPM75/tP0ADVN+4P8IIiBBTQiE+LZFJHcj8MkO2r4"
    "gH56YdqLAP0AlYpPSQavkZhkADUe5OEwatDpVnam4iECnNqnZtAntfzdadyPMlkznPTjTEizEoBcya3XY5ViKFlZcb9xXo/3k4NS"
    "A8Ipmdonx+LKwIZHsvl4GB6pEQLIOLG/8RYMsB8hwB5T5SI7OkqqUxfcxOceBvqgduIUOIG40pTiJfK1w7McOTwZUfTiLBw/AXo/"
    "HiWRv7QUrw3lw/ySxgwz8aK2Y0Hxx66SZioUQFRejDRkXCX0FPkeA0XXyWpppzDQtFM3X8NRSEJIUq/x2iLSByosNZeXv80d6zsv"
    "JK1MsG/68kIgr1l/ki5bXi53CGTZb61PbAu7zWvpX0WcZYuJM1jzej7zc47K9Lu0TWj0Vr+NotaTnlN/aMTFGhF359eyifECRjC3"
    "GME8KKesylmEc4umk1bsic4gCHO/2U184EfRpfWezBroCce2ohj516+fnZ2tna2vZfnR9dbNmzevT5FkFykBvkbHZfcKtbsFMTu9"
    "PB4VwBBEaNxOUfZlfkIHYNNpAwFyrPiGoHFL1L9964fX5a+GzI8+zE4jIUmRCb/pwdUnLAd8xA51tbvCu4gxo3A8npOisPLe9cSI"
    "xVahAztGpNHXuJvpn3Aaidz7jOrRjH4E4hmQmV9p+ukexbH1Igm0IwLasGECMS21yG6Ro5YI888qHXgwzWTomMUwPeIwnS5F/v3g"
    "evXb7wHbI7dTaqQK32sGeSUYHzEYX22jDs7X9KRhPclsEi034sA3si6wurPlecl7HV2ODHKGDJKFkqbFvVtoQo55dNmYjdY/Fygk"
    "QZ8VgT9iIW5A+UMZSMY6HHa4Hx+QilgynN3PcPGAJ/Xj7873a574pWhDNlJl6Nn9pfSZZt7Ch6zRACA+zsVA2Ecas9A7weXHV+Ly"
    "4y9w+fEVxEmx29UzjC/j+n1d7TykaGw9NLJcjG4iQjdo9rnUWoxuIkI39ac1F6qOJc1pjqPiTgFL/GFSRE6DXhLOnBSOrOu69efb"
    "wD52mkmbLqJyxDKGc4yCA7sODt/PlV/+az6iam27HkO0i8SplwpMS2sL0y5wXfhCV/GzWd6cZqv330qSLeAVuZeqYjVE9DqYz8vC"
    "lVRxHiUcXe8OvICx3PJFoMgqmxMLbFISsyO9qaP6mjgtWm52RYaGeC2b//LquRmpH7MZmtKQJB4kGz2kSuSREG7SUfDJ8HMuFz0Z"
    "BSNRgvpLYO2ciHM/JbVjaUmuRGZe0vg8rqGwrqHuzCax4KjaJJYryYKXcL5waShqlFwLvg/5os0X6sf3ThqRmUrZPv4LtvcV0/6q"
    "kpK276vl5Qecn1ZWi0uWE4G7N3CEjtcc3pvbm1tNcjnQGq44oHPBiNN8QbcRz8S+VMna2toWx7CSqw76Y7ECyl4ZNQ1huOtYLLvM"
    "Qo+TsGdHO1wTO4DZcnXE7uBsRTOXiDg8cmsX8yrZxZJNYTf1bX27Hgkaxql8CCnZoquVpCV1Fm6ucbgQcEhoE+Xg0dCR2aMyiRDX"
    "EHfpIGNEI/ix7vpo3UeWz4zvqOU5mBzHVZp85RGAa63EPSZ4wiR3Fmv5K2KhVlM19yJ0Sur+mto3riyME2pwccHqDpqt5WdfC+V5"
    "xckmC5h1m6cM8l3SoX8eO4QZNXge4WI27fARpr3LDMqygGx+vMyyJbGMC1RvaAFtBXqwuEaboeQ7mtqeDyiVLrw6dXiMQYDJbE+a"
    "ekvZ8hYthrFX0t4JVXcYGexFORcoM8HSAEqxdFStGlv1uBqxJLZNf1QPJjypNCLnQ8u4cFuNMpMGQmqsslLdcG2/ksr4sxKWrDhb"
    "lE+jNSt7U2Phip5J4SilQTPTLc/eRNdGPcaFyAOhYu0IXlv6tSnWWzzOS6oTcSsqhiaztnGe49Z/wp5TH79e5Li3P44tB104uEhg"
    "mdOrgKE0oDYZC5Zyl3AIXITMZZlcSWZbbq4oBTspFt2BwroDYhRNV5mkqo+YYaqJDYTuoea4w9NXVbAh8Eb7Bzj11To7WFoPHJ3x"
    "Vvtu69OxzG+7JKyQSqqSgWFGyQeF1a1nwlDp+pmvayrb3ExTqdZWYjZEUWAb+6pl0+q+etPfnsgjZ/ntFNwmV1iLdulk+cKMCsZe"
    "QTlVW6BIWKfXe5V4X8KkZXUp4lAXIxZrl8N30bK1T3JItvptq9KG65fRUFujS1a2ycvmZZvCLanb4gEDZTq1hRqwxUoqRDRCTxdJ"
    "AkWNOYiWV7HkxoxM1kSWnpImq153VWkTKcqIcNtVWtfTfxQuJoovcxpdRO6mlciBlXQnmAkeicS5jr31PZYHaAv5uRireWMTR1cl"
    "cy6zeqOTvvA8aTaVnSeygftEEch3KHTbmRWidS8qKiFaoczHIJefpWpCuyePeZws0rcR/7hkqB/l824FDcHosoVMMCnCyaLOTZro"
    "K8sUO5GkMfHNdFxWaqW2BZrjnYkVwfHpVNs57GbBHoCBoI+MzTMMYE3FUjYAlQlGNSjZgpjbxRhLfBSr8CoeADVeuJv254IhivyL"
    "AvhE9BqxGEMWtvB1HJ3NZmdx2s/OdCpIjJKgWsO6/Fkk+cmRscpRLLcjggsBo3qBOuEw7R1nOTnfCy2qKno2GKCPF/nJoXBDhIhV"
    "T+ItpVE0bC0AbPVTprUrmE3GtWguAiagpc9qy+vhP314GsD/R0DPDaVRCMmPOx1jVjntjJD7n82kD9JIdwPP6+Sfnq0AF4W14tks"
    "X1CrB7WApR5xNnwdJfQrwcgw9FJg7XrOFIqZKkGTsMNgBOOddtQwkTZHmwzp6ECxVzH6RLG8vLKCynPhCg10B5bGWIqxEBFb9LCU"
    "OuIeSOomCCnFKBjCh6M1DAGZkmBgDr3PiwAthFZbs1mP/krqTBy5kM5Yb64yBwmcgEsoKzSpQtOqQBN6ngUXtMNRH9UTGBBanaQX"
    "eHwwb/deghAA7nXns6HrAVIGnz1joO6UEFurKbkeY7LvMt/0z6jUUGYkrN0LaFWnwMZoOVbmSM1RYTSPGlvzkrVGa9O3rMuhhXMr"
    "iuXT4LxEZp+xEoEyji3x1SQ4XhSkxLECPVHgJwRs3acs4tNT1ztzO8flrAS1YWomczb4dbJm/xgsZIs7H/k5b3U/ctVo0Gj41vub"
    "y8sf1/oS3ki9FBZxxVqlQkmOJgWQEmcp3roknS0JD9cxXYeAxTsEi1Pt0OztuMIswhCEEfNgUidH1cYDJFxYPutChZDPgzsTjyC7"
    "d26QwjfjsmUQo+0Fy664326+Vs7fnZcyrSJoxEvc6WcIERxKabIsMtEoH7tEpZvu6F8y/iwlMVVRa9+IAFGxix6Z1KiMtywMopnt"
    "WBJr9JTa47dDO5cHn1qDh+sfpNbgi8rgEc0I8WSn0GPPAZGqpJ9yiITG+RC/zbh5m0T25f55DJgaie6mj+ni7JMEJfO6DNVdTBDk"
    "s0TTbCzZqD41anqJD1GGziqu8a0nXqDMrEelOALK3l8G3TbggvVETUTXUhQ1evphkLOHDxl7SKbsIZ4e0KBskQQL9qGGWZZiRHVi"
    "kajWhd8OfaHmWe6wLDth2eFHLG1iZFwg1M9183PDfPWY4phHFhFwVbdD7FGW2R5YzPWQBGVXcT/sRNL7YhOZA/Fzy/xsbatBSLO2"
    "srkcm52rXDLQC3Kh7+WcHPZ1eyaUr1l0no06K0euh85UzHpY5Vw4mdinr2vpILa7BaMq1mJK+SZQDoEVv6gpc0pNOOj8YVqhPMfW"
    "NwVaL6ckK+EOL5ErxEPSTzvLCDcR+lJ5qmazVGnrdPBcJ+UKPOMqkws3GScygUO0jgi3XC+XvcWazqh9z5Iqf8/VrltTexWuPIN3"
    "X5hB7XsiuT/KyzpILd7mk/Z7FK6lRUVY21MOXJZbj/HHHDHHyb1UW9nv4R7tZMNhXNyPP0T5q3RYDqtJ3NyCes57DEGiEmMrFa2F"
    "Dnai2awYUxZ6pfcU+/IR7YUHaUdNWc/R+4hSZ1iBBH4ZIDxI0fToYyQmyNJKWWc84teEk0SF65cLXP9jqYh5dtlOddv+dx/Ka8D4"
    "/LrRCDiht7yMVXDGCOhgOPCIjS4aBfD+atVwjYpF9CSdnmbdgvLWygT3hia8EbjtRMKmfpGGAWkoQ6oYEsvFzDicwJLkFOkMFEkV"
    "k1TxiLQcOtdGjHA5Xt5wiarClA6Z69VTVXpmnTKPIMYtzxtqNqqZ4/JSMMyaE09HPldJsso6bxlssSh7jta2q+UXIdHMOK1wwQTa"
    "Lb++vA2QSGXi2Ikw2dtOhIFZ66WfZtuhbu5W2lRUmS5nmOrDhFNdJRo7ZSR9mZToVInDImDeIRY1Ep1dO5uSAjbLd0NYG+3Sol0M"
    "n9nJVHIXSFlMupKTvxQlXUGVu0ivklCuQz6PSWoHeNc0oCW+Mg4mzU5+q1D2b/nKihpGsZ8faJY2DlDXBfsXZB1J9ISG+ZXAL7SA"
    "H1y8kJ1AAdW56Qkwh3aduptsf7HxHb6Yh1BTUlMw848LLUNQLgo4IhbxuW0sJMzIWISCTs/AgR4nY13jDEL0pTj5fTr5mOa9D3sk"
    "TO8tcUN7e3ODNiPVWkjjbjQZOZQfnjkXsX0e2QJKo5REvE/UWR2Tcinom6Siw4/InXg5ACSSRAILuu5FmmyHqcZYoK73Uyme1OTp"
    "U+C3xGeb/LNLqs8tYFYexmarbTITwC8EccqVt8Td10zi0q+1W/h6uy5bIE5jjCkv0R/0kuGT7HKD4m5w2ipRXpP1yUfgSjEdlfXK"
    "j+GuiSRcXq8Kj6pQyFMHkwA4RSQSpmGk2RNYt5GHaPmKJWk41OZr9/qU09ObZk4IiEe65NFTLN0xAUpkt3oKSmQrgVytATlceiP8"
    "s9I66AxsW8vEG7n+4FJby5e8ljGmpEWH4vMQ/g68Ed4fBWZsE8NJ5lQCfGjTt2f9yktlJCeC9ie2yesas3jtXPIu4K4RMh55LCMy"
    "TI0NYeLxet6UbAgxDDcvJqeBqllhzfdxxarQr6ukbb33D/xGA/t054lwsbniFdxaAAzo5H3R1K6NecKse1BNu4OHNDHi7CuPbL12"
    "ZNb9vsTBi+4GGZWUAusu7tyiQa2OSyE17EGZKKDKOxG1pOQIm9TTLglDa/H4Ienfg9hbimezpMbfkpXVtge0wmFIamhXLhEROCXi"
    "ChZzECxcO61UtkiwviDBMDW4mPEOuutWgDZphS/IXbx+hB4/S2bK6Pm7NCD9tTBXRAD0GeiPgfbaHBjSA1+Ogs/BgAvjJaAYBp+9"
    "aTCU+zC8EhIEnLXhDaFyDXZp+YA7+Dsh7B8yfGG0gudfJrUv8mAIbJRqj+5ECtzKuaS+yxan55L6LmuHzy+nvsWpxqi7pbu0WZ5P"
    "5WwM663xLp5NnJFrInjMp9poYqqIoKH3OZi6PtWcD4KBJmAE+TgQR2AUREo3pSRv9DTQZpSDYCSARTBiAKXfpYtEmEYnwEW7cGXP"
    "bslarTfosTMeJeF5w2uksGjwJ4bVy4swLRoAUNfk60C8dX0ntLruwVPJEpdGkQXaML4StkB36XZ7qn0h4g7F17rT+302PrSrvwQs"
    "zpVMZqSjtVhrh8vGRs6gbb/baPilaVzWk+pI9ASb3W6j5lL+Xp/NRrXhtqGcRPNY144LM7LFi6ipHNXEheEKSxnabVQrYx2VZays"
    "gDUATyOUYUiKHTtV8tbyq7LsVdWkj3ToGDv4UA1eqgLdVknXZH3E+Dh61vyooOeRgVhuC6I88llAn0jDEMukMhzplFS5Uk0AZ8RD"
    "5FSZIUVn5RY7p9TuLBGrppxh3RSR7OU6OO76uop7Q8LyDkn+MGVBx8LnErUKpXu+kLcLZSskASUy9XKVXcuo7HrlI91z55EZ5jxd"
    "xpCWJnkyFELBDZ4GUnvnIyLqo8bAvOyPuIBSrLVtbM9xk1jHzx6CL3HgKbatuMB4rXKV1itZgNc/UfbdpUzHt2GsXy8INTIPF3y/"
    "E3XC4FMuyfwdQlqf8iDzELtj+pmlvsS5CRt4BmPuacPQjA04q49v/PXESchZSGIGzS1ngBl6rk/vxZ2OdS+fgeKB9YzRcFkH1O7A"
    "SLxPGLAXKY35PTwHMnetzU1v38DcizxEvewygS5j1xdfmp2j54uyKl9cuc9ccY8NG4mKEQbgPSxXu5J+HyXDwERvemUKQ+l4LZJC"
    "tQ/wZAloLxUwi4y4q3mhHGmMrTIx12r3y+ym0fWX3ridvCZ9Clz2qgzwCtYB7lwFBLAYWn1mh5iNI7bdy6URQVbVfGfcAq5QsRMt"
    "TKN3Q+AbDtG03TdbbJvaq1aYD0VqpsK1CSlxE0vbZqSAegPRmkkl4lsQFEHaMH4/V6+ecfNCap5MZJyaGARr47xH+Ybhb0BPZQbQ"
    "4nv4srT9SijBtBb7iwvTLxvD9C2l+iDolyP6AgVjVRkB8WiMHsnISvq/50hblpGwsuhQ2LZsXKjsUL9s8YGXVO0cCZG+xZweEqkM"
    "y3YgQyngE8YIn5lJ2VzG+NChLFl4vKp9SFG1DzEQ69kXIVZN9wpuKXDK5cDffQhfXzoEEphdBQKa/KOa9wGAuOHpBe7JBS4QXX8Z"
    "RlY1HHV58kx+etZvLQwtjQITZ8znJpO1/pifCVU5Lg15UwOwL3yYUS+lwpSRLZfscGjvsM5ichHW7HBYs8PYyM40eBIWx2u9KE68"
    "F0k5ffg94ExwbFHufRPW5xaHfkrld/GLnSwdxEfeu6DpnUqBpTLOOMFA2e/wn/E4GBZOE6hvfDoVwa+8Fxg+Ko7hn/ch/iONPJ7I"
    "zw+x8OM4aF1vevekSckTMv17kEnbGIka3pJhcCSfXiXw3SE6tXyS9SYJ2XpiTAB92l9GjjYOebe81UWBij9BXdxqqztJ4CfJWJg5"
    "SWGZkyij+mUAHyfkGtU9iZZXTyI/nLK0JJpk6SfSWQ1+fOpjDsu+iAj/wJOOVfBb2NWuRaci4kVk8oO3tvyUomwjCsE88H7LDG3K"
    "4qbBCdls3jocS+GdtQ4aCm5vum7naU5xunPXc5YcmIcrfLtOI1e63J2iBFO8QvlWPMNoZERrAL1yiH2e4FjeRMLTvxDq33dinnb6"
    "E9hGXM2VzWbTK+Ll5Slm8eQxkCNb59GTqTEICIRDk+8sD55iFGYxPFhxv+kqM4ima+Rdj3oYMMNuR4m8VNnzPM7yuDgPTALeNMiX"
    "V/OaOmRVdiHgK+8B72zLVYY2zW42dV5OrFQArn8yqJR546nDApPiGm+5YlXIa0lHE1cg9y2qBrVfRBHshbYOvQje9UvZJ4rgLKnP"
    "wlAED/plJgsqA/d4DmylNxjZg53XLFlaXtuCIZLBSFsFmpvn4RRLngvtGzLnZ2XLkZwA+gaFhbycnLC5YdUXj0QpDna+vA43LYdm"
    "o+kozlWOiVnqpsHrhM6xWHc4CdIg/V3n3SxoS4b3eAREl3OKAwEagu59iudbwSd+zu8VtAxup59dQ7xwZ6oINqM9H+FSha60BMBo"
    "AnfRGeVFou0HYwCtCFK1MWXQ9J1TDmHTAEDCXOqym9IYEzg4UlqdZCS0FobPDsXlCd6KsLCuOr5iV4rgNBdjBjhNtzuXd5tkzV6h"
    "qJAtV77VrqEkExfjZSzrEq02sp27U4eit+k19tQAYznAWA8wVgOMzQCvPEKtFh3EaTw+jvpvsvwkwEuvCoSvZI7H06Jf/LJTDUJI"
    "GYhvB7t8EgESKnEvMHU1DMyitt5sttc32huutK5Pg8MQT8Iq+Yy1mrdkAAI6rk3hrS/ak2toZz7xnGQ5d0UMYsRWaBEJNIA6s5X6"
    "yzqG/loRD6NsUjwM034SBY8zZ6ewTA/EZDSPOl8ww43SDNFtr73RpPmxoM4oxiKUhQ5ymNJitdVp3so7St6x3lodohlEJw5at25l"
    "aG+AusXstshnkKFELfj9eC4y/2CcZHQ4xExiTqvdvJ134V9/Yxt/wb9+q0k/8Y/fuikqwB9/PVqHn/Cvv7FOpfgHamw1f7AzdfLr"
    "+MvFdmEnMKzzVVcp/8IqbdYckHruY719E4VXOsK3ObolaApgrlsCw75t3Po24wjz/diEplQX8bJoiI6ETSyZJJrtvZap6hHYtOkA"
    "P8F5oe2kxqzfZMIemdmxk4X1E+2mC78i/0lEAWHR2DA5d6AZLlgDeBAZoVqqVQXanQLTGxmxTEk4UPAIrWgLleVw6grLWPHLFjAk"
    "p2OeEx20yhJ6Xin8WTpNnRiunc4XuNSSRoH6ca44QOWsatuA4DSMBtM1HBnAtUJDTybKFlKztFYSnpYl4SmXhMshNTuGG5inZVG3"
    "5hO43clcfWr255DFlU/har4PPfwTx14Z5syIEmBgCaoJK2bCrxS+hKACAIS0o7ZUAASyZQOAACuxXxwgnYCd5IyQeEkcKcx9Ee2A"
    "NEJHnCEJVGXWMZZwjN0yZtQlj3pHpa4R+AdJ2LYSqxNm6khvLiQNgTB7K6JauSq2/WLkmVaRZ0HIsw7R6Mtr4a06pFrGZKnHgI9X"
    "mqtZya9CDi6IpGkJFln2jCwrtAxA6PziHVx4ScXXE+5si54QVxSZOxmpDAPEAwi6lm2T7FqMI08Zp4SJudTVs14IUucB5g7WJumO"
    "Ge0DDFVn1cfRp55FVJsBo+/pBTCl47H22H7vjMcMOknYeFHaDck92Mvf1OSrhUwUmFql6CUlRAMHvZhSlEJN1bnCArpfp+1ROh7j"
    "Jy2MBLmfNCaNQvdbAkMy/AGKhcdowyr2BR2nS7LXOj9oG7E9Cu1AkajOKaVNaa375DBcStdRLWv6L0InL7kJlzTTSpSHm8SVWbCc"
    "QPJGKFmIKEmM3juh1AM6+B1mTbPEC+/DII4DEjIASlLShceFHYUEtjC99VhjiRSwBF3Vx8V+ekDGtjGKvZMoPI36zOvKKjfmoom0"
    "Egb0UigHFooLZEk+0W6YbInFHyR6xI9srr8K8vnjwspzw3DuSLJY0hYZj466O8RAZIaBuJt4nxOuwirblej8bVqJla99ImRrJUVR"
    "wxIrrqyh559RIoMbdBcXehoFA6AXJHvydoxymSEgYu+b0HKN1hmr7FQfQoUcwVXHTVSCJEXW+sxiVSf8COG694JUMCcnwEwpmoYS"
    "I3rGqpMF5JMhJk0ZmdxWxYn9oOcNgtBDQbX0t1hyBkysgWrsplCGt1ry76bUyw7hIyMfH3bhQ27aN7SM0AclQXvJPgPei8AZQ/HX"
    "9UutCcvWupBQc2HDdjJxMsJ2U30Qp1a207OJM/UyzKqOqGuqgy99nDix1/coEv4UVrrfUZ6wJbLsPLA9WdEiei8qOk/JsLlXCswU"
    "PBWKvnP5VquwdcQUgcQvWP89x1TrmQyf7S2XWTJ8RfpRsUM0kjMz9zM99yXnjAe4wr08s4hhWI4zsxz3Q+d87PSAUzcjmMdBL5Cl"
    "Hjl5b4hQVG0XRZmSGIZf+/GB/34s8iOQ/jNDFwIJzmMrcJxO3UqjQnpoNVWxfFTuxePgGwAnXg+pl2NcnGPXtqVu+WHQo6qTQFiI"
    "eh+D2BaqLzmxHU5M3oQJksT3ojw+lYfofp4NaaX57ZjNPpav1UdL1L6DZHIp8mFmrvxSJgzfP7roWnGVSe8E73HSoZ70jrURSh8s"
    "5Sga2M6naCchxS176My95wn2ihsWOii/CozdsTZUEXBHy2YM+EUxEB2uKDCiGkXFvbBgr2aL7iY+A+B4mC8cEcEMAEck/BHpL0lb"
    "4deGixJ1vWbOi2JZZU/dRKmKE8esYDYDsvOURLKmF0nlcrKvLWVmX5JklaVXz8vSq0RKrxIuvVL4B0lItg45I3Vs+reN9hxq5Syx"
    "1oitFnYuNFN943A2HMHGscneqVbCuEbHMO5K3SHzxD0dca9b4PvfoVdcyU/V9kb1FLbqTrEhHxFVGcUx8Tx3++1olF1Sn0aMPdMG"
    "OIDCpA78ZCrcf7iCT8JvrHYDz7U6gnOW8c+NbIQYlSN/lZ2JBV8K529L41+lSNJ5wYKPNBpcKTag0ggYk8kcvrFNVQl/B5E8PrpK"
    "h8f122SbRpwOc4J8gIGTOeUvOJp63uGxTgNuWAe7KtbTsS3tHWQfA8l1jfgZMWrN+dDZX8SnIoPAmYmOckiwuImOZf9RSuB4FWaE"
    "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"
    "4o/Lv8+W/rlmEcLvfOeFWN3v/AISYvcTJx6wyv3ebefmJ3/pUN2nh37pVXCz8K8epgO+9/CljKIsLcJXv/zSq7/17nZQUnk7WuDx"
    "QIh7rd993/TPi49G+PP7Arvw7fhp8bbz4k+7t+0tfnHbwu8+M/v2e+WichYWfhMC5PFbFINeKrbkA8W2OAHPQYdrEjbhjXT3Rqv0"
    "9eOtN/dNBe967JO2z3Ovmd7cTz3vvDR7Ls+9frr15rb53XsReIH6not291mz26zxtxaJ6j65JfPePJTbb1791e/9y7/45//ov/3p"
    "H/3XH/7uq5vmef0cDHv2NT5SBG+eu/Hql14B3OMQ/F7mncJsaeWXb6lMDy7I9//W9186TTdEc5P9n3+CNQvNH7dDgx68p6eI0w9+"
    "cAsw/uAH1seDdenc24fzyV+44Df+PCY9PSWuz9XtXOnbeHiIBDzK511cXy8ClH4y3kXoSV7e/jRhepbmF9K0/PBBnt7cd2h6tb0p"
    "08flfIup+9aDVCx1v3ywuCJNnra3qPwtWyJuvEVxBq8+fLn3M+bvndb0Zuse5qVve9mnz+tqsnsMpHmfq3iPbj1xDHk/xm51vuzK"
    "cyHg1X/7z//Xuy//+Cf/6tf+4kf/4dXbz++LDrNnPxJ9iGKUi4opl3e+C+dni5w+f7kte7qvS7ilEixicHvQpd1d0r51k7Tymew3"
    "CPCw4PLPf+c2cfnpreyTdL95LyvA+1dAP/v+31pE8vuf3qfqlnF4042nh7WjTbjAliZ8sj63LUu+/e3ik/4WjUn9y/S2XeT9tsPP"
    "482bfNwD20+LN8IHE/jpt6FbWHBBR352m9tZ3vXz8pOqueME9mEDzNvq3oeBHj3Y7LdG//q+cekj2nqCmtlLpn3+PuVzfOt9kwkL"
    "be57un6v7cqqCoPPXv3ST7783/7ij/7FQp1nnvzyI2lfpz+LkJ8+lSjv+bCfvXr3w3/0k//0x+++/K2/+NGfv/vyV18BDw+AVz/5"
    "0T//yx/98bsf/uP33Hrg1SPfF0VVPtD5QdL+J0n8ePWewrdzZb64bcz2RGP/Rpz/Lo3Ll2jqs9eLnS8f7Hz5ZP3uzT5UeccbXXI3"
    "RMvNsv1eWd1OaYr9j3/15tM787xn5n3xQj1NN8f3vupgcfxfP8zYvX7sF90Hafm4wuIHP3i8eQ1Pl7R7+egWb3k8tOTWq+cNr29H"
    "Wt7mIReRfwnQ3++g+ryx8X3S6j1BH7Xg0p9b795+O2vffKwRs/aenvO4VcTNFAGfQKtbevnj/rzvQ3r+rdx9YYfW+unjIqzFq3u+"
    "LXjLQFxUzMP2ZK/au2b0P4lu0hAW/vS49CN7G3wSL0Vvmum+BSR9b/c1HP7t25LS9M3T89v699uy3tTLdl5eHcqXpT9ZrW6Fl97C"
    "q/+xXzzVD5S306puTsxtzcjNL33+Utzn59LiPsxupe7x2fvCvvuXsnp9r2BpFVvGbvjZ6+Y1gUJvobdLd968bV6jFLpcLv+Q+34s"
    "zWuKJG9PYfz2FEZgarnGlseP8QK5fRkvuKH3Gx/l9hsW7DkKvvziPXS4D7CFqg+g8iYBHzkO3/nOT/MbHmISzz+W2zdvbx15e/lw"
    "KvsW7XjST0vb4ftVOPfB/93ws1f/9bf+4bf+4jf/7V/+7z/81j2C8N4XudmHV58yt1mOt9R7MMs8zD6/DO7d58/6+6++15Wdlz2n"
    "Ar5eWni9IFrg1ZtHVRWlL2Ict/59fqPV6486dmv1G5GpXfU4QB+iUh8Y2LuEtp3+bGffD7P7yHkG5h/VGT8y7IlZn7OvH9Nh3n31"
    "B+++/mfvvv43777+s3df/fnt8+t/cf/8tXdf/t67L//k3Q+/fPfV//3u63/97qt/dbv51X969/Xv3Qp8+cd//dUf/PUf/dN3X/7h"
    "uy//4N1Xv3b7/PLvvPvqV999+St//cN/9pc//j/fffn7f/3jf79U8pP/9f9ZtPW7L//fd1/+6N1X/+TVW/z9ouhb9OLe+Z8BMr7z"
    "nZ+BMe5ZTA+qddE8D9S6Ee/tfA90/U/V94xZPohJfWDUonQx/O++/pU7VX714UWfcMWrd1/+kxthHt/+7//V7/69xT69+/J374T5"
    "++++/Ld/9ft/9JM//meafCfub796tvldeEuleTY3HyjIL26hrifLcpfKj+xI+F7T31H/wt33Xfj9f/eTf/gn7778jXv79448seFv"
    "/uxX7+xZLOmf/+RX/sFf/tMf/82f/dqrt+jCmxeT8s8nvz8EHz+/mZrFcbibmk+LLz4MRN7LLLghfppg+ymu8tNsHfQQsVz+3Txf"
    "/tkZfvj25AXfJzMe5h8vH+ZEPQeLboHNh3DXZ5/ctya4JZ8vBuynhyKew7xhWCx8++h13nzSJWHx2i+eIpx3en/xoAV/rrxptvcx"
    "5Jexy58rn3P7yvsU5cdjUK0+iv48zUl/aOruZ5Q/OcbFo6d+92Efdut8DlZ///4WDxT57E67n/ucuwUS78HiL77zQMDHew/A4Ivv"
    "P23ykj3bYU55jEm8b/VFGOKWBPB+OuMxPe0lH7JP8rBtvTh8ZsfTsP4fq/weV+O/23zM3Nvh9TdCQu+V2guhPN505It5358yd3WD"
    "QJ+/mDSGfkqZ+HF+60kkboDqvUg0YXYXiAeKLa4m+7p7flssfDKNofcywjE9xLqXm+ELC3CO3+8d771Znj6s0nik1BPjnyKC3YMU"
    "37X0u6+Xgfuv3339h+++/uG7r379r39zUSj/8D5k/+Qvf/Qv/+p3f1Nf31XJbQzfL/7BfXj/9sMwfqFil1rfo8bHqn/47uvfvFX9"
    "1Z+8+3oxA1/fLpY6fnqTf/hgDP7mz/7zgw77mz/7L//1V3793Q//PjdWWdmEzbfAb/G3DJLmW0slj7/64T9YarjbmH9/r+G37ipo"
    "qe3/uGmkL//OooIeM0O//A/vvvzTm1PwX/7dX//4z2/t3l7oH7/7aqnnx++++nJpetFpP/nTP71141bhbzyo0LvKIl686yNT3/4M"
    "4v2dF0rwt2/RgLfwLYD8wMrHdQLvlwA9HSX4nOoRZg/p/ff1VZ8//uCtEd6XGL8gd3PbRva2dry4Xdw2+e0+CAE1n3S/gGLQd75z"
    "n4TwTu3t3IL73q328mx88wvkT3nkLI+m5dH7hhfBetnwcvvz5tPi7S2e0336vrm346fP1b+dnq+dL556/rGykh/3qvJve6k2+Wvr"
    "s++/+2rBBb91E5Svfv0h6fbJpP/2uy//3t/82Y//1nPW7ruvvlqcvNuzr/7uQ4mFzy9zem/yeuPN79xBxU2y/uLf/M4iIH/1H//T"
    "T/7eb9zr/fECHu7SvIjnYjv/7l/+6D88t7fw/N0Pv/r+fX+j/263Xn36P9D1h7F0wytPdvOjF7i19+YlLnvSGbephXv+6KNmfdyw"
    "8nXxrfRxd9My+tZtT6THffGWkVc8a5GXMOiL9xMi/1PTIPdI7IuV9Tfj9JGt87LsHgz42MaFN90WPvXqpaItvA9Dqo8zqo9ZD7ep"
    "2Odg333Garh//CL02fL5KfS+nuutN7/06r5nftgs/b/tB7X8+vHqmoQLevjl59jC0qFn4/2NyaTwaSLpgxzX98L+xdvPq9sc1hDe"
    "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"
)


def ui_page():
    return zlib.decompress(base64.b64decode("".join(UI_PACK))).decode("utf-8")


def page_html():
    return HTML if (LEGACY_UI or not UI_PACK) else ui_page()


HTML = r'''<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>PADDOCK SCOUT</title>
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'%3E%3Crect width='32' height='32' rx='7' fill='%23050505'/%3E%3Ccircle cx='16' cy='16' r='9' fill='none' stroke='%233ad1ff' stroke-width='2.5'/%3E%3Ccircle cx='16' cy='16' r='3.2' fill='%23f0f0f0'/%3E%3C/svg%3E">
<style>
/* shadcn/ui (zinc · dark) 風。外部ライブラリは使わず、オフラインで動く素のCSS */
:root{--background:#09090b;--foreground:#fafafa;--card:#111113;--muted:#18181b;--muted-fg:#a1a1aa;--dim:#71717a;--accent:#27272a;
--border:#27272a;--input:#3f3f46;--primary:#fafafa;--primary-fg:#18181b;--ring:rgba(212,212,216,.35);
--emerald:#34d399;--amber:#fbbf24;--red:#f87171;--sky:#38bdf8;--violet:#a78bfa;--radius:8px;
--sans:"Geist","Inter","Segoe UI Variable Text","Segoe UI","Noto Sans JP","Hiragino Sans","Yu Gothic UI","Meiryo",system-ui,sans-serif;
--mono:"Geist Mono",ui-monospace,"Cascadia Mono","SFMono-Regular",Consolas,Menlo,monospace;color-scheme:dark}
*{box-sizing:border-box}
html,body{height:100%;margin:0}
body{background:var(--background);color:var(--foreground);font:14px/1.5 var(--sans);display:flex;flex-direction:column;overflow:hidden;-webkit-font-smoothing:antialiased}
svg.i{width:16px;height:16px;flex:none;stroke:currentColor;fill:none;stroke-width:2;stroke-linecap:round;stroke-linejoin:round}
button,input,select,textarea{font:inherit;color:inherit}
button{display:inline-flex;align-items:center;justify-content:center;gap:6px;height:32px;padding:0 12px;border-radius:var(--radius);font-size:13px;font-weight:500;border:1px solid var(--border);background:var(--background);color:var(--foreground);cursor:pointer;white-space:nowrap;transition:background .15s,color .15s,border-color .15s;box-shadow:0 1px 2px rgba(0,0,0,.25)}
button:hover{background:var(--accent)}
button:focus-visible{outline:none;box-shadow:0 0 0 3px var(--ring)}
button:disabled{opacity:.5;cursor:default}
button.pri{background:var(--primary);border-color:var(--primary);color:var(--primary-fg)}
button.pri:hover{background:#e4e4e7}
button.ghost{background:transparent;border-color:transparent;box-shadow:none;color:var(--foreground)}
button.ghost:hover{background:var(--accent)}
button.danger{color:var(--red)}
input[type=text],input[type=number],select,textarea{height:34px;background:transparent;border:1px solid var(--input);border-radius:var(--radius);padding:0 10px;outline:none;font-size:13.5px;box-shadow:0 1px 2px rgba(0,0,0,.25);transition:border-color .15s,box-shadow .15s}
textarea{height:auto;padding:8px 10px;resize:vertical}
input::placeholder,textarea::placeholder{color:var(--dim)}
input:focus,select:focus,textarea:focus{border-color:#71717a;box-shadow:0 0 0 3px var(--ring)}
select{appearance:none;-webkit-appearance:none;padding-right:30px;cursor:pointer;background:transparent url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='%23a1a1aa' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='m6 9 6 6 6-6'/%3E%3C/svg%3E") no-repeat right 9px center}
select option{background:#18181b;color:var(--foreground)}
input[type=checkbox],input[type=radio]{accent-color:#fafafa;width:15px;height:15px;margin:0;cursor:pointer}
.mono{font-family:var(--mono)}
/* header */
header{height:56px;display:flex;align-items:center;gap:14px;padding:0 16px;border-bottom:1px solid var(--border);flex:none}
.logo{display:flex;align-items:center;gap:10px;font-size:14px;font-weight:600;letter-spacing:-.01em;line-height:1.15;white-space:nowrap}
.logo .mark{width:30px;height:30px;border-radius:8px;background:var(--primary);color:var(--primary-fg);display:grid;place-items:center}
.logo .mark svg{width:18px;height:18px}
.logo small{display:block;font-size:10px;font-weight:500;color:var(--dim);letter-spacing:.12em;margin-top:2px}
#roots{display:flex;gap:8px;flex-wrap:nowrap;overflow:hidden;flex:1;min-width:0}
.rchip{display:inline-flex;align-items:center;gap:8px;height:28px;padding:0 11px;border:1px solid var(--border);border-radius:999px;font-size:12.5px;white-space:nowrap;min-width:0;max-width:480px}
.rchip .t{overflow:hidden;text-overflow:ellipsis}
.rchip .m{color:var(--dim);font:11.5px var(--mono)}
.rchip.off{border-color:rgba(248,113,113,.4);background:rgba(239,68,68,.08)}
.dot{width:8px;height:8px;border-radius:50%;background:var(--dim);flex:none}
.dot.on{background:var(--emerald);box-shadow:0 0 0 3px rgba(52,211,153,.15)}
.dot.off{background:var(--red);box-shadow:0 0 0 3px rgba(248,113,113,.2);animation:blink 1s steps(2) infinite}
.dot.busy{background:var(--amber);box-shadow:0 0 0 3px rgba(251,191,36,.15)}
#conn{font-size:12px;color:var(--red);display:none;white-space:nowrap}
@keyframes blink{50%{opacity:.3}}
@keyframes pulse{50%{opacity:.45}}
@keyframes flashbg{0%{background:rgba(56,189,248,.18)}100%{background:transparent}}
.hbtns{display:flex;gap:4px;align-items:center}
.vsep{width:1px;height:20px;background:var(--border);margin:0 6px}
.switch{display:inline-flex;align-items:center;gap:8px;font-size:13px;font-weight:500;cursor:pointer;user-select:none;white-space:nowrap;padding:0 4px}
.switch input{position:absolute;opacity:0;pointer-events:none}
.switch .track{width:36px;height:20px;border-radius:999px;background:var(--input);position:relative;transition:background .15s}
.switch .thumb{position:absolute;top:2px;left:2px;width:16px;height:16px;border-radius:50%;background:var(--foreground);transition:transform .15s,background .15s;box-shadow:0 1px 2px rgba(0,0,0,.4)}
.switch input:checked+.track{background:var(--primary)}
.switch input:checked+.track .thumb{transform:translateX(16px);background:var(--primary-fg)}
.switch input:focus-visible+.track{box-shadow:0 0 0 3px var(--ring)}
/* alert */
#banner{display:none;margin:12px 16px 0;border:1px solid var(--border);border-radius:10px;padding:10px 14px;font-size:13.5px;gap:10px;align-items:center;flex-wrap:wrap;background:var(--card)}
#banner.warn{border-color:rgba(251,191,36,.35);color:#fde68a;background:rgba(251,191,36,.06)}
#banner.bad{border-color:rgba(248,113,113,.4);color:#fecaca;background:rgba(239,68,68,.07)}
/* layout */
main{flex:1;display:grid;grid-template-columns:330px minmax(0,1fr) 340px;min-height:0}
@media (max-width:1180px){main{grid-template-columns:300px minmax(0,1fr)}#logpane{display:none}main.showlog #logpane{display:flex;position:fixed;right:0;top:0;bottom:0;width:360px;z-index:20;background:var(--background);border-left:1px solid var(--border);box-shadow:-20px 0 40px rgba(0,0,0,.6)}}
@media (min-width:1181px){#bLog{display:none}}
section{min-height:0;display:flex;flex-direction:column}
#left{border-right:1px solid var(--border)}
#logpane{border-left:1px solid var(--border)}
.ph{padding:12px;display:flex;gap:8px;align-items:center}
.ph h2{font-size:14px;font-weight:600;margin:0;flex:1;letter-spacing:-.01em}
.scroll{overflow:auto;flex:1;min-height:0}
::-webkit-scrollbar{width:10px;height:10px}::-webkit-scrollbar-thumb{background:#27272a;border-radius:999px;border:3px solid var(--background)}::-webkit-scrollbar-track{background:transparent}
.search{position:relative;flex:1}
.search svg{position:absolute;left:10px;top:9px;width:16px;height:16px;color:var(--dim)}
.search input{width:100%;padding-left:34px}
.tools{display:flex;gap:8px;align-items:center;padding:0 12px 12px;font-size:13px;color:var(--muted-fg);flex-wrap:wrap;border-bottom:1px solid var(--border)}
.tools label{display:flex;gap:7px;align-items:center;cursor:pointer;white-space:nowrap}
.tools select{height:30px;font-size:12.5px}
#venue{flex:1 1 100%;height:34px;font-size:13.5px;color:var(--foreground)}
/* sidebar list */
.rhead{padding:12px 16px 10px;font-size:13px}
.rhead .r1{display:flex;align-items:center;gap:8px}
.rhead .rl{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:600;font-size:13.5px}
.rhead .r2{display:flex;align-items:center;gap:10px;margin-top:4px}
.rhead .r2 .prog .bar{width:90px}
.rhead .cnt{font-size:12px;color:var(--sky);font-weight:500}
.rhead .p{display:block;margin-top:4px;font:11px var(--mono);color:var(--dim);overflow:hidden;text-overflow:ellipsis;white-space:nowrap;direction:rtl;text-align:left}
.rhead .tb{display:flex;gap:2px;flex:none}
.rhead .tb button{width:28px;height:28px;padding:0;color:var(--muted-fg)}
.rhead .tb button:hover{color:var(--foreground)}
/* 会場（大見出し・色分け・スクロールしても上に残る） */
.vhead{position:sticky;top:0;z-index:2;display:flex;align-items:center;gap:10px;margin-top:8px;padding:9px 12px 9px 14px;background:var(--background);border-top:1px solid var(--border);border-bottom:1px solid var(--border);cursor:pointer;user-select:none}
.vhead::before{content:"";position:absolute;left:0;top:0;bottom:0;width:3px;background:var(--vc)}
.vhead:hover{background:#0f0f12}
.vhead .vic{width:26px;height:26px;border-radius:7px;display:grid;place-items:center;flex:none;color:var(--vc);background:color-mix(in srgb,var(--vc) 16%,transparent);border:1px solid color-mix(in srgb,var(--vc) 35%,transparent)}
.vhead .vic svg{width:15px;height:15px}
.vhead .vn{font-size:15px;font-weight:700;letter-spacing:-.01em;flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.vhead .cnt{font-size:12px;color:var(--muted-fg);white-space:nowrap}
.chev{display:inline-grid;place-items:center;color:var(--dim);transition:transform .15s}
.chev svg{width:15px;height:15px}
.fold .chev{transform:rotate(-90deg)}
.vhead.fold{border-bottom-color:transparent}
.flashh{animation:flashbg 2.5s ease-out}
/* セッション（折りたたみ） */
.shead{display:flex;gap:6px;align-items:center;margin:6px 8px 2px;padding:6px 8px;border-radius:var(--radius);font-size:12.5px;font-weight:500;color:#d4d4d8;cursor:pointer;user-select:none}
.shead:hover{background:var(--muted)}
.shead .sn{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.shead .sep{color:var(--dim)}
.shead .cnt{font:11.5px var(--mono);color:var(--dim)}
.shead.fold{color:var(--muted-fg)}
.pdot{width:7px;height:7px;border-radius:50%;background:var(--amber);flex:none;animation:pulse 1.2s infinite}
.grp.hier{margin-left:26px}
.grp.hier::after{content:"";position:absolute;left:-11px;top:4px;bottom:4px;width:1px;background:var(--border)}
.vbadge{display:inline-flex;align-items:center;gap:6px;height:24px;padding:0 9px 0 7px;border-radius:7px;font-size:13px;font-weight:600;color:var(--foreground);background:color-mix(in srgb,var(--vc) 14%,transparent);border:1px solid color-mix(in srgb,var(--vc) 38%,transparent)}
.vbadge svg{width:14px;height:14px;color:var(--vc)}
.vdot{display:inline-block;width:8px;height:8px;border-radius:3px;background:var(--vc);margin-right:6px;vertical-align:0}
.grp{margin:1px 8px;padding:8px 10px;border-radius:var(--radius);cursor:pointer;position:relative;transition:background .12s;scroll-margin-top:60px}
.grp:hover{background:var(--muted)}
.grp.sel{background:var(--accent)}
.grp.flash{animation:flashbg 2.5s ease-out}
.grp .n{display:flex;gap:8px;align-items:center}
.grp .nm{flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:13.5px;font-weight:500}
.grp.unread .nm{font-weight:600}
/* 受付状況：受付済み=緑 / 未受付=グレー / コピー中=黄 */
.grp .sti{display:inline-grid;place-items:center;flex:none}
.grp .sti svg{width:16px;height:16px}
.grp.st-recv{background:rgba(16,185,129,.08);box-shadow:inset 3px 0 0 var(--emerald)}
.grp.st-recv:hover{background:rgba(16,185,129,.13)}
.grp.st-recv .sti{color:var(--emerald)}
.grp.st-none .sti{color:#52525b}
.grp.st-none .nm{color:var(--muted-fg)}
.grp.st-copying{background:rgba(245,158,11,.08);box-shadow:inset 3px 0 0 var(--amber)}
.grp.st-copying .sti{color:var(--amber)}
.grp.st-copying .sti svg{animation:spin 1.1s linear infinite}
.grp.sel{background:var(--accent)}
@keyframes spin{to{transform:rotate(360deg)}}
.prog{display:inline-flex;align-items:center;gap:6px;font:500 11.5px var(--mono);color:var(--muted-fg);white-space:nowrap}
.prog .bar{width:42px;height:5px;border-radius:999px;background:var(--accent);overflow:hidden;flex:none}
.prog .bar i{display:block;height:100%;background:var(--emerald);border-radius:999px}
.prog.done{color:var(--emerald)}
.prog.zero{color:var(--dim)}
.rtag{display:inline-flex;align-items:center;gap:5px;height:22px;padding:0 8px;border-radius:6px;font-size:12px;font-weight:600}
.rtag svg{width:14px;height:14px}
.rtag.recv{background:rgba(16,185,129,.12);color:var(--emerald);border:1px solid rgba(16,185,129,.3)}
.rtag.none{background:var(--muted);color:var(--muted-fg);border:1px solid var(--border)}
.rtag.copying{background:rgba(245,158,11,.12);color:var(--amber);border:1px solid rgba(245,158,11,.3)}
.grp .pre{color:var(--dim);font-weight:400}
.grp .ago{color:var(--dim);font-size:11.5px;white-space:nowrap}
.badge{display:inline-flex;align-items:center;justify-content:center;background:var(--sky);color:#082f49;font-size:11px;font-weight:600;border-radius:999px;padding:0 6px;min-width:18px;height:18px}
.meta{color:var(--muted-fg);font-size:12px;display:flex;gap:4px 8px;flex-wrap:wrap;margin-top:4px;align-items:center}
.chip{display:inline-flex;align-items:center;height:19px;font:500 11px var(--mono);padding:0 6px;border:1px solid var(--border);border-radius:6px;color:var(--muted-fg)}
.c-PPT{color:#fdba74}.c-KEY{color:#7dd3fc}.c-PDF{color:#fca5a5}.c-動画{color:#c4b5fd}.c-音声{color:#6ee7b7}.c-画像{color:#fde68a}
.tag,.kind{display:inline-flex;align-items:center;gap:4px;height:20px;padding:0 7px;border-radius:6px;font-size:11.5px;font-weight:500;white-space:nowrap;border:1px solid transparent;line-height:1}
.t-ok,.k-add{background:rgba(16,185,129,.12);color:var(--emerald);border-color:rgba(16,185,129,.25)}
.t-warn,.k-mod{background:rgba(245,158,11,.12);color:var(--amber);border-color:rgba(245,158,11,.25)}
.t-bad,.k-del{background:rgba(239,68,68,.12);color:var(--red);border-color:rgba(239,68,68,.3)}
.t-info,.k-acc{background:rgba(14,165,233,.12);color:var(--sky);border-color:rgba(14,165,233,.25)}
.k-ren{background:rgba(139,92,246,.12);color:var(--violet);border-color:rgba(139,92,246,.28)}
.t-dim{background:var(--muted);color:var(--muted-fg);border-color:var(--border)}
.copying{color:var(--amber);animation:pulse 1.2s infinite}
.empty{padding:48px 24px;color:var(--muted-fg);text-align:center;line-height:1.8;font-size:13.5px}
.empty .ico{width:44px;height:44px;border-radius:12px;border:1px solid var(--border);display:grid;place-items:center;margin:0 auto 14px;color:var(--muted-fg);background:var(--card)}
.empty .ico svg{width:20px;height:20px}
.empty b{color:var(--foreground);font-weight:600;display:block;margin-bottom:4px}
/* folder */
.fh{padding:20px 24px 16px;border-bottom:1px solid var(--border);position:sticky;top:0;background:rgba(9,9,11,.92);backdrop-filter:blur(8px);z-index:3}
.crumb{color:var(--muted-fg);font-size:13px;display:flex;gap:6px;flex-wrap:wrap;align-items:center}
.crumb svg{width:14px;height:14px;color:var(--dim)}
.crumb b{color:var(--foreground);font-weight:500}
.fh h1{margin:6px 0 6px;font-size:24px;font-weight:600;letter-spacing:-.02em;word-break:break-all;line-height:1.25}
.facts{color:var(--muted-fg);font-size:13px;display:flex;gap:4px 16px;flex-wrap:wrap;align-items:center}
.acts{display:flex;gap:8px;margin-top:12px;flex-wrap:wrap;align-items:center}
.pathline{font:11.5px var(--mono);color:var(--dim);word-break:break-all;margin-top:10px;user-select:all}
.sec{padding:20px 24px 0}
.sec h3{margin:0 0 10px;font-size:15px;font-weight:600;letter-spacing:-.01em;display:flex;align-items:center;gap:8px}
.sec h3 small{font-size:12.5px;font-weight:400;color:var(--muted-fg)}
.ana{border:1px solid var(--border);border-radius:12px;margin:0 0 12px;background:var(--card);overflow:hidden;box-shadow:0 1px 2px rgba(0,0,0,.3)}
.ana .hd{display:flex;gap:10px;align-items:center;padding:12px 16px;border-bottom:1px solid var(--border);flex-wrap:wrap}
.ana .hd .fn{font-weight:600;word-break:break-all;flex:1;min-width:150px}
.ana .hd .x{font-size:12.5px;color:var(--muted-fg)}
.ana table{width:100%;border-collapse:collapse;font-size:13px}
.ana td{padding:10px 16px;border-top:1px solid var(--border);vertical-align:top}
.ana tr:first-child td{border-top:0}
.ana td.k{width:120px;color:var(--muted-fg);white-space:nowrap}
.ana td.v .sub{display:block;color:#d4d4d8;font-size:12.5px;word-break:break-all;margin-top:5px}
.ana td.v .sub b{font-weight:600}
.ana .msg{padding:10px 16px;color:#fecaca;font-size:13px}
.evlist,.tcard{border:1px solid var(--border);border-radius:12px;background:var(--card);overflow:hidden;box-shadow:0 1px 2px rgba(0,0,0,.3)}
.evc{padding:12px 16px;border-top:1px solid var(--border)}
.evc:first-child{border-top:0}
.evc.u{background:rgba(56,189,248,.05)}
.evc .top{display:flex;gap:8px;align-items:center;flex-wrap:wrap;font-size:13px}
.evc .t{font-size:12px;color:var(--muted-fg)}
.evc ul{margin:8px 0 0;padding:0;list-style:none;font-size:13px}
.evc li{display:flex;gap:8px;padding:2px 0;align-items:baseline}
.evc li .op{font:600 12px var(--mono);width:16px;text-align:center;flex:none}
.evc li .x{color:var(--muted-fg);font-size:12px;white-space:nowrap}
.evc li .fn{word-break:break-all}
.o-add{color:var(--emerald)}.o-mod{color:var(--amber)}.o-del{color:var(--red)}.o-ren{color:var(--violet)}
table.files{width:100%;border-collapse:collapse;font-size:13px}
table.files th{text-align:left;font-weight:500;font-size:12.5px;color:var(--muted-fg);padding:0 12px;height:38px;border-bottom:1px solid var(--border);background:var(--card);position:sticky;top:0}
table.files td{padding:9px 12px;border-bottom:1px solid var(--border);vertical-align:middle}
table.files tr:last-child td{border-bottom:0}
table.files tbody tr:hover td{background:rgba(39,39,42,.45)}
table.files tr.dir td{color:var(--muted-fg)}
table.files td.nm{word-break:break-all}
table.files td.num{color:var(--muted-fg);white-space:nowrap;text-align:right;font-variant-numeric:tabular-nums}
table.files td.tm{color:var(--muted-fg);white-space:nowrap;font-variant-numeric:tabular-nums}
table.files tr.hl-add td.nm{color:var(--emerald)}table.files tr.hl-mod td.nm{color:var(--amber)}table.files tr.hl-ren td.nm{color:var(--violet)}
table.files tr.pend td.nm{color:var(--amber)}
.stl{font-size:12px;font-weight:500;white-space:nowrap}
.memo{border:1px solid rgba(250,204,21,.35);border-radius:12px;background:rgba(250,204,21,.06);margin:0 0 10px;overflow:hidden}
.memo .mh{display:flex;gap:10px;align-items:baseline;padding:8px 14px;border-bottom:1px solid rgba(250,204,21,.2);font-size:12.5px;color:var(--muted-fg)}
.memo .mh b{color:#fde68a;font-weight:600;word-break:break-all}
.memo .mb{margin:0;padding:10px 14px;font:14px/1.6 var(--sans,inherit);white-space:pre-wrap;word-break:break-word;max-height:260px;overflow:auto;color:var(--foreground)}
.memo .dim,.memo-more{color:var(--dim);font-size:12.5px}
table.optab{border-collapse:collapse;width:100%}table.optab th{text-align:left;font-weight:500;color:var(--muted-fg);font-size:12.5px;padding:2px 6px}
table.optab td{padding:3px 6px}table.optab select{width:100%}
.opday{display:inline-flex;align-items:center;gap:6px}.opday select{font-size:12.5px;padding:2px 6px}
.gone{margin:20px 24px 0;padding:12px 16px;border:1px solid rgba(248,113,113,.4);border-radius:10px;color:#fecaca;background:rgba(239,68,68,.07);font-size:13.5px}
/* log */
.ev{margin:2px 8px;padding:10px 12px;border-radius:10px;cursor:pointer;transition:background .12s}
.ev:hover{background:var(--muted)}
.ev.u{background:rgba(56,189,248,.06)}
.ev .top{display:flex;gap:8px;align-items:center}
.ev .t{font-size:12px;color:var(--dim);white-space:nowrap;font-variant-numeric:tabular-nums}
.ev .ti{font-weight:600;font-size:13.5px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;flex:1}
.ev.u .ti::before{content:"";display:inline-block;width:6px;height:6px;border-radius:50%;background:var(--sky);margin-right:6px;vertical-align:2px}
.ev .wh{font-size:12px;color:var(--muted-fg);margin-top:2px}
.ev .sm{font-size:13px;color:#e4e4e7;margin-top:2px}
.ev .dt{font-size:12px;color:var(--muted-fg);word-break:break-all}
.ev .an{font-size:12px;margin-top:4px;color:#d4d4d8}
.ev .an.w{color:var(--amber)}
.ev .rl{font-size:11px;color:var(--dim)}
.ws{display:inline-flex;align-items:center;height:18px;font-size:10.5px;font-weight:600;color:var(--amber);border:1px solid rgba(245,158,11,.35);border-radius:6px;padding:0 5px}
/* dialog */
#modal{position:fixed;inset:0;background:rgba(0,0,0,.65);backdrop-filter:blur(2px);display:none;align-items:flex-start;justify-content:center;z-index:50;overflow:auto;padding:48px 16px}
#modal.open{display:flex}
.dlg{background:var(--background);border:1px solid var(--border);border-radius:14px;width:min(880px,100%);padding:24px;box-shadow:0 25px 60px rgba(0,0,0,.7)}
.dlg h2{margin:0;font-size:18px;font-weight:600;letter-spacing:-.01em}
.dlg .desc{margin:4px 0 0;color:var(--muted-fg);font-size:13.5px}
.dlg h3{margin:22px 0 10px;padding-top:20px;border-top:1px solid var(--border);font-size:14px;font-weight:600}
.dlg .hint{color:var(--muted-fg);font-size:12.5px;margin:8px 0 0;line-height:1.7}
.dlg .hint b{color:var(--foreground);font-weight:600}
.rrow{display:grid;grid-template-columns:160px 1fr 110px auto auto auto;gap:8px;align-items:center;margin-bottom:8px}
.rrow input[type=text]{width:100%}
.rrow label{display:flex;gap:6px;align-items:center;font-size:13px;color:var(--muted-fg);white-space:nowrap}
.addrow{display:grid;grid-template-columns:1fr auto;gap:8px;margin-top:4px}
.addrow2{display:grid;grid-template-columns:minmax(0,1fr) 120px auto;gap:8px;margin-top:8px}
.grid2{display:grid;grid-template-columns:auto 1fr;gap:10px 14px;align-items:center;font-size:13.5px}
.grid2 input[type=number]{width:90px}
.checks{display:flex;flex-wrap:wrap;gap:10px 18px;font-size:13.5px}
.checks label,.lbl{display:flex;gap:8px;align-items:center;cursor:pointer}
textarea#ig,textarea#coi{width:100%;height:110px;font:12.5px var(--mono)}
textarea#coi{height:100px}
.foot{display:flex;justify-content:space-between;gap:8px;margin-top:24px;padding-top:16px;border-top:1px solid var(--border);align-items:center}
.err{color:var(--red);font-size:13px;white-space:pre-wrap;margin-top:10px}
#toast{position:fixed;right:16px;bottom:16px;background:var(--card);border:1px solid var(--border);border-radius:10px;padding:12px 16px;display:none;z-index:60;max-width:min(440px,80vw);font-size:13.5px;box-shadow:0 10px 30px rgba(0,0,0,.6)}
/* 会場オペレーターモード：コピー状況 */
.cp{display:inline-flex;align-items:center;gap:3px;height:19px;padding:0 6px;border-radius:6px;font-size:11px;font-weight:600;border:1px solid var(--border);color:var(--dim);white-space:nowrap}
.cp svg{width:11px;height:11px}
.cp-ok{color:var(--emerald);border-color:rgba(16,185,129,.35);background:rgba(16,185,129,.1)}
.cp-run{color:var(--amber);border-color:rgba(245,158,11,.35)}
.cp-run svg{animation:spin 1.1s linear infinite}
.cp-warn{color:var(--amber);border-color:rgba(245,158,11,.45);background:rgba(245,158,11,.1)}
.cp-bad{color:var(--red);border-color:rgba(239,68,68,.45);background:rgba(239,68,68,.1)}
#opbar{display:none;align-items:center;gap:8px 18px;padding:7px 16px;border-bottom:1px solid var(--border);font-size:12.5px;flex:none;flex-wrap:wrap;background:linear-gradient(90deg,rgba(139,92,246,.09),transparent 60%)}
#opbar .opt{display:inline-flex;align-items:center;gap:7px;font-weight:600;color:var(--violet);white-space:nowrap}
#opbar .opt b{color:var(--foreground);font-size:13px}
#opbar .od{display:inline-flex;align-items:center;gap:7px;white-space:nowrap;min-width:0;max-width:440px}
#opbar .od .l{font-weight:600}
#opbar .od .m{font:500 11.5px var(--mono);color:var(--muted-fg)}
#opbar .od .p{font:11px var(--mono);color:var(--dim);overflow:hidden;text-overflow:ellipsis;min-width:0}
#opbar .od.off .m{color:var(--red)}
#opbar .act{display:inline-flex;align-items:center;gap:7px;color:var(--amber);white-space:nowrap;min-width:0}
#opbar .act svg{width:13px;height:13px;animation:spin 1.1s linear infinite}
#opbar .act .bar{width:80px;height:5px;border-radius:999px;background:var(--accent);overflow:hidden;flex:none}
#opbar .act .bar i{display:block;height:100%;background:var(--amber)}
.dest{display:flex;gap:10px;align-items:center;flex-wrap:wrap}
.dest b{font-size:13.5px}
.dest .pathline{flex:1 1 100%;margin-top:2px}
.drow{display:grid;grid-template-columns:140px minmax(0,1fr) auto auto auto;gap:8px;align-items:center;margin-bottom:8px}
.drow input[type=text]{width:100%}
.drow label{display:flex;gap:6px;align-items:center;font-size:13px;color:var(--muted-fg);white-space:nowrap}
#opBox select{min-width:240px}
/* 差し替え・受信の進み具合 */
.t-repl,.k-repl{background:rgba(139,92,246,.15);color:#c4b5fd;border-color:rgba(139,92,246,.4)}
.rx{flex:1 1 100%;display:flex;align-items:center;gap:8px;min-width:0;font:500 11.5px var(--mono);color:var(--amber)}
.rx .rbar{flex:1 1 auto;max-width:180px;min-width:60px;height:6px;border-radius:999px;background:rgba(245,158,11,.15);overflow:hidden}
.rx .rbar i{display:block;height:100%;border-radius:999px;background:var(--amber)}
.rx .rbar.ind i{width:100%;background:repeating-linear-gradient(-45deg,rgba(251,191,36,.95) 0 7px,rgba(251,191,36,.35) 7px 14px);background-size:20px 20px;animation:stripe .8s linear infinite}
.rx .rt{white-space:nowrap;overflow:hidden;text-overflow:ellipsis;min-width:0}
.bp .rx .rbar{flex:0 0 56px;min-width:0}
.rx.op{color:#c4b5fd}.rx.op .rbar{background:rgba(139,92,246,.18)}.rx.op .rbar i{background:var(--violet)}
@keyframes stripe{to{background-position:20px 0}}
.vfmt{display:block;margin-top:3px;font-size:12px;color:var(--muted-fg)}
.vfmt b{font-weight:600}
/* 表示切替（リスト / 会場ボード） */
.seg{display:inline-flex;border:1px solid var(--border);border-radius:var(--radius);overflow:hidden;flex:none;box-shadow:0 1px 2px rgba(0,0,0,.25)}
.seg button{height:30px;border:0;border-radius:0;box-shadow:none;background:transparent;color:var(--muted-fg);padding:0 12px;font-size:12.5px}
.seg button+button{border-left:1px solid var(--border)}
.seg button:hover{background:var(--muted);color:var(--foreground)}
.seg button[aria-selected=true]{background:var(--accent);color:var(--foreground)}
.seg button svg{width:15px;height:15px}
@media (max-width:1280px){.seg button .lb{display:none}.seg button{padding:0 10px}}
/* 会場ボード */
#boardpane{display:none}
#dhead{display:none}
main.vboard{grid-template-columns:minmax(0,1fr)}
main.vboard #left,main.vboard #logpane{display:none}
main.vboard #boardpane{display:flex}
main.vboard.showlog #logpane{display:flex;position:fixed;right:0;top:0;bottom:0;width:360px;z-index:35;background:var(--background);border-left:1px solid var(--border);box-shadow:-20px 0 40px rgba(0,0,0,.6)}
main.vboard #center{position:fixed;top:0;right:0;bottom:0;width:min(820px,94vw);z-index:30;background:var(--background);border-left:1px solid var(--border);box-shadow:-24px 0 48px rgba(0,0,0,.65);transform:translateX(104%);transition:transform .18s ease-out;visibility:hidden}
main.vboard.drawer #center{transform:none;visibility:visible}
main.vboard #dhead{display:flex;align-items:center;gap:8px;padding:8px 12px;border-bottom:1px solid var(--border);flex:none;font-size:12.5px;color:var(--muted-fg)}
#dhead .t{flex:1;min-width:0}
body.vboard #bLog{display:inline-flex}
.bbar{display:flex;align-items:center;gap:8px 16px;padding:10px 16px;border-bottom:1px solid var(--border);font-size:13px;color:var(--muted-fg);flex:none;flex-wrap:wrap}
.bbar b{color:var(--foreground);font-weight:600}
.bbar .prog .bar{width:72px}
.bbar .st{display:inline-flex;align-items:center;gap:6px;white-space:nowrap}
.bbar .st.scp b{color:var(--amber)}.bbar .st.sun b{color:var(--sky)}
.bbar .flt{display:flex;align-items:center;gap:8px 14px;flex-wrap:wrap;margin-left:auto}
.bbar .flt label{display:flex;gap:7px;align-items:center;cursor:pointer;white-space:nowrap}
.bbar .search{flex:none;width:210px}
.bbar .search input{height:30px;font-size:12.5px}
.bbar .search svg{top:7px}
.bbar select{height:30px;font-size:12.5px;max-width:220px}
.bleg{display:flex;gap:14px;align-items:center;padding:7px 16px 0;font-size:12px;color:var(--muted-fg);flex:none;flex-wrap:wrap}
.bleg span{display:inline-flex;gap:6px;align-items:center;white-space:nowrap}
.bleg .sw{width:10px;height:10px;border-radius:3px;display:inline-block}
.board{flex:1;display:grid;grid-auto-flow:column;grid-auto-columns:minmax(270px,460px);gap:12px;padding:10px 16px 16px;overflow-x:auto;overflow-y:hidden;min-height:0;align-items:stretch}
.board>.empty{grid-column:1/-1}
main.vboard.drawer .board{padding-right:calc(min(820px,94vw) + 16px)}
.col{display:flex;flex-direction:column;min-height:0;border:1px solid var(--border);border-radius:12px;background:#0c0c0e;overflow:hidden}
.col .vh{padding:11px 14px 10px;border-top:3px solid var(--vc);background:color-mix(in srgb,var(--vc) 8%,transparent);border-bottom:1px solid var(--border);flex:none}
.col .vh .n{display:flex;align-items:center;gap:8px;font-size:16px;font-weight:700;letter-spacing:-.01em;min-width:0}
.col .vh .n .vn{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.col .vh .n svg{width:16px;height:16px;color:var(--vc);flex:none}
.col .vh .rl{font-size:11px;color:var(--dim);font-weight:500;margin-top:1px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.col .vh .s{display:flex;gap:10px;align-items:center;margin-top:6px;font-size:12px;color:var(--muted-fg);flex-wrap:wrap}
.col .vh .s .prog .bar{width:64px}
.col .vh .s .cpg{color:var(--amber);display:inline-flex;align-items:center;gap:5px}
.col .vh .s .cpg svg{width:13px;height:13px;animation:spin 1.1s linear infinite}
.col .vh .s .uc{color:var(--sky);font-weight:500}
.col .list{overflow:auto;padding:4px 8px 10px;flex:1;min-height:0}
.col .list .empty{padding:24px 12px;font-size:12.5px}
.col .ses{display:flex;align-items:center;gap:8px;margin:14px 0 5px;padding:8px 10px;font-size:14.5px;font-weight:700;letter-spacing:-.01em;color:var(--foreground);min-width:0;position:sticky;top:-4px;z-index:1;background:color-mix(in srgb,var(--vc) 17%,#0c0c0e);border:1px solid color-mix(in srgb,var(--vc) 45%,#0c0c0e);border-radius:8px;box-shadow:0 2px 6px rgba(0,0,0,.45)}
.col .list>.ses:first-child{margin-top:6px}
.col .ses{cursor:pointer;user-select:none;flex-wrap:wrap;row-gap:4px}
/* セッションの時刻と進行状況 */
.tl{flex:1 1 100%;display:flex;align-items:center;gap:6px;flex-wrap:wrap;min-width:0;padding-left:22px;font-weight:500}
.shead .tl{padding-left:21px}
.stime{font:600 11.5px var(--mono);color:#e4e4e7;background:rgba(255,255,255,.07);border:1px solid rgba(255,255,255,.12);border-radius:5px;padding:0 6px;height:19px;display:inline-flex;align-items:center}
.sst{font-size:11.5px;font-weight:600;white-space:nowrap}
.sst.done{color:var(--dim)}
.sst.live{color:var(--emerald)}
.sst.live::before{content:"";display:inline-block;width:7px;height:7px;border-radius:50%;background:var(--emerald);margin-right:5px;vertical-align:1px;animation:pulse 1.2s infinite}
.sst.next{color:var(--muted-fg)}
.sst.next.soon{color:var(--amber)}
.sw-un{font-size:11px;font-weight:700;color:#fff;background:rgba(239,68,68,.85);border-radius:5px;padding:0 6px;height:18px;display:inline-flex;align-items:center}
.tbar{flex:1 1 100%;height:4px;border-radius:999px;background:rgba(0,0,0,.35);overflow:hidden;margin:0 0 0 22px}
.tbar i{display:block;height:100%;background:var(--emerald)}
.col .ses.st-done{opacity:.55}
.col .ses.st-done:hover{opacity:.8}
.col .ses.st-live{box-shadow:0 0 0 2px var(--emerald),0 2px 6px rgba(0,0,0,.45)}
.shead{flex-wrap:wrap;row-gap:3px}
.shead.st-done{opacity:.55}
.shead.st-live{background:rgba(16,185,129,.08)}
.dsep{display:flex;align-items:center;gap:8px;margin:14px 2px 2px;font-size:12px;font-weight:700;color:var(--muted-fg);letter-spacing:.04em}
.dsep::after{content:"";flex:1;height:1px;background:var(--border)}
.dsep span{font-size:10.5px;color:#082f49;background:var(--sky);border-radius:999px;padding:0 6px}
.dsep.today{color:var(--foreground)}
.col .list>.dsep:first-child{margin-top:6px}
.dchip{font-size:11px;font-weight:600;color:var(--sky);border:1px solid rgba(56,189,248,.35);border-radius:5px;padding:0 5px;margin-right:6px}
.nowl{display:flex;align-items:center;gap:7px;margin-top:6px;font-size:12px;color:var(--muted-fg);min-width:0}
.nowl b{font-weight:700;color:var(--foreground);flex:none}
.nowl.live b{color:var(--emerald)}
.nowl .nn{color:#e4e4e7;font-weight:600;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;min-width:0}
.nowl .nr{font:500 11.5px var(--mono);white-space:nowrap;flex:none}
.nowl.done b{color:var(--dim);font-weight:500}
.bp,.grp{user-select:none}
/* 会場取得済（「取得済」の目印） */
.bp.st-got{background:rgba(56,189,248,.09);box-shadow:inset 3px 0 0 var(--sky)}
.bp.st-got:hover{background:rgba(56,189,248,.14)}
.bp.st-got .sti{color:var(--sky)}
.grp.st-got{background:rgba(56,189,248,.07);box-shadow:inset 3px 0 0 var(--sky)}
.grp.st-got .sti{color:var(--sky)}
.rtag.got{background:rgba(56,189,248,.12);color:var(--sky);border:1px solid rgba(56,189,248,.3)}
/* 現場の目印（発表終了・取り下げ・会場直・動画有 など） */
.ana details.vok{margin-top:4px}
.ana details.vok summary{cursor:pointer;color:var(--muted-fg);font-size:12.5px;padding:3px 0;user-select:none}
.ana details.vok summary:hover{color:var(--foreground)}
.rtag.done{background:var(--muted);color:#d4d4d8;border:1px solid var(--border)}
.rtag.drop{background:rgba(239,68,68,.1);color:#fca5a5;border:1px solid rgba(239,68,68,.3)}
.rtag.direct{background:rgba(139,92,246,.12);color:var(--violet);border:1px solid rgba(139,92,246,.35)}
.fl{display:inline-flex;align-items:center;height:19px;padding:0 6px;border-radius:6px;font-size:10.5px;font-weight:600;white-space:nowrap;border:1px solid var(--border);color:#d4d4d8;background:rgba(255,255,255,.04);line-height:1}
.fl-warn{color:var(--amber);border-color:rgba(245,158,11,.5);background:rgba(245,158,11,.13)}
.fl-direct{color:var(--violet);border-color:rgba(139,92,246,.5);background:rgba(139,92,246,.13)}
.fl-more{color:var(--muted-fg)}
.facts .fl{height:22px;font-size:11.5px;padding:0 8px}
.t-drop{background:rgba(239,68,68,.1);color:#fca5a5;border-color:rgba(239,68,68,.3)}
.t-done{background:var(--muted);color:#d4d4d8;border-color:var(--border)}
.t-direct{background:rgba(139,92,246,.12);color:var(--violet);border-color:rgba(139,92,246,.35)}
.bp.st-done,.grp.st-done{opacity:.55}
.bp.st-done .sti,.grp.st-done .sti{color:var(--muted-fg)}
.bp.st-drop,.grp.st-drop{opacity:.6}
.bp.st-drop .nm,.grp.st-drop .nm{text-decoration:line-through;color:var(--muted-fg)}
.bp.st-drop .sti,.grp.st-drop .sti{color:var(--red)}
.bp.st-direct,.grp.st-direct{background:rgba(139,92,246,.08);box-shadow:inset 3px 0 0 var(--violet)}
.bp.st-direct .sti,.grp.st-direct .sti{color:var(--violet)}
.bp.st-done:hover,.bp.st-drop:hover,.grp.st-done:hover,.grp.st-drop:hover{opacity:.9}
.mkt{width:100%;border-collapse:collapse;margin-top:4px}
.mkt td{padding:2px 4px 2px 0}
.mkt input[type=text],.mkt select{height:30px;font-size:13px}
tr.mkrow td{color:var(--muted-fg)}
.mkt input{width:100%}
.mkt select{width:100%}
.mkt td:last-child{width:34px}
.mkt .x{width:30px;height:30px;padding:0}
.t-got{background:rgba(56,189,248,.12);color:var(--sky);border-color:rgba(56,189,248,.3)}
.gotc{font:500 11.5px var(--mono);color:var(--sky);white-space:nowrap}
.gotc.done{font-weight:700}
.dhint{font-size:12px;color:var(--amber);white-space:nowrap}
.col .ses:hover{background:color-mix(in srgb,var(--vc) 24%,#0c0c0e)}
.col .ses:focus-visible{outline:2px solid var(--ring);outline-offset:1px}
.col .ses .chev{color:var(--muted-fg);margin-left:-2px}
.col .ses .chev svg{width:16px;height:16px}
.col .ses.fold{margin-bottom:2px;opacity:.92}
.col .ses.fold .sn{color:#d4d4d8}
.col .ses .badge{font-size:10.5px}
.col .vh .n .cf{width:26px;height:26px;padding:0;color:var(--muted-fg);flex:none;margin-left:2px}
.col .vh .n .cf:hover{color:var(--foreground)}
.col .vh .n .cf svg{width:15px;height:15px;color:inherit}
/* 会場ナビ（会場が画面に入りきらないときだけ出す） */
.bnav{display:none;align-items:center;gap:6px;padding:8px 16px 0;flex:none;min-width:0}
.bnav.on{display:flex}
.bnav .nv{width:30px;height:30px;padding:0;flex:none}
.bnav .nv svg{width:16px;height:16px}
.bnav .chips{display:flex;gap:6px;overflow-x:auto;min-width:0;flex:1;scrollbar-width:none}
.bnav .chips::-webkit-scrollbar{display:none}
.vchip{display:inline-flex;align-items:center;gap:6px;height:28px;padding:0 10px;border-radius:999px;border:1px solid var(--border);background:transparent;box-shadow:none;font-size:12.5px;font-weight:600;color:var(--muted-fg);flex:none;white-space:nowrap}
.vchip i{width:8px;height:8px;border-radius:3px;background:var(--vc);flex:none}
.vchip .c{font:500 11px var(--mono);color:var(--dim)}
.vchip .c.done{color:var(--emerald)}
.vchip .badge{height:16px;min-width:16px;font-size:10px;padding:0 5px}
.vchip.vis{color:var(--foreground);border-color:color-mix(in srgb,var(--vc) 55%,var(--border));background:color-mix(in srgb,var(--vc) 12%,transparent)}
.board::-webkit-scrollbar{height:14px}
.board::-webkit-scrollbar-thumb{background:#3f3f46;border:3px solid var(--background);border-radius:999px}
.board::-webkit-scrollbar-thumb:hover{background:#52525b}
.bbar .fb{height:30px;padding:0 10px;font-size:12.5px;color:var(--muted-fg)}
.bbar .fb:hover{color:var(--foreground)}
.col .ses .sn{flex:1;min-width:0;overflow:hidden;white-space:normal;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;line-height:1.3;word-break:break-all}
.col .ses .sep{color:var(--muted-fg);font-weight:500}
.col .ses .prog{font-size:12px;color:#d4d4d8}
.col .ses .prog.done{color:var(--emerald)}
.col .ses .prog .bar{width:28px;background:rgba(0,0,0,.35)}
.col .ses .prog{gap:4px}
.col .list .bp{margin-left:6px}
.bp{display:flex;align-items:center;flex-wrap:wrap;gap:4px 8px;padding:7px 9px;border-radius:8px;margin:2px 0;font-size:13px;cursor:pointer;position:relative;transition:background .12s;scroll-margin:40px 0}
.bp:hover{background:var(--muted)}
.bp .sti{display:inline-grid;place-items:center;flex:none}
.bp .sti svg{width:16px;height:16px}
.bp .nm{flex:1 1 7.5em;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:500}
.bp .tg{display:flex;flex-wrap:wrap;gap:4px;flex:0 1 auto;min-width:0}
.bp .tg .tag{height:19px;font-size:10.5px;padding:0 6px;font-weight:600}
.bp .tg .cp{height:19px}
.bp.st-recv{background:rgba(16,185,129,.09);box-shadow:inset 3px 0 0 var(--emerald)}
.bp.st-recv:hover{background:rgba(16,185,129,.14)}
.bp.st-recv .sti{color:var(--emerald)}
.bp.st-none{color:var(--muted-fg)}
.bp.st-none .nm{font-weight:400}
.bp.st-none .sti{color:#52525b}
.bp.st-copying{background:rgba(245,158,11,.09);box-shadow:inset 3px 0 0 var(--amber)}
.bp.st-copying .sti{color:var(--amber)}
.bp.st-copying .sti svg{animation:spin 1.1s linear infinite}
.bp.unread{outline:1px solid rgba(56,189,248,.6);outline-offset:-1px}
.bp.unread .nm{font-weight:600}
.bp.sel{outline:2px solid #e4e4e7;outline-offset:-2px}
.bp.flash{animation:flashbg 2.5s ease-out}
.bp:focus-visible{outline:2px solid var(--ring);outline-offset:-2px}
@media (max-width:1180px){.bbar .flt{margin-left:0}}
@media (max-width:760px){.rrow{grid-template-columns:1fr 1fr}.rrow .pth{grid-column:1/-1}.addrow2{grid-template-columns:1fr}.drow{grid-template-columns:1fr 1fr}.drow .pth{grid-column:1/-1}}
</style>
</head>
<body>
<header>
  <div class="logo"><span class="mark"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round"><circle cx="12" cy="12" r="8"/><circle cx="12" cy="12" r="2.5" fill="currentColor" stroke="none"/></svg></span><span>PADDOCK SCOUT<small>SEVENTHWELL · READ ONLY</small></span></div>
  <div id="roots"></div>
  <span id="conn">再接続中…</span>
  <div class="seg" role="tablist" aria-label="表示の切り替え"><button type="button" role="tab" id="vList" data-view="list" title="会場・セッション・演者の一覧と、フォルダの中身"></button><button type="button" role="tab" id="vBoard" data-view="board" title="全会場を横に並べて受付状況を一覧"></button></div>
  <div class="hbtns">
    <label class="switch" title="更新があったフォルダを自動で表示（操作中の15秒間は切り替えない）"><input type="checkbox" id="swFollow"><span class="track"><span class="thumb"></span></span>自動表示</label>
    <span class="vsep"></span>
    <button id="bLog" class="ghost"></button>
    <button id="bTest" class="ghost" title="デスクトップ通知が出るか確認"></button>
    <button id="bAll" class="ghost"></button>
    <button id="bCfg"></button>
    <button id="bQuit" class="ghost" title="アプリを終了">終了</button>
  </div>
</header>
<div id="opbar"></div>
<div id="banner"></div>
<main id="main">
  <section id="left">
    <div class="ph"><div class="search"><span id="qi"></span><input id="q" type="text" placeholder="演者・セッションを検索" autocomplete="off"></div></div>
    <div class="tools">
      <select id="venue" title="この会場だけ表示・通知"></select>
      <select id="lday" title="表示する日（日ごとのフォルダがあるとき）" style="display:none"></select>
      <label><input type="checkbox" id="onlyU">未確認のみ</label>
      <label><input type="checkbox" id="onlyN">未受付のみ</label>
      <span style="flex:1"></span>
      <select id="sort"><option value="name">会場・セッション順</option><option value="recent">変更が新しい順</option><option value="unread">未確認を上に</option></select>
    </div>
    <div class="scroll" id="groups"></div>
  </section>
  <section id="boardpane">
    <div class="bbar">
      <span class="st" id="bTot"></span>
      <span class="st scp" id="bCp"></span>
      <span class="st sun" id="bUn"></span>
      <div class="flt">
        <span style="display:inline-flex;gap:2px"><button class="ghost fb" id="bOpenAll" title="すべてのセッションを開く"></button><button class="ghost fb" id="bCloseAll" title="すべてのセッションを閉じる（演者を隠してコンパクトに）"></button></span>
        <div class="search"><span id="bqi"></span><input id="bq" type="text" placeholder="演者・セッションを検索" autocomplete="off"></div>
        <select id="bday" title="表示する日。day1などの名前のときは、選んだ日を「今日」として進行状況を出します（翌日になると自動で次の日へ）" style="display:none"></select>
        <span id="bdayhint" class="dhint" style="display:none">← 今日の日を選ぶと進行状況が出ます</span>
        <select id="bvenue" title="この会場だけ表示・通知"></select>
        <label><input type="checkbox" id="bOnlyU">未確認のみ</label>
        <label><input type="checkbox" id="bOnlyN">未受付のみ</label>
      </div>
    </div>
    <div class="bleg"><span><i class="sw" style="background:var(--emerald)"></i>受付済み</span><span><i class="sw" style="background:var(--sky)"></i>会場取得済</span><span><i class="sw" style="background:var(--amber)"></i>コピー中</span><span><i class="sw" style="border:1.5px dashed #52525b"></i>未受付</span><span><i class="sw" style="background:var(--violet)"></i>会場直</span><span style="opacity:.6"><i class="sw" style="background:#71717a"></i>発表終了</span><span style="opacity:.7;text-decoration:line-through">取り下げ</span><span><i class="sw" style="outline:1px solid var(--sky);outline-offset:-1px"></i>未確認（新着）</span><span style="color:var(--dim)">演者をクリックすると中身と解析結果を表示</span></div>
    <div class="bnav" id="bnav"><button class="ghost nv" id="bPrev" title="前の会場へ（←キー）"></button><div class="chips" id="bchips"></div><button class="ghost nv" id="bNext" title="次の会場へ（→キー）"></button></div>
    <div class="board" id="board"></div>
  </section>
  <section id="center"><div id="dhead"><span class="t">フォルダの中身</span><button class="ghost" id="bDClose" title="閉じる（Esc）"></button></div><div class="scroll" id="fold"></div></section>
  <section id="logpane">
    <div class="ph" style="border-bottom:1px solid var(--border)"><h2>変更ログ</h2><button class="ghost" id="bLogClose" style="display:none">閉じる</button></div>
    <div class="scroll" id="log"></div>
  </section>
</main>
<div id="modal"></div>
<div id="toast"></div>
<script>
"use strict";
const TOKEN="__TOKEN__";
const APPKIND="__APPKIND__";        /* watch / reception / operator */
const SV=(d)=>`<svg class="i" viewBox="0 0 24 24">${d}</svg>`;
const IC={
 search:SV('<circle cx="11" cy="11" r="7"/><path d="m20 20-3.5-3.5"/>'),
 bell:SV('<path d="M6 8a6 6 0 0 1 12 0c0 7 3 9 3 9H3s3-2 3-9"/><path d="M10.3 21a1.94 1.94 0 0 0 3.4 0"/>'),
 check2:SV('<path d="M18 6 7 17l-5-5"/><path d="m22 10-7.5 7.5L13 16"/>'),
 cog:SV('<path d="M20 7h-9"/><path d="M14 17H5"/><circle cx="17" cy="17" r="3"/><circle cx="7" cy="7" r="3"/>'),
 cols:SV('<rect width="18" height="18" x="3" y="3" rx="2"/><path d="M9 3v18"/><path d="M15 3v18"/>'),
 list:SV('<path d="M8 6h13"/><path d="M8 12h13"/><path d="M8 18h13"/><path d="M3 6h.01"/><path d="M3 12h.01"/><path d="M3 18h.01"/>'),
 folder:SV('<path d="M20 20a2 2 0 0 0 2-2V8a2 2 0 0 0-2-2h-7.9a2 2 0 0 1-1.69-.9L9.6 3.9A2 2 0 0 0 7.93 3H4a2 2 0 0 0-2 2v13a2 2 0 0 0 2 2Z"/>'),
 ext:SV('<path d="M15 3h6v6"/><path d="M10 14 21 3"/><path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"/>'),
 copy:SV('<rect x="8" y="8" width="14" height="14" rx="2"/><path d="M4 16c-1.1 0-2-.9-2-2V4c0-1.1.9-2 2-2h10c1.1 0 2 .9 2 2"/>'),
 chev:SV('<path d="m9 18 6-6-6-6"/>'),
 chevL:SV('<path d="m15 18-6-6 6-6"/>'),
 alert:SV('<path d="m21.73 18-8-14a2 2 0 0 0-3.48 0l-8 14A2 2 0 0 0 4 21h16a2 2 0 0 0 1.73-3"/><path d="M12 9v4"/><path d="M12 17h.01"/>'),
 info:SV('<circle cx="12" cy="12" r="10"/><path d="M12 16v-4"/><path d="M12 8h.01"/>'),
 inbox:SV('<path d="M22 12h-6l-2 3h-4l-2-3H2"/><path d="M5.45 5.11 2 12v6a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2v-6l-3.45-6.89A2 2 0 0 0 16.76 4H7.24a2 2 0 0 0-1.79 1.11z"/>'),
 file:SV('<path d="M15 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V7Z"/><path d="M14 2v4a2 2 0 0 0 2 2h4"/>'),
 plus:SV('<path d="M5 12h14"/><path d="M12 5v14"/>'),
 x:SV('<path d="M18 6 6 18"/><path d="m6 6 12 12"/>'),
 building:SV('<path d="M6 22V4a2 2 0 0 1 2-2h8a2 2 0 0 1 2 2v18Z"/><path d="M6 12H4a2 2 0 0 0-2 2v6a2 2 0 0 0 2 2h2"/><path d="M18 9h2a2 2 0 0 1 2 2v9a2 2 0 0 1-2 2h-2"/><path d="M10 6h4"/><path d="M10 10h4"/><path d="M10 14h4"/><path d="M10 18h4"/>'),
 down:SV('<path d="m6 9 6 6 6-6"/>'),
 ok:SV('<circle cx="12" cy="12" r="10"/><path d="m9 12 2 2 4-4"/>'),
 todo:SV('<circle cx="12" cy="12" r="10" stroke-dasharray="3.2 3"/>'),
 spin:SV('<path d="M21 12a9 9 0 1 1-6.22-8.56"/>'),
 expand:SV('<path d="m7 15 5 5 5-5"/><path d="m7 9 5-5 5 5"/>'),
 collapse:SV('<path d="m7 20 5-5 5 5"/><path d="m7 4 5 5 5-5"/>'),
 chk:SV('<path d="M20 6 9 17l-5-5"/>'),
 flag:SV('<path d="M4 15s1-1 4-1 5 2 8 2 4-1 4-1V3s-1 1-4 1-5-2-8-2-4 1-4 1z"/><path d="M4 22v-7"/>'),
 ban:SV('<circle cx="12" cy="12" r="10"/><path d="m4.9 4.9 14.2 14.2"/>'),
 direct:SV('<path d="M15 3h4a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2h-4"/><path d="m10 17 5-5-5-5"/><path d="M15 12H3"/>'),
 hd:SV('<path d="M22 12H2"/><path d="M5.45 5.11 2 12v6a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2v-6l-3.45-6.89A2 2 0 0 0 16.76 4H7.24a2 2 0 0 0-1.79 1.11z"/><path d="M6 16h.01"/><path d="M10 16h.01"/>'),
};
const KIND={incoming:["受信中","mod"],folder_new:["新規フォルダ","acc"],add:["追加","add"],mod:["更新","mod"],rename:["名前変更","ren"],del:["削除","del"],folder_rename:["フォルダ名変更","ren"],folder_del:["フォルダ削除","del"],offline:["接続断","del"],online:["復帰","add"],copied:["コピー完了","add"],copy_err:["コピー要確認","del"]};
const OPS={add:["＋","add","追加"],mod:["✎","mod","更新"],rename:["↔","ren","名前変更"],del:["−","del","削除"],dir_add:["＋","add","フォルダ追加"],dir_del:["−","del","フォルダ削除"],folder_rename:["↔","ren","フォルダ名変更"],copy:["⇢","add","コピー"]};
/* コピー状況（会場オペレーターモード） */
const CPL={ok:["コピー済み","ok"],todo:["コピー待ち","dim"],copying:["コピー中","run"],wait:["受信完了待ち","dim"],srcbusy:["NAS側で使用中","warn"],busy:["差し替え待ち","warn"],edited:["コピー先で変更あり","warn"],err:["エラー","bad"],off:["接続できません","bad"]};
const MKC={recv:"t-ok",got:"t-got",done:"t-done",drop:"t-drop",direct:"t-direct",warn:"t-warn",info:"t-dim"};
const MKR={recv:"受付済",got:"会場取得済",done:"発表終了",drop:"演題取り下げ",direct:"会場直",warn:"注意",info:"表示だけ"};
const OPON=()=>!!(S&&S.op&&S.op.enabled);
const opDests=()=>OPON()?S.op.dests.filter(d=>d.enabled):[];
function cpPill(label,st,msg){const x=CPL[st]||[st,"dim"];const ic=st==="ok"?IC.chk:st==="copying"?IC.spin:"";
  return `<span class="cp cp-${x[1]}" title="${esc(label)}: ${esc(x[0])}${msg?" — "+esc(msg):""}">${ic}${esc(label)}</span>`}
const ST={add:["追加","add"],mod:["更新","mod"],ren:["名前変更","ren"],pending:["コピー中…","mod"]};
const $=s=>document.querySelector(s);
const esc=s=>String(s==null?"":s).replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const nfc=s=>{try{return String(s==null?"":s).normalize("NFC")}catch(e){return String(s)}};
const ls={get(k,d){try{const v=localStorage.getItem("swnw."+k);return v==null?d:JSON.parse(v)}catch(e){return d}},set(k,v){try{localStorage.setItem("swnw."+k,JSON.stringify(v))}catch(e){}}};
function fmtSize(n){if(n==null)return"";const u=["B","KB","MB","GB","TB"];let i=0;while(n>=1024&&i<u.length-1){n/=1024;i++}return(i?n.toFixed(n<10?1:0):n)+" "+u[i]}
function p2(n){return String(n).padStart(2,"0")}
function hms(t){const d=new Date(t*1000);return p2(d.getHours())+":"+p2(d.getMinutes())+":"+p2(d.getSeconds())}
function dtm(t){const d=new Date(t*1000),n=new Date();const day=(d.toDateString()===n.toDateString())?"":(d.getMonth()+1)+"/"+d.getDate()+" ";return day+p2(d.getHours())+":"+p2(d.getMinutes())}
function ago(t){const s=Math.max(0,Date.now()/1000-t);if(s<60)return Math.floor(s)+"秒前";if(s<3600)return Math.floor(s/60)+"分前";if(s<86400)return Math.floor(s/3600)+"時間前";return Math.floor(s/86400)+"日前"}
function kindPill(k){const x=KIND[k]||[k,"acc"];return `<span class="kind k-${x[1]}">${esc(x[0])}</span>`}
function toast(msg,ms){const t=$("#toast");t.textContent=msg;t.style.display="block";clearTimeout(toast._t);toast._t=setTimeout(()=>t.style.display="none",ms||3200)}
/* 並べ替え用の読み替え：①〜⑳・㉑〜㊿・⑴・⒈・全角数字などは NFKC で数字に、❶➀➊⓫⓵ など NFKC で変わらない丸数字も数字に直してから
   「数字は数値として」比べる（そのままだと ⑩ が「1」「0」扱いになり ① の直後に来てしまう） */
const DINGNUM=(()=>{const m={};const put=(from,n0,cnt)=>{for(let i=0;i<cnt;i++)m[String.fromCharCode(from+i)]=String(n0+i)};
  put(0x2776,1,10);put(0x2780,1,10);put(0x278A,1,10);put(0x24EB,11,10);put(0x24F5,1,10);put(0x24FF,0,1);return m})();
const SKC=new Map();
function nameKey(s){s=String(s==null?"":s);let k=SKC.get(s);if(k!==undefined)return k;
  try{k=s.normalize("NFKC")}catch(e){k=s}
  k=k.replace(/[❶-➓⓫-⓿]/g,c=>DINGNUM[c]!==undefined?DINGNUM[c]:c);
  if(SKC.size>20000)SKC.clear();SKC.set(s,k);return k}
const COLL=new Intl.Collator("ja",{numeric:true,sensitivity:"base"});
const cmpName=(a,b)=>COLL.compare(nameKey(a),nameKey(b))||(nfc(a)<nfc(b)?-1:nfc(a)>nfc(b)?1:0);
function cmpPath(a,b){const x=a.split("/"),y=b.split("/");for(let i=0;i<Math.min(x.length,y.length);i++){const c=cmpName(x[i],y[i]);if(c)return c}return x.length-y.length}
const whereText=w=>nfc(w).split("/").join(" › ");
function sl(arr){const a=[...new Set(arr)].sort((x,y)=>x-y);const out=[];for(let i=0;i<a.length;){let j=i;while(j+1<a.length&&a[j+1]===a[j]+1)j++;out.push(i===j?a[i]+"枚目":a[i]+"〜"+a[j]+"枚目");i=j+1}return out.join("、")}

async function api(path,body){
  const o=body===undefined?{cache:"no-store"}:{method:"POST",headers:{"Content-Type":"application/json","X-SW-Token":TOKEN},body:JSON.stringify(body)};
  const r=await fetch(path,o);let j={};try{j=await r.json()}catch(e){}
  if(r.status===403&&j.error==="token"){location.reload();throw new Error("reload")}
  if(!r.ok)throw new Error(j.error||("HTTP "+r.status));return j}

let S=null,SEL=ls.get("sel",null),F=null,lastId=0,ready=false,lastVer=-1,boot=null,liveUnread=0;
let VENUE=ls.get("venue",""),FOLLOW=ls.get("follow",true),lastInteract=0;
["pointerdown","keydown","wheel"].forEach(t=>document.addEventListener(t,()=>{lastInteract=Date.now()},{passive:true,capture:true}));
function rootById(id){return S&&S.roots.find(r=>r.id===id)}
function effVenue(){return OPON()?S.op.root+"|"+(S.op.venue||""):VENUE}
function inVenue(root,group){const V=effVenue();if(!V)return true;const i=V.indexOf("|");if(root!==V.slice(0,i))return false;if(group==null||group===""||!V.slice(i+1))return true;
  if(OPON()&&S.op.venue&&root===S.op.root)return (group+"/").startsWith(S.op.venue+"/");   // 会場オペレーターモードはNASの最上位フォルダ単位
  const r=rootById(root);return r?fuOf(r,group)===V.slice(i+1):group.split("/")[0]===V.slice(i+1)}

async function loadState(){
  const st=await api("/api/state");
  if(S&&st.boot===S.boot&&st.ver<S.ver)return;   // 遅れて届いた古い状態で上書きしない
  S=st;updateRates();
  ANYGOT=S.roots.some(r=>(r.groups||[]).some(g=>g.mk_got||g.mk_done));
  if(!ready){ready=true;lastId=S.last_event_id;boot=S.boot;connect();}
  renderAll();
  if(SEL&&!rootById(SEL.root)){SEL=null;ls.set("sel",null);renderFolderEmpty();return}
  if(SEL)loadFolder(false);else renderFolderEmpty();
}
let rT=null;function refresh(){clearTimeout(rT);rT=setTimeout(()=>loadState().catch(e=>console.warn(e)),200)}

let es=null;
function connect(){
  es=new EventSource("/api/stream?since="+lastId);
  es.addEventListener("ev",e=>{const ev=JSON.parse(e.data);lastId=Math.max(lastId,ev.id);onEvent(ev)});
  es.addEventListener("incoming",e=>onIncoming(JSON.parse(e.data)));
  es.addEventListener("status",e=>{const st=JSON.parse(e.data);if(boot&&st.boot!==boot){location.reload();return}
    $("#conn").style.display="none";applyStatus(st);if(st.ver!==lastVer){lastVer=st.ver;refresh()}});
  es.onerror=()=>{$("#conn").style.display="inline"};
}
function onIncoming(x){
  if(!S||!inVenue(x.root,x.group))return;
  if(S.notify.incoming!==false)queueN("inc",x);
  maybeFollow(x);flashRow(x);refresh();
}
function onEvent(ev){
  if(!S)return;
  if(!S.events.some(e=>e.id===ev.id)){S.events.push(ev);if(S.events.length>400)S.events.shift()}
  const live=ev.ts>Date.now()/1000-120;
  if(live&&inVenue(ev.root,ev.group)){
    if(wantNotify(ev))queueN("ev",ev);
    maybeFollow(ev);flashRow(ev);
    if(ev.group!=null&&(document.hidden||!document.hasFocus())){liveUnread++;flashTitle()}
  }
  refresh();
}
function wantNotify(ev){const ks=ev.kinds&&ev.kinds.length?ev.kinds:[ev.kind];return ks.some(k=>S.notify[k]!==false)}
function maybeFollow(x){
  if(!FOLLOW||x.group==null||Date.now()-lastInteract<15000)return;
  /* 会場ボード：中身の表示（右パネル）を開いていなければ、その演者までスクロールするだけ */
  if(VIEW==="board"){followKey=x.root+"|"+x.group;if(!drawerOpen())return}
  if(SEL&&SEL.root===x.root&&SEL.group===x.group)return;
  selectGroup(x.root,x.group,true);
}
let flashKeys=new Set();
function flashRow(x){if(x.group!=null){flashKeys.add(x.root+"|"+x.group);setTimeout(()=>flashKeys.delete(x.root+"|"+x.group),2600)}}

/* ---------- notifications ---------- */
const nQ=[],lastInc={};let nT=null,AC=null;
const tagOf=x=>"sw-"+x.root+"|"+(x.group==null?"#":x.group);
const anaWarn=x=>(x.ana||[]).some(a=>a.warn);
function queueN(kind,x){
  const tag=tagOf(x);let sound=true,re=true;
  if(kind==="ev"&&x.kind==="copied"){sound=false;re=false}          /* 「追加」の通知をそのまま「コピー完了」に書き換える */
  else if(kind==="ev"&&x.kind==="copy_err"){sound=true;re=true}
  else if(kind==="ev"){const inc=lastInc[tag]&&Date.now()-lastInc[tag]<300000;delete lastInc[tag];
    if(inc){const w=anaWarn(x)||["del","folder_del","offline"].includes(x.kind);sound=w;re=w}}
  else lastInc[tag]=Date.now();
  nQ.push({kind,x,tag,sound,re});if(!nT)nT=setTimeout(flushN,450);
}
function bodyOf(x){
  const L=[];if(x.where)L.push(whereText(x.where));L.push(x.summary);if(x.detail)L.push(nfc(x.detail));
  (x.ana||[]).forEach(a=>L.push(nfc(a.file)+": "+(a.text||a.na||"解析中…")));
  if(S.roots.length>1||x.group==null)L.push("["+nfc(x.root_label)+"]");return L.join("\n");
}
function flushN(){
  nT=null;const L=nQ.splice(0);if(!L.length)return;
  if(OPON())return;   // 会場オペレーターモード：このPCでスライドショーをしているので、通知も音も出さない
  const snd=L.filter(i=>i.sound);
  if(snd.length)chime(snd.some(i=>i.kind==="ev"&&(anaWarn(i.x)||["offline","del","folder_del","copy_err"].includes(i.x.kind))));
  if(!("Notification" in window)||Notification.permission!=="granted")return;
  const m=new Map();L.forEach(i=>m.set(i.tag,i));const items=[...m.values()];
  if(items.length>3){
    const n=new Notification(items.length+"件の変更",{body:items.slice(0,4).map(i=>(i.x.where?whereText(i.x.where)+" › ":"")+nfc(i.x.title)+"  "+(i.kind==="inc"?"受信中":i.x.summary)).join("\n")+(items.length>4?"\n…":""),tag:"sw-batch",renotify:true,requireInteraction:!!S.ui.sticky,silent:!!S.ui.sound||!snd.length});
    n.onclick=e=>{e.preventDefault();window.focus();showLog();n.close()};return;
  }
  items.forEach(i=>{const x=i.x;
    const n=new Notification((x.while_stopped?"[停止中の変更] ":"")+(i.kind==="inc"?"受信中: ":"")+(x.repl?"【差し替え"+x.repl+"回目】":"")+nfc(x.title),{body:bodyOf(x),tag:i.tag,renotify:i.re,requireInteraction:!!S.ui.sticky,silent:!!S.ui.sound||!i.sound});
    n.onclick=e=>{e.preventDefault();window.focus();if(x.group!=null){selectGroup(x.root,x.group);if(S.ui.click==="both"&&S.ui.os_open)openOS(x.root,x.group)}else showLog();n.close()};
  });
}
function unlockAudio(){try{if(!AC)AC=new(window.AudioContext||window.webkitAudioContext)();if(AC.state==="suspended")AC.resume()}catch(e){}}
document.addEventListener("pointerdown",unlockAudio);
function chime(bad){
  if(!S.ui.sound||OPON())return;unlockAudio();if(!AC)return;
  const t=AC.currentTime+.02;
  const tone=(f,s,d,v)=>{const o=AC.createOscillator(),g=AC.createGain();o.type="sine";o.frequency.value=f;g.gain.setValueAtTime(.0001,t+s);g.gain.exponentialRampToValueAtTime(v||.22,t+s+.012);g.gain.exponentialRampToValueAtTime(.0001,t+s+d);o.connect(g);g.connect(AC.destination);o.start(t+s);o.stop(t+s+d+.05)};
  if(bad){tone(740,0,.22);tone(494,.24,.38)}else{tone(988,0,.16);tone(1319,.15,.3)}
}
let flT=null;
function flashTitle(){
  if(flT||OPON())return;let on=false;
  flT=setInterval(()=>{if(!document.hidden&&document.hasFocus()){clearInterval(flT);flT=null;liveUnread=0;setTitle();return}
    on=!on;document.title=on?"● 新着 "+liveUnread+"件":setTitle(true)},900);
}
function setTitle(ret){const u=S?S.unread_total:0;const t=(u?"("+u+") ":"")+"PADDOCK SCOUT";if(ret)return t;document.title=t}
window.addEventListener("focus",()=>{liveUnread=0;setTitle();if(SEL&&S&&S.local&&(VIEW==="list"||drawerOpen()))api("/api/seen",SEL).then(refresh).catch(()=>{})});

/* ---------- render ---------- */
/* クリックの途中（押してから離すまで）に画面を作り直すとクリックが消えるので、離してから作り直す */
let PDOWN=false,PENDR=false;
document.addEventListener("pointerdown",e=>{if(e.target.closest&&e.target.closest("#groups,#board"))PDOWN=true},{capture:true});
["pointerup","pointercancel"].forEach(t=>window.addEventListener(t,()=>{if(!PDOWN)return;PDOWN=false;if(PENDR){PENDR=false;setTimeout(renderAll,0)}},{capture:true}));
function renderAll(){if(PDOWN){PENDR=true;return}
  renderRoots();renderOpBar();renderBanner();renderVenue();if(VIEW!=="board")renderGroups();renderBoard();renderLog();setTitle();renderFollow()}
function renderFollow(){$("#swFollow").checked=!!FOLLOW}
$("#swFollow").onchange=()=>{FOLLOW=$("#swFollow").checked;ls.set("follow",FOLLOW)};
$("#bLog").innerHTML=IC.list+"ログ";$("#bTest").innerHTML=IC.bell+"テスト通知";$("#bAll").innerHTML=IC.check2+"すべて既読";$("#bCfg").innerHTML=IC.cog+"設定";
$("#qi").outerHTML=IC.search;
function applyStatus(st){if(!S)return;for(const r of st.roots){const x=rootById(r.id);if(x)Object.assign(x,r)}renderRoots()}
function renderRoots(){
  const el=$("#roots");if(!S.roots.length){el.innerHTML=`<span class="rchip"><span class="dot"></span>監視フォルダ未設定</span>`;return}
  el.innerHTML=S.roots.map(r=>{
    const st=!r.enabled?["","停止中"]:r.online===false?["off","接続できません"]:r.online===null?["busy","確認中…"]:r.pending?["busy","変化を確認中 "+r.pending]:["on","監視中"];
    const m=r.online?`${(r.count||0).toLocaleString()}件 · ${r.scan_ms!=null?(r.scan_ms/1000).toFixed(1)+"s":""}${r.last_scan?" · "+hms(r.last_scan):""}`:"";
    return `<span class="rchip ${r.online===false?"off":""}" title="${esc(r.path)}${r.error?"\n"+esc(r.error):""}${r.n_warns?"\n読めないフォルダ "+r.n_warns+"件":""}"><span class="dot ${st[0]}"></span><span class="t"><b>${esc(nfc(r.label))}</b> ${esc(st[1])}</span><span class="m">${m}${r.n_warns?" · ⚠"+r.n_warns:""}</span></span>`}).join("");
}
function renderOpBar(){
  const el=$("#opbar");if(!OPON()){el.style.display="none";el.innerHTML="";return}
  const o=S.op;let h=`<span class="opt" title="自分の会場だけを監視し、受信が完了した演者フォルダをコピー先へコピーします（NASには書き込みません）">${IC.hd}会場オペレーター <b>${esc(nfc(o.venue||"監視フォルダ全体"))}</b></span>`;
  if((o.days||[]).length)h+=`<span class="opday" title="日ごとに分かれている学会：いまの日を選ぶと、その日の会場フォルダを監視・コピーします">いまの日 <select id="opDaySel" ${S.local?"":"disabled"}>${o.days.map(d=>`<option ${d===o.day?"selected":""}>${esc(d)}</option>`).join("")}</select></span>`;
  for(const d of opDests()){const c=d.count||{};const okn=(c.ok||0)+(c.edited||0);const bad=(c.err||0)+(c.off||0);const busy=(c.busy||0)+(c.srcbusy||0);
    const dot=d.online===false||bad?"off":(busy||c.copying||c.todo||c.wait)?"busy":d.online?"on":"";
    const txt=d.online===false?"接続できません":`コピー済み ${okn}/${d.total||0}${busy?" · 差し替え待ち "+busy:""}${bad?" · エラー "+bad:""}`;
    h+=`<span class="od ${d.online===false?"off":""}" title="${esc(d.path)}${d.error?"\n"+esc(d.error):""}"><span class="dot ${dot}"></span><span class="l">${esc(d.label)}</span><span class="m">${txt}</span><span class="p"><bdi>${esc(nfc(d.path))}</bdi></span></span>`}
  if(o.active){const pct=o.active.total?Math.floor(o.active.done*100/o.active.total):0;
    h+=`<span class="act">${IC.spin}コピー中 ${esc(nfc(o.active.rel.split("/").pop()))}<span class="bar"><i style="width:${pct}%"></i></span>${pct}%${o.queue>1?" · 残り "+(o.queue-1):""}</span>`}
  const ae=document.activeElement;if(ae&&ae.id==="opDaySel")return;   // 選んでいる途中は描き直さない
  el.innerHTML=h;el.style.display="flex";
  const ds=$("#opDaySel");if(ds)ds.onchange=async()=>{const v=ds.value;
    try{const j=await api("/api/opday",{day:v});toast("いまの日を「"+v+"」にしました（"+j.venue+" を監視・コピーします）",5000);await loadState()}
    catch(e){toast(e.message,6000)}};
}
function renderBanner(){
  const b=$("#banner");let h="",warn=false;
  if(!S.roots.length){h=`監視するNASのフォルダがまだ設定されていません。<button class="pri" onclick="openCfg()">設定を開く</button>`}
  else if(!("Notification" in window)){h="このブラウザはデスクトップ通知に対応していません。Chrome / Edge で開いてください。";warn=true}
  else if(OPON()){}   /* 会場オペレーターモードでは通知を使わないので、許可を求めない */
  else if(Notification.permission==="default"){h=`デスクトップ通知がまだ許可されていません。<button class="pri" onclick="askPerm()">通知を許可</button>`}
  else if(Notification.permission==="denied"){h="デスクトップ通知がブロックされています。Chrome / Edge のサイト設定で 127.0.0.1 の「通知」を許可してください（音とログ表示は動作します）";warn=true}
  else if(!S.local){h="閲覧専用で表示中（別端末）。既読・設定などの操作は監視PC側で行ってください。";warn=true}
  if(S.op_moved&&APPKIND==="watch"){h=`このPCでは「会場オペレーターモード」（発表PCへのコピー）を使っていました。コピーは <b>PADDOCK GATE</b> に分かれたため、このアプリではコピーしません。発表PCでは PADDOCK GATE を使ってください（このアプリと同じ場所にZIPを展開すれば、はじめて起動したときに会場・コピー先の設定を引き継ぎます）。`+(h?"<br>"+h:"");warn=true}
  const off=S.roots.filter(r=>r.enabled&&r.online===false);
  const offd=opDests().filter(d=>d.online===false);
  if(offd.length){h=offd.map(d=>`⚠ コピー先「${esc(d.label)}」に接続できません（つながったら自動でコピーします）`).join("　")+(h?"<br>"+h:"");warn=true}
  if(off.length){h=off.map(r=>`⚠ ${esc(nfc(r.label))}: ${esc(r.error)}`).join("　")+(h?"<br>"+h:"");warn=true}
  b.innerHTML=h?(off.length?IC.alert:warn?IC.alert:IC.info)+`<span style="flex:1">${h}</span>`:"";b.className=off.length?"bad":warn?"warn":"";b.style.display=h?"flex":"none";
}
async function askPerm(){try{await Notification.requestPermission()}catch(e){}unlockAudio();renderBanner()}

function renderVenue(){
  const opts=[];let h,dis=false,show=true;
  if(OPON()){const r=rootById(S.op.root);h=`<option value="">${esc(nfc(S.op.venue||(r?r.label:"")))}（会場オペレーター）</option>`;dis=true}
  else{
    for(const r of S.roots){if(r.depth<2)continue;
      const segs=[...new Set((r.groups||[]).filter(g=>g.key).map(g=>fuOf(r,g.key)).filter(Boolean))].sort(cmpName);
      segs.forEach(s=>opts.push([r.id+"|"+s,(S.roots.length>1?nfc(r.label)+" / ":"")+nfc(s)]));}
    if(VENUE&&!opts.some(o=>o[0]===VENUE))opts.push([VENUE,VENUE.slice(VENUE.indexOf("|")+1)+"（現在なし）"]);
    show=opts.length>0;
    h=`<option value="">すべての会場</option>`+opts.map(o=>`<option value="${esc(o[0])}" ${o[0]===VENUE?"selected":""}>${esc(o[1])}</option>`).join("");
  }
  for(const sel of [$("#venue"),$("#bvenue")]){sel.disabled=dis;sel.style.display=show?"":"none";
    if(sel.dataset.h!==h){sel.innerHTML=h;sel.dataset.h=h}
    if(!dis&&sel.value!==VENUE)sel.value=VENUE}
}
function setVenue(v){VENUE=v;ls.set("venue",VENUE);renderVenue();renderGroups();renderBoard();renderLog()}
$("#venue").addEventListener("change",()=>setVenue($("#venue").value));
$("#bvenue").addEventListener("change",()=>setVenue($("#bvenue").value));

/* 差し替え（受付後の変更）回数 */
function replTag(g){if(!g||!g.repl)return"";
  return `<span class="tag t-repl" title="受付後に${g.repl}回変更されています${g.repl_ts?"（最終 "+dtm(g.repl_ts)+(g.repl_sum?"："+esc(g.repl_sum):"")+"）":""}">差替 ${g.repl}</span>`}
/* 受信中（NASへ書き込み中）の進み具合。全体のサイズはNASの一覧からは分からないので、受信済みサイズ・速度・経過時間を出す */
const RATE={};let SKEW=0;
function updateRates(){
  if(!S)return;SKEW=S.now-Date.now()/1000;const live=new Set();
  for(const r of S.roots)for(const g of (r.groups||[])){if(!g.pending)continue;const k=r.id+"|"+g.key;live.add(k);
    const b=g.pbytes||0,x=RATE[k];
    if(!x){RATE[k]={b,t:S.now,v:null};continue}
    const dt=S.now-x.t;if(dt<1.5)continue;
    const dv=(b-x.b)/dt;x.v=dv>0?(x.v?x.v*.5+dv*.5:dv):(dt>6?0:x.v);x.b=b;x.t=S.now}
  Object.keys(RATE).forEach(k=>{if(!live.has(k))delete RATE[k]});
}
function mss(sec){sec=Math.max(0,Math.floor(sec));const h=Math.floor(sec/3600),m=Math.floor(sec%3600/60),s2=sec%60;return (h?h+":"+p2(m):m)+":"+p2(s2)}
function rxText(rid,g){const x=RATE[rid+"|"+g.key];const sp=x&&x.v>0?" · "+fmtSize(x.v)+"/s":"";
  return `受信中${g.pending>1?" "+g.pending+"件":""}${g.pbytes?" "+fmtSize(g.pbytes):""}${sp} · <span data-ps="${g.pstart||""}">${g.pstart?mss(S.now-g.pstart):""}</span>`}
function opActiveFor(rid,g){if(!OPON()||rid!==S.op.root||!S.op.active)return null;const a=S.op.active;return a.rel.startsWith(g.key+"/")?a:null}
function progHtmlRow(r,g){
  let h="";
  if(g.pending)h+=`<div class="rx" title="NASへの書き込み中（全体のサイズはNASの一覧からは分からないため、受信済みサイズと速度を表示）"><span class="rbar ind"><i></i></span><span class="rt">${rxText(r.id,g)}</span></div>`;
  const a=opActiveFor(r.id,g);
  if(a){const pct=a.total?Math.floor(a.done*100/a.total):0;const lb=(S.op.dests||[]).filter(d=>(a.dests||[]).includes(d.id)).map(d=>d.label).join("・");
    h+=`<div class="rx op" title="${esc(nfc(a.rel))}"><span class="rbar"><i style="width:${pct}%"></i></span><span class="rt">${esc(lb)}へコピー ${pct}% · ${esc(nfc(a.rel.split("/").pop()))}</span></div>`}
  return h;
}
setInterval(()=>{if(!S)return;const now=Date.now()/1000+SKEW;document.querySelectorAll("[data-ps]").forEach(e=>{const ps=+e.dataset.ps;if(ps)e.textContent=mss(now-ps)})},1000);
function anaChips(a){
  if(!a||!a.n)return"";let h="";
  if(a.done<a.n)h+=`<span class="tag t-dim">解析中</span>`;
  if(a.err)h+=`<span class="tag t-bad">解析不可</span>`;
  if(a.video){
    if(a.vwarn)h+=`<span class="tag t-bad">外部動画⚠</span>`;
    if(a.vfbad)h+=`<span class="tag t-bad" title="会場のWindows PCで再生できない可能性が高い形式の動画があります">動画形式NG</span>`;
    else if(a.vfwarn)h+=`<span class="tag t-warn" title="形式の確認が必要な動画があります（試写推奨）">動画要試写</span>`;
    if(!a.vwarn&&!a.vfbad&&!a.vfwarn)h+=`<span class="tag t-info">動画あり</span>`;
  }
  if(a.abad)h+=`<span class="tag t-bad" title="リンクされた音声ファイルが見つからない、または発表者PCの場所を指しています">音声リンク⚠</span>`;
  if(a.links)h+=`<span class="tag t-info">リンクあり</span>`;
  if(a.done===a.n&&a.done>a.err)h+=a.coi?`<span class="tag t-ok">COI</span>`:`<span class="tag t-warn">COIなし</span>`;
  if(a.auto)h+=`<span class="tag t-warn">自動送り</span>`;
  if(a.noclick)h+=`<span class="tag t-bad">クリック無効</span>`;
  return h;
}
/* 会場の色分け・折りたたみ状態（このPCに保存） */
const VPAL=["#38bdf8","#a78bfa","#34d399","#fbbf24","#f472b6","#fb923c","#2dd4bf","#818cf8","#f87171","#a3e635"];
let VCOL=ls.get("vcol",{});
/* ---------- 階層の読み取り：日（day1・1日目・10月11日など）／会場／セッション ----------
   日の階層は自動で見つける（会場の上でも下でも）。日の階層がなくても、セッション名の先頭が「day1_」「1日目 」なら日として扱う */
const DAY_RE=/^(?:\d{1,3}[_\-\s.]+)?(?:day\s*[-_.]?\s*(\d{1,2})|(\d{1,2})\s*日目|第\s*(\d{1,2})\s*日目?|(\d{1,2})\s*月\s*(\d{1,2})\s*日|(\d{4})\s*[-_.年]\s*(\d{1,2})\s*[-_.月]\s*(\d{1,2})\s*日?)/i;
function dayInfo(name){const t=nameKey(name);const m=DAY_RE.exec(t);if(!m)return null;
  const o={tok:m[0].replace(/^\d{1,3}[_\-\s.]+/,"").trim(),rest:t.slice(m[0].length)};
  if(m[1]||m[2]||m[3])o.n=+(m[1]||m[2]||m[3]);
  else if(m[4])o.date={m:+m[4],d:+m[5]};else if(m[6])o.date={y:+m[6],m:+m[7],d:+m[8]};
  return o}
const LAYC={};
function lay(r){
  const c=LAYC[r.id];if(c&&c.ref===r.groups&&c.depth===r.depth)return c;
  const L=Math.max(0,(r.depth||1)-1);const keys=(r.groups||[]).map(g=>g.key).filter(Boolean);
  let dl=-1;
  for(let i=0;i<L&&dl<0;i++){const vals=new Set();for(const k of keys){const x=k.split("/")[i];if(x!=null)vals.add(x)}
    const tokN=new Map();
    if(vals.size&&vals.size<=31&&[...vals].every(v=>{const d=dayInfo(v);if(d)tokN.set(d.tok,(tokN.get(d.tok)||0)+1);return d&&d.rest.replace(/[\s_\-.()（）［］\[\]・,、曜月火水木金土日]/g,"").length<=8})
       &&[...tokN.values()].every(n=>n===1))dl=i}   // 「day1_第1会場」「day1_第2会場」のように同じ日が並ぶなら日の階層ではない
  const others=[];for(let i=0;i<L;i++)if(i!==dl)others.push(i);
  const vl=others.length>=2?others[0]:-1,sl=others.length>=2?others.slice(1):others;
  let sd=false;
  if(dl<0&&sl.length){const vals=new Set(keys.map(k=>k.split("/")[sl[0]]));let hit=0;vals.forEach(v=>{if(v&&dayInfo(v))hit++});sd=hit>0&&hit*2>=vals.size}
  const o={ref:r.groups,depth:r.depth,dl,vl,sl,sd,L};LAYC[r.id]=o;return o}
function parts(r,key){const y=lay(r);const segs=String(key).split("/");
  const venue=y.vl>=0?(segs[y.vl]||""):"";const sesSegs=y.sl.map(i=>segs[i]).filter(x=>x!=null&&i_ok(x));
  let day=y.dl>=0?(segs[y.dl]||""):"";
  if(!day&&y.sd&&sesSegs.length){const d=dayInfo(sesSegs[0]);if(d)day=d.tok}
  return {venue,day,ses:sesSegs.join("/"),sesKey:segs.slice(0,-1).join("/"),name:segs[segs.length-1]}}
function i_ok(x){return x!==""}
/* 「この会場だけ」の単位：会場（会場の階層がなければ最初のフォルダ。階層2ならセッション＝従来どおり） */
function fuOf(r,key){const y=lay(r);const segs=String(key).split("/");
  if(y.vl>=0)return segs[y.vl]||"";const i=y.dl===0&&y.sl.length?y.sl[0]:0;return segs[i]||""}
function dayOrd(label){const d=label?dayInfo(label):null;if(!d)return 1e9;
  if(d.date)return (d.date.y||new Date().getFullYear())*10000+d.date.m*100+d.date.d;return d.n!=null?d.n:1e9-1}
function cmpDay(a,b){return (a?0:1)-(b?0:1)||dayOrd(a)-dayOrd(b)||cmpName(a,b)}
function isTodayLabel(label){const d=label&&dayInfo(label);if(!d||!d.date)return false;const t=new Date();
  return d.date.m===t.getMonth()+1&&d.date.d===t.getDate()&&(!d.date.y||d.date.y===t.getFullYear())}
/* 表示する日（PCごとに保存）。「1日目」を選んだまま翌日になったら、自動で「2日目」に進める */
let DAYSEL=ls.get("day",null);
function ymd(t){t=t||new Date();return t.getFullYear()+"-"+p2(t.getMonth()+1)+"-"+p2(t.getDate())}
function allDays(){const set=new Set();const EV=effVenue();
  for(const r of (S?S.roots:[])){if(EV&&EV.slice(0,EV.indexOf("|"))!==r.id)continue;for(const g of (r.groups||[]))if(g.key){const d=parts(r,g.key).day;if(d)set.add(d)}}
  return [...set].sort(cmpDay)}
function effDay(days){if(!DAYSEL||!DAYSEL.v)return "";days=days||allDays();
  if(!days.length)return "";                       // 日のフォルダがない（別の学会など）：前に選んだ日では絞り込まない
  const d=dayInfo(DAYSEL.v);
  if(d&&d.n!=null&&DAYSEL.at){const diff=Math.round((new Date(ymd()+"T00:00:00")-new Date(DAYSEL.at+"T00:00:00"))/864e5);
    if(diff>0){const hit=days.find(x=>{const e=dayInfo(x);return e&&e.n===d.n+diff});if(hit)return hit}}
  return days.includes(DAYSEL.v)?DAYSEL.v:""}
function dayOK(r,key,ed){if(!ed)return true;const y=lay(r);if(y.dl<0&&!y.sd)return true;return parts(r,key).day===ed}
/* 進行状況の基準になる「今日」：日付の名前なら今日の日付、day1 などなら選んでいる日。日の情報がなければ全部今日 */
function todayDay(days,ed){const t=days.find(isTodayLabel);return t||ed||null}
/* セッション名の時刻：0900-1030 / 9:00〜10:30 / 9時30分 / 先頭の0900_ など */
const TMS=String.raw`(\d{1,2})(?::([0-5]\d)|時(?!間)(?:([0-5]?\d)分?)?)`,SEPS=String.raw`\s*[-~〜ー−–—]+\s*`;
const RE_TR=new RegExp(String.raw`(?<!\d)`+TMS+SEPS+TMS),RE_T=new RegExp(String.raw`(?<!\d)`+TMS);
const RE_HR=/(?<!\d)([01]\d|2[0-3])([0-5]\d)\s*[-~〜ー−–—]+\s*([01]\d|2[0-3])([0-5]\d)(?!\d)/,RE_HH=/(?:^|[_\s])([01]\d|2[0-3])([0-5]\d)(?=[_\s\-.]|$)/;
function sesTime(path){if(!path)return null;const t=nameKey(path);let m,a=null,b=null;
  const tm=(h,mm,m2)=>{h=+h;const mi=mm!=null&&mm!==""?+mm:(m2!=null&&m2!==""?+m2:0);return h<=24&&mi<60?h*60+mi:null};
  if((m=RE_TR.exec(t))){a=tm(m[1],m[2],m[3]);b=tm(m[4],m[5],m[6])}
  else if((m=RE_HR.exec(t))){a=+m[1]*60+ +m[2];b=+m[3]*60+ +m[4]}
  else if((m=RE_T.exec(t)))a=tm(m[1],m[2],m[3]);
  else for(const seg of t.split("/")){if((m=RE_HH.exec(seg))&&+m[2]%5===0){a=+m[1]*60+ +m[2];break}}   // 「1101_一般演題」「2026」などの番号は時刻にしない
  if(a==null)return null;if(b!=null&&b<=a)b=null;return {s:a,e:b}}
const fmtT=m=>Math.floor(m/60)+":"+p2(m%60);
const fmtDur=m=>m>=60?Math.floor(m/60)+"時間"+(m%60?(m%60)+"分":""):m+"分";
/* 同じ会場・同じ日のセッション（開始順）から、終了／進行中／次 を決める。終わりの時刻がなければ次のセッションの開始まで */
function sesStatus(list){const now=new Date();const nm=now.getHours()*60+now.getMinutes()+now.getSeconds()/60;
  const out=new Map();let nextSet=false;
  list.forEach((x,i)=>{const end=x.t.e!=null?x.t.e:(list[i+1]?list[i+1].t.s:null);let st;
    if(nm<x.t.s){st=nextSet?"later":"next";nextSet=true}
    else if(end!=null?nm<end:nm<x.t.s+180)st="live";else st="done";
    out.set(x.key,{st,s:x.t.s,end,rem:end!=null?Math.max(0,Math.ceil(end-nm)):null,until:Math.ceil(x.t.s-nm),
      pct:end!=null&&end>x.t.s?Math.min(100,Math.max(0,(nm-x.t.s)*100/(end-x.t.s))):null})});
  return out}
function timeChip(t){return t?`<span class="stime">${fmtT(t.s)}${t.e!=null?"–"+fmtT(t.e):"〜"}</span>`:""}
function statusHtml(st,list){if(!st)return"";const un=list.filter(isTodo).length;
  const soon=st.st==="live"||((st.st==="next"||st.st==="later")&&st.until<=30);
  const warn=un&&soon?`<span class="sw-un" title="開始前・進行中なのに未受付の演者がいます">未受付 ${un}</span>`:"";
  if(st.st==="done")return `<span class="sst done">終了</span>${warn}`;
  if(st.st==="live")return `<span class="sst live">進行中${st.rem!=null?" · 残り"+fmtDur(st.rem):""}</span>${warn}`;
  if(st.st==="next")return `<span class="sst next ${st.until<=30?"soon":""}">次 · あと${fmtDur(Math.max(0,st.until))}</span>${warn}`;
  return warn}
function computeVenueColors(){let ch=false;for(const r of S.roots){if(lay(r).vl<0)continue;
  const vs=[...new Set((r.groups||[]).filter(g=>g.key).map(g=>parts(r,g.key).venue).filter(Boolean))].sort(cmpName);
  const used=new Set(Object.keys(VCOL).filter(k=>k.startsWith(r.id+"|")).map(k=>VCOL[k]));
  for(const v of vs){const k=r.id+"|"+v;if(VCOL[k])continue;
    VCOL[k]=VPAL.find(c=>!used.has(c))||VPAL[used.size%VPAL.length];used.add(VCOL[k]);ch=true}}
  if(ch)ls.set("vcol",VCOL)}
const venueOf=(root,group)=>{const r=rootById(root);if(!r||!group)return null;const v=parts(r,group).venue;return v||null};
const vColor=(root,v)=>VCOL[root+"|"+v]||"#a1a1aa";
let FOLD=ls.get("fold",{});
const isFold=k=>!!FOLD[k];
function setFold(k,v){if(v)FOLD[k]=1;else delete FOLD[k];ls.set("fold",FOLD)}
/* 開閉のキー：会場＝「root|会場名」、セッション＝「root|演者フォルダの親のパス」（日をまたいでも別々に開閉できる） */
function foldKeysOf(root,group){const r=rootById(root);if(!r||!group||r.depth<2)return[];const segs=group.split("/");const ks=[];
  const v=parts(r,group).venue;if(v)ks.push(root+"|"+v);
  if(segs.length>1)ks.push(root+"|"+segs.slice(0,-1).join("/"));return ks}
function unfold(root,group){let ch=false;foldKeysOf(root,group).forEach(k=>{if(FOLD[k]){delete FOLD[k];ch=true}});if(ch)ls.set("fold",FOLD);return ch}
/* 受付状況：ファイルが1つ以上確定していれば「受付済み」 */
/* 「取得済」の目印＝会場側が受け取った。「受付済」の目印 か データがあれば受付済み */
/* 目印：「演題取り下げ」→取り下げ（受付の数に入れない）、「発表終了」→発表終了、「会場直」→データがなくても未受付にしない */
const recvState=g=>g.pending?"copying":g.mk_drop?"drop":g.mk_done?"done":g.mk_got?"got":((g.files>0||g.mk_recv)?"recv":g.mk_direct?"direct":"none");
const RECV_OK=new Set(["recv","got","done","direct"]);
/* 差し替えを受信中（コピー中）でも、もともと受付済みなら受付済みとして数える */
const isRecv=g=>{const s=recvState(g);return RECV_OK.has(s)||(s==="copying"&&!!(g.files>0||g.mk_recv||g.mk_got||g.mk_done||g.mk_direct))};
const isGot=g=>{const s=recvState(g);return s==="got"||s==="done"||(s==="copying"&&!!(g.mk_got||g.mk_done))};
const actv=list=>list.filter(g=>!g.mk_drop);
const isTodo=g=>!g.mk_drop&&!isRecv(g);
const STL={got:"会場取得済",recv:"受付済み",copying:"コピー中",none:"未受付",done:"発表終了",drop:"演題取り下げ",direct:"会場直"};
const stIcon=st=>st==="got"?IC.check2:st==="recv"?IC.ok:st==="copying"?IC.spin:st==="done"?IC.flag:st==="drop"?IC.ban:st==="direct"?IC.direct:IC.todo;
/* 目印のチップ（注意 → 会場直 → 表示だけ の順。max を超えた分は「+n」） */
const FLO={warn:0,direct:1,info:2};
function flagChips(g,max){const f=(g.fl||[]).map((x,i)=>[x[0],x[1],i]).sort((a,b)=>(FLO[a[1]]??3)-(FLO[b[1]]??3)||a[2]-b[2]);if(!f.length)return"";
  const sh=max&&f.length>max?f.slice(0,max-1):f;
  return sh.map(([l,r])=>`<span class="fl fl-${esc(r)}" title="目印：${esc(nfc(l))}">${esc(nfc(l))}</span>`).join("")+(sh.length<f.length?`<span class="fl fl-more" title="${esc(f.slice(sh.length).map(x=>nfc(x[0])).join("、"))}">+${f.length-sh.length}</span>`:"")}
let ANYGOT=false;
function gotHtml(list){if(!ANYGOT)return"";list=actv(list);const t=list.length,n=list.filter(isGot).length;
  return `<span class="gotc ${t&&n===t?"done":""}" title="会場取得済（「取得済」の目印あり）">取得 ${n}/${t}</span>`}
function progHtml(list,suffix){list=actv(list);const t=list.length,n=list.filter(isRecv).length;const pct=t?Math.round(n*100/t):0;
  return `<span class="prog ${t&&n===t?"done":n?"":"zero"}" title="受付 ${n}/${t}"><span class="bar"><i style="width:${pct}%"></i></span>${n}/${t}${suffix||""}</span>`}
/* リスト用：会場ごと・日ごとの進行状況 */
function listTimeline(r,v,sessions,SI){const days=allDays(),ed=effDay(days),td=todayDay(days,ed);const out=new Map();
  if(days.length&&!td)return out;
  const arr=[];for(const [skey] of sessions){const info=SI[skey];if(!info)continue;if(days.length&&info.day!==td)continue;
    const t=sesTime(info.ses);if(t)arr.push({key:skey,t})}
  arr.sort((a,b)=>a.t.s-b.t.s);return sesStatus(arr)}
function renderGroups(){
  const el=$("#groups");const q=nfc($("#q").value).toLowerCase().trim();const onlyU=$("#onlyU").checked;const sort=$("#sort").value;
  if(!S.roots.length){el.innerHTML=`<div class="empty"><div class="ico">${IC.folder}</div><b>監視フォルダがありません</b>［設定］から学会名フォルダを追加してください。<br><span class="mono" style="font-size:11.5px;color:var(--dim)">例: \\\\192.168.0.10\\share\\学会名</span></div>`;return}
  computeVenueColors();renderDaySel(allDays(),effDay());
  const onlyN=$("#onlyN").checked;
  const filtering=!!(q||onlyU||onlyN);
  let h="";
  for(const r of S.roots){
    const EV=effVenue();if(EV&&EV.slice(0,EV.indexOf("|"))!==r.id)continue;
    const ED=effDay();
    let gs=(r.groups||[]).filter(g=>inVenue(r.id,g.key)&&(g.key===""||dayOK(r,g.key,ED)));
    if(q)gs=gs.filter(g=>nfc(g.key).toLowerCase().includes(q));
    if(onlyU)gs=gs.filter(g=>g.unread);
    if(onlyN)gs=gs.filter(g=>g.key!==""&&isTodo(g));
    gs.sort((a,b)=>{
      if(a.key==="")return 1;if(b.key==="")return -1;
      if(sort==="recent")return (b.last_ts||0)-(a.last_ts||0)||cmpPath(a.key,b.key);
      if(sort==="unread")return (b.unread?1:0)-(a.unread?1:0)||(b.last_ts||0)-(a.last_ts||0)||cmpPath(a.key,b.key);
      return cmpPath(a.key,b.key)});
    const all=(r.groups||[]).filter(g=>g.key!==""&&inVenue(r.id,g.key)&&dayOK(r,g.key,ED));const un=all.filter(g=>g.unread).length;
    const hier=sort==="name"&&r.depth>=2;
    h+=`<div class="rhead"><div class="r1"><span class="dot ${r.online===false?"off":r.online?"on":"busy"}"></span><span class="rl">${esc(nfc(r.label))}</span>${hier?`<span class="tb"><button class="ghost" data-all="open" data-r="${esc(r.id)}" title="すべて開く">${IC.expand}</button><button class="ghost" data-all="close" data-r="${esc(r.id)}" title="すべてたたむ">${IC.collapse}</button></span>`:""}</div><div class="r2">${progHtml(all," 受付")}${gotHtml(all)}${un?`<span class="cnt">未確認 ${un}</span>`:""}</div><span class="p" title="${esc(r.path)}"><bdi>${esc(nfc(r.path))}</bdi></span></div>`;
    if(!gs.length){h+=`<div class="empty" style="padding:18px">${r.online===false?"接続できません":filtering?"該当なし":"フォルダがありません"}</div>`;continue}
    if(!hier){for(const g of gs)h+=rowHtml(r,g,false);continue}
    // 会場 → （日）→ セッション → 演者 のツリー（日の階層があれば、会場の中で日ごとに並べる）
    const tree=new Map();const rest=[];const SI={};
    /* 見出しの「受付 n/t」・未確認数・進行状況は、絞り込み（未受付のみ・検索など）に関係なく、その会場・セッションの全員で数える */
    const FV=new Map(),FS=new Map();
    for(const g of all){const pp=parts(r,g.key);if(!FV.has(pp.venue))FV.set(pp.venue,new Map());const m=FV.get(pp.venue);
      if(!m.has(pp.sesKey))m.set(pp.sesKey,[]);m.get(pp.sesKey).push(g);if(!FS.has(pp.sesKey))FS.set(pp.sesKey,m.get(pp.sesKey));
      if(!SI[pp.sesKey])SI[pp.sesKey]={day:pp.day,ses:pp.ses}}
    for(const g of gs){
      if(g.key===""){rest.push(g);continue}
      const pp=parts(r,g.key);const v=pp.venue;const sk=pp.sesKey;
      if(!tree.has(v))tree.set(v,new Map());const m=tree.get(v);if(!m.has(sk))m.set(sk,[]);m.get(sk).push(g);
      if(!SI[sk])SI[sk]={day:pp.day,ses:pp.ses};
    }
    const venues=[...tree.keys()].sort(cmpName);
    for(const v of venues){const sessions=new Map([...tree.get(v).entries()].sort((a,b)=>cmpDay(SI[a[0]].day,SI[b[0]].day)||cmpPath(SI[a[0]].ses,SI[b[0]].ses)));
      const vfull=FV.get(v)?[...FV.get(v).values()].flat():[...sessions.values()].flat();
      const vlist=vfull;
      const vk=r.id+"|"+v;
      if(v){
        const vfold=!filtering&&isFold(vk);const vun=vfull.filter(g=>g.unread).length;const vpend=vfull.some(g=>g.pending);
        const vflash=vfold&&vlist.some(g=>flashKeys.has(r.id+"|"+g.key));
        h+=`<div class="vhead ${vfold?"fold":""} ${vflash?"flashh":""}" data-fold="${esc(vk)}" tabindex="0" role="button" aria-expanded="${!vfold}" style="--vc:${vColor(r.id,v)}"><span class="vic">${IC.building}</span><span class="vn">${esc(nfc(v))}</span>${vpend?`<span class="pdot" title="コピー中"></span>`:""}${progHtml(vlist)}${vun?`<span class="badge">${vun}</span>`:""}<span class="chev">${IC.down}</span></div>`;
        if(vfold)continue;
      }
      const TL=listTimeline(r,v,FV.get(v)||sessions,SI);
      for(const [skey,list] of sessions){
        const info=SI[skey]||{day:"",ses:""};const ses=info.ses;const sall=FS.get(skey)||list;
        if(ses||info.day){
          const sk=r.id+"|"+skey;const sfold=!filtering&&isFold(sk);
          const sun=sall.filter(g=>g.unread).length;const spend=sall.some(g=>g.pending);
          const sflash=sfold&&list.some(g=>flashKeys.has(r.id+"|"+g.key));
          const tt=sesTime(ses);const st=TL.get(skey);
          h+=`<div class="shead ${sfold?"fold":""} ${sflash?"flashh":""} ${st?"st-"+st.st:""}" data-fold="${esc(sk)}" tabindex="0" role="button" aria-expanded="${!sfold}"><span class="chev">${IC.down}</span><span class="sn">${info.day&&lay(r).dl>=0?`<span class="dchip">${esc(nfc(info.day))}</span>`:""}${(ses||"").split("/").map(x=>esc(nfc(x))).join('<span class="sep"> › </span>')}</span>${spend?`<span class="pdot" title="コピー中"></span>`:""}${progHtml(sall)}${sun?`<span class="badge">${sun}</span>`:""}${tt?`<span class="tl">${timeChip(tt)}${statusHtml(st,sall)}</span>`:""}</div>`;
          if(sfold)continue;
        }
        for(const g of list)h+=rowHtml(r,g,true);
      }
    }
    for(const g of rest)h+=rowHtml(r,g,false);
  }
  el.innerHTML=h;
}
function rowHtml(r,g,hier){
  const segs=g.key.split("/");const name=g.key===""?(r.depth>1?"（演者フォルダより上のファイル）":"（直下のファイル）"):segs[segs.length-1];
  const where=segs.length>1?segs.slice(0,-1).join("/"):"";
  const v=venueOf(r.id,g.key);
  const isSel=SEL&&SEL.root===r.id&&SEL.group===g.key;
  const cats=Object.entries(g.cats||{}).filter(([c])=>!(g.ana&&c==="PPT")).sort((a,b)=>b[1]-a[1]).slice(0,3).map(([c,n])=>`<span class="chip c-${esc(c)}">${esc(c)}${n>1?" "+n:""}</span>`).join("");
  const pre=!hier&&where?`<span class="pre">${v?`<span class="vdot" style="--vc:${vColor(r.id,v)}"></span>`:""}${esc(whereText(where))} › </span>`:"";
  const st=g.key===""?"":recvState(g);
  const sti=st?`<span class="sti" title="${STL[st]||""}">${stIcon(st)}</span>`:"";
  const cps=OPON()&&g.cp?opDests().map(d=>g.cp[d.id]?cpPill(d.label,g.cp[d.id]):"").join(""):"";
  const stTag=st==="drop"?`<span class="tag t-drop">演題取り下げ</span>`:st==="done"?`<span class="tag t-done">発表終了</span>`:st==="none"?`<span class="tag t-dim">未受付</span>`:"";
  const fc=flagChips(g);
  const meta=(!g.files&&!g.pending)?`${stTag}${(st==="recv"||st==="got"||st==="done")&&g.key!==""?`<span class="tag t-dim">データなし</span>`:""}${fc}${g.last_kind&&st!=="none"?kindPill(g.last_kind):""}${progHtmlRow(r,g)}`:`${stTag}${cps}${replTag(g)}${fc}<span>${g.files}ファイル</span><span>${fmtSize(g.size)}</span>${anaChips(g.ana)}${cats}${g.last_kind?kindPill(g.last_kind):""}${progHtmlRow(r,g)}`;
  return `<div class="grp ${hier?"hier":""} ${st?"st-"+st:""} ${g.unread?"unread":""} ${isSel?"sel":""} ${flashKeys.has(r.id+"|"+g.key)?"flash":""}" data-r="${esc(r.id)}" data-g="${esc(g.key)}">
    <div class="n">${sti}<span class="nm">${pre}${esc(nfc(name))}</span>${g.unread?`<span class="badge">${g.unread}</span>`:""}<span class="ago">${g.last_ts?ago(g.last_ts):""}</span></div>
    <div class="meta">${meta}</div></div>`;
}
$("#groups").addEventListener("click",e=>{
  const a=e.target.closest("[data-all]");
  if(a){const rid=a.dataset.r;const r=rootById(rid);if(!r)return;
    const keys=new Set();(r.groups||[]).forEach(g=>foldKeysOf(rid,g.key).forEach(k=>keys.add(k)));
    keys.forEach(k=>{if(a.dataset.all==="close")FOLD[k]=1;else delete FOLD[k]});ls.set("fold",FOLD);renderGroups();return}
  const f=e.target.closest("[data-fold]");if(f){setFold(f.dataset.fold,!isFold(f.dataset.fold));renderGroups();return}
  const dh=dblHit(e);if(dh){openFolderOS(dh.r,dh.g);return}
  const d=e.target.closest(".grp");if(!d)return;
  if(d.dataset.g!=="")noteClick(e,d.dataset.r,d.dataset.g);selectGroup(d.dataset.r,d.dataset.g)});
$("#groups").addEventListener("keydown",e=>{const f=e.target.closest("[data-fold]");if(f&&(e.key==="Enter"||e.key===" ")){e.preventDefault();setFold(f.dataset.fold,!isFold(f.dataset.fold));renderGroups();const n=[...document.querySelectorAll("[data-fold]")].find(x=>x.dataset.fold===f.dataset.fold);if(n)n.focus()}});
$("#q").addEventListener("input",renderGroups);
/* 「未確認のみ」「未受付のみ」はリストと会場ボードで共通 */
function syncFilter(src,dst,key){$(dst).checked=$(src).checked;ls.set(key,$(src).checked);renderGroups();renderBoard()}
$("#onlyU").addEventListener("change",()=>syncFilter("#onlyU","#bOnlyU","onlyU"));
$("#bOnlyU").addEventListener("change",()=>syncFilter("#bOnlyU","#onlyU","onlyU"));
$("#sort").addEventListener("change",()=>{ls.set("sort",$("#sort").value);renderGroups()});
$("#onlyN").addEventListener("change",()=>syncFilter("#onlyN","#bOnlyN","onlyN"));
$("#bOnlyN").addEventListener("change",()=>syncFilter("#bOnlyN","#onlyN","onlyN"));
$("#onlyU").checked=$("#bOnlyU").checked=ls.get("onlyU",false);$("#onlyN").checked=$("#bOnlyN").checked=ls.get("onlyN",false);$("#sort").value=ls.get("sort","name");

function renderLog(){
  const el=$("#log");const evs=S.events.filter(e=>inVenue(e.root,e.group)).reverse();
  if(!evs.length){el.innerHTML=`<div class="empty"><div class="ico">${IC.inbox}</div><b>まだ変更はありません</b>NAS上のフォルダに変化があるとここに出ます。</div>`;return}
  const multi=S.roots.length>1;
  el.innerHTML=evs.map(e=>`<div class="ev ${e.u?"u":""}" data-id="${e.id}">
    <div class="top"><span class="t">${dtm(e.ts)}</span>${kindPill(e.kind)}${e.repl?`<span class="kind k-repl">差替${e.repl}</span>`:""}<span class="ti">${esc(nfc(e.title))}</span>${e.while_stopped?`<span class="ws" title="アプリ停止中に起きた変更">停止中</span>`:""}</div>
    ${e.where?`<div class="wh">${venueOf(e.root,e.group)?`<span class="vdot" style="--vc:${vColor(e.root,venueOf(e.root,e.group))}"></span>`:""}${esc(whereText(e.where))}</div>`:""}
    <div class="sm">${esc(e.summary)}</div>${e.detail?`<div class="dt">${esc(nfc(e.detail))}</div>`:""}
    ${(e.ana||[]).map(a=>`<div class="an ${a.warn?"w":""}">▸ ${esc(nfc(a.file))}: ${esc(a.text||a.na||"解析待ち")}</div>`).join("")}
    ${multi?`<div class="rl">${esc(nfc(e.root_label))}</div>`:""}</div>`).join("");
}
$("#log").addEventListener("click",e=>{const d=e.target.closest(".ev");if(!d)return;const ev=S.events.find(x=>x.id==d.dataset.id);if(ev&&ev.group!=null){selectGroup(ev.root,ev.group);if(innerWidth<=1180||VIEW==="board")$("#main").classList.remove("showlog")}});
function showLog(){if(innerWidth<=1180||VIEW==="board")$("#main").classList.add("showlog");$("#log").scrollTop=0}
$("#bLog").onclick=()=>$("#main").classList.toggle("showlog");
$("#bLogClose").onclick=()=>$("#main").classList.remove("showlog");
if(innerWidth<=1180)$("#bLogClose").style.display="inline-block";

/* ---------- 会場ボード（全会場を横に並べて受付状況を一覧） ---------- */
let VIEW=ls.get("view","list")==="board"?"board":"list",followKey=null,boardHtml="";
const drawerOpen=()=>VIEW==="board"&&$("#main").classList.contains("drawer");
function openDrawer(){if(VIEW!=="board")return;const m=$("#main");
  if(!m.classList.contains("drawer")){const c=$("#board .col");if(c)$("#board").style.gridAutoColumns=c.getBoundingClientRect().width+"px"}  // 開いても列の幅を変えない
  m.classList.add("drawer");setTimeout(updNav,0)}
/* 右パネルに隠れないよう、演者の列を左側へスクロールして見せる */
function revealInBoard(row){
  row.scrollIntoView({block:"nearest",inline:"nearest"});
  const bd=$("#board");const c=row.closest(".col")||row;const br=bd.getBoundingClientRect();
  const lim=drawerOpen()?innerWidth-$("#center").offsetWidth-12:br.right-12,r=c.getBoundingClientRect();
  if(r.right>lim)bd.scrollLeft+=Math.ceil(r.right-lim);           // 列全体が見えるように
  else if(r.left<br.left+12)bd.scrollLeft-=Math.ceil(br.left+12-r.left);
}
function closeDrawer(){$("#main").classList.remove("drawer");$("#board").style.gridAutoColumns="";document.querySelectorAll(".bp.sel").forEach(x=>x.classList.remove("sel"));setTimeout(updNav,0)}
function setView(v,save){
  VIEW=v==="board"?"board":"list";if(save!==false)ls.set("view",VIEW);
  const m=$("#main");const b=VIEW==="board";
  m.classList.toggle("vboard",b);document.body.classList.toggle("vboard",b);m.classList.remove("showlog");if(!b){m.classList.remove("drawer");$("#board").style.gridAutoColumns=""}
  $("#vList").setAttribute("aria-selected",String(!b));$("#vBoard").setAttribute("aria-selected",String(b));
  $("#bLogClose").style.display=(b||innerWidth<=1180)?"inline-flex":"none";
  if(!S)return;
  boardHtml="";renderBoard();
  if(!b){renderGroups();const row=SEL&&[...document.querySelectorAll(".grp")].find(x=>x.dataset.r===SEL.root&&x.dataset.g===SEL.group);if(row)row.scrollIntoView({block:"nearest"})}
}
$("#vList").innerHTML=IC.list+`<span class="lb">リスト</span>`;$("#vBoard").innerHTML=IC.cols+`<span class="lb">会場ボード</span>`;
$("#vList").onclick=()=>setView("list");$("#vBoard").onclick=()=>setView("board");
$("#bDClose").innerHTML=IC.x+"閉じる";$("#bDClose").onclick=closeDrawer;
$("#bqi").outerHTML=IC.search;
$("#bq").addEventListener("input",renderBoard);
function bpRow(r,g){
  const name=g.key.split("/").pop();const st=recvState(g);
  const isSel=drawerOpen()&&SEL&&SEL.root===r.id&&SEL.group===g.key;
  const sti=stIcon(st);
  const cps=OPON()&&g.cp?opDests().map(d=>g.cp[d.id]?cpPill(d.label,g.cp[d.id]):"").join(""):"";
  const cats=Object.entries(g.cats||{}).filter(([c])=>!(g.ana&&c==="PPT")).sort((a,b)=>b[1]-a[1]).slice(0,2).map(([c,n])=>`<span class="chip c-${esc(c)}">${esc(c)}${n>1?" "+n:""}</span>`).join("");
  const fc=flagChips(g,3);
  const tags=st==="none"?`<span class="tag t-dim">未受付</span>`+fc:st==="drop"?`<span class="tag t-drop">取り下げ</span>`+fc:st==="done"?`<span class="tag t-done">発表終了</span>`+replTag(g)+fc:(!g.files&&!g.pending&&st!=="direct"?`<span class="tag t-dim">データなし</span>`:"")+replTag(g)+cps+fc+anaChips(g.ana)+cats;
  const stl=STL[st]||"";
  const tip=nfc(name)+"\n"+stl+(g.files?` · ${g.files}ファイル · ${fmtSize(g.size)}`:"")+(g.recv_ts?` · 受付 ${dtm(g.recv_ts)}`:"")+(g.repl?` · 差し替え ${g.repl}回`:"")+(g.last_ts?` · 最終変更 ${dtm(g.last_ts)}`:"")+(g.unread?` · 未確認 ${g.unread}`:"")+(g.fl&&g.fl.length?"\n目印: "+g.fl.map(x=>nfc(x[0])).join("、"):"")+(S.ui.os_open&&S.local?"\nダブルクリックでフォルダを開く":"");
  return `<div class="bp st-${st} ${g.unread?"unread":""} ${isSel?"sel":""} ${flashKeys.has(r.id+"|"+g.key)?"flash":""}" data-r="${esc(r.id)}" data-g="${esc(g.key)}" tabindex="0" role="button" title="${esc(tip)}"><span class="sti">${sti}</span><span class="nm">${esc(nfc(name))}</span>${g.unread?`<span class="badge">${g.unread}</span>`:""}${tags?`<span class="tg">${tags}</span>`:""}${progHtmlRow(r,g)}</div>`;
}
function renderBoard(){
  if(VIEW!=="board"||!S)return;
  const el=$("#board");
  const q=nfc($("#bq").value).toLowerCase().trim();const onlyU=$("#bOnlyU").checked,onlyN=$("#bOnlyN").checked;
  const filtering=!!(q||onlyU||onlyN);
  computeVenueColors();
  COLSES={};const nav=[];
  const DAYS=allDays(),ED=effDay(DAYS),TD=todayDay(DAYS,ED);renderDaySel(DAYS,ED);
  const EV=effVenue();let scope=[],h="";
  S.roots.forEach((r,ri)=>{
    if(EV&&EV.slice(0,EV.indexOf("|"))!==r.id)return;
    const y=lay(r);
    const base=(r.groups||[]).filter(g=>g.key!==""&&inVenue(r.id,g.key)&&dayOK(r,g.key,ED));scope=scope.concat(base);
    const byV=new Map();
    for(const g of base){const v=parts(r,g.key).venue;if(!byV.has(v))byV.set(v,[]);byV.get(v).push(g)}
    if(!byV.size){
      if(q)return;
      h+=`<section class="col" data-col="${esc(r.id)}|" style="--vc:${VPAL[ri%VPAL.length]}"><div class="vh"><div class="n">${IC.building}<span class="vn">${esc(nfc(r.label))}</span></div></div><div class="list"><div class="empty">${r.online===false?"接続できません":r.online==null?"確認中…":"演者フォルダがありません"}</div></div></section>`;return}
    for(const v of [...byV.keys()].sort(cmpName)){
      const full=byV.get(v);
      let gs=full;
      if(q)gs=gs.filter(g=>nfc(g.key).toLowerCase().includes(q));
      if(onlyU)gs=gs.filter(g=>g.unread);
      if(onlyN)gs=gs.filter(isTodo);
      if(q&&!gs.length)continue;
      const vc=y.vl>=0?vColor(r.id,v):VPAL[ri%VPAL.length];
      const vname=y.vl>=0?v:r.label;
      const sub=y.vl>=0&&S.roots.length>1?r.label:"";
      const vun=full.filter(g=>g.unread).length,vcp=full.filter(g=>g.pending).length;
      {const a=actv(full);nav.push([r.id+"|"+v,vname,vc,a.filter(isRecv).length,a.length,vun])}
      h+=`<section class="col" data-col="${esc(r.id+"|"+v)}" style="--vc:${vc}"><div class="vh"><div class="n">${IC.building}<span class="vn" title="${esc(nfc(vname))}">${esc(nfc(vname))}</span>${vun?`<span class="badge" title="未確認の演者">${vun}</span>`:""}${COLSES_MARK}</div>${sub?`<div class="rl">${esc(nfc(sub))}</div>`:""}<div class="s"><span>受付</span>${progHtml(full)}${gotHtml(full)}${vcp?`<span class="cpg">${IC.spin}コピー中 ${vcp}</span>`:""}</div>${NOW_MARK}</div><div class="list">`;
      if(!gs.length){h=h.replace(COLSES_MARK,"").replace(NOW_MARK,"");h+=`<div class="empty">${onlyN&&!onlyU?"全員受付済み":onlyU&&!onlyN?"未確認はありません":"該当なし"}</div></div></section>`;continue}
      // セッションごとにまとめる（会場の中で 日 → セッション名 の順。日が2つ以上なら日の区切りを入れる）
      const sessions=new Map();
      for(const g of full){const pp=parts(r,g.key);const k=pp.sesKey;if(!sessions.has(k))sessions.set(k,{all:[],vis:[],day:pp.day,ses:pp.ses});sessions.get(k).all.push(g)}
      for(const g of gs)sessions.get(parts(r,g.key).sesKey).vis.push(g);
      const order=[...sessions.keys()].sort((a,b)=>{const A=sessions.get(a),B=sessions.get(b);return cmpDay(A.day,B.day)||cmpPath(A.ses,B.ses)});
      // 進行状況（今日の分だけ）：開始順に並べて 終了／進行中／次 を決める
      const tl=[];for(const k of order){const x=sessions.get(k);if(DAYS.length&&(!TD||x.day!==TD))continue;const t=sesTime(x.ses);if(t)tl.push({key:k,t})}
      tl.sort((a,b)=>a.t.s-b.t.s);const STS=sesStatus(tl);
      const multiDay=new Set(order.map(k=>sessions.get(k).day)).size>1;
      const colKey=r.id+"|"+v,fks=[];let lastDay=null;
      for(const k of order){
        const x=sessions.get(k);if(!x.vis.length)continue;
        x.vis.sort((a,b)=>cmpPath(a.key,b.key));
        if(multiDay&&x.day!==lastDay){lastDay=x.day;h+=`<div class="dsep ${x.day&&x.day===TD?"today":""}">${esc(nfc(x.day||"日の指定なし"))}${x.day&&x.day===TD?"<span>今日</span>":""}</div>`}
        if(x.ses||x.day){
          const fk=r.id+"|"+k;fks.push(fk);
          const sf=!filtering&&isFold(fk);const sun=x.all.filter(g=>g.unread).length;
          const sflash=sf&&x.all.some(g=>flashKeys.has(r.id+"|"+g.key));
          const tt=sesTime(x.ses),st=STS.get(k);
          const label=x.ses||x.day;
          h+=`<div class="ses ${sf?"fold":""} ${sflash?"flashh":""} ${st?"st-"+st.st:""}" data-fold="${esc(fk)}" tabindex="0" role="button" aria-expanded="${!sf}" title="${esc(nfc((x.day&&!multiDay&&y.dl>=0?x.day+" / ":"")+label))}（クリックで${sf?"開く":"閉じる"}）"><span class="chev">${IC.down}</span><span class="sn">${label.split("/").map(t=>esc(nfc(t))).join('<span class="sep"> › </span>')}</span>${x.all.some(g=>g.pending)?`<span class="pdot" title="コピー中"></span>`:""}${sun?`<span class="badge" title="未確認の演者">${sun}</span>`:""}${progHtml(x.all)}${tt?`<span class="tl">${timeChip(tt)}${statusHtml(st,x.all)}</span>`:""}${st&&st.st==="live"&&st.pct!=null?`<span class="tbar"><i style="width:${st.pct.toFixed(1)}%"></i></span>`:""}</div>`;
          if(sf)continue;
        }
        h+=x.vis.map(g=>bpRow(r,g)).join("");
      }
      // 会場の見出しに「いま／次」
      {let nowh="";const live=tl.find(z=>STS.get(z.key).st==="live"),nx=tl.find(z=>STS.get(z.key).st==="next");
        const nm=z=>esc(nfc(sessions.get(z.key).ses.split("/").pop()));
        if(live){const a=STS.get(live.key);nowh=`<div class="nowl live"><b>いま</b><span class="nn">${nm(live)}</span>${a.rem!=null?`<span class="nr">残り${fmtDur(a.rem)}</span>`:""}</div>`}
        else if(nx){const a=STS.get(nx.key);nowh=`<div class="nowl"><b>次</b><span class="nn">${nm(nx)}</span><span class="nr">${fmtT(a.s)}〜（あと${fmtDur(Math.max(0,a.until))}）</span></div>`}
        else if(tl.length)nowh=`<div class="nowl done"><b>本日のセッションは終了</b></div>`;
        h=h.replace(NOW_MARK,()=>nowh)}
      COLSES[colKey]=fks;
      if(fks.length&&!filtering){const allF=fks.every(isFold);
        const btn=`<button class="ghost cf" data-colfold="${esc(colKey)}" title="この会場のセッションを${allF?"すべて開く":"すべて閉じる"}">${allF?IC.expand:IC.collapse}</button>`;h=h.replace(COLSES_MARK,()=>btn)}
      h=h.replace(COLSES_MARK,"");
      h+=`</div></section>`;
    }
  });
  if(!S.roots.length)h=`<div class="empty"><div class="ico">${IC.folder}</div><b>監視フォルダがありません</b>［設定］から学会名フォルダを追加してください。</div>`;
  else if(!h)h=`<div class="empty"><div class="ico">${IC.search}</div><b>該当なし</b>検索の文字や絞り込みを変えてください。</div>`;
  if(h!==boardHtml){
    const sv={};el.querySelectorAll(".col").forEach(c=>{const l=c.querySelector(".list");if(l)sv[c.dataset.col]=l.scrollTop});
    const sx=el.scrollLeft;el.innerHTML=h;boardHtml=h;
    el.querySelectorAll(".col").forEach(c=>{const l=c.querySelector(".list");if(l&&sv[c.dataset.col])l.scrollTop=sv[c.dataset.col]});
    el.scrollLeft=sx;
  }
  renderNav(nav);
  {let anyT=false;if(DAYS.length&&!TD)for(const r of S.roots){for(const g of (r.groups||[])){if(g.key&&sesTime(parts(r,g.key).ses)){anyT=true;break}}if(anyT)break}
    $("#bdayhint").style.display=anyT?"":"none"}
  if(followKey){const k=followKey;followKey=null;const row=[...el.querySelectorAll(".bp")].find(x=>x.dataset.r+"|"+x.dataset.g===k);
    if(row)revealInBoard(row);
    else{const i=k.indexOf("|"),fk=foldKeysOf(k.slice(0,i),k.slice(i+1)).slice(-1)[0];   // 閉じたセッションなら、その見出しまで
      const sh=fk&&[...el.querySelectorAll(".ses[data-fold]")].find(x=>x.dataset.fold===fk);if(sh)revealInBoard(sh)}}
  const scp=actv(scope.filter(g=>g.key!==""));const n=scp.filter(isRecv).length,t=scp.length,pct=t?Math.round(n*100/t):0;
  $("#bTot").innerHTML=`全体 <b>受付 ${n}/${t}</b><span class="prog ${t&&n===t?"done":n?"":"zero"}"><span class="bar"><i style="width:${pct}%"></i></span>${pct}%</span>`;
  const cpn=scp.filter(g=>g.pending).length,unn=scp.filter(g=>g.unread).length;
  $("#bCp").innerHTML=`コピー中 <b>${cpn}</b>`;$("#bUn").innerHTML=`未確認 <b>${unn}</b>`;
}
let COLSES={};const COLSES_MARK="<!--cf-->",NOW_MARK="<!--now-->";
/* 日の切り替え（ボードとリストで共通。PCごとに保存） */
function renderDaySel(days,ed){
  const show=days.length>0;
  const h=`<option value="">すべての日</option>`+days.map(d=>`<option value="${esc(d)}" ${d===ed?"selected":""}>${esc(nfc(d))}${isTodayLabel(d)?"（今日）":""}</option>`).join("")+(ed&&!days.includes(ed)?`<option value="${esc(ed)}" selected>${esc(nfc(ed))}（現在なし）</option>`:"");
  for(const sel of [$("#bday"),$("#lday")]){sel.style.display=show?"":"none";if(sel.dataset.h!==h){sel.innerHTML=h;sel.dataset.h=h}if(sel.value!==ed)sel.value=ed}}
function setDay(v){DAYSEL=v?{v,at:ymd()}:null;ls.set("day",DAYSEL);boardHtml="";renderBoard();renderGroups();renderDaySel(allDays(),effDay())}
$("#bday").addEventListener("change",()=>setDay($("#bday").value));
$("#lday").addEventListener("change",()=>setDay($("#lday").value));
/* セッションの開閉（このPCに保存。リスト表示の開閉と共通） */
function toggleSes(fk){setFold(fk,!isFold(fk));renderBoard();renderGroups();
  const n=[...document.querySelectorAll("#board .ses[data-fold]")].find(x=>x.dataset.fold===fk);if(n)n.focus({preventScroll:true})}
function setFoldMany(keys,v){keys.forEach(k=>{if(v)FOLD[k]=1;else delete FOLD[k]});ls.set("fold",FOLD);renderBoard();renderGroups()}
function boardSesKeys(){const out=[];Object.values(COLSES).forEach(a=>out.push(...a));return out}
$("#board").addEventListener("click",e=>{
  const dh=dblHit(e);if(dh){openFolderOS(dh.r,dh.g);return}
  const cf=e.target.closest("[data-colfold]");if(cf){const ks=COLSES[cf.dataset.colfold]||[];setFoldMany(ks,!ks.every(isFold));return}
  const f=e.target.closest(".ses[data-fold]");if(f){toggleSes(f.dataset.fold);return}
  const d=e.target.closest(".bp");if(!d)return;
  noteClick(e,d.dataset.r,d.dataset.g);selectGroup(d.dataset.r,d.dataset.g)});
$("#board").addEventListener("keydown",e=>{if(e.key!=="Enter"&&e.key!==" ")return;
  const f=e.target.closest(".ses[data-fold]");if(f){e.preventDefault();toggleSes(f.dataset.fold);return}
  const d=e.target.closest(".bp");if(d){e.preventDefault();selectGroup(d.dataset.r,d.dataset.g)}});
/* 演者をダブルクリック → Explorer / Finder でそのフォルダを開く（設定で「Explorer / Finder で開く」がオンのときだけ） */
function openFolderOS(root,group){
  if(!S.local){toast("フォルダを開くのは監視PCでのみできます",4000);return}
  if(!S.ui.os_open){toast("ダブルクリックでフォルダを開くには、［設定］→「Explorer / Finder で開く」をオンにしてください（会場側への影響を避けるため、通常はオフです）",7000);return}
  openOS(root,group);toast("フォルダを開いています…",1800)}
/* 1回目のクリックで画面が書き換わっても判定できるよう、「同じ演者を0.45秒以内に2回クリック」でダブルクリックとみなす */
let LASTCLK=null;
function dblHit(e){const c=LASTCLK;if(!c)return null;if(Date.now()-c.t<450&&Math.abs(e.clientX-c.x)<8&&Math.abs(e.clientY-c.y)<8){LASTCLK=null;return c}return null}
function noteClick(e,r,g){LASTCLK={r,g,t:Date.now(),x:e.clientX,y:e.clientY}}
$("#bOpenAll").innerHTML=IC.expand+"開く";$("#bCloseAll").innerHTML=IC.collapse+"閉じる";
$("#bOpenAll").onclick=()=>setFoldMany(boardSesKeys(),false);
$("#bCloseAll").onclick=()=>setFoldMany(boardSesKeys(),true);
/* ---------- 横スクロール：会場ナビ・ホイール・←→キー ---------- */
let navHtml="";
function renderNav(nav){
  const h=nav.length>1?nav.map(([k,name,vc,n,t,un])=>`<button class="vchip" data-goto="${esc(k)}" style="--vc:${vc}" title="${esc(nfc(name))} へ移動"><i></i>${esc(nfc(name))}<span class="c ${t&&n===t?"done":""}">${n}/${t}</span>${un?`<span class="badge">${un}</span>`:""}</button>`).join(""):"";
  if(h!==navHtml){$("#bchips").innerHTML=h;navHtml=h}
  updNav();
}
function colStep(){const c=$("#board .col");return c?c.getBoundingClientRect().width+12:300}
function updNav(){
  const bd=$("#board"),nv=$("#bnav");if(!bd||!nv)return;
  const over=VIEW==="board"&&bd.scrollWidth>bd.clientWidth+4&&navHtml!=="";
  nv.classList.toggle("on",over);if(!over)return;
  const br=bd.getBoundingClientRect(),lim=drawerOpen()?Math.min(br.right,innerWidth-$("#center").offsetWidth):br.right;
  const vis=new Set();bd.querySelectorAll(".col").forEach(c=>{const r=c.getBoundingClientRect();if(r.right>br.left+40&&r.left<lim-40)vis.add(c.dataset.col)});
  let first=null;document.querySelectorAll("#bchips .vchip").forEach(b=>{const on=vis.has(b.dataset.goto);b.classList.toggle("vis",on);if(on&&!first)first=b});
  $("#bPrev").disabled=bd.scrollLeft<=2;$("#bNext").disabled=bd.scrollLeft+bd.clientWidth>=bd.scrollWidth-2;
}
function scrollCols(dir){const bd=$("#board");bd.scrollBy({left:dir*colStep(),behavior:"smooth"})}
$("#bPrev").innerHTML=IC.chevL;$("#bNext").innerHTML=IC.chev;
$("#bPrev").onclick=()=>scrollCols(-1);$("#bNext").onclick=()=>scrollCols(1);
$("#bchips").addEventListener("click",e=>{const b=e.target.closest("[data-goto]");if(!b)return;
  const c=[...document.querySelectorAll("#board .col")].find(x=>x.dataset.col===b.dataset.goto);
  if(c){const bd=$("#board");bd.scrollTo({left:Math.max(0,c.offsetLeft-bd.offsetLeft-16),behavior:"smooth"})}});
let navRaf=0;$("#board").addEventListener("scroll",()=>{if(navRaf)return;navRaf=requestAnimationFrame(()=>{navRaf=0;updNav()})},{passive:true});
window.addEventListener("resize",()=>updNav());
/* 列の中（演者の一覧）以外でホイールを回すと横に動く。列の中は今まで通り縦スクロール */
$("#board").addEventListener("wheel",e=>{if(e.ctrlKey||e.target.closest(".list"))return;
  if(Math.abs(e.deltaY)>Math.abs(e.deltaX)){const bd=$("#board");if(bd.scrollWidth>bd.clientWidth){bd.scrollLeft+=e.deltaY;e.preventDefault()}}},{passive:false});
document.addEventListener("keydown",e=>{
  if(VIEW!=="board"||e.ctrlKey||e.altKey||e.metaKey||(e.key!=="ArrowLeft"&&e.key!=="ArrowRight"))return;
  if(e.target.closest("input,textarea,select,#center")||$("#modal").classList.contains("open"))return;
  e.preventDefault();scrollCols(e.key==="ArrowLeft"?-1:1)});
setView(VIEW,false);

/* ---------- folder ---------- */
function selectGroup(root,group,auto){
  SEL={root,group};ls.set("sel",SEL);
  if(unfold(root,group)){renderGroups();if(VIEW==="board"){boardHtml="";renderBoard()}}
  document.querySelectorAll(".grp.sel,.bp.sel").forEach(x=>x.classList.remove("sel"));
  const row=[...document.querySelectorAll(".grp")].find(x=>x.dataset.r===root&&x.dataset.g===group);if(row){row.classList.add("sel");if(VIEW==="list")row.scrollIntoView({block:"nearest"})}
  if(VIEW==="board"){openDrawer();const b=[...document.querySelectorAll(".bp")].find(x=>x.dataset.r===root&&x.dataset.g===group);if(b){b.classList.add("sel");revealInBoard(b)}}
  loadFolder(true);
  if(S.local&&(!auto||document.hasFocus()))api("/api/seen",{root,group}).then(refresh).catch(()=>{});
}
async function loadFolder(scrollTop){
  if(!SEL)return;const want=SEL.root+"|"+SEL.group;let res;
  try{res=await api(`/api/folder?root=${encodeURIComponent(SEL.root)}&group=${encodeURIComponent(SEL.group)}`)}
  catch(e){if(!SEL||SEL.root+"|"+SEL.group!==want)return;F=null;delete foldEl().dataset.h;foldEl().innerHTML=`<div class="empty">${esc(e.message)}</div>`;return}
  if(!SEL||SEL.root+"|"+SEL.group!==want)return;      // 速く続けて選んだとき、前の演者の結果で上書きしない
  F=res;
  const el=$("#fold");const st=el.scrollTop;renderFolder();el.scrollTop=scrollTop?0:st;
}
/* フォルダ表示の書き込み先（受付アプリでは上に受付パネルがあるので #foldbody に書く） */
function foldEl(){return $("#foldbody")||$("#fold")}
function renderFolderEmpty(){delete foldEl().dataset.h;foldEl().innerHTML=`<div class="empty" style="padding-top:90px"><div class="ico">${IC.folder}</div><b>演者フォルダを選択</b>左の一覧か通知をクリックすると、<br>その演者フォルダの中身と解析結果がここに表示されます。<br><br><span style="color:var(--dim);font-size:12.5px">NAS上のファイルは書き換えません（一覧・属性の取得と、PowerPoint解析のための読み取りのみ）</span></div>`}
function sortKey(p,isDir){const s=p.split("/");return s.map((x,i)=>((i<s.length-1||isDir)?"0":"1")+x)}
function cmpKeys(a,b){for(let i=0;i<Math.min(a.length,b.length);i++){if(a[i]!==b[i]){if(a[i][0]!==b[i][0])return a[i][0]<b[i][0]?-1:1;return cmpName(a[i].slice(1),b[i].slice(1))}}return a.length-b.length}

function vfmtLine(v){const f=v.fmt;if(!f)return"";
  const parts=[f.container,f.video,f.audio&&("音声 "+f.audio),f.res].filter(Boolean).map(x=>esc(x)).join(" · ");
  const cls=f.v==="bad"?"o-del":f.v==="warn"?"o-mod":f.v==="unk"?"":"o-add";
  const lab=f.v==="bad"?"再生できない可能性大":f.v==="warn"?"要試写":f.v==="unk"?"形式不明":"再生OK（H.264等）";
  return `<span class="vfmt">形式：${parts||"—"}　<b class="${cls}">${lab}</b>${f.why?`<br><span class="${cls}">${esc(f.why)}</span>`:""}</span>`}
function vline(v){
  const st={here:["同じフォルダにあり","o-add"],missing:["見つかりません","o-del"],abs:["発表者PCのパス（会場PCでは再生できない可能性大）","o-del"],unc:["ネットワーク上のパス","o-mod"],online:["ネット接続が必要","o-mod"]};
  if(v.kind==="embed")return `<span class="sub">${sl(v.s)}　埋め込み ${esc(v.name)}${v.size?" · "+fmtSize(v.size):""}${vfmtLine(v)}</span>`;
  const x=st[v.st]||["外部リンク","o-mod"];
  return `<span class="sub">${sl(v.s)}　<b class="${x[1]}">${v.kind==="online"?(v.av==="audio"?"オンライン音声":"オンライン動画"):(v.av==="audio"?"リンク音声":"リンク動画")}</b> ${esc(nfc(v.target||v.name))} — <span class="${x[1]}">${x[0]}</span>${vfmtLine(v)}</span>`;
}
/* 動画：問題のあるもの（再生NG・要試写・形式不明・リンク切れなど）を先に。本数が多いときは再生OKの分を折りたたむ */
const vProb=v=>!!((v.fmt&&v.fmt.v!=="ok")||(v.kind==="embed"&&!v.fmt)||(v.kind!=="embed"&&v.st!=="here"));
function videoRow(a,key){const vs=a.video||[],nv=a.n_video!=null?a.n_video:vs.length;
  if(!nv)return["動画","t-dim","なし",""];
  const cnt=k=>vs.filter(v=>v.fmt&&v.fmt.v===k).length;const nb=cnt("bad"),nw=cnt("warn"),nu=cnt("unk");
  const nl=vs.filter(v=>v.kind!=="embed").length,nlb=vs.filter(v=>v.kind!=="embed"&&(v.st==="missing"||v.st==="abs")).length;
  const sum=[nb&&`再生できない形式 ${nb}`,nw&&`要試写 ${nw}`,nu&&`形式不明 ${nu}`,nlb&&`リンク切れ ${nlb}`].filter(Boolean).join("・");
  const cls=nb||nlb?"t-bad":nw||nu||nl?"t-warn":"t-info";
  const prob=vs.filter(vProb),ok=vs.filter(v=>!vProb(v));
  let body;
  if(vs.length<=10)body=vs.map(vline).join("");
  else{body=prob.map(vline).join("");
    if(ok.length)body+=`<details class="vok" data-k="${esc(key||"")}"${prob.length?"":" open"}><summary>${prob.length?`問題のない動画 ${ok.length}本（再生OK）を表示`:`すべて再生OK（${ok.length}本）`}</summary>${ok.map(vline).join("")}</details>`}
  if(nv>vs.length)body+=`<span class="sub">ほか ${nv-vs.length}本（表示を省略）</span>`;
  return["動画",cls,`あり ${nv}${sum?"（"+sum+"）":""}`,body]}
function autoText(auto){const m=new Map();auto.forEach(([s,sec])=>{if(!m.has(sec))m.set(sec,[]);m.get(sec).push(s)});return [...m].map(([sec,ss])=>`${sl(ss)}：${sec}秒`).join("　")}
function anaCard(it){
  const a=it.a;const nm=esc(nfc(it.p));const chip=`<span class="chip c-${esc(it.c)}">${esc(it.c)}</span>`;
  if(a.na)return `<div class="ana"><div class="hd">${chip}<span class="fn">${nm}</span><span class="tag t-dim">${esc(a.na)}</span></div></div>`;
  if(a.pending)return `<div class="ana"><div class="hd">${chip}<span class="fn">${nm}</span><span class="tag t-dim ${a.inuse?"":"copying"}">${a.copying?"コピー完了後に解析":a.inuse?"PowerPointで開かれているため解析待ち（閉じたら自動で解析）":"解析中…"}</span></div></div>`;
  if(!a.ok)return `<div class="ana"><div class="hd">${chip}<span class="fn">${nm}</span><span class="tag t-bad">解析できません</span></div><div class="msg">${esc(a.error||"")}</div></div>`;
  const rows=[];
  rows.push(videoRow(a,it.p));
  if(a.audio&&a.audio.length){const ab=a.audio.filter(v=>v.kind!=="embed"&&(v.st==="missing"||v.st==="abs")).length;
    rows.push(["音声",ab?"t-bad":"t-info",`あり ${a.n_audio!=null?a.n_audio:a.audio.length}${ab?`（リンク切れ ${ab}）`:""}`,a.audio.slice(0,40).map(vline).join("")])}
  const nl=a.n_links!=null?a.n_links:a.links.length;
  let ls2=a.links.slice(0,8).map(l=>`<span class="sub">${sl(l.s)}　${esc(l.url)}</span>`).join("")+(nl>8?`<span class="sub">ほか ${nl-8} 件</span>`:"");
  if(a.other&&a.other.length)ls2+=a.other.slice(0,5).map(o=>`<span class="sub">${sl(o.s)}　<b class="o-mod">外部リンク(${esc(o.type)})</b> ${esc(o.target)}</span>`).join("");
  rows.push(nl||(a.other&&a.other.length)?["ハイパーリンク","t-info",`あり ${nl}`,ls2]:["ハイパーリンク","t-dim","なし",""]);
  rows.push(a.coi.length?["COI","t-ok","あり",a.coi.map(c=>`<span class="sub">${sl([c.s])}　「${esc(nfc(c.text))}」</span>`).join("")]
                       :["COI","t-warn","なし",`<span class="sub">COI・利益相反・ディスクロージャー等の文字が見つかりません（画像で貼られている場合は検出できません）</span>`]);
  if(!a.auto.length)rows.push(["自動送り","t-dim","なし",""]);
  else if(a.use_timings)rows.push(["自動送り","t-warn",`あり ${a.auto.length}枚`,`<span class="sub">${autoText(a.auto)}</span>`]);
  else rows.push(["自動送り","t-dim",`設定あり ${a.auto.length}枚（無効）`,`<span class="sub">「タイミングを使用」がオフのため、スライドショーでは自動で進みません</span>`]);
  if(a.kiosk)rows.push(["クリック無効","t-bad","全スライド",`<span class="sub">「自動プレゼンテーション（キオスク）」設定のため、クリックで進めません</span>`]);
  else if(a.noclick.length){const autoSet=new Set(a.use_timings?a.auto.map(x=>x[0]):[]);const stuck=a.noclick.filter(s=>!autoSet.has(s));
    rows.push(["クリック無効",stuck.length?"t-bad":"t-warn",`あり ${a.noclick.length}枚`,`<span class="sub">${sl(a.noclick)}${stuck.length?`<br><b class="o-del">${sl(stuck)}は自動送りもないため、クリックで先に進めません</b>`:"（自動送りで進みます）"}</span>`])}
  else rows.push(["クリック無効","t-dim","なし",""]);
  const head=`${a.slides}枚${a.hidden&&a.hidden.length?`（非表示 ${sl(a.hidden)}）`:""}`;
  return `<div class="ana"><div class="hd">${chip}<span class="fn">${nm}</span><span class="x">${head}</span></div><table>${rows.map(r=>`<tr><td class="k">${r[0]}</td><td class="v"><span class="tag ${r[1]}">${esc(r[2])}</span>${r[3]}</td></tr>`).join("")}</table></div>`;
}
function renderFolder(){
  const segs=F.group.split("/");const r=rootById(F.root);
  const name=F.group===""?((r&&r.depth>1)?"（演者フォルダより上のファイル）":"（直下のファイル）"):segs[segs.length-1];
  const files=F.items.filter(i=>!i.d&&!i.mk);const size=files.reduce((a,i)=>a+(i.s||0),0);const latest=files.reduce((a,i)=>Math.max(a,i.m||0),0);
  const pend=F.items.filter(i=>i.st==="pending"&&!i.mk).length;
  const cats={};files.forEach(i=>cats[i.c]=(cats[i.c]||0)+1);
  const osName=S.os==="win"?"Explorer":S.os==="mac"?"Finder":"ファイラー";
  const fv=venueOf(F.root,F.group);
  let h=`<div class="fh"><div class="crumb"><span>${esc(nfc(F.label))}</span>${segs.length>1?segs.slice(0,-1).map((s,i)=>r&&i===lay(r).vl&&fv?`${IC.chev}<span class="vbadge" style="--vc:${vColor(F.root,fv)}">${IC.building}${esc(nfc(s))}</span>`:`${IC.chev}<b>${esc(nfc(s))}</b>`).join(""):""}</div>
    <h1>${esc(nfc(name))}</h1>
    <div class="facts">${F.group===""?"":(()=>{const rr=rootById(F.root);const gg=rr&&(rr.groups||[]).find(x=>x.key===F.group);
      const st=pend?"copying":gg?recvState(gg):(files.length?"recv":"none");
      return `<span class="rtag ${st}">${stIcon(st)}${STL[st]||""}</span>${gg?flagChips(gg):""}`})()}<span>${files.length} ファイル</span><span>${fmtSize(size)}</span>${latest?`<span>最終更新 ${dtm(latest)}</span>`:""}${F.track&&F.track.recv?`<span>受付 ${dtm(F.track.recv)}</span>`:""}${F.track&&F.track.n?`<span class="tag t-repl">差し替え ${F.track.n}回（最終 ${dtm(F.track.last)}）</span>`:""}${pend?`<span class="copying">● コピー中/確定待ち ${pend}</span>`:""}${(()=>{const rr=rootById(F.root);const gg=rr&&(rr.groups||[]).find(x=>x.key===F.group);return rr&&gg?progHtmlRow(rr,gg):""})()}</div>
    <div class="acts">${S.local&&S.ui.os_open?`<button id="bOpen" title="NAS上のフォルダを${osName}で開く">${IC.ext}${osName}で開く</button>`:""}<button id="bCopy">${IC.copy}パスをコピー</button>
      ${Object.entries(cats).sort((a,b)=>b[1]-a[1]).map(([c,n])=>`<span class="chip c-${esc(c)}">${esc(c)} ${n}</span>`).join("")}</div>
    <div class="pathline">${esc(nfc(F.path))}</div></div>`;
  if(!F.exists&&F.group!==""){h+=`<div class="gone">このフォルダは現在NAS上に見つかりません（削除・名前変更された可能性）。${F.op?"コピー先のファイルは消していません。":""}</div>`}
  const memo=F.memo||[];
  if(memo.length)h+=`<div class="sec"><h3>メモ<small>演者フォルダの中のテキスト（.txt）</small></h3>`+memo.map(m=>m.more?`<div class="memo-more">ほか ${m.more}個の .txt（表示を省略）</div>`:
    `<div class="memo"><div class="mh"><b>${esc(nfc(m.p))}</b><span>${m.m?dtm(m.m):""}</span></div>${m.pending?`<div class="mb dim">受信中（受け取りが終わると表示します）</div>`:m.error!=null?`<div class="mb dim">読めませんでした：${esc(m.error)}</div>`:
      `<pre class="mb">${esc(m.text)||'<span class="dim">（空のファイル）</span>'}</pre>${m.trunc?`<div class="mb dim">長いため途中まで表示しています</div>`:""}`}</div>`).join("")+`</div>`;
  const fd=F.op?F.op.dests.filter(d=>d.enabled):[];
  if(fd.length){
    h+=`<div class="sec"><h3>コピー先<small>受信が完了したら自動でコピーします（NASには書き込みません）</small></h3><div class="evlist">`+fd.map(d=>{
      const x=d.state?CPL[d.state]:null;const tg=x?`<span class="tag ${x[1]==="ok"?"t-ok":x[1]==="bad"?"t-bad":x[1]==="dim"?"t-dim":"t-warn"} ${x[1]==="run"?"copying":""}">${esc(x[0])}</span>`:`<span class="tag t-dim">${files.length?"確認中":"ファイルなし"}</span>`;
      return `<div class="evc dest"><b>${esc(d.label)}</b>${tg}<span style="flex:1"></span><button class="ghost" data-cpath="${esc(d.path)}">${IC.copy}パスをコピー</button><div class="pathline">${esc(nfc(d.path))}</div></div>`}).join("")+`</div></div>`;
  }
  const ana=F.items.filter(i=>i.a).sort((a,b)=>cmpPath(a.p,b.p));
  if(ana.length)h+=`<div class="sec"><h3>PowerPoint 解析<small>動画・リンク・COI・自動送り・クリック無効</small></h3>${ana.map(anaCard).join("")}</div>`;
  if(F.events.length){
    h+=`<div class="sec"><h3>最近の変更</h3><div class="evlist">`+F.events.slice(0,8).map(e=>{
      const items=(e.items||[]).slice(0,30).map(it=>{const o=OPS[it.op]||["·","",""];
        const nm=(it.op==="rename"||it.op==="folder_rename")?`${esc(nfc(it.path))} <span class="x">→</span> ${esc(nfc(it.to))}`:esc(nfc(it.path));
        const sz=it.op==="mod"&&it.old_size!=null?`${fmtSize(it.old_size)} → ${fmtSize(it.size)}`:it.size!=null?fmtSize(it.size):"";
        return `<li><span class="op o-${o[1]}" title="${o[2]}">${o[0]}</span><span class="fn">${nm}</span><span class="x">${sz}</span></li>`}).join("");
      const more=(e.n_items||0)>30?`<li><span class="op"></span><span class="x">ほか ${e.n_items-30} 件</span></li>`:"";
      return `<div class="evc ${e.u?"u":""}"><div class="top">${kindPill(e.kind)}${e.repl?`<span class="kind k-repl">差し替え ${e.repl}回目</span>`:""}<span class="t">${dtm(e.ts)} (${ago(e.ts)})</span>${e.while_stopped?`<span class="ws">停止中の変更</span>`:""}<span style="font-size:12px">${esc(e.summary)}</span></div>${items||more?`<ul>${items}${more}</ul>`:""}</div>`}).join("")+`</div></div>`;
  }
  const rows=F.items.map(i=>Object.assign({k:sortKey(i.p,i.d)},i)).sort((a,b)=>cmpKeys(a.k,b.k));
  const nmk=F.items.filter(i=>i.mk).length;
  h+=`<div class="sec"><h3>ファイル<small>${files.length}件${nmk?`（ほかに目印 ${nmk}）`:""}</small></h3>`;
  if(!rows.length){h+=`<div class="tcard"><div class="empty" style="padding:28px">空のフォルダです</div></div></div>`}
  else{
    h+=`<div class="tcard"><table class="files"><thead><tr><th>名前</th><th>種類</th><th style="text-align:right">サイズ</th><th>更新日時</th><th>状態</th>${fd.length?"<th>コピー</th>":""}</tr></thead><tbody>`;
    const now=Date.now()/1000;
    h+=rows.map(i=>{const dep=i.p.split("/").length-1;const nm=i.p.split("/").pop();
      const s=i.st?ST[i.st]:null;const fresh=i.ct&&now-i.ct<1800;
      const cls=(i.d?"dir ":"")+(i.mk?"mkrow ":"")+(i.st==="pending"?"pend":(s&&fresh?"hl-"+i.st:""));
      return `<tr class="${cls}"><td class="nm" style="padding-left:${8+dep*16}px">${i.d?"▸ ":""}${esc(nfc(nm))}${i.mk?` <span class="tag ${MKC[i.mk]||"t-dim"}" title="ファイル名から判断した目印（${MKR[i.mk]||""}）。データとしては数えません">目印：${esc(nfc(i.ml||""))}</span>`:""}</td><td>${i.d?"":i.mk?`<span class="chip">目印</span>`:`<span class="chip c-${esc(i.c)}">${esc(i.c)}</span>`}</td><td class="num">${i.d?"":fmtSize(i.s)}</td><td class="tm">${i.m?dtm(i.m):""}</td><td>${s?`<span class="stl o-${s[1]} ${i.st==="pending"?"copying":""}">${s[0]}${i.ct?" "+hms(i.ct):""}</span>`:""}</td>${fd.length?`<td style="white-space:nowrap">${i.d?"":fd.map(d=>i.cp&&i.cp[d.id]?cpPill(d.label,i.cp[d.id][0],i.cp[d.id][1]):"").join(" ")}</td>`:""}</tr>`}).join("");
    h+=`</tbody></table></div></div><div style="height:32px"></div>`;
  }
  /* 更新のたびに作り直すと、開いていた「問題のない動画」が閉じ、スクロール位置も戻ってしまう：中身が同じなら作り直さない */
  const fe=foldEl();
  if(fe.dataset.h===h&&fe.childElementCount)return;
  const openK=new Map([...fe.querySelectorAll("details[data-k]")].map(d=>[d.dataset.k,d.open]));
  fe.innerHTML=h;fe.dataset.h=h;
  fe.querySelectorAll("details[data-k]").forEach(d=>{if(openK.has(d.dataset.k))d.open=openK.get(d.dataset.k)});
  const bo=$("#bOpen");if(bo)bo.onclick=()=>openOS(F.root,F.group);
  $("#bCopy").onclick=()=>{copyText(F.path).then(()=>toast("パスをコピーしました"),()=>toast("コピーできませんでした"))};
  document.querySelectorAll("[data-cpath]").forEach(b=>b.onclick=()=>copyText(b.dataset.cpath).then(()=>toast("コピー先のパスをコピーしました"),()=>toast("コピーできませんでした")));
}
/* クリップボード（LANの他の端末から http で開いたときは navigator.clipboard が使えないので、昔の方法で） */
function copyText(t){if(navigator.clipboard&&window.isSecureContext)return navigator.clipboard.writeText(t);
  return new Promise((ok,ng)=>{const a=document.createElement("textarea");a.value=t;a.style.position="fixed";a.style.opacity="0";document.body.appendChild(a);a.select();
    let r=false;try{r=document.execCommand("copy")}catch(e){}a.remove();r?ok():ng()})}
function openOS(root,group){api("/api/open",{root,rel:group}).catch(e=>toast(e.message,5000))}

/* ---------- header buttons ---------- */
$("#bAll").onclick=()=>api("/api/seen",{all:true}).then(refresh).catch(e=>toast(e.message));
$("#bTest").onclick=async()=>{
  if(OPON()){toast("会場オペレーターモードでは、スライドショーの邪魔にならないよう通知と音は出しません",6000);return}
  unlockAudio();
  if("Notification" in window&&Notification.permission==="default")await askPerm();
  chime(false);
  if("Notification" in window&&Notification.permission==="granted"){const n=new Notification("PADDOCK SCOUT テスト通知",{body:"この通知が見えていれば設定OKです",tag:"sw-test",silent:!!S.ui.sound});n.onclick=()=>{window.focus();n.close()}}
  else toast("通知が許可されていません（音のみ再生）",4000);
};
$("#bCfg").onclick=()=>openCfg();
/* 終了（コンソールを出さずに起動したときは、これで止める） */
$("#bQuit").onclick=async()=>{if(!S||!S.local){toast("終了は、このアプリを動かしているPCでのみできます");return}
  if(!confirm("アプリを終了しますか？"))return;
  try{await api("/api/quit",{})}catch(e){if(!(e instanceof TypeError)){toast(e.message,6000);return}}
  document.body.innerHTML='<div style="display:grid;place-items:center;height:100vh;color:#a1a1aa;font:15px sans-serif">終了しました。このウィンドウを閉じてください。</div>';setTimeout(()=>{try{window.close()}catch(e){}},600)};

/* ---------- settings ---------- */
let CFG=null,DEF=null;
async function openCfg(){
  if(!S.local){toast("設定は監視PCでのみ変更できます");return}
  const j=await api("/api/config");CFG=JSON.parse(JSON.stringify(j.config));DEF=j.defaults;CFG._data=j.data_dir;renderCfg();$("#modal").classList.add("open");
}
function closeCfg(){$("#modal").classList.remove("open")}
function depthSel(v,id){return `<select ${id?`id="${id}"`:""} data-k="depth" title="演者フォルダの階層">${[1,2,3,4,5,6].map(n=>`<option value="${n}" ${n==v?"selected":""}>階層 ${n}</option>`).join("")}</select>`}
const OPAPP=APPKIND==="operator";
function renderCfg(){
  const c=CFG;
  if(OPAPP){c.op=c.op||{enabled:false,root:"",venue:"",dests:[],max_mbps:0};if(!c.op.dests.length)c.op.dests=[{label:"メイン",path:"",enabled:true},{label:"バックアップ",path:"",enabled:true}]}c.op=c.op||{enabled:false,root:"",venue:"",dests:[],max_mbps:0};const nk=[["incoming","受信開始（コピー中にすぐ知らせる）"],["folder_new","新しい演者フォルダ"],["add","ファイル追加"],["mod","ファイル更新（差し替え）"],["rename","ファイル名変更"],["del","ファイル削除"],["folder_rename","フォルダ名変更"],["folder_del","フォルダ削除"],["offline","NAS接続断"],["online","NAS復帰"]];
  $("#modal").innerHTML=`<div class="dlg">
  <h2>設定</h2><p class="desc">${OPAPP?"見るNASのフォルダ、この発表PCの会場とコピー先、解析の動作を設定します。":"監視するNASのフォルダ、検出のタイミング、通知と解析の動作を設定します。"}</p>
  <h3>監視フォルダ</h3>
  <div id="rlist">${c.roots.length?c.roots.map((r,i)=>`<div class="rrow" data-i="${i}">
     <input type="text" data-k="label" value="${esc(r.label)}" placeholder="表示名（例: 学会名）">
     <input type="text" class="pth mono" data-k="path" value="${esc(r.path)}">
     ${depthSel(r.depth)}
     <label><input type="checkbox" data-k="enabled" ${r.enabled?"checked":""}>有効</label>
     <button class="ghost" data-act="rebase" title="今の状態を基準にし、未確定の変化を捨てる（通知しない）">基準リセット</button>
     <button class="ghost danger" data-act="del">削除</button></div>`).join(""):`<div class="hint" style="margin:0 0 8px">まだありません</div>`}</div>
  <div class="addrow"><input type="text" id="nPath" class="mono" placeholder="\\\\NASのIP\\共有名\\学会名  /  Z:\\学会名  /  /Volumes/共有名/学会名"><button id="bPick">参照…</button></div>
  <div class="addrow2"><input type="text" id="nLabel" placeholder="表示名（任意）">${depthSel(3,"nDepth")}<button class="pri" id="bAdd">${IC.plus}追加</button></div>
  <p class="hint">「階層」= 監視フォルダから見て演者フォルダが何段目にあるか。<br>
  <b>階層3</b>: 学会名フォルダ／会場／セッション／<b>001_演者名</b>／…（学会名フォルダを登録）<br>
  階層2: 会場フォルダ／セッション／<b>演者</b>　　階層1: セッションフォルダ／<b>演者</b><br>
  NAS側で「読み取り専用のユーザー」を作り、そのユーザーで接続しておくと、誤操作でも書き込めないので確実です。</p>
  ${OPAPP?opSectionHtml(c):""}
  <h3>検出</h3>
  <div class="grid2">
    <span>確認する間隔</span><span><input type="number" id="poll" min="1" max="60" step="1" value="${c.poll_sec}"> 秒</span>
    <span>確定待ち時間</span><span><input type="number" id="settle" min="0" max="300" step="1" value="${c.settle_sec}"> 秒</span>
    <span></span><span class="hint" style="margin:0">コピーが始まった時点で「受信中」をすぐ通知し、サイズ・更新日時がこの秒数変わらなくなったら「追加・更新」に差し替えます（解析結果つき）</span>
  </div>
  <p style="margin:10px 0 0"><label class="lbl"><input type="checkbox" id="rws" ${c.report_while_stopped?"checked":""}>アプリを止めていた間の変更も、起動時に通知する</label></p>
  <h3>PowerPoint 解析</h3>
  <p style="margin:0"><label class="lbl"><input type="checkbox" id="ana" ${c.analyze?"checked":""}>動画・ハイパーリンク・COI・自動送り・クリック無効を解析する</label></p>
  <p class="hint">解析のため .pptx / .ppsx などの中身を「読み取り」ます（書き込みはしません）。Keynote・旧形式(.ppt)は対象外です。</p>
  <p class="hint" style="margin-top:10px">COIとみなす文字（1行1つ・大文字小文字/全角半角は区別しない）</p>
  <textarea id="coi" spellcheck="false">${esc((c.coi_keywords||[]).join("\n"))}</textarea>
  <p class="hint"><button class="ghost" id="bCoiDef">初期値に戻す</button></p>
  <h3>目印のファイル（00_受付済.jpg・17_会場取得.jpg など）</h3>
  <p class="hint" style="margin:0 0 8px">演者フォルダの画像（またはテキスト）ファイルの名前にこの文字が入っていれば、データではなく<b>目印</b>として扱います。全角半角・大文字小文字・空白や「_」は区別せず、先頭の番号（00_ など）があってもかまいません。2つ以上に当てはまるときは長い文字のほうを使います。</p>
  <table class="mkt" id="mkt"><tbody>${(c.marks||[]).map(mkRow).join("")}</tbody></table>
  <p class="hint"><button class="ghost" id="bMkAdd">${IC.plus}行を追加</button> <button class="ghost" id="bMkDef">初期値に戻す</button></p>
  ${OPAPP?`<h3>通知</h3><p class="hint" style="margin:0">このアプリはスライドショーをしている発表PCで使うため、<b>通知も音も出しません</b>（画面の表示だけ更新します）。</p>`:`
  <h3>通知する変化</h3>
  <div class="checks">${nk.map(([k,l])=>`<label><input type="checkbox" data-n="${k}" ${c.notify[k]!==false?"checked":""}>${l}</label>`).join("")}</div>
  <h3>通知の動作</h3>
  <div class="checks" style="flex-direction:column;gap:8px">
    <label><input type="checkbox" id="snd" ${c.ui.sound?"checked":""}>通知音を鳴らす（アプリ独自の音。OSの通知音は鳴らさない）</label>
    <label><input type="checkbox" id="stk" ${c.ui.sticky?"checked":""}>通知を自動で消さない（クリックするまで残す）</label>
    <label><input type="checkbox" id="osOpen" ${c.ui.os_open?"checked":""}>「Explorer / Finder で開く」を使えるようにする（通常はオフ推奨）</label>
    <label style="padding-left:23px"><input type="radio" name="clk" value="app" ${c.ui.click!=="both"?"checked":""}>通知クリック → アプリ内でフォルダの中身を表示（NASに一切触れない）</label>
    <label style="padding-left:23px"><input type="radio" name="clk" value="both" ${c.ui.click==="both"?"checked":""} ${c.ui.os_open?"":"disabled"}>通知クリック → アプリ内表示 ＋ Explorer / Finder でも開く</label>
  </div>
  <p class="hint">※ Explorer / Finder はこのアプリの管理外です。表示設定によってはサムネイル作成のためにファイルを読みに行ったり、Thumbs.db（Windows）や .DS_Store（Mac）をNASに作ったりすることがあります。会場側への影響を完全になくすため、通常はオフのままにしてください。<br>※ 会場の絞り込みと「自動表示」は画面上部・左上で切り替えます（このPCだけの設定）。</p>
  `}
  <h3>無視するファイル名（1行1パターン、* と ? が使えます）</h3>
  <textarea id="ig" spellcheck="false">${esc(c.ignore.join("\n"))}</textarea>
  <p class="hint"><button class="ghost" id="bIgDef">初期値に戻す</button>　設定の保存先: <span class="mono">${esc(c._data||"")}</span></p>
  <div class="err" id="cerr"></div>
  <div class="foot"><span class="hint" style="margin:0">PADDOCK SCOUT v__VERSION__ · © SEVENTHWELL</span><span style="display:flex;gap:8px"><button id="bCancel">キャンセル</button><button class="pri" id="bSave">保存</button></span></div>
  </div>`;
  $("#rlist").oninput=$("#rlist").onchange=e=>{const row=e.target.closest(".rrow");if(!row)return;const r=CFG.roots[+row.dataset.i];const k=e.target.dataset.k;if(!k)return;r[k]=e.target.type==="checkbox"?e.target.checked:k==="depth"?+e.target.value:e.target.value};
  $("#rlist").onclick=e=>{const b=e.target.closest("button");if(!b)return;const i=+b.closest(".rrow").dataset.i;const r=CFG.roots[i];
    if(b.dataset.act==="del"){if(confirm(`「${r.label||r.path}」を監視対象から外しますか？（NAS上のファイルには何もしません）`)){keepForm();CFG.roots.splice(i,1);renderCfg()}}
    if(b.dataset.act==="rebase"){if(!r.id){toast("保存後に使えます");return}api("/api/rebaseline",{root:r.id}).then(()=>toast("次の確認で今の状態を基準にします")).catch(e=>toast(e.message))}};
  $("#bPick").onclick=async()=>{try{const j=await api("/api/pick",{});if(j.path)$("#nPath").value=j.path}catch(e){toast(e.message,5000)}};
  $("#bAdd").onclick=()=>{const p=$("#nPath").value.trim().replace(/^"|"$/g,"");if(!p){toast("パスを入力してください");return}
    keepForm();CFG._np=null;CFG.roots.push({path:p,label:$("#nLabel").value.trim(),depth:+$("#nDepth").value,enabled:true});renderCfg()};
  if(CFG._np){$("#nPath").value=CFG._np.p||"";$("#nLabel").value=CFG._np.l||""}
  $("#bIgDef").onclick=()=>{$("#ig").value=DEF.ignore.join("\n")};
  $("#bCoiDef").onclick=()=>{$("#coi").value=DEF.coi.join("\n")};
  $("#bMkDef").onclick=()=>{$("#mkt tbody").innerHTML=(DEF.marks||[]).map(mkRow).join("")};
  $("#bMkAdd").onclick=()=>{const tb=$("#mkt tbody");tb.insertAdjacentHTML("beforeend",mkRow({w:"",role:"info"}));const ins=tb.querySelectorAll(".mkw");ins[ins.length-1].focus()};
  $("#mkt").onclick=e=>{const b=e.target.closest("[data-mkdel]");if(b)b.closest("tr").remove()};
  if($("#osOpen"))$("#osOpen").onchange=()=>{const b=document.querySelector("input[name=clk][value=both]");b.disabled=!$("#osOpen").checked;if(b.disabled&&b.checked)document.querySelector("input[name=clk][value=app]").checked=true};
  $("#bCancel").onclick=closeCfg;
  $("#bSave").onclick=saveCfg;
  const da=$("#bDAdd");if(da)da.onclick=()=>{keepForm();CFG.op.dests.push({label:"",path:"",enabled:true});renderCfg()};
  if($("#dlist")){
  $("#dlist").oninput=$("#dlist").onchange=e=>{const row=e.target.closest(".drow");if(!row)return;const d=CFG.op.dests[+row.dataset.i];const k=e.target.dataset.k;if(!k)return;d[k]=e.target.type==="checkbox"?e.target.checked:e.target.value};
  $("#dlist").onclick=async e=>{const b=e.target.closest("button");if(!b)return;const i=+b.closest(".drow").dataset.i;
    if(b.dataset.act==="del"){keepForm();CFG.op.dests.splice(i,1);renderCfg()}
    if(b.dataset.act==="pick"){try{const j=await api("/api/pick",{dest:true});if(j.path){CFG.op.dests[i].path=j.path;b.closest(".drow").querySelector("[data-k=path]").value=j.path}}catch(err){toast(err.message,5000)}}};
  }
  const orr=$("#opRoot");
  if(orr){if(!CFG.op.root||!CFG.roots.some((r,i)=>(r.id||"#"+i)===CFG.op.root))CFG.op.root=orr.value;
    orr.onchange=()=>{CFG.op.root=orr.value;CFG.op.venue="";CFG.op.days=[];OPD.dirs=null;loadVenues();opDaysInit()};
    $("#opVenue").onchange=()=>{CFG.op.venue=$("#opVenue").value};loadVenues();opDaysInit()}
}
function opSectionHtml(c){return `
  <h3>このPCの会場とコピー先</h3>
  <p class="hint" style="margin:0 0 6px">自分の会場だけを監視し、NASへの受信が完了した演者フォルダを、下のコピー先（この発表PC・バックアップPCなど）へコピーします。</p>
  <div id="opBox">
    ${c.roots.length?`<div class="grid2" style="margin-top:12px">
      <span>監視フォルダ</span><span><select id="opRoot" ${c.roots.length<2?"disabled":""}>${c.roots.map((r,i)=>`<option value="${esc(r.id||"#"+i)}" ${(r.id||"#"+i)===c.op.root?"selected":""}>${esc(r.label||r.path)}</option>`).join("")}</select></span>
      <span>フォルダの分け方</span><span class="checks" style="flex-direction:column;gap:6px;align-items:flex-start">
        <label><input type="radio" name="opDm" value="0" ${opDayMode(c)?"":"checked"}>学会 → 会場 → …（会場フォルダが直下にある）</label>
        <label><input type="radio" name="opDm" value="1" ${opDayMode(c)?"checked":""}>学会 → 日（DAY1・DAY2…） → 会場 → …（日ごとに分かれている）</label></span>
      <span class="opNoDay">自分の会場</span><span class="opNoDay"><select id="opVenue"><option value="${esc(c.op.venue)}">${esc(c.op.venue||"読み込み中…")}</option></select></span>
      <span class="opDay">日ごとの会場</span><span class="opDay"><div id="opDays"></div>
        <p class="hint" style="margin:6px 0 0"><button class="ghost" id="bDayAdd">${IC.plus}日を追加</button>　1つの日で会場を選ぶと、ほかの日にも同じ名前の会場があれば自動で入ります。</p>
        <p class="hint" style="margin:8px 0 0"><label><input type="checkbox" id="opDayDir" ${c.op.day_dir!==false?"checked":""}>コピー先に日のフォルダ（DAY1 など）を作って分ける</label>（日が違う同じ名前のセッションが混ざらないように。おすすめ）</p></span>
      <span class="opDay">いまの日</span><span class="opDay"><select id="opDay"></select><span class="hint">　メイン画面の上の帯からも切り替えられます</span></span>
      <span>速度の上限</span><span><input type="number" id="opMbps" min="0" max="1000" step="1" value="${c.op.max_mbps||0}"> MB/秒（0 = 制限なし）</span>
    </div>`:`<p class="hint">先に「監視フォルダ」に学会名フォルダを追加してください（追加すると、ここで会場を選べます）。</p>`}
    <p class="hint" style="margin-top:14px">コピー先（最大4か所。メインPC・バックアップPCなど。バックアップPCは共有フォルダのパス \\\\PC名\\共有名\\… で指定）</p>
    <div id="dlist">${c.op.dests.map((d,i)=>`<div class="drow" data-i="${i}">
       <input type="text" data-k="label" value="${esc(d.label)}" placeholder="名前（例: メイン）">
       <input type="text" class="pth mono" data-k="path" value="${esc(d.path)}" placeholder="D:\\発表データ  /  \\\\BACKUP-PC\\共有\\発表データ">
       <button class="ghost" data-act="pick">参照…</button>
       <label><input type="checkbox" data-k="enabled" ${d.enabled?"checked":""}>有効</label>
       <button class="ghost danger" data-act="del">削除</button></div>`).join("")}</div>
    <p class="hint" style="margin-top:0">${c.op.dests.length<4?`<button class="ghost" id="bDAdd">${IC.plus}コピー先を追加</button>`:""}</p>
    <p class="hint">・コピー先には、会場より下（セッション／演者フォルダ）を同じ構成で作ります。<br>
    ・<b>NASには一切書き込みません</b>（読むだけ）。受信中の演者フォルダはコピーせず、NAS上で開かれているファイルにも触れません。<br>
    ・コピー先で<b>開かれているファイル（発表中など）は上書きしません</b>。閉じられてから新しい版に差し替えます。<br>
    ・差し替えた旧版はコピー先の「_差し替え前」フォルダに残します。<b>コピー先のファイルを消すことはありません</b>（NAS側で消えても残します）。<br>
    ・コピー先で編集したファイルは、NAS側が更新されない限り上書きしません。</p>
  </div>`}
const MKROLES=[["recv","受付済にする"],["got","会場取得済にする"],["done","発表終了にする"],["drop","取り下げ（数に入れない）"],["direct","会場直（未受付にしない）"],["warn","注意（黄色のチップ）"],["op","オペが対応（発表者ツール・演台上げなど）"],["info","チップで表示するだけ"]];
function mkRow(m){return `<tr><td><input type="text" class="mkw" value="${esc(m.w||"")}" maxlength="40" spellcheck="false" placeholder="ファイル名に入る文字（例: 動画有）"></td><td style="width:240px"><select class="mkr">${MKROLES.map(([k,l])=>`<option value="${k}" ${m.role===k?"selected":""}>${l}</option>`).join("")}</select></td><td><button class="ghost x" data-mkdel title="この行を削除">${IC.x}</button></td></tr>`}
/* ---- 日ごとに分かれている学会（学会 → DAY1 → 会場 …）：日ごとに会場フォルダを指定する */
const OPD={dirs:null,sub:{},root:""};
function opDayMode(c){return !!(c.op._dm!=null?c.op._dm:(c.op.days||[]).length)}
function opRootPath(){const rr=CFG.roots.find((r,i)=>(r.id||"#"+i)===CFG.op.root);return rr?rr.path:""}
function opJoin(a,b){const sep=a.includes("\\")||/^[A-Za-z]:/.test(a)?"\\":"/";return a.replace(/[\\/]+$/,"")+sep+b}
async function opList(path){return (await api("/api/venues?root=&path="+encodeURIComponent(path))).venues}
async function opDaysInit(){
  const box=$("#opDays");if(!box)return;
  const dm=document.querySelector("input[name=opDm]:checked");const on=dm&&dm.value==="1";
  document.querySelectorAll(".opDay").forEach(x=>x.style.display=on?"":"none");
  document.querySelectorAll(".opNoDay").forEach(x=>x.style.display=on?"none":"");
  document.querySelectorAll("input[name=opDm]").forEach(x=>x.onchange=()=>{CFG.op._dm=x.value==="1";
    const rr=CFG.roots.find((r,i)=>(r.id||"#"+i)===CFG.op.root);
    if(CFG.op._dm&&rr&&rr.depth<4){keepForm();CFG.op._dm=true;rr.depth=rr.depth+1;renderCfg();toast("日のフォルダが1段増えるため、監視フォルダの「階層」を "+rr.depth+" にしました",6000);return}
    opDaysInit()});
  if(!on)return;
  const rp=opRootPath();if(!rp){box.innerHTML=`<span class="hint">先に監視フォルダを選んでください</span>`;return}
  if(OPD.root!==rp){OPD.root=rp;OPD.dirs=null;OPD.sub={}}
  if(!OPD.dirs){box.innerHTML=`<span class="hint">読み込み中…</span>`;
    try{OPD.dirs=await opList(rp)}catch(e){box.innerHTML=`<span class="hint">${esc(e.message)}</span>`;return}}
  if(!(CFG.op.days||[]).length){   // はじめて：日らしいフォルダ（DAY1・1日目・10月23日 など）を並べる
    const ds=OPD.dirs.filter(n=>dayInfo(n));CFG.op.days=(ds.length?ds:OPD.dirs.slice(0,4)).map(n=>({label:n,venue:n+"/"}))}
  await Promise.all(CFG.op.days.map(async d=>{const f=d.venue.split("/")[0];if(f&&!OPD.sub[f]){try{OPD.sub[f]=await opList(opJoin(rp,f))}catch(e){OPD.sub[f]={err:e.message}}}}));
  opDaysRender()}
function opDaysRender(){
  const box=$("#opDays");if(!box)return;
  box.innerHTML=`<table class="optab"><thead><tr><th>日のフォルダ</th><th>その日の自分の会場</th><th></th></tr></thead><tbody>`+CFG.op.days.map((d,i)=>{
    const f=d.venue.split("/")[0],v=d.venue.split("/").slice(1).join("/");const sub=OPD.sub[f];
    const fo=(OPD.dirs||[]).slice();if(f&&!fo.includes(f))fo.push(f);
    const vo=Array.isArray(sub)?sub.slice():[];if(v&&!vo.includes(v))vo.push(v);
    return `<tr data-i="${i}"><td><select data-k="f"><option value="">（選ぶ）</option>${fo.map(x=>`<option value="${esc(x)}" ${x===f?"selected":""}>${esc(nfc(x))}</option>`).join("")}</select></td>
      <td><select data-k="v"><option value="">（選ぶ）</option>${vo.map(x=>`<option value="${esc(x)}" ${x===v?"selected":""}>${esc(nfc(x))}${Array.isArray(sub)&&!sub.includes(x)?"（現在見つかりません）":""}</option>`).join("")}${sub&&sub.err?`<option disabled>${esc(sub.err)}</option>`:""}</select></td>
      <td><button class="ghost danger" data-del>削除</button></td></tr>`}).join("")+`</tbody></table>`;
  const sel=$("#opDay");if(sel){const cur=CFG.op.day;sel.innerHTML=CFG.op.days.filter(d=>d.label).map(d=>`<option ${d.label===cur?"selected":""}>${esc(d.label)}</option>`).join("");sel.onchange=()=>{CFG.op.day=sel.value}}
  box.onchange=async e=>{const tr=e.target.closest("tr");if(!tr)return;const d=CFG.op.days[+tr.dataset.i];
    if(e.target.dataset.k==="f"){const f=e.target.value;const old=d.venue.split("/").slice(1).join("/");d.label=f;d.venue=f+"/";
      if(f&&!OPD.sub[f]){try{OPD.sub[f]=await opList(opJoin(OPD.root,f))}catch(er){OPD.sub[f]={err:er.message}}}
      if(old&&Array.isArray(OPD.sub[f])&&OPD.sub[f].includes(old))d.venue=f+"/"+old;opDaysRender()}
    else{const v=e.target.value;d.venue=d.venue.split("/")[0]+"/"+v;
      if(v)CFG.op.days.forEach(o=>{const f=o.venue.split("/")[0];if(o!==d&&f&&!o.venue.split("/")[1]&&Array.isArray(OPD.sub[f])&&OPD.sub[f].includes(v))o.venue=f+"/"+v});
      opDaysRender()}};
  box.onclick=e=>{const b=e.target.closest("[data-del]");if(!b)return;CFG.op.days.splice(+b.closest("tr").dataset.i,1);opDaysRender()};
  const ba=$("#bDayAdd");if(ba)ba.onclick=()=>{CFG.op.days.push({label:"",venue:""});opDaysRender()}}
async function loadVenues(){
  const sel=$("#opVenue");if(!sel||!CFG.op.root)return;
  const cur=CFG.op.venue,root0=CFG.op.root;let vs=[],err="";
  const rr=CFG.roots.find((r,i)=>(r.id||"#"+i)===root0);
  try{vs=(await api("/api/venues?root="+encodeURIComponent(rr&&rr.id||"")+"&path="+encodeURIComponent(rr?rr.path:""))).venues}catch(e){err=e.message}
  if(!$("#opVenue")||CFG.op.root!==root0)return;     // 待っている間に監視フォルダを選び直した
  let h=`<option value="">（監視フォルダ全体）</option>`+vs.map(v=>`<option value="${esc(v)}" ${v===cur?"selected":""}>${esc(nfc(v))}</option>`).join("");
  if(cur&&!vs.includes(cur))h+=`<option value="${esc(cur)}" selected>${esc(nfc(cur))}（現在見つかりません）</option>`;
  if(err)h+=`<option disabled>${esc(err)}</option>`;
  sel.innerHTML=h;
}
function keepForm(){
  if($("#nPath"))CFG._np={p:$("#nPath").value,l:$("#nLabel").value};   // 画面を作り直しても、入力中のパスを消さない
  CFG.poll_sec=+$("#poll").value;CFG.settle_sec=+$("#settle").value;CFG.report_while_stopped=$("#rws").checked;CFG.analyze=$("#ana").checked;
  document.querySelectorAll("[data-n]").forEach(x=>CFG.notify[x.dataset.n]=x.checked);
  if($("#snd"))CFG.ui={sound:$("#snd").checked,sticky:$("#stk").checked,os_open:$("#osOpen").checked,click:(document.querySelector("input[name=clk]:checked")||{}).value||"app"};
  CFG.ignore=$("#ig").value.split("\n").map(s=>s.trim()).filter(Boolean);
  CFG.coi_keywords=$("#coi").value.split("\n").map(s=>s.trim()).filter(Boolean);
  if($("#mkt"))CFG.marks=[...document.querySelectorAll("#mkt tbody tr")].map(tr=>({w:tr.querySelector(".mkw").value.trim(),role:tr.querySelector(".mkr").value})).filter(m=>m.w);
  delete CFG.mark_recv;delete CFG.mark_got;
  // コピーするのは PADDOCK GATE だけ。コピー先が1つ以上あれば有効
  CFG.op.enabled=OPAPP&&CFG.op.dests.some(d=>d.enabled&&String(d.path||"").trim());
  if($("#opMbps"))CFG.op.max_mbps=Math.max(0,+$("#opMbps").value||0);
  if($("#opRoot"))CFG.op.root=$("#opRoot").value;
  if($("#opVenue")&&$("#opVenue").options.length)CFG.op.venue=$("#opVenue").value;
  const dm=document.querySelector("input[name=opDm]:checked");
  if(dm){if(dm.value==="1"){CFG.op.days=(CFG.op.days||[]).filter(d=>d.label&&d.venue.split("/")[1]).map(d=>({label:d.label,venue:d.venue}));
      CFG.op.day_dir=$("#opDayDir").checked;if($("#opDay")&&$("#opDay").value)CFG.op.day=$("#opDay").value}
    else CFG.op.days=[]}
}
async function saveCfg(){
  keepForm();const body=Object.assign({},CFG);delete body._data;delete body._np;
  if(body.op&&String(body.op.root||"").startsWith("#"))body.op=Object.assign({},body.op,{root:""});   // 保存前の監視フォルダ（1つだけなら自動でそれを使う）
  const np=$("#nPath").value.trim();if(np){toast("入力中のパスは［追加］を押してから保存してください",4500);return}
  try{const j=await api("/api/config",body);closeCfg();if(j.warnings&&j.warnings.length)toast(j.warnings.join(" / "),7000);else toast("保存しました");setTimeout(refresh,300)}
  catch(e){$("#cerr").textContent=e.message}
}
$("#modal").addEventListener("mousedown",e=>{if(e.target.id==="modal")closeCfg()});
document.addEventListener("keydown",e=>{if(e.key!=="Escape")return;
  if($("#modal").classList.contains("open")){closeCfg();return}
  if($("#main").classList.contains("showlog")){$("#main").classList.remove("showlog");return}
  closeDrawer()});
setInterval(()=>{if(S){renderGroups();renderBoard()}},30000);

/* 画面の中身を簡単に覗けないように（右クリックメニュー・開発者ツールのショートカットを封じる。入力欄の右クリックは可） */
document.addEventListener("contextmenu",e=>{if(!e.target.closest("input,textarea"))e.preventDefault()},true);
document.addEventListener("keydown",e=>{const k=(e.key||"").toLowerCase();
  if(e.key==="F12"||(e.ctrlKey&&e.shiftKey&&["i","j","c","k"].includes(k))||(e.ctrlKey&&["u","s"].includes(k))||(e.metaKey&&e.altKey&&["i","j","c","u"].includes(k))){e.preventDefault();e.stopPropagation()}},true);
loadState().catch(e=>{$("#fold").innerHTML=`<div class="empty">起動できません: ${esc(e.message)}</div>`});
</script>
</body>
</html>
'''

if __name__ == "__main__":
    main()
