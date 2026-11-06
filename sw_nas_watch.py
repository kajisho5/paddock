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
VERSION = "1.17.10"
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
        # 目印の名前の .txt（読んでください.txt・連絡.txt など）も、中身があればメモとして出す
        txt = [it for it in items if not it["d"] and it["p"].lower().endswith(".txt") and (not it.get("mk") or (it.get("s") or 0) > 0)
               and it.get("mk") != "meta"]
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
    "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"
    "YfnXAP0lK+JzYuP7otULQR+l4NKfW+/efzdt331TIqbtPTznMVXETRUBn0CrW3j5Y37eF5eefyt339ihtX76uAlrwZXPtwVvmYiL"
    "iHlIT/amvUtG/5Poxg1h4U+PWz+y98En8VL0JpnuKSDpe7tv4fCv3LaUpu+ent/2v9+29aZetvPy6lC+Lv3JanUrvPQWXv33/eKp"
    "fqC8nVZ1M2Jue0aC24+fvhT39bm0uE+zW6m7f/a+se/+paze3itYWsWWuRt+9rZ5S6DQe+j90p1375u3KIUul8s/5J6PpXlLkeTt"
    "KYzfnsIITC3X2PL40V9gta/9BTf0fhtHq/2WBnv2gi+/eIEO9wm2UPUBVN6zNXxsOHzvez/PbnjwSTz/2Grfvb915P3l46Xsm7fj"
    "ST4tbYcvu3Duk//74Wdv/stv/63v/Mlv/ds//d9+/J27B+HFFrnphzefHm+rHO+pFzB7fFh9fu3cu6+f9fdf/aArOy97DgV8u7Tw"
    "dkG0wJt3j6KqSl/5OG79+/xGq7ff6Nit1W95pszqcYI+eKU+UrB3Dm07/VnPvkyz+8x5BubfqPP6OGBPg/U5+/YxHObDV//qw9f/"
    "8MPX/+bD13/04as/vn1+/U/un7/54ct//uHLP/jw4y8/fPV/f/j6X3746p/dbn71Hz98/c9vBb78/T//6l/9+e/9/Q9f/usPX/6r"
    "D1/95u3zy7/64avf+PDlr//5j//hn/70//jw5b/485/++6WSn/0v/88irT98+f9++PInH776e2/e4y+bom/ei3vnfwHI+N73fgHG"
    "uEcxPYjWRfI8UOtGvPe7u6Prf6i+Z8zykU/qI6VWpYvi//D1r9+p8hsPL/qEK958+PLv3Qjz+PZ/489+968v+unDl797J8zf+PDl"
    "v/2zf/F7P/v9f6jJd+L+zptnnd+Ft1CaZ3XzkYD84ubqetIsd678hh4JXyT9HfUvo/vShX/x7372t/7gw5f/4N7+vSNPw/AXf/Qb"
    "9+FZNOkf/+zX/+af/v2f/sUf/eab9+gyNi9C23g++f3B+fj5TdUshsNd1XxafPGxI/JeZpFU8dMC288xlZ9W66AHj+Xy72b58s/G"
    "8MO3Jyv4vpjxsP54+Tgm6tlZdHNsPri7PvvknprgFny+KLCf74p4dvOGYbGM2zde590nXRIWb4PiycN5p/cXD1Iw9G6S7SW2/rXv"
    "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"
    "noen4Th4pPNhu1/21TyxGJvLZ9dCplqfHAq1qrTy59n0YZ31pWMLZCDj4jzhHyZRvN19uCQKfSY8Bz/V7vV6faGCj2XZWV2IiKIU"
    "dse6wUbCPu+ItbYslqpFLsiUpmnZFQnRAJT8QbdnsagkIz3QN0FZ7Jc9A5kQSNbrq4/kBrgcvlZ8Vs4cucdegV5kliVGyjSSsXav"
    "PeJ9K0+o0A0kkvN2OV/kDxfxcDrhLSWLDfS6G5KOxybZxOEq0YqX+JQ70cvUqkf1NJuYCPnEtJURaolkYsqOaSLhkTOxZLabpj29"
    "TiUdCAqFkH0xC8yHrpk4bzbcySNgiEbXHUnHx91gubfKsC7BlXXF+qFBozla9LhSGW9vSrHpxqQ+q04TCcuxY0VGM7NbFfH23buZ"
    "mXNByOToxnDGkegFR3sV2mq7Q/KcJO9R0QFPzqYUJztJkSJkKsVS6JfVwjLcxGK7QTlFio1aGChucVBOeSVQ8EvbLYUujURqGF2R"
    "Dr2iEUUMnIQgUNwgMWLYgZWyHSut9enoHYkiRHJ08M1vkYxIstQeuYxaPB7LHrlS/opRS8jieuFbAiGP9gZRy9Tr3vO6933OAPoH"
    "d77p6FMsCxVoJYrBvTAR3AvuueE/z57Hu+cm3XuhPd9eBP3L+iTfvnfPtx8xVlv0uJ2+Pa+H8Dgj/j384cb/+ZzwDTdDjihy4jU2"
    "5AlDK6E9T4jdD+wHzL307nnc+yFnYA/+FTy+PU9QqYSnjTXAYEKj7Z5A+6Esrs5Ik5BKkxCmiW/rtnp3cxM1xUrQlkiR8t6CGcgj"
    "eDhs2RtRDD2Sle9LVHZvhT9F+OE1dQTINYdSpr4FtGvfdLCMJBvHAsQYeXym4mGg/o5r4e1rPnjU6fZsXYNnd1wMqxe/6ZBGPAUd"
    "oPdkkeCkIS9OoxaJJFjK6na6I75QwGbZGzIssCs5E0VgxQTP8qJlT5JFfgJsy/EcZTH2zLsXhCezYfiIBcNO9x7+UP5DF/c8kSDc"
    "94SCOwrgq0oFnpA/5kF3PMbb/j3D0z4v3MEfKpfipz2b9rcL4PZxBWHvhcrVnve2ecYbVtkCimLOUKbTRQP1pgw3k4zzF8CT5cek"
    "BWE1MboXZG60xaZBkAyfM0h4nZ499E/pp2/PVwCRiLD7fjSsfX9PmasFIZhqDO75WP+eH0r5TdUiicj6tzjG64Hq9nFx0x0kKSNV"
    "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"
    "m7cOf3Dr8IX7/vLRqzXs4q3D5x6pFZi59tbhs7cOXzz3l49+WjvRitXxSH+yZk4Tj/+JCVm1lQPx4V4sgxKPpzglfnWo5o+4gIJh"
    "iDtj53zxH+3id2swJzuP7Bdhd2A1pVuH12or+RLebiVn5NTznhxrWJ14vhWiIYo4qBCNUBY+E6j83pRvvo6nzaODGzSNKZXBKNjL"
    "ElxeVU8Zd4nu2XtP4KAsT/W0/KY2KAc1wzAqrqDgF4hTqvdQ+BP9X1rKewSgPGzu2g10BrX5v9Kw76F7WQE6FioZqOERzin6x3c4"
    "hILfdUB8OBdwTBLmLs6H3mhLf3qQvRF9Dj3lmYaKf0JRXHx0oUQI1X/dgxFFA7xQxwHKTYYlA8Srwr+GRcOvGuQLh8EFidqrBuoH"
    "LaUJuPCoCXLf5x1DrBX8zbAabaoQvjju0GkY1lafHuyOfWA8ROAcH2GTRihJplc518C0mAcH8JIXubB/bViZiAoF8P7t928YJnSN"
    "cu4c/enH9J11QmgY76DNA9q1DM7ySWbGuP3q26waw6ShWxgJxaBcoBaYGaqWsF2fN6bmV9I7cOvax7wPqkoTfmCHVH4lBanQc5Ke"
    "nIlK8d7GUvSy5yztigCEeprepEEJTpbwA3/9yQcf8PSNb3JVkhYG+zZpjd5EZ4LrmPaRqpHTwXX5LHF9AqYsOUeEC8xwb3916/GX"
    "WYKjo2cRLf/27966/b1n0fccHZy09B5s0DS5tz964bPXbzKIKzHL0ZY97yBUKjo/s22bd/Bs4D6EjcngfWiz8W+4tVBQdirRtiuY"
    "DoNf4N8jk96wFTO2uIaJeOVf9keWUc6Vc6vr8D+Dg0MwtwTYuWEwcFIMKnU3qDODP7x9GgqM6R+YrA0D2fWOgJ3th4G/h9YxO8gX"
    "i62i6FlB/PRNlsljtXRKzb9BaoUJbLoH10vrudOl1dxGaS13pnQ2d7a0kTtVOnn3rfAnD7ieU7dhTQJ/4DXUp+iaLh4zbxKaU0Yr"
    "/uomlLq18Gyezq0PT5Y2Fq5mI2O6osrTOn62dJa6jv+wvseaUaaVtKr/87N6Ot4z7Echawue5FtwlW/B07AF19LX5Z4mppP4wnZd"
    "B7ZxlI7ki5mduZOznrlsolu9wG8FIDv89Z0H0bNjHImTpbXzJ0tncvgfdTR3OrdaLp35x/g0RHWrGxgZir+6aUA7fPHkopPQPZlb"
    "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"
    "XvmeyYxW+eHZuFoY2dhkgyfBi4LTi/AZcGTcZjCynu6a0HR6pbYwqNPFsmq+Qfi9aqSJEC964g91vkDHLD929C6CuDGXZxHs8of6"
    "/VR8Bxf5jyFJOJzhBv7RuuhtR6K9z519gA03iNRZtNmx6WA9Aa8m1BmRZf3HH0GEV5BnkNuZCdCbtPygM8JYxOULu/G0WYExH3+8"
    "iIPjOC1yJGNybY+JscN1ly+KXZ/bEKhD07YzP50IafC66WRbzBiBbhbXmeWv2GkJydq7FfGviffnCEkTX8E9yrF75CXyCkPFIAKv"
    "vBcV30ZzrOmxz5FVd7Vm3zI1Ag5g8Fyn2ZAGWGF8o2jQ53iZN/hoBeMFgxqz/WTG2jcpobnpfR3IwuqLy77cEdgZC7fE3UmcrnaH"
    "b8LppPz9Lo06HcujqADeDK5yY0rJLUdxGC4aR0cnl1o8+Q5HgxqpggkZuq/rFIeaIwzbLzBHkPm2cPJafCIEPpXc25EearyrnSxW"
    "BlOlEwYrVwHFR4ZbPeGUUSuPnSqnTRkpkT8/X8zrpMlpMUScuyBEsLCAYLY9jjXofPSG+/MAoTEiQBzxzUciVE24FawcNDgjG0/Q"
    "GVkMzsha35KWJ0gnfTPdR1jMpaBj+A/q5OI4W1EHe80nBpEZJO5W1AXZyqNuha5R4SaAj3T2c+hQVEFPje49qtUJotWxpvYR+hdU"
    "uivVmXNRLXcRTXVhr33Dn6axNYLoJKu1VMKbzu1hsmmncCHo7NHyM9dnrPR14CeBkUhOxHS+0us3MD5GEh7aLNKRdzUfgCuuFt/t"
    "JOLuzBmI3dr+OGVk5Kwtp/nz8WVgh8pUbhQllBmqL86VQ67Ax97ShEIu4xhg7ixONF+1NtEgzKvC8CboEHO4GVrirEDj14vnQHCg"
    "kjxXE+z3OGk7gnDtcdX4D6DrFBEZi9V3dXkufrz42E5DSKPNixTjitsoyTwCuKB35/JKZITgoj5UXR3Da5P5ZVsvNxZo2XWmNAN1"
    "vIZ45QCJaePhF1kRlyMQlku+PzPHu+561ptr346pSXh1sJsjnaLwxP2CpUgGsrtSOcm03sUOZ1UK3QfmKFrXPlvpk/aEHEmx+nlk"
    "yVuI7UJLDfmtLs9SCXqWelj8Q1FHm9wRyVrldQndi15G2eQ06y9mb6omb9pt7rjYLzqeqrrcnjp7p9W4wNlNT+aN+2vndaNoPJNE"
    "tvH7YqDfa+HDvw4tO7vFcnupJBc2XQwUTP3bqYDExQtNij1p4nhqfFYJakabDF6gJwFB67a+yK7Xhr8msgl+NdryGfoWq+4gBLzJ"
    "HRr5937Jqgc5REh+PS7ODcaB9PbBaYuA83AB+13SQv2cgrPUMozKN3CAgj/cYcfFnUql3BO3iNd91Q9sF710BOA5lYwh2BosOlWv"
    "+G6eRX44FGU/2l8LNzZz+KuzHw5pQ3jnCTfPHn22+RfwKGa+lXN/vjBe4/XZ/rhjM/HKbPrrJk6vSHKQZUakB59Hln2+1YLUNLEW"
    "dY9Yliwrk8uB2iKHvCQ/naLXIYTlCXgnrV61RkCjhBm6Vdb9HcuWFke2OF2aktW4OegdrO5g7jEitW1lpIrYOXMtLrytk8blOBc9"
    "9qVjWa6ak3C+J2F+qs3xi9uHuNeD+Ux4MBcHiL/lk5sezEexg+ufUK4/vjr8edtDveH02+EwOxNet3tuLagVjmaOrWXsLWHQ+JEZ"
    "m0I34XhGZyzVZmyYikA1ZMrSwsuauAbY1tqj9k3Rqsy/4JUBv9jENBGABDuBciVj4MHPA0nCKl/dmriD+p+cakoG/Eku0BgvUKWT"
    "AFLmYbUp8tXlY0GiTNVE0JM6bZEw2KKM00YFTkqFRzv0u6SV6eK9sNtH8U6yrh8DnUPcWC2iIDVXrYq8XG46E/xS+D/popfyiw9k"
    "IC6PwNgtBYCBCsb2lmBBizisB1OOm5AS3M2qZRJ6hKNgX9QqdqGQ7QcWaSLmSleka1LJHjvPYvnXGo8kBmoQ3SND3MlbIfckugkp"
    "8ZBZO6rPSD0rJ9oOojLpuqVUlZ2tLPJrT+4IVCj6qRc2lRmTXJNiUrc4D3gnh5t2IFZlaEhNVmxLU3mLJ1dI0S4cTNP4h2LUzBUp"
    "UtY7Gk8LLvZrtDzULhtpm8d77XSHm9y4otgNwEi3DWm4NJrzGHLNO9tK0FMG9JWvxet2qZtjLwdGdBZZ0BnH8QO7FNvlkIuQEUTN"
    "Dy/gIlpuzChl1h5xh3hAAd36uFt9j22E+O+At2ehqIYyYmBlL+/N4K7NnWkJjTIeuZdjjvxQIfd1KAYTRNXBcqT4dVdF9lOc2KJA"
    "/E4IHWTj6USxetc5gJoNqRB0FN4M2F5UgQdrV6CIhv1buXS6pn5cUFzmJdscQBFD2eEF13L2yh3CzF3XgS2Sfi5PF01NB2v+KPnD"
    "j512l+BZA4lV2H+02QL1Tid4lImx3TpeUJ29snaBioeEBoXgoftrx8vvfdFf6Rb+SFBe6AVCSfuEjlo0RCicPx8vLSHqTEUY1tkX"
    "dX6TVBIn/Ma7ODYi5Pk0HvohkWsIRwRM6nBmDXcImvOLuX1mZXXwm9Ig/yY8/Xwo8UAf9rY4vkXS1l/+zk7PQJPLTP1yGfbCOUXe"
    "VIVUg79liPhYg2yuzp8j+H2xfDBV6P6ElmM/zWeel1seT+9bCNihyookB4AYKsBQaGn0TOO4M2shBKFleYrpEUWUNtpdme02LIPc"
    "FKQseHi1xuBV/pGPsKGMgvv9mHtvwh8/EtZZh+tNOirmcBdpa9yoxIyj7aS0Bbf6EX05l3ISV3vnXVUECUSTkpht0hdBb2PBy5gE"
    "eYzS8ZWRQzCar3rUgJTTHqmx/6itd3m1CflfG+qCEBICRpRUgbR60cJxQbYRLckQ97ZFRCo0R/lo84G6Ccud1g1gCSjpdSTdTDQe"
    "mJGXXSYNGkzPESOBtwRQXgJoSqknc6OYKJIR5Hlmb20i3PC+/5oEmv1rWbgeFnZyMAKDB1jlZ2JBldEXSq9co7erq7jjJ+ejrbQ4"
    "fKLGRJg2/qC+5k7tDMe1GN3y1qKfivLovHcxl9/SvEO3Dp1HbOg4bcojV95raTIjAIS6VKdOD/ot9+TEbZ5gbVV6mKNa94KouTac"
    "Ox2Cwade+pDcUIdrnXy3zdztNwydpnm5CjcGi3tDsytJx49zj5M0eGgv3eV98zZXmkDcnBwEufADOXf7UeMUXh+RIycfOlXhXHYL"
    "4cmnAImanuMmdJb9rmbqXb1GL9vDynk2KFXRKrB083+3WEjWM8bp7rPNXzBqd98d+4JxvPvt2BcM7d13w76AqUHPY/hyz75c9sJi"
    "j3rQiF2W7qYQ33Uulu0Rx5YnvPPsAwyPiWsvsAoQBdGrNHfvBVarXdfuxlT4FfCswTbluwsX65fIrHf/6icR3qe7IPjpwCFZW+9u"
    "PSo914s1eOsCdLQIXJ/74LD2IE6vkwJhefrF7TV6I7oVSxXkNZT4C9+n9xpSOAHib/eEmm8RBKkFLd8ig5lubsJSEbEzAjrKPkTE"
    "OqR+FFPeg7alBsu8ZsSezkBaPI/GP3NgI9TjC2WRpW2xRoanmDGAKMsZsgaB4eNBfUAFh0KcfUGp3xbaF3fnnXvC3n26xj2q9Chv"
    "SYuE2LOfsY0WKQzL9IqvPeIKXuvA6Cn3/pK5UXU89qd7qy/D8+HWR/e57ltnecK9xOv+2h0X0pOGBRGYMgrp66Fq4cq0CRlHKlDP"
    "ToMY6AYNV+5E0k704LC6Cfw9MKtmSIzUWHi8HosS54NRotkkvMB6V98UUc9axdNNpBAHDlkMgoMoqNEuwZReo9Vme9BPmSXeJt+1"
    "M60zfPiDrJ/MXEQ95IZs0EvQFz0tLAxaQaYGOWhsiRFvgUujfdD6yMcB81zJDfmgpKwIipq1uHdaRFKMMoYFWygSUcDJNArJ9Reh"
    "IPDahKNA1jAJHyKRvDjkrxoCrk22pBYwlsvHqkfHgxGgBlIDJFs85qgWsF5gRV+R1KEYUQMEJRvoIoUWmnX1NGPrzevaX6j8uhzI"
    "RqJlxzdTvj6ymv0+Se4DS0Sv28pF+WPXCiF3Gw0LcEOY2iESLgLTqVLdAEQQ8Q5UHO7bFsLKVYgSx7KmLx3wpdrY/5UwsJY0ko0l"
    "iF43H8IgNa30UL/OW8zRx2ISRZPI4lpbocn/6riPpuXl2gs9aspIrFT7xU8qVN0dALSClTzygN4iWSdvbiGJWMNU0kCFH/iQsLnb"
    "dV568l0m7fLoNgLyUNwmfAtGodvlJE1ydPi6+8SeI9FNedu8iJe9gxZvqln9KP1io7WbjUUFL0OAmxIg2nJmyP1m+h2JdTPxFcBu"
    "ehDuBgHUoIEzl7FVBsZW0ENUH1f5u5uohHxON5lWFH20sfpmyxxcWVHdQ/dLrAWFWM2cuJ5ZO9zKhT3VgYY4xlvYGQ6VOvyFgZ3Y"
    "iw9zdQNgVVQd4FU1ZcM0ahealWS/i9jtLtzQQPQ83k9vbZ2AJZzu3ToWOo+ETMfw9C4GzwRw3SenaEV0EcxiPKtCE+C1uInhWnTG"
    "XBnq8w/sSuizfu4Cj/LvUTxnvKEnjgrQjWYWJ4Hg8WoqZJlWpokWJKyTCIXHWScP1J5W43NsOHRzvQALB+JqPG7SQemm0mnyTXwX"
    "Fr6fKeNIP19F6XzKVfcBsLMXgy7nvNpa0bkpimEmvexR2INZgj35fWd63sGNgOiBkZ7UMUQ3Sk7W9ZNpDsgdr7K42OYNFpa8F8ZK"
    "fjOFtM6can4qDEZf1fvt26ctI/rL50XY0PtBMvlZSDa72/WnY8Bu5mG9CTYyXC7er7EpjkP7DdP5lUmpDKM4KfYeRy7rfFlX3cVH"
    "jknstGGwm8ALAHTPTdkTu0G8u6W6GMRjtt/C3fFPue9xuhIEpU/H7fWkqFCVXmXyjbo3r+5bDfRSu9nVfS+CFzbpRns2QnS3fvUa"
    "ddq5s5tIYm7XdsrrDcZk7eJCwOsYSWsXzua5gkng/iLxvD3DZ0pD9Im83WPDXq/NXC5fDXxG6r10ELZfiKpYqpcnbsaGGcFm1JNz"
    "bqSPDhtCaE545zO4CANs7rxMwN/6xTM9wju7d4qs6RAO3gfWqC0hFJQMov2mgx3XImdrviUu92bdrDCb0bdJUbi3+YEakBQmkJvM"
    "fdmLCgtl3mmbifL9z71yTnTv1JRqPZUFnjS7J0hAE8LGxlCbTeTYLdU5Hxk7VyH+06epd2hUilcQDYRRTSJA95NEer03WDugeFUH"
    "BKXJdElb3cGxmk/rbQmE9Wa7W1EXcjHmRquiqu+h2WZ8EngDgbrHCI9ALqVUlGYcwvH0ke7Al2EfbyswwnML1wFNnncXWEvxaAjv"
    "jYT4IZpl50ZYBrutfThnhlYTvcbI6Zk5YdK2mxnEq7m0AUdEmDmBZEeErLmVdkcEmbmhZDi7a6cc0H2sscJbGL1dOjgO/FJd+uNJ"
    "WhXkt7XZ+SH/uieT3tWp665mPQbR5iNWpe2k300eDAfgXsRudzU28HbpIE7Hkvvq+eIwjb3hm5GfHGigBjfd9NJQZNcuP1XFk/yH"
    "r74yEJ91vxhNOwpWVDRX0usSWtdvTN5lJN3ScVdFN2zX3Hjspq3XALHiDhd5Z9P6wTChdrOlatHcC/y63tctVhUOkTw1rGgu89fj"
    "S1Cd9yz53fAge9uNqKG7ueImiNbbXVHdtxVIA0G9uRg24dZqdPle22Hrhw6mNkJjz3Z3Z+A2/9HaLp92uWP/ioZjYyAgp3IyFIZ4"
    "zKp23tNZxl079wT1cKmHLByn0X6994UIcS2e43TpcwKsJWs2NFL3L+XxC0yS43ozip6KA59Ov6WUXmGzg7fbWUV4WbUrsHe7bx/s"
    "OXdWkbBxQPA5lLAmpUEbFiEMjsfOIQxuwXbdzaMbpT746+NpsVWCGYVjsNwmJdFoXQbJ2q0tRi5X+RqZcOwTNh5E0AONLaB7C3NY"
    "gaWOWBDE91sDljDvpLuiJaQDOlBqzkbgTFwrQ4otvK7ok7FRtN1zvR+61R4epWSt0m6i5+OlzYSrdTMcOPxKa02M2y6n9L3TsVWH"
    "zR7GCNJhtlqh7jFO4ulg7gaKFa9+5u3GfW+6Zi9eb2mQitcb7M7dHNiEMzv9GTBWY9tFs+pjMoLoy6YLjMQKjgBVq/3F4WfILreq"
    "+3bhp7CgvfzQDfnCy0ZfPPwaZBsgGqemgr0c+U65fVtv34rVHKNs6+iphzhnf5bT0dzLoZDLy2ML3lj8vm74lSjd1yTUGQRcn9do"
    "tZNXFLpoQxf+QNwNvgqmS2iniC8/FVnO9uDfaLXEfEVsYEVgDPExboaIox+65G6p19mnqPP9avvaeLhkKT7fZmilCvkgRlnKIpkQ"
    "O9w0mxZtjy66qFPyqVyOGlCXZvwFnHXjkrpisa6RCRy+4QmcC1YMDdKEbfeyvOXXf6Q+D/nN2CkeBLcY21XaiVjAeA+aV0WCTb+t"
    "fBpx3x6sN/Ty/HSoN5z6/nRcsbfitu4Q3XJ30ihwbazZN6+PuEo3lNKlj6A7drfQbhhsdH08GmLBdr9/HZF6aWpuxUlHSWbJSPUQ"
    "/GJ8uXNRuY29/p82j0e6JwEO64LePR2ObnXIGP5V1+Hb7TQjNeN58EbT+1ptb3r/Undhx7EgZWpHHLmGER1insvDROI/hSdA6ujv"
    "eGIMwsXL7ltFb/H445s8fmoIZyecDsa29Q8hOc6Rsyf2fNI0a1Rg3Mo2eJ46xH14lbDmQRUjCNjpF4PQFHsCoBPTolG+q81gMprd"
    "AY6AnlIbl+pwbouP++CCJ9V3Sjhbxk9zEJ3YOmJBnv+UfB4makd7m2g/iLKLVUsX/HHwd3CNDtW+uFgOpCcOTtLr8VRb6g+HnOJA"
    "YjYqcNF/03u6i9Q8VD31VERU16KeZM0yRum48nDyvECLwTIW2HTHfZsu2rrgn8XkrTaBCD9rcx+374uuLvflhHC5bh9nA2KmPBVb"
    "vQccTC2eNV/THuJxW9Z+ACXfwVBz0SsiFaWi4wsWdGyDOgK3XAeXiyrMzK1Mztzwvjdu9I4pl+aFy4vtFE7noTpxcodqWRarLjCl"
    "Nvtqy8l/29T7dWCuRYHhCV/DWnS3Q0UpjZ7j1qIyYkuiC+vYJKnobbl5vhjYlpsxDr7SxajmYvPs00jY1ghY+ry7uBW96tU0eJQp"
    "VM2fy6KwPtfRhx1Z6T6kkNjYfzouLq2vT6yQz2209EP5hpEFmroT4bkLozO+MX76cq9llZun1zpKiJ7ObYcFg9j0iwRK5lSn2/kb"
    "Rjd0+dZqSD5zxeLMjFicxELiticq07yZO5N+owKi1GUg4omA9/alG0ClfFvv8ufq7kvAUHV7OwgY/3iHrYum78y09tYLr4lnNHYa"
    "d2qVPYHvfJ47fNoGvcWoHHbHRnrsapTbiTfusElFXdfI77ZwlVSW5UCQ+P2dv3FcOtWg9HQBqQ6cWpCJy8sS6atVRSHLgaK7w5ae"
    "U/4mSLQmOt+0nrDdoqGINaFB+nk2xKB4fkanotrSWfvIp+oTYYcuxqV+J+/QQhHI8Ea7Pn7tmzoo2/+LWgHSEFAWUky8wpk2qNS7"
    "NRy6YVPkjrd9mb9bj3V/Psjie3jLEEXvL8C79I7DMFIfC0MKuoGyRIWPgHBkE0pqMulpHi1bKCFAGTTUHMBsTNr3QRX0IhCewO1f"
    "qCnzMegCbapmd5tD0UkLUHDPkwjpqBaq3PvDN7yhWysPMDG2Eb6upYEmAJyo4RDnN32+U+Fw0whe5Sa31eQih+/kTFUR/CCfjyYz"
    "9rvj/r4VyITcov5n8PkoEQhE1Z+lFlycWnE4ray766ulfTJ2Hh2OddEGr2sch5VvZVF5bi7tanKDqc29wBqL/D4+ZYl20zss0wvg"
    "2GLqMiIj64PBlVU6gm7FmKtbNKrw+mEEuZW12TSF6gf4T2Qn3g3NbUpV+b7wXEaiBMRYJs0WZUl+VS/bk+9IYZF1d6iuqLH3DGez"
    "rWo3Q2tsIihI2OaJi21OZs4QGOWbbhna+lhqpK56SzrTyool7aBDFSP7ntCqxPlLOqNlqF5XpPV2Uo3UJup8y9ePiQe4fiFWDfb1"
    "Bm1oOnrSRTH9FmS77PtQGKOqcuZR9EIjRIXluex12/Br8AZiUBcSzMh37PAkNFYk4/h1YxiR9KYdadsfpLVUM4reGvemt0gr/cih"
    "bthL2QM7HZpdl6u6xcJeAavJ9u5L1+BpGkwvnncK/fTP5219fO2Al5Fhn2nwyPimW/e+DvAzlwN8PsYel0saW/7vkZKsjznb08a3"
    "4k2NXqx4SaQ/XaHAh2MA6ygtH8J4SFBNHdo268jCrk09hsMw0AiHDqc604E9KjylGwUy170Q4ERQb2R8RpXDzHp7CKJk5g6WwDIv"
    "JOxD7J2tcAaRJ71Wp5tV6Ynp6q2y8Dr3bqliOkmwo/T2MJU1nCdYr7uvngha07+i9LzVc6a46ToxVIfr11eYg+Y0dBxGH12un9kt"
    "XV20NzZQSKCq2K0pTM4V+1U2IqP0EW7CqSxgZUEm/wOXLvxo+M+o6uKEdoY+HYsey7jfC+VkmBY8bJnoFyBm1BBGJz+oPxZpKAM1"
    "LZ+NvvvSHZKji8s96erCpjhcuDF/NBl/ZB34DCfv5wAlr4o63+6qCK1IDbwEzbvTcIYTATwotOGB1Rr/Dj7yRwQ3ht5MSD+Z0kxq"
    "WO+bFmer0qq+adQY4hPHz2xd4nmXv3pgdThuCN5TNqD8wvZiUTvJS89oeH1PZkuzqLEGmifEKCEh94McQnBJxqFxX437kIObuVUJ"
    "UGS4WKyBbc7+ZoRVUW6XTyz3vMtL+F1dow04bnEKYJrN6CBweT2nax3IEMikMDqeVvl7z1irwvcrDRAcywDBgn6QLiU5ayJkuya7"
    "HauYwpaslMeA3eUL9vEuglGLEavZLMKksJYFgg7eTgI6VZ9+IbFjpzxzVbJHZM+6qdmbC/oBjDpvTJ5dyLqvH51gpyTNONqJNQGO"
    "dZ9RDeZdGjo+WJCrFoYpX7ELUacu7ALn003y4w+fOOlB41UdvdWqZb4rPkWPmV6jYg9GgZz8bXIntfrjtdmhP3QY7XBiDReekOrI"
    "+zaHmhBzjvH4OmOkVn20SqXRRJXT57HabPfsUOptE+KNo761NlUuz7TCZw2P9EMTqO3unJGqw/q+rtNHs2skZYedKVJ4pweBXPAp"
    "a0tsc2c4Sn4TCqJhdS6HyUD8kHTxIKRPRntJ5RSttZj4Cq2QGOUTO57b18K0wrF38hRd+T0HHas1ESLhIg+Byr57Orp9JLqA46Ny"
    "jH42bgw5SAQ3fjeQZlOr2YDxcBtRlZszqPpgjaBVH3mqk83F63Q4v3Dhq20F479G+ekUvQ7RFXEg1KchJoK13w5Vekc6QHXddBhk"
    "Q1yY9eHCuT1H6iuGx3ILBCyjzgIeNrphDgk7KA6Zt+HqVLL7So5tXX3JT+bSnU9dlk5Q/7hVJQswuG8XFK/EAmF4+Plo0Dok70z7"
    "QgoihWJ5QRTlefRRWcuORWpHq/DKXEynUYIL2B42jKqq54JkHhavrOlK0E163MPhkXxn5vtOjGOtDViEs9Y/QooaGGsDkR4dE8CS"
    "I/iyHt98m78BRoNE05KvY5BCRC3zg1SELRgL6Ba+8misqJnNeJL28aCH0FB4Cg0xkgnudQhnMmg8rsMb+Nfb/elY1oyANimV//SJ"
    "t38K48HAPsl4g0j5m8slZ9ue14KroGgsJgPRIqoMax5ThbSwPZifq7mytKhhLftpUay506F+p4THdGEsNVsvVu8Thj2nTgDD8nmR"
    "f0rH41D+f5TMBrqbQHKNctKIfdvMihfjOmw3JEXGx31w3PFEH/eVxH73L3PqWObqy7ZebhjTVrIRhernBjxX9mpP3P1hC53gHEDx"
    "7Lo8kIFg/4Fb5mKvvzBVlcJaDJiKu7SrO/CBIUwVUVaEKDXJ+h0ZvuGdd7C6J70iFfqpHrfDKZ+paJNXUKxhyiznu43lqUdJQE6x"
    "IY9QOa6ufgAmXjjQK1bf1eW5+PFiCickV3gqi3VRglZ4dV4Wq+H+iIMM+G/GIyrKLOxGH4WS0Ak5VRE6nvWwIVlYfTzHxVC87yoB"
    "m5A/CGdnkxZRkjUHH15GOj8NbeRVELRS6qGT7BWSTbIbwlvvRIjnPux6imHn8o9MQPRCH+jQeCJD972l8/PkjTDoITyMo/RndNL8"
    "BFFTmQwwmlTqNh7W2z08revzgRtyghiy+pSGfzrvTyIqzPUXn1Fy//1f/eIzkCvs78Vx9c7+Wm1fg+3qu29gC33z/S8+s99QSOR+"
    "3tT73fd/9f8Bjnhp+A=="
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
