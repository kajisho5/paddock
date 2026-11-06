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
VERSION = "1.17.7"
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
    "bs1FU2UlDOil1A4sFBfIkXyi3TDZEss/SPTIH/ncfBUW80elk+eG4dxjxWIpW2Q8OvruEAMRWQbieSpupVyFVbUrMfnbjBKrWPtA"
    "yNZJiqKHJVdcW0PPb6FEBjfoOS70NA6HQC8o9uTBBOUyU0DE4kHkuEabjFVuqg+pQo7hquMmakGSJmsDZrFqEn5EcN37YSaZk/fA"
    "TGmahhIjCmvVyQLyqRCTtoxMbuvixEHYF8MwEiioVv4WS96QiTVQjd2WyvBOR/3dUnrZEXxk5eOjHnzITftGjhH6sCJor9hnwHsZ"
    "OGMk//pBpTVa02FTSKi5tGF7f+LlhO2m5iBOnWynn068qcgxqzqirqkJvvTuxEvEQFAk/Cms9KCrPWErZNlp6HqyokX0Xlx2n5Bh"
    "c78SmCl8IhV9p+qtUWGbiCkSiZ+x/vuerda3GT7Xt31myXCZ9KNyh2gkn+zcP5m5L3mfeIAr3MtPDjEMy/HJLsfdyHs38frAqdsR"
    "zJOwH6pSQU7emzIU1bqPokxFDMOv/eQgOJzI/Aik/8zRhUCB88QJHGdSt9KokB5azXQsH5178Th8A+BE9JF6OcbFOfZdW+pOEIV9"
    "qnoSSgtR8S5MXKH6kpe44cTUTThBkvh2XCQf1SG6W+QjWml+O2azd9Vr9c4Rte8imVyJfBjZK78UScP3dz66Vlxk0rvhIU46MpPe"
    "dTZC64OVHMUA2/kR2kkoccseOnPvCcleccNCD+VXobU7NoYqEu4Y2YwFvygGosMVh1ZUo6m4xw7sNWzR8zRgABwP85knI5gB4Iil"
    "PyL9JWkr/Nr0UaJu1sx7XC7r7KlbKFXx8oQVzGZAdn4kkaztRVG5nOxbVzKzL0myqtKrR1XpVaqkVymXXmn8gyQkW4eCkTou/buO"
    "9hx65Ryx1pitFnYuNVMD63A2HcPGscnerleCVSpHMO5a3SnzxD0dc69b4Ptfo1dcxU/V9UYVGlv1jrChABFVFcUx8Tx3++0alF1R"
    "n8aMPTMGOIDClA58byrdf7iCT8FvrHYVz7U+gnOW8c+PXYQYVyN/VZ2JJV8K52/b4F+tSDJ5wcInNBpcKTagyggYk8kcvrFNXQl/"
    "h7E6PqZKl8f122KbRpwOc4K8J1KXhSASaAHv8NSkAbesg1sV65nYlu4Oso+B5LpE/IwatZl+9xw+FRkEzkx0tUOCw010HfuPSgLH"
    "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"
    "hNdL1+77kAvLvwboL+eMnxMb3zetXgj6KAWX/tx69/67afvumxIxbe/hOY+pIm6qCPgEWt3Cyx/z87649PxbufvBDrX108dDWAuu"
    "fL4teMtCXETMQ3qyN+1dMvqfRDduCAt/ejz6kb0PPomXojfJdE8BSd/bfQuHf+V2pDR99/T8dv79dqw39TLDy6tD+br0J6vVrfDS"
    "W3j13/eLp/qB8va2qpsRczszEtx+/PSluO/PpcV9md1K3f2z94N99y9l9fZewdIqtqzd8LO3zVsChd5D75fuvHvfvEUpdLlc/iH3"
    "fCzNW4okb09h/PYURmBqucaWx0/+gva1v+CG3m/zaLXf0mDPXvDlFy/Q4b7AFqo+gMp7toaPDYfvfe/n2Q0PPonnH1vtu/e3jry/"
    "fLyVffN2PMmnpe3w5RTOffF/P/zszX/57b/1nT/5rX/7p//bj79z9yC82CI3/fDmU+O2y/GeegGzxsPu82vn3n3/rL//6gdd2XnZ"
    "cyjg26WFtwuiBd68exRVVfrKx3Hr3+c3Wr39RsdurX7LM7WtHhfog1fqIwV759C205717Msyu6+cZ2D+jTrPjxP2NFmfs28fw2E+"
    "fPWvPnz9Dz98/W8+fP1HH77649vn1//k/vmbH7785x++/IMPP/7yw1f/94ev/+WHr/7Z7eZX//HD1//8VuDL3//zr/7Vn//e3//w"
    "5b/+8OW/+vDVb94+v/yrH776jQ9f/vqf//gf/ulP/48PX/6LP//pv18q+dn/8v8s0vrDl//vhy9/8uGrv/fmPf5yKPrmvbh3/heA"
    "jO997xdgjHsU04NoXSTPA7VuxHvP3B1d/0P1PWOWj3xSHym1Kl0U/4evf/1Old94GOgTrnjz4cu/dyPM4+j/xp/97l9f9NOHL3/3"
    "Tpi/8eHLf/tn/+L3fvb7/1CV78T9nTfPOr8Lb6E0z+rmIwH5xc3V9aRZ7lz5DT0Svkj6O+pfZvelC//i3/3sb/3Bhy//wb39e0ee"
    "puEv/ug37tOzaNI//tmv/80//fs//Ys/+s0379Flbl6Etv785vcH5+PnN1WzGA53VfNp8cXHjsh7mUUGxU8bbD/HVH7arYMePJbL"
    "v5vlyz8bww/fnqzg+2bGw/7j5eOYqGdn0c2x+eDu+uyTe2qCW/D5osB+vivi2c0bhsUyb98YzrtPuiQs3gbFk4fzTu8vHqRg6N0k"
    "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"
    "YNpse8stnYoLkt0cocvPbI5K0Coh/VK9VxaoneHUy/oTdbPfVcVM9ooIP5vHn8e5RSGRh52y9vf7+QhDQs2V/tCx2srtx0zD4MAS"
    "9HuUS/mhh0BkwL8rCV8HZtDCAhZ8X+FWYI7ag22SHBzvjhZ0w5hsLBf9rMXcS4xuhF1OHHq/N9b3bhSMCFLoOS3Vu1MiXFRh7+rA"
    "VdwpNUTaZRBDMSTPy3dKPdMt9aC1sALz4feqJZiHkOVYU17uSHHfDCopTK8EKIq5LYT4axy9L0zqScNdvzHWXbjQmNhRAms7DBAA"
    "s9UDU7ZTroG0jImmOnBvwD9L7vLyBTdaSjfBL4VBTNvV4VCFwlEPdV7os5EWpRY2kiGwIrwWJlF9hT9g/ZqhUVWVqSxpturMQWZV"
    "TA9mIFzt/z388IMbjz9x+G//ToBcqBtnoBb9cHkZ/y5p41iwVZbfW2mVzQcIEdDoF5/+6fDpfzPk066PT5mWF3kico9ljpmiK5Vb"
    "6URcj4x+kp++wXSiStBHfAG8QTc2YRiG/CAuaiH7rTD2UvU+B97osoR5WS/VNVcivuGYC5stN2hdbFAbESsw72h119upwz6tMd/y"
    "ZqVRbeysCoQLhmgmHqDHQ5X+ykdoUucI28xKxP+JGZzS8NKaEnOSkBEw0wQiSmH75ZoVQSIiEQTZtw4tVo3cZ5dehHfxC8H3mTbD"
    "FsieFy20fknZ71n8wm69FKIKCc+H2B/nPKyzL6EryWsG7jGezsQEsgZMa8dCShVFePkRquXsmzUdkZJdmnJk2X2g+25eH2a2JW9M"
    "rtU2cfDTwnSW/xD5xHO+HFHaCI9yvTfKlXOneiNjqloQfv1Rwrn0beYYHV0PDaGkTNVRSpUjCxfCZB8pug/MNBARYNOt5PF77+AA"
    "/ynI536lQ5t30B/D7r0f/fzuh4szzBFyya/FyvxQOtcyH/ubT12NsEeF/yuZk+A2/CH+evk99Mq9ck23YL5iWK6EjHEVnBigVNrb"
    "H0Q5rN6LgaOwCbt+6UqsZyzvCj189uarf0jRPlt6I/FrXwkQmC+72x0nALrIJDP+ZSF0q6i2JB6uDlilo7Aw6MZnFZf/n6HXA3YA"
    "I4nfz+G3/TaIbZhcAT57pnH46s/h8kGetpbtfc2CR818+sIo+MdZcL2aI+GDsZTvClusw9TvpLHFhrJ8r6idngmeK881345Rl8I5"
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
