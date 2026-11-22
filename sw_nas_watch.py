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
VERSION = "1.17.21"
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
    while "." in stem and ext_of(stem) in CATS[5][1]:      # 「16_取得済.jpg.jpg」（拡張子を隠した表示で名前に .jpg を付けた）も同じに
        stem = stem.rsplit(".", 1)[0]
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
    t = unicodedata.normalize("NFKC", str(s)).lower()
    t = "".join(c for c in t if unicodedata.category(c) != "Cf")    # 見えない文字（ゼロ幅スペースなど）は無視
    t = _MK_SEP.sub("", t)
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

    def copied_now(self, items):
        """items（[(rel, (size, mtime_ns)), ...]）が、使っているコピー先すべてに「いまの NAS の版のまま」コピー済みか。
        コピーの状態の集計（gagg）は NAS の変化より少し遅れることがあるので、コピーしたときの元の大きさ・更新日時と比べる。"""
        dids = [d["id"] for d in self.mgr.cfg["op"]["dests"] if d["enabled"]]
        if not items or not dids:
            return False
        with self.lock:
            for did in dids:
                fs, man = self.fst.get(did, {}), self.man.get(did, {})
                for rel, sig in items:
                    st, m = fs.get(rel), man.get(rel)
                    if not st or st[0] != "ok" or not m or m[0] != sig[0] or m[1] != sig[1]:
                        return False
        return True


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

    def copied_now(self, items):
        return False


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
                self.ver += w.ver + 1     # 状態の番号（total_ver）が下がらないように（下がると画面が新しい状態を「古い」と思って捨てる）
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


_WIN_FG_PS = ("Add-Type -AssemblyName System.Windows.Forms;"
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
              "if($j){[void][SW.U]::AttachThreadInput($b,$a,$false)}}catch{};")


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
        ps = (_WIN_FG_PS +
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


def pick_file(kind="image"):
    """画像ファイルを1つ選ぶ（会場取得の目印画像など）。読むだけで、選んだファイルにもフォルダにも何も書かない。"""
    title = "目印にする画像を選択"
    exts = sorted(CATS[5][1])
    if IS_MAC:
        r = subprocess.run(["osascript", "-e", 'POSIX path of (choose file with prompt "%s" of type {"public.image"})' % title],
                           capture_output=True, text=True)
        return r.stdout.strip() or None
    if IS_WIN:
        flt = "画像|" + ";".join("*." + e for e in exts) + "|すべてのファイル|*.*"
        ps = (_WIN_FG_PS +
              "$d=New-Object System.Windows.Forms.OpenFileDialog;"
              "$d.Title='%s';$d.Filter='%s';$d.Multiselect=$false;$d.CheckFileExists=$true;" % (title, flt) +
              "[Console]::OutputEncoding=[System.Text.Encoding]::UTF8;"
              "$r=$d.ShowDialog($f);$f.Close();"
              "if($r -eq [System.Windows.Forms.DialogResult]::OK){[Console]::Out.Write($d.FileName)}")
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
            raise RuntimeError("ファイル選択ダイアログを開けませんでした。ファイルの場所を直接入力してください")
        root = tk.Tk()
        root.withdraw()
        root.attributes("-topmost", True)
        root.lift()
        root.focus_force()
        p = filedialog.askopenfilename(parent=root, title=title,
                                       filetypes=[("画像", " ".join("*." + e for e in exts)), ("すべて", "*.*")])
        root.destroy()
        return os.path.normpath(p) if p else None
    if shutil.which("zenity"):
        r = subprocess.run(["zenity", "--file-selection", "--title=" + title], capture_output=True, text=True)
        return r.stdout.strip() or None
    raise RuntimeError("この環境ではファイル選択ダイアログを使えません。ファイルの場所を直接入力してください")


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
                p = pick_file() if body.get("file") == "image" else pick_folder(dest=bool(body.get("dest")))
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
    "3oceud7ElTfX+xsyBJBcrNqcKvMQKhExZdDCogBXn1L1Xb9brCUl1VvOYGFH5Hq/nm4gOkb6btFarvW7CYCX0t1RfAif+FsJKPfN"
    "x3fvSAepmmK81fVodzgkOH4W4JDPoh9xFPXTbpaIFJ5OqZtMYjFShefd3Ty9jpQYIxrBuGJAOkBc9WiqWFMUcU5UodsTChmZ8JpH"
    "NVMwURmNhkgV05nD76BypMkro0sBEFNyp3XlEBfHmGoSlEWO7lTF8MJ5ClVW3a8YdjNVPb9XNVVdFCRPCfwpzxvdlTNHT/QIkYFC"
    "jExOJnpkmRKz2z5ldjsEkd3pIRxzO9+J5V6CWr/b6Rbu9VRMMOnMe4wE5k4H/AKa/C29VDrKGWbKSu1q3ZMpXbn9bl3I8Ao3mV/O"
    "QqteV57uD7c5TR71sjSOUX7Tq43Eb9JfRMKq3VODXLEOKZlWXhoQuXoCSRkJtrzgydn3Xf8IUOlhFVWmEywrFLXyoIw0MsEUEFEk"
    "6Q21CC5psDTINEUwShRb2SaEH7A+JpOKvOKe1Jgklqyl2RfNEjRdptSmxT2MJ7wHwn6tmRdbkBXlv7yqBVlR2ss02gRJudyIiiaJ"
    "3067mq6xwTLYPgorUdsszYG+J7l7LTsElDoiEz4Hia+6pi1llkSYqwxPo+PY4uCC7HiSnUo8Grj3YqMziC0rHG95+vwv9Gnri5M+"
    "pOOI7PcIG87WHhNys+VPfHCaAkhxDXelk7KRU7SuV/5dasoUayq5Ev+9ILW0SrfcdDIwLSo+81HI1WtOtKEe2ALO/Rj60WJJzaq6"
    "3iKUPQmpit4N6d/n5KpOPtxZwTNCZEKW3jvFh6XSkp92zPRqwSnz/HsZhVwbotCcaNOHYu+alnLgDuNZth6/6IsDVavZdG8h/zXG"
    "QGpfSUF8U0YTFgdnqfmM5k3G4hVyRQmwKuFaWcIkoEGUJ+/Ajm0JlFc+u/C/0THfBGJkMq9RyQG9IN4vL5scLqY7Qt1WyGvFY03R"
    "h/bEqy7p+C+XbZbLOVt/lGyQrWl9J9uAnSlsG50JC22KS+5H3TjdgsLGq/W6SS/E+QM2la7iFI+Jm7QIajTIkNurxqtbeZqKixCH"
    "ap+robjU4nt7QNJKZcnubj9KhToLVodWfOmdkUo0FCPR0Kb3zmg93ihUIAKTuX4OLi41bGdLVo8ETVuqhSAZL913ggkN7IdEsEdc"
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
