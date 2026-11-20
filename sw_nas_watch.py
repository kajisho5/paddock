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
VERSION = "1.17.17"
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
    "LdZ2XO66ECce9Qjsg+uJEogCUakqJUxAU/AyIxFP4ooevuyO7oDhj4bAWZqZgbVcXkxOqMxIE7cqPyxY/shT6kx1BDCbFxETGZU5"
    "PcW/R2Dp2mkl89QNNPPUgUIcrZCckGRfYZSfwvugwAwMRU+zuvMePDwY9GXDfMvvgr+2vicZM8SMFD4IvuyX9k2qC58tc2fMACvu"
    "LJ3OnWHMqwXNOxmZ0x/zNJHbW/U0ilJPevXqRSM21pDFu1alnBhNkQQzRxKECbcQi5VZOOcOUyf92GOdRxB9v9iJWxBIKaz1qswd"
    "6IvYtjwfts6ff/ny5fzLxfk02z7fvHjx4vkx8ewiMcADCl72TlG6k7O008uiYQ6JICT3dsbal1kK66BN+zUiyJESHILaJVH+8qWv"
    "npe/ajJL+i4MbUKVItN+84WnVxiyTY+sRV3+XO7DstWiYhM2FZaee75osZgqdDYlVBq9jTup/onVyOzeKzKQpvwjENc4zFqlqu+u"
    "M5otYCAF0Q6ZaGf+njiYoEZnBEnraAkpC62yggcHqYSPmU7TQ5um86bIvhxdL7/7JWg7VFyFSsr0vaKRp6LxoUXjy3VU0fmKL2la"
    "z0qbWCuObOIbOhtY7dliv+S+Dk8+DDLrMIinqpqmf905JmSbd09qs7H7Z+IIiSlqRZwfkdA3kAKiSCQjDYrd3Yg22UYsJc7OLWw8"
    "CKWt6OcX/LVQ/EjUISspS/TW/uUkmqbfIooMSg6orTLREOslfbLwMyHmR6cS86O3iPnRKfRJkdfRPYxOEvtbutjLLiOy9cjNcvpx"
    "E/JxQ46fM83px03Ix031as2ErWNGS5rw67mSY4if7SHuosYP+cwcAOtPwrl41evb0D5rNbM5XSBzRBLJOSXNgVuGmt/KVGj+Y7tF"
    "5dJuOeugnaZPPVFjWhhbdDuncbEHunw+m+HNuLd6/p1U2YJecYCpuq2aSHEHk0lRu5IoyaNwRldHBE8RLFdaAiyyLOYMxGlS0LMT"
    "v6mhfQ1Wi1acnVKgYVnLlb/8amlGGshcgabQJHkOspcecSVySYhI6TD4wMhznq16MhZG5gT1mxDt6qEt/RTsjoUhORWbeULlk6iC"
    "wzpDxjOXxcJSdVksT7IFD7G+aGgYOUqOhT0P2bTJF/bHD2EPYz+Voof8W7zvS879ZSulMJFjeX1sC9TKcXHGiSPwblN+EI6d0INx"
    "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"
    "Pm78SoQiSWS+vvFw84OHr73IqVT81JgPtl/6SqObClRtQ4FQDyrXG3G0Ur06ii7vTQUdBoilI4aRcb69k0gNWcQj7mFzR0UsuTqz"
    "pNsxIuDFJSx22Ff+SK8YuG2skK1AaVApxg/FnVCPdZzwgPRiPhbUGQl8vakeibynIC81xbNFMjkpRnAvCq4Kv7FK7Bof2AOCkdi3"
    "T5+PYC2iVSgDQkOkbcerGw9fuOvLi22cHUD0xN5RJCwFA3+5c+u2z5eL8NifdQcnBXVV+yW0cz5WLnNtkZHeXlD8tvukdNlN27Tc"
    "zs0oLLiRtcMQ3mSms5jVVtQUKznvGhoalpk644bErkgCZWvkX+WCZUAxWgRwTkgi4T9hwfFjObG7EBe2X7tDWg8SKd8MLuv2+ysH"
    "QPZ7Isgwtm98JAzpP/e+nq/RuVTbynrW8K7CJXGXXZX2iFZnr2lxQqSWSrkbtyKyUjRP9CwWGUzUV+I+/mQ1Y8luE24jzLbYYHnD"
    "tttZcVH4JxZY1m7g8I7uDifShLehtEJTbqT44Ij702MnJrrOjtuxQ2PjJ8+f7WKeWqkobpu6J9xvjz58iTP0P2BPEGDm77fvfLV9"
    "8yWVj7L9Fki7VBj+TYBoi+wR4kxIltl+4U8iezMzRYY7C2lBfb+Yh299/eOd/xZOIS2Fjpdo4ZSE+KZgkGi/ozxihLxx/Q7Ad3Yc"
    "AAQ4QKw24UXqm4gC6kEtOenEt+/6rDy7zvgclxIXmOlCyunXwDx/wCHI91TS749pKtfXGZ/uMno9Ty8Fffjxr8xXE621Hn781c6f"
    "n5f4awoCTMDMVySxWm5jkG7JVDdzKz8pQQquIrLsBCxhYOwJYVlg6zSTpDCeWT++8/XOV69pOncGBgP6xzd+LfXpgWzI9OoT3uo3"
    "2Q/pHVWa4qb+EysIH2iHW9xNSrQJ8m/KK8D+qbBwvLMNHRaGhSt8+erGsGioCFKmjv1m6PJhmfMthtN9PWWUsj4YVF2lUtncfvGF"
    "7c1/kCXiw1sEBRKubwb8MQkfn25tfCakEalhDY/7QBMONe75p4LvnLT16RD0Tdoh6PkmwmjIaeREkp0NDn0A6pDWgYMkrt9pIv6c"
    "zlewL0IMvv/jW68JEIVoLjLrA37woJNQD6kMXmUVh05CWggtvzYlFvoICnCPqhFIcmm42/1MkL4IK6sOZba6hiDMBtlo6F4sdh0t"
    "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"
    "/v3y9/5+8UXAsjfmtW5h7ttTXxEfGZWxf/mpYq44tYiUZ3L49Xb/m4GDgiRUYPreEgEj++yvkZzl2a/uEFQkZ77fvv7hxe8+up4l"
    "4Que+Ivf+fDi9+/57/df3aAqfnjxhUc3cuJX/vDi8x9efOnIf7//k43ba7EyHu3tHvZHicv/R5Ssjfk9/eE2uoc0nraFnrxvx050"
    "cYIUwz7NjPWjC98oLXxzA32y/uj2AmYHFbMIl+rGfHaRTjfQTgVlGIx0W/vF3XYn3yePGUtQffKW5emaTh/QHqnJ12w7/RjQBE0T"
    "Sk3UDNVyEYdXsW21e5HP2dtup0bl2zYk9BGnUQGZptEqZaBQBwignV1S/nT9gcVvM9PzoApnOKFWS+qvQSC0CQeXQ8X6VqpsXKI+"
    "JSB/U3E9dFpIqYGdWJGnCK5dNb1eN8B/6N5Ek0eQfrFQqU+kiuuPDdzRR/Ffh33GgvbfX6YGmklGd4ZErEX/enluftFj0B5FQSRK"
    "L3pkH8xbr8CBx6/gOANVMSKFod+8fL3OBeJLgDSD8F+d6PGF8zsdCB46wk+1sMUtNFtmGzEAlL9zbw8PtSOs/ZcQNaQL1BkCkNsd"
    "MbqwvHhiSOTvUgltYbxJThe8FyHQIvIZYQZQ5rekGITEUNPzFLIlnDMoBT3DxTIJLeL+/cfSKwB/v6qDbdLED7JIzVc2kGo7Jxvq"
    "RVWK1zaWS1iuS34YzVz1LD/JjdKSLBMd/vqjd99VeSavKlOSE6/7FluNrhLq4RLlp+RiTHcoZwK3K8mnluwjJjAWgl64FV6RTEz7"
    "zxOt/43fv3njyefJ9E1ILCcPiTSaOxe0aIDdCxeX7uVoyh4NiNOVUNoybbMBrQ2ah5iYwkPEk019o6lFinJQiKYd8rIIT4T6HjkI"
    "B7WYtweuRSJWv7czzHtLmaXM8p34z1MsFoKfwMwFMVaQ4tEpN8KyIBPw9Bdwww7/QWfd5ZG43tT8uDDhdDbJPQebxMJCbUHXLKd/"
    "ekhSjiwvft5OFMJmhV1Muq/cuXhn5guLy5m7Fg9n7l78YuaLi3dlPr94x62/RV05DaN0GSz9HowSiG+3rhKGXl8W2Av3qewV/3Id"
    "ytWauTe/kLlzcMfiXTMXc9eY7ooKT6v4Fxe/yFWnP1L32GusbmWr6j+/V78QrxnVIzduCt6hpuCymoJfwBQ8nD4u/6tKeS8+s1nX"
    "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"
    "fN2MOkITHbuiaRwYX0g+o4sxLk3BSAchO3itSdc4Qfr9fhX+KYvk6Pd7bfinIbOiizAenQ4dkBOn/ROVDh1Yf/qVXl/kQb/f68Hv"
    "vs59fr9Xg39KRs7z+906/FPmJOf3yw34py3Tm2M/anWV3vx+/RT+6Yu05vdPa/BPR6cz15WNNOaqu+Qgul+v1uv0aoDzvl+ut6q1"
    "1rkwmEFPOv1O7/Rc6Jhw/6RRqqJXGbRa4LCrNIDN6Fxa9eBVSvBuvXOp9EKJav2shY2jhgnNnZ2elurnynYGnen1q9SEUEGb91vl"
    "eqWEV0Dlxg5U6pX6uTRpYoVepVc5lxp58377rNwp4zuDmgsj0Km2et1zaciDLnV7Z9Ql1oLhfbuVRvfsnNVu6GHjrNyunCtzY/N+"
    "p99vUQ2hl0OZ3mntDL8QGkSwh/BPS/zkTtXgH/ziSL3DV/p9mCTqCs6Sbq/eaMkr1psqJ3CZk/oyFrqU4D/FUi2fEHAnh8gz95ZI"
    "O68/KugQJP3al/DbGtN0VZjP4fv1WvA5O+IKQOWNL0plun3jA+CVDXgpzEHGa611Fwe+dHJWr5+Ja+DWGMBAdVqNVqkmrmFIcvN+"
    "5aRepXHBS72bDq4InnT+ouwCj4+zJvGSWJKldqlXrsglWWqUWqWuWpLlcrle7uglWT6Bj1zRS7LcqJQqLbkk4V69WjWWZLlXOa2W"
    "zSVZaVVPahWxJHtVmFMluSQ7tU6/29ZLstFvlWhG0ZJslBr9s76xJFVlY0mqd+ElWW20u/2GWJKVdrtRb6glSd+/Vk3KjVpSLtUA"
    "h3eS1+vzpN9tnNXl+lTtiPVJdU/qUPcsqdQaUJcmkFysp91utd9Ri7V/ctYrtY3FKhD6JwnsAkm5LKurldtvt/uVmly5vX4N/qdX"
    "LteuniX1Bv6f6Ldcxf3Gafm0LFdx67TR7rf0Kqa65fppUob6lZOSrC3XdKfWhjdXa7pS6VZ7PWNNU/1qLalArytVfHglby7w+mkP"
    "vpJa4KrrcoG7fYd4S3Oxl7vlVqlvLvaTTq1FH1QtdrX8Uxe7XtBqBscXdKlWKZesBQ3zsHVaMxe0+qZqQfc7rZPWib2g1fgZC7re"
    "6522T+0FrV5CL+izakdXFQu6UQfDRkdJGwQYbSJg9Fy4SQGNIf+uNotV9aPWrBRrSxNfYeMgKpUEpl0VZrABg3DKnJzAQEKp2okD"
    "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"
    "oaPXXn0Av7GQuPtguJqMX/vQ/wOZgOrJ"
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
