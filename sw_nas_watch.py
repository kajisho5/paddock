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
VERSION = "1.17.16"
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
