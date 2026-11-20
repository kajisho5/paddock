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
VERSION = "1.17.18"
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
    "WK5+Q4kXWl3jkaI1qjRxXMOYxgwP6CftlP34PUPSU9qBuJ4NIcQItjJ2KTsfvcc+lZukhCPm633OA/k5ZRm9/g6xkqi/u5dV7J6/"
    "L1KjdKnSIqHaskziKupS31bKW93S08i2qY3YVEXNjZTAtcPFE229LOCk+f9T967dcVTXuvD38ytaddg+3VFJlmxCSIt2D+NL8I6R"
    "nYhwidC22323+kZ1qSXF6ncYQ4gBE0ISyCYhISQEE0zsZOdGMCRjnJ8SkA2f9l84z5xzrVVrVVVfZEh23jHA6q6uWrXua16e+cz6"
    "uIy4gZsRt/6ZMuKupGXEFUUAoq1OiivJGviCnRQXaacuqAIKblYrP/w8k+KuCHFA7L0MhBn32n6Fog5W5ll4JalZnuOvhW3n3s85"
    "R+xKkiFD3q1lhe14vqBw7zliDUvhxzcJ2n37uT/d+vbzZOp7/f1b77+idEysrtfegbGHl8p1qCq7V14hoe6FtxnTTgqcXmOWQupS"
    "EZHUsEJkDRfMzswRqddsfq5IKjCmmCrJoKLRiI+VCtE+VSoZxd16lwDg2hp1dVxT1Gu0K3abnt82m77LkiTPEdE6Z4p86rJ3x0l3"
    "+WQL2tmzsMTdpaf7zo7Mv6Gwz8sWB1X8k9+9oSJ1lW00otKWMKU0GP415tp5mUHoP7LNYWdFVJGtQWU1q1NWM3LFjsr6C/tNfpRd"
    "dGQO9Vj0n8e1+HkyVT0bKhuFyfmD0jYu6PR7Ix7rnI7vDPauAF0mWl4rxGNF9j44KzDPYswozu5Grgs5h06c1gmxsbXho97lOG/2"
    "N/PxK/sf7rY2MN/2m2f2mxvS5hcTFLvMYWmOiZV05jjYGleUS8JumeOQWKEluTJdMuyxnisZmgN7GZuT9jESzLdSx6I1YSyck+bm"
    "TTZ9PevFdnDkGKPd2yoWO6wT7zqeIzqZME93fKQOp5p7WV9aUckrWDtmRwpU5hT91+x/esEKAIgDF1Z8EdfRTVr75FOIm+Zkvm4l"
    "bQvhFLn7oqx9SlLZGL9GkZeU7jo/UYaZwoFLcTJs1cFeWMgoac8xKDGjF/GDvZVmbgKv+cu3rv+Rw/mvWdFlyXif1DgpefdB7gZL"
    "UnHpDl4U6RgfYrmDcWVE/NXCwuIZqa5a3lBNX5S0vakvYdqMm/Bd8wE6fc3vnlDzEdWjxFu6VntvnMqWrJzjU2XqovGASvL3l97I"
    "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"
    "8BsLibsvjdbTySsf+n8AAswvMA=="
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
