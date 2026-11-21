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
VERSION = "1.17.19"
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
    "+oD75pm759AsolNYidyj7mnxqUUz2xgV1Td+Olj2K2Z3uMCkDlJtSF8SL4c5fUHzOSgP4XoMwJ3c8arkL00CgQzS25ptRDOTxoMp"
    "jtXtZBnpaO+We+yxwmvtMrHfb79545PXfhb/Xe1BJOAf6bSbuI9T4zpREx9e/iMzlr6bXbiY7W796Fe3Xr48ogrP/OnWtxnLupjk"
    "AIzdG0kkth0rrM0+iE5SBilnVSeg8+sp4q8DA9ROHv9I/BfJX3OC5eXy15osLIuk7J/ERYrnOTpDf++fv29ubgz16Vfy7C7yGPnW"
    "ZJIDb20VkYr0zfXvlPmTVzxx4MDJstfqkJkGt1CO+ZQlkAaedz2rlKCxeN/01udcGBXqU/b+/hJo00h0xgZTUPUazSWSM+uK5eoH"
    "qF/WVnGIiIStzHz2QiTAoATLXXn91ku/EblU1hiHvH8lKsLbFZuMFej8ptbsbt568be2b9OO3PV0cczo3lTEDzqJxRJ6F2M7acuU"
    "wsBM1Nodffvld6Fnxnh6DsH49NF7v2JblMNVSrYrMjVdZX0UOiCi/X+w99er0g2K/BQAShW6x4hhgdnbwoO+39zpxdNyuJEJPKAe"
    "WTRWyyOjE1ID7Sdgk23aAQ3N/QQ0qKo9iqEZjHgodJ9xLTPpjT4xwp4OoXUQYuP3SHY4QbJD0pVq9Ed7bZ0gKBytbHDqe9PH4KzD"
    "Z5X6IWPfsoNuWjjylvpAb5HLciMAmMNad+I2Fq38YbK4VTEx6d/lh3ESrqiRWwJRPss1xYdFmcaaLkZ3Uf0QwmdfmcdZSp9E7i3E"
    "9sujdexatF/6rMLIwdvX5+6I4I7UEy3b1x+LvjtkI7JGBZekGDXcTGt3H9qNIVratfz2kHMaRDR6jTVJQt5NwUaHpWVijOqGFSiv"
    "ga+TDVBCgFobGELvk1d/v/dLeJ2m1SWfGPdSElwp+CKRShaYnG8YGTF6MzWSRdU1tlzQRZKl9cX1Ltk/iI1vBr3kEZmNXcLeU8/d"
    "/uGrWp2nSH9jr957/Vq86I/fuPTxr9/Ye+rlWPF7H/xi7/3nkX7h1n9+l3g0udDTX8Z+++DsoXvvuf0bykOYEMdT3KnoUVft4oJ5"
    "o4UxkOnPFFWWbQkyBVhxLB32HW20tibD645DywR2fA9KjdFAfh00kK16UDf8k/HwHd6xeW+gUcBykrwAZFNNTYDnq7FdQaqJAZ04"
    "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"
    "p21inOGBUbvGnHeNjtg11rxrrEO7xtraNebmrjEjJ7RIYpxhLzWOy52fn1JO/jmdJr5lXNhSngmVGYYH+L+rBrz5MVDIw3DAYMxo"
    "MNbwkkt6yYns9Ji3urnyjbo6GSI9+meSH4HV8hnmAu8ikyhoJR+j/47OPoWYSggqVIadBTovn2+Sp1Z7GG8eclPeyBMIJhrUfOml"
    "BWMiAEKCiqo0DkiUxPbpAdB8Cc1p6Poyn+JjEqSblNuDbgHaTTzX5rB0Z5UARyf8W4UWXDumuAD/KmzVWsHk3QbiFOa/DilbDrZd"
    "CAzC5FHwRCBVw++XPJ+o1qdG65LjNMo+OzxTZdCuMYQjRDzW6IHc32/P1KXT24AlaQk7Oixb4AKw7Dm3rpFGlrtTDzsbwitwT9R7"
    "XGGWAM1cMITct/wNCWxFOxBdUyT378CT37LJZTF/+NX5lTxGoARAhcEW8vxx8sy2FXDhUtT1rYYr2mpyq26i6Wd4IXv+GnIuKIkI"
    "+YhfKzEf8lv6/WGUyJK3fXZwK0fgNXciPlP9RONJ3LX+WglZPK883zrq3deJJ7EVhkt0aiNrHYQvJ30jng+iBlZrcQlNJHCFbDcz"
    "ze/OeQ0B909fFcLdV/SOqQz0nYmcdUU5OzgmlrIpwx7Av4ZFYaMT0h8YgsbFtrJCLeF9KZqed3347ovNwTDRm0jJCXaFEtuhH+z6"
    "S+bGA8cCmM1k7OtQxb7OxCGCW9kQXUiwicP2P/sI/H5GMhy3jh3/JEmpKWCUaa6AgQ+kjf5ZERdEkbjUnXLwRSE8qHNAPAaPgJWA"
    "ojH4iYKzdX7OYCDmD8Cn/goKiEMBwJBk3KfDGHHl7dnQ8WhFbIPJa2fqtV+5BVlp8fJtheXqR3UwO70G0c+YBLvYnSOx2LyCkirO"
    "LtGvj6WdDXOx9Whnx6sgskYGX5QBJuklYoFkI6/P+kYTPB36bxfbnXfekUHX2reVhVtfInQtT9ZIPvCpvHHah5yrS1OoooSGqjgr"
    "y4Os6sveBhxHA2HB+Ozt88GFbu2j+BNrq5BHsOHNOGGLveVc9cWkLTk5lCLxK/M1IL+HAHkW0ejDCsbsUBgZxocOK1cLhKzAvxFV"
    "gtzVKPz0LrvzGzl+9BuTk2Mzov9UDwPNwPb1PYlxVuQ43zMwq1/V6MfPf12KGoKKCOwJJH9IK43BJWS2zE8+d/OGg5cUrEVMX/h9"
    "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"
    "/lkRp1Dx1VcewW8sJO4+Gq2nk1c/8P8A98GPyg=="
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
