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
VERSION = "1.17.15"
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
    "8dvTDxZVc3//qeBvvv8hW7rIFiH83vdeidX9zi8jIXo/ceIRq9zv3XZufvaXjOo+PfSrb4KbhX/zOB3wg8cvZRRlaRG++bXXXv2t"
    "dbeTksrbKdxPB0LcS/3+h6p/SXkywp/fF9iFD+OnxUPnxZ92D+0tfnHbwu8+M/sQercoifdzIMAlflij0GvFdv5IsS1OwEvQ4ZqE"
    "zf14t3ulefr26da7+6aCdz32SdvnuddM7+4Hn3demr28z759vvXutvndBxF4hfpeXu3us2a3WePvLBLVfXJL5r15KLffvPmzf/ZP"
    "/uQf/q3/+oe/919+/Ltvbprn7Usw7MXX+IYiePfSjDe/+gZgn4bgDzLvFGZLLb92S2V6dEF++Jd++IoYlxuiucn+Lz3DmoXmT9uh"
    "QY/e03PE6Uc/ugUYf/Qj65uDdWncw+MR5a9c8Bt/npKenhPXzep2tPRtPDxGAp7k8y6ubxcBSj8Z7yL0LC8PP0+YXqT5lTQtP3yU"
    "p3f3HZre7G7K9Gk532LqvvMoFUvZrx8srkiTp+0tKn/Llogbb1GcwZuPO/dhxvyD05rebN3jvPRtL/v0ZV1Ndo+BNB9yFe/RrWeO"
    "Ia/G2FLm66a8vAS8+a//6f96/+Xv/+yf/uaf/OTfv3n4/L7oMHvxI9ePUYxyUTHl0ue7cH62yOnLl9uyp/u6hFsqwSIGtwdd2t0l"
    "7Ts3SStfyH6DAI8LLv/4H90mLj+9vfss3e8+yArwoQvrz374lxaR/OGn96m6ZRzedOPpce1oEy6wpQmfrc9ty5Lvfrf4pL9FY1L/"
    "Mj20i7zfdvh5unmTj3tg+3nxRvhoAj/9LnQLCy7oyM9ucztLXz8vP6maO05gHjfAXDDR00CPHm32Q92/vW9c+oS2nqFm9pppn39I"
    "+RwfvG8zYaHNfU/XH7RdWVVh8NmbX/3Zl//bn/zeP16o88KTX3si7dv0FxHy0+c3yns+7Gdv3v/4b/3sP/7++y9/+09+8sfvv/yN"
    "N8DjA+DNz37yD//0J7///sd/+wO3Hnn1xPdFUZWPdH6UtP9BEj9dfaDw7VyZL24bsz3T2L8R579J4/I1mvrs7WLny0c7Xz5bv3u1"
    "j0Xe8UaX3A3RcrNsf1BWt1Oazv43f/Xu0zvzvBfmffFaPd0c3/tx6ovj/za9z9i9fWoX1Qdp+bTC4kc/erp5DU+XtHv9aFEJz4eW"
    "3Fr1suH10rT7POQi8q8B+oddEV82Nr5PWn0g6JMWvGHs9BaRT9t339SIaXtPz3naKuJmioBPoNUtvfxpf94PIT3/9t59YYfa+unT"
    "IqwFV77c5r1lIC4q5nF7sjftXTP6n0Q3aQgLf3pa+pE9BJ/Ey6s3zXTfApK61/sWDv/ybUlp+u75+W39+21Zb+plhpdXh/L125+s"
    "VreXl9bCq/++XzyXD5S306puTsxtzUhw+/Hzl+I+P5cW92F2e+sen70v7Lt/Kau39wKWWtFl7IafvW3e4mvoAXpYmvPuoXm7JtfL"
    "5fIPue/H0rwlCeL2FMZuT2EEJpdrdHn8FC/Q29fxght6v/FRb79lwV6i4MsvPkCH+wBbqPoIKm8S8A3H4Xvf+3l+w2NM4uXHevvu"
    "4daQh8vHU9m3aMezflrqDj+swrkP/u+Hn735L7/9N7/zJ7/1b/70f//xd+4RhA++yM0+vPlUus1yPJAfwKz0OPv8Orh3nz/r77/6"
    "QVd2XvaSCvh2qeHtgmiBN++eVFWSvl6CsbTv8xut3n6jYbdavxWZsqqnAfoYlfrIwN4ltO20Fzv7YZjdR84LMP9Gmbsnhj0z63Pm"
    "7VM6zPuv/uX7r//B+6//9fuv/+j9V398+/z6H98/f/P9l//s/Zd/8P7HX77/6v9+//W/eP/VP73d/Oo/vv/6n91e+PL3//yrf/nn"
    "v/f33n/5r95/+S/ff/Wbt88v/8r7r37j/Ze//uc//gd/+tP/8/2X//zPf/rvlkJ+9r/+P4u2fv/l//v+y5+8/+rvvnnAPiyKvkcv"
    "bo3/BSDje9/7BRjjnsX0qFoXzfNIrRvxHsx7oOt/qLwXzPJRTOojo5aki+F///Wv36nyG48dfcYVb95/+XdvhHnq/V//s9/9a4t9"
    "ev/l794J89fff/lv/uyf/97Pfv8fqNKduL/z5sXmd+EtlebF3HykIL+4hbqeLctdKr9hR8IPmv6O+hfufmjCP/+3P/ubf/D+y79/"
    "r//ekGc2/MUf/cadPYsl/eOf/frf+NO/99O/+KPffPOwXnjzalL+5fD3x+Dj5zdTszgOd1PzafHFx4HI+zvvHp5i8A8/11V+nq2D"
    "HiOWy7+b58u9OMOP35694PtkxuP84+XjnKiXYNEtsPkY7vrsk/vWBLfk88WA/fxQxEuYNwyLhW/f6M67T7okLN4GxXOE807vLx61"
    "YOHdNNuH3PqPYpfeS6add5+i/OYY1KtvRH+e56Q/NnX3Y8qfHePiyVO/+7CPu3W+BKt/eO/FI0U+u9Puf/6cvQUS78HiL773SMCn"
    "e4/A4IsfPm/ykr3YYVZ+ikl8qPVVGOKWBPBhOuMpPe01H7JP8rBtvTh8YcfzsP7vK/weV+O+33yTubfz62+EhD4otddCedORr+Z9"
    "f87c1Q0Cff5q0hj6Oe+cn+a3nkXiBqg+iEQTZneBeKTY4moyb7uX3qLhs2l8Ol/jiX2bx1j3cjN8ZQHY+GUru85btLv3uErjiVLP"
    "jH+OCHaPUnzX0u+/Xgbuv3j/9b96//WP33/1d/78txaF8jfvQ/YP/vQn/+TPfve3tM1dldzG8P3ib9yH9+88DuNXKnYp9QNqfCr6"
    "x++//q1b0V/9wfuvFzPw9e1iKePnV/mvHo3BX/zRf3rUYX/xR//5v/z633n/47/OjlVWNmHzHfA73C2DpPnOUsjTr378N5YS7jbm"
    "391L+O27ClpK+z9uGunLv7KooKfM0C///fsv//DmFPznf/vnP/3jW723Dv3t918t5fz0/VdfLlUvOu1nf/iHt2bcCvz7jyr0rrLw"
    "V319YurDLyDeX3mlBH/nFg14gG8B5EdWPq0TeOGb83xi4EuqR5c9pvff11d9/vSDh214X2L8itzNbRvZ29rx4nZx2+S3+ygE1HzS"
    "/fIahb73vfskhHdqb+cW3PdutZdn47tfJn7OI2d5NC2PPlS8CNbripfbnzefFg+3eE736YfqHsZPX4p/mF6unS+eW/5NZcU/7VXl"
    "3/ZSbfK31mc/fP/Vggt++yYoX/2dx6TbZ5P+O++//Gt/8Uc//UsvWbvvv/pqcfJuz776q49vLHx+ndN7k9cbb/7RHVTcJOtP/vU/"
    "WgTkz/7Df/zZX/v793J/uoCHuzQv4rnYzr/6pz/59y/1LTx//+Ovfnjf3+i/2aw3n/53NP1xLN3wyrPd/EYHbvW9e43LnnXGbWrh"
    "nj/6pFmfNqx8W3wnfdrdtIy+c9sT6WlfvGXkFS9a5DUM+uLDhMj/0DTIPRL7QbdRN+P0DVvnZdk9GPBNGxfedFv43KrXirb1Pg6p"
    "Ps2oPmU93KZiX4J99xmr4f7xK9Bny+en0IdytFtrfvXNfc/8sFnaf9sPavn109U1CRf08GsvsYWlQS/G+1uTSeHzRNJHOa4fhP2L"
    "h8+r2xzWEN422/C9amleeO/3u4dfXOrHbbukL876t9+8w66X6axvuyKvfIbFxt/xzCtk8gET3ROYbgbyaXLgm9gk/IVg5C4ZHztV"
    "l3vi7qtc0y8ekHD97uG5yOp+lN9jgeH9/VfJvS/72d0XmX6Yy/u42oePJ34//8hkPw/dFxN0Q5i3UGz4LYTwsu7H7r//+X2jtE/f"
    "3GY/P03z5TWwKuJfuu2Kgq0fUpNWjSsk8XFJLf/t9seEPcbLlXD7uln+d5a/DKPlW3m5uOBQxuqmsV71qyB06cBEkELDyXlu4AEz"
    "zbo71bDFnEKURRzhOib+ifILauNexIsCQbXTcEdRQU2qMlLHVBLFLff1cdA0kbomsaFfakuvlash06zonPTrNHKX69iwnSiBzqXa"
    "Ho/5UJkpOfRRGBJoC+LFarBX/Wj1tSUzJpleVDJrBq0HIyLqQwTE0a2l7pO6dxKFIunVZr2fBybaHiiB4a1rVzlXTbSmqmLHo0I6"
    "hZ1hXnppKPRw0Dnfq7eVdt5sqgqYTGkTq8ImUfVIhNn9AYx2/LZMhTIWKE/Qlauee9xOFqDjzvAubaKn1+tMJ42Z0pqqZOZ4Fo/B"
    "iLSpUXRnJla38UajjsZWPAwr7ORV+QaNO1bVlRCvdcHp2GBblEJ4JUliJEPO7ihrTRQFg0PGZbX1yBlCUqaeQs+x03pvEoEzltJO"
    "B3ayCO4YTormaaJIgDLjUuAhVZx1ew+FQmEN8Kp2rMOqh8wchCB2VPdR42zgNTWyu4rIaMBMzXR1pPf1Bl8XjLsFxS2HGu5AxhxE"
    "7EztHC7dPVxlJVU6G0VO3aoO+oneEylQllMs1V6xp0/GYaKo01xXHZuTIBrHTUQ4jES49VglF4JVuXrLzsoVdmiexQVFj1OppkuD"
    "219WCkduq12idNrZB/yZO8e9PZKMy1gFWEtQRJvHjpejdUUymGWaOmupikpFGTvsj451tBnOjStna1Y2s64zfEa8AQOi2mNj0rsE"
    "UMeeaAZ2MEq+6PUkWCEgwrFVGjYcHbcYOLc+4Tuh7fnwiEO5Bh18/rrHylUsFHHjUHBKH/gNqgEn5MiS0Nrp2z1fRBU+g3VFHz2g"
    "ZLCzlvuGNV1ci/RlEzwxKpuv/TXTIqTMzfYhQlI/pZmLI3CTYKCUJJxWlkXIUa/52aAVmFMgcJ40WDECzHqvH6EUGyWRTs4GraNn"
    "/yyvx5Fljc2R5YyD6Bkhp+g7krogjePtbHciHPSMn/riXE7ShMIHT2ZKJhBRzDRgLCzlCAwDZh2stIN73kPriHLndaOur/OG1ifP"
    "LdKUcIyqpjdcR/NGw6h9NVjX/gRA25m0BrXYgfYcTuKEbqfsero6zq5d7YIeKScKU+sjSBJng6CiiD/vGnBlRU6cuSuLTUDICyQy"
    "t8ZJqs/NybAONKP5yvasdTZ8TQY7gdTBwvWIp3dn5OqZstvpuDtoeNAJmrIGji4b142H+BF6XRHh+gBHkX6qGZeERzPhDNGvQL+8"
    "GvU6DzYn2iQaa7CgM8Ig7Dg7O03TgYvdT1wPh6cYWUZkAGZDSiJz6WiFBjqRdo5A8og23XkX2IIqEy0Kky4+aVFYZ7wqkpnjB2dM"
    "Pe/wM3SYXOdkCsAuVc6XXWbNoGU5V3nlz0mgmyGCri5DUiMgclkG7wXsp24p72KGKLrFEeJ8xjdUvcm19aRp4zG74BZyXPDymh9q"
    "tTnRkmuaPpqzeDrzxRVXDvVGk6kh0k4zTVxPQ+MPe2SQ2dxMQl8ZYJStSNHJwkKMsvjk85AiFKTZzLtuhceGqXm7JGQdPlTjBN95"
    "3aVHPHQGV+cDN+PA2obw/SCLW2QiIsBPwFBfAaKnhbIXlAcDjHj2jGGLJSFnDA2wkmkL9hQzmYWbvg4GlzMIBhG/0goOMQuPH5UO"
    "AnGJz9xYSbdkHXQ+qe6YMz+GEkpW0Ok0k8RUlQWoJTBtbu1zWy/kb/pgUzM1rCX7FTJIhFM72nFr1sEMRdd8twX94Bh4m7hxR5Nq"
    "9DVKDVq1BYnK3CJFHUT7RpREHnfXcjslI19WaBMMG26l4ZccIGN8dzkNmnmUJm4EtySEjzEchcp2ANtqxtpylcrubPvDeYqvaX3w"
    "NtApiGTygjcttEIOohNeUNoaeLpL+LWyJoCEhM+YRZBaaKbQ3jiMG2gbevjaEzlho+FVfUgB9zKCKWlPeLWq3XLNelouGpgLAwoR"
    "ziiK+zQZKC6eQTgJ6RenyoouEgMVDJqe9L3kxCyw6ZRV/ZZgGBqccKb2epXoCXiNO+BCozYNBVcsEHqUTwRIy2C2CnZbn7LwU2ya"
    "R4BoQbeH1xh14pNtQEZwTNt9vNKhmVotVkItN4BJmqsaSLYUhSfWoIFGjDQHT0B24uQf5EPfyukAVvst4c7QJkSECQo4oAUvEYNv"
    "x0M4XDBrVY/5tXJiDh87CSn0s1rHp6huzFNx6UqpjvloEtYAODrA2aNki/FHJMoPWwla8MO2IlhxAopA3JdisaG3FcCVid3TZ2Qk"
    "RKBanZZm1Z0dAYs4z3VRxTQLT9fpalI7xqu9nCJC7LrQ10osI4+3a3C7awtN7CX+sjJdNxgms2WF8jJ7rhoeIgg4we1p29IloIn4"
    "QdmXAAWfcNfZXjqbi2K3tVBIbS4BQPtbZYfHcLAT7dLCZA2zuwSKpZ0iHjZG6116qt4f/N1OE/hZsrATyOL6Rs91V9kR8o5iXfO0"
    "RxIs9w4DZ55XVuBBmcJ6BzdRe642TwsrQmI+sq2775RjTbT7tRDR3GU+ZFwjQZQWFSN6nUdylyR9RZbH9orWaWIFqMxzGkVlrpGq"
    "2YkkWU011F0reyYv2PplBytBtcuIINMgQcgvjXv2wdLKAplX8CNVN6USawTLxpTOmAcJP15429uZQnQYVFcLzIIA4c06TlOPrtNC"
    "7SdvUWiwN0ADTNZgCzujnTOSdcHJljs3Bc8ag3F1Y3okSiCDM6vDzNwK576mTRSPlcpf1ZeqSBpxRtYrSopob04KVmqqlvOtCOrp"
    "Set7qFhQBJpTWjWPh81sssauymCo3PqtkV0py00gx6KzlbdgHovaZhl3pBsI1hMCKj2/Fk6ZEku+zsNOrvc7Mtjn7CVpFwA6k9gk"
    "Xihhn+4OhcBJ2S5Sqes+vhzlQCcuolnu592RcieXGIhjI+pnywOgkSZI1Qwv6WZ9trdXm7Z85jIZVe/aeLGDh6urANm81xPyqgcT"
    "JwQ23hiFfrxMo9Ps7XFrkcnZIvWC0ZyFjB0V7CHWX3XxKPj0WkeKvFbDyB4EP7/mR6Hnj1ARsIICbUS9HxBrgzoYktUFyuwWs9ag"
    "67qENQlv1RAfZyHn17VvGerlqqdLvwygba4O6WOnLOv4MN4Xm8xpREo46OAhPYjhZpxcM8ZChp58RpxKdBwip3PRvbeSdYQQtYpZ"
    "Q2o7HVBfC9uCO6LDNQ9kKI6wyVfCqxOoVzQq6Qkr+9IoT4tFCw7lEcVidsWYRRhs7fi4wFSN2dbSMeSPzIZORekyZRQyqP2CgUBn"
    "TZ/7nXsI7I1bVUoVwNdDqPINWhP+nlxwoXOO5APrHY1EdlQ+WcMjNDZwlUhBbs8oVIfOjtdMS4WvwlDE51brZTckjHmg3SucbECq"
    "nHQNDRcEWgVondWEGB6BVOJUds3UWLM5r8jrwGPMGisBfbIlwzqFoYddwNwO9fxkW2TXAJK9U2zw2hzq8/Fqj5QKmF59IKZ8kJDt"
    "LjA4IoMXKZ9lbKRk9tD0NUKKxuIkhJq2m+KLXvCoAh4OogVr0aYJUNdZrTpdoGBs1aj+PrKOW28eFGz5h8+91A6lqW5wepYBxwUL"
    "SNwXHJ37vasH8LrkD4BX9e3YqLrBXTGTXh1Ujt/ALhrgzdYC0MWckDa+puuE2WDHk6keEW/d7/QO4LYNsiXIUBHz0oc9z6N3K/Q6"
    "qLmXy5jkGR1YjU3f+MjQjAngspqCno9VD+NCrXi5Ix2oHANEKwgaYlvz6FzKhC+1K8qmeItjipVJNsAW5lFjGNzzdA6DuTNVsdqv"
    "UDltUE7P6Ok0WYUOHHfmtBFZig7PhwPDTQg0MOphb/aLqWbRQjck2i/hSWgQefagBNrmycWh0BPlkQ6aFKUyW1cLAsi2QTuMV9fj"
    "wHvkGm4HUdjryspEmt1ErHJpt2bUgIQ0ybLXFut4eGJHIVdoW76NomhDJuSK08SDJEysaW48Ke71suynqTxeBRu6+jqRkq0rsB08"
    "NwBiQRndNMpWC8om0UmGCAmFpo8CZ2bBKUxWV7Oeo0kTrlm7lY1uQ658CRq9SI14/dheioSeagSIG2pc8bNoujFQFa0/B+0hQbuE"
    "vhZWI6sk6awvg+baV9QLDg3DO+uc9rVNG68FBUOvqpGUw4GWmAs/rqHl3tSmRX46RJzBnfJUSVeR7SenHTDZqW2XoSm0lEFMjI8o"
    "JW/C5gxxq80OHSUNoKimvrqyoKnoYMkifMUTqkLNA5jpqbTVHX20Fx0U5FDd4ucTgRCh53LoMq4O5XYMadqRU32d+OjZHkC8FfCN"
    "s9HixQnZoolPXEmYCIRYJ9w4Xfd5FhsT4wh0aq4Ng1c2iz+0imdKoy9xWwpJSS0SjIwB64upxZcBQ8pemKobEznPncFmNAKu8L3n"
    "MnBylss1dlRSQqUDPVl7loAPpS26eVGBka1KIYapG50tSyRPRwRrzcMqyZOwj5NUl3c7meApW7Uj+aiXdF+x9Z4bRFFfc8l2y+Tr"
    "IZHrqpx1h4p6vzH24h4M5b1bYzPXkIq5o2ndJWkLIpj0kPFZVpzDMNdYa4UJR9fcbN05DE6yjmPydVtdjfMFLrbiIPmiiG83QcPv"
    "Cf+A0Dk8mHgfZsy24AjCPm8mu+Yvh3EK+Wu9JhNoMRMcn6UXFMB83Tie15y1xsha6FYwBNOS1rFyks6joUgV27dJJGxSWNwyp4vK"
    "Bh3qSYoE5kl9UoUCQ9CLBMqrVD2buym5BGHDaOaGPoslKIaJHq0OTXBmgMCXAH0BnGBb+G4zlI7heHWiaWJanIQ5lMn1TK5Q+mrm"
    "iuQIE4gf59t4neXjpaP6Fbciai+pMzGkZEwwBJbJKRI21ry/MsNc9Qm0x3BeZqkI0cNLzZtrDOn3cj+F1Ug72e5a4VOJL4gXn08w"
    "HlzHfqgRmjB63yntXaDzVrxHzmvg0CA4usor+FpHWyxhkx7ot/1+B8Mnx7YGB3PclnUs2zFhqxgDJZqV095eFV5qhFsRd2iuo9jj"
    "NUUQDDpSZ+I0o6syPplwTiz6a2YOtVzYWHiEj6Jg0JvrNlJY8RC2OV/jQ3GNVzsFpu1iKywAltWVtOfBCMGOFeQc6GZBKZeUvCTH"
    "mbQvSoTRp5AvobVNElFzIDu8MIXzuciluNki6PUs5ViFB+1GvmRIxLaAOQvqqt5aGh329lb3hxBmHYSN1ycu06VyFcMDCDAreAOo"
    "+Z5PKzGf+ngAroAjDdGi0RAgKXbd1E9CkYmrZMtl0tzsC0oAuwbcJs0aGdcDR5mYxaYXm4XSajrX1+vR79aOQorhpec9OLSxDSRX"
    "+zRCj4kwaBI3QuCEgOgqo3dwaUrqZhlxOUWn0iKu++0ZGq3MIuez1ThpNRZqtECJXrMSdGuEWBtIRmTMZXseUYk/YoLrY+lIdeaG"
    "mlJ5rs6TBxWlyxGH425fr1zCIhfvO8OMta0k1w4LltF5PAn54ZpmdrKoOeYCXQ60MUHppHNMMrIzj3QsP4+jqOxcQ64C3XcWDzJk"
    "JdvwJ5HXL/ujROY2czgqUwDDhru4EIzPU+k64MiduwYuGVWNvjGe6XrLi1FkxnxJd0aR8g60uAubmYzX3FaT87PQ9OPIZ7vYBepe"
    "7SJorJH2LKTD8XK+8k7WITM3U0ebsVpVG9UCxAfHqKcT68CcFLNJ4TupVdB7Gy4GbCK6cnd0sX7wNtemF01sj7pVUofyTKDXA0Hs"
    "CEse0UrZQbtkOrahfLEE4RJmNispOs4L7dFe7w/l5QKZXBpKzorLgWgaExw4rxuG6PU0m8jt4vHx2omt9UM+toqTznVmSlVCnWRo"
    "pVT9lVQ5yvWaYt/GIbZfm1azb+YqSfC+b3gbr8Ss7y/yFdQ362y+hGCjExCcHxe40zurmddYoVqxxrHi9xJq5nyXEnAjATMq5mHJ"
    "DosNHFEDiHJABsFIGckE1vydu09TpXbdXbSDxFE5kqPukOmRV2S9WswmHdD2tUBdQNMdjhrNTW15qa04OsOxDBVz5y2KrzOoYXfU"
    "6AiGX14zHbfTkpvaErmsbUfdJ8rmQI9KGK5yRZ6vwNUHwCgxh0Hi7dzzwJIbt3laNMB0PdGLdHc7sBjrzXWx5XrOt8N5cUsjyAr6"
    "CbCukgO7liCT+31xcdezu3fnY11mIjhz15VGzHa0Tfe7bYT4puykyl7j0Z7bL0YkzXvuLHDKNamwy1G0/NDYimNTR6zFmlO353OA"
    "7t39VBuFQmTdPBx5zmAWHz5tMS7ZmOk5kC8C5DOlqyz02wkJUmRFYZLr68TsDlyHbFwYP8xNW7Klki/IYdvlEXdZ4BxbKyvKNLm4"
    "3ApjIwxSiNA7X+ObG8aRdWKkp3xh7GEeoWRDAL4rmJp1vDIdscdW0GZ/DDAiOGjXbmxyAruWjmkESCUcmYZouYks5EyqcgqzEi+U"
    "l2Ge44jUKGYs2InkHpVqas7Dxebq2adBRJa8sBB62cax1s8361NFGytCrDJVaxFDqK6dsrRmnRghg55dFqvshLIWUDUdO7Y/zQf3"
    "gJaacZS34FzYPAAo+kVC+oamJ0GHrknWtUWxeLU9Om6ujHaQNyAvTftNIeIK62b4qgWIw8AGUqNjkupKbA7jOlZ7PcbQ8ZlvccYk"
    "1k4m0kWbIkPhccfZ1GwP4A+gSCLhdZoZX5hHeEFS0443aefC0DLVrJgFnsaRSWaX8gJITJFY2ekcz9qZ8dY4yo1hM0i0UFBGmYzO"
    "bmo9HovsPNOqwxEHg3Zeh5pOnNrJXa9QjIgJuN8q2IrCTE7sg/Xym426MTRjlZ2KhZZ8yFuwfi6bNNsu32FJTbY2yfWEHK4UoxUn"
    "Sd/RG7dN4HLBEuF1IGs12uqUSKDn4bwTNLqPzyzXKcc+Wi+4QOMvqsPNQn9lEkRR/ICfAnDbl0mubOdcBbRupZxRvFO9bazVK7AH"
    "jlqNjmG8haTFYAt87QWRiM3jhpIqPS3t4nw20PVlc/CajC23DK3G0+SjZmDb3vmKuuVqrNKNV0HZsSV8jxH91W7XJFALHec8ISLP"
    "KSVaLpVuEFbpZHG01FLdWcM6lEXDuYMPRWI2BHyZJdZYiDGChVnWpHgM1DY0L1O/ALvgAitSKW/2tCWZ1h5JWhtd7fSVXasFeZjj"
    "qJSMvkU3GQyZLgAQcrq51p0uUn1MsRs+Fq1MFhgbPDOzqDb5jF8Rkc3nds3bXWPWx1ZoVp5V6mYh+0TgLb4wZVhBNvdD3pPd5PCm"
    "RoUGhWCn5JhT7Y5SbJfbnPXrwuGtV3BRyfPN7rrjqjN+XDFACpVIIm+kOuaO63y3krrOmAKy23ulCe00g+A3YhXpPMQunkc5CRZ3"
    "upYnh90mFXfhYK/Ki8CXL6cgF01UVMrGGU4jEamGtA1K9+yfz/zxYu3laQVcucs2nnQRDS5NZ6KCt+VUQ4jlDaXDNLth9hxCHywn"
    "9Aib2gR6qiPbRVytQ4oH5mDFR+HSHXKnqbYGYK0RJNRLIrgqzGZ9YRKZ0XWOkkMpFtD8AIA7KRLCgzHMNslGbRHtes6WpfNghteq"
    "I41Un3cnDVv8kfPFPkGAx7ROHzCFrw8wlXVgvjp4TLFVs3VC+wi8gpCNeAKABtKrUQYyQ1G43XWylFki7dhZr3UGEkWxSJ3s7AAm"
    "ociLO29N/JCLqzI8MtP6csohbxogZToewk5itg6i7ljBULArwYX4YZMP+0rg6Kbd5aRnerwXrDNQ881kuiJpil7yWaf3yCQ5ckZR"
    "MqkL8nVCZp/XJw+I+MDFJoGA48ABs6Yf5Eg9jXSxZS/NyoLj+GKFmx4j+hZvHAjqGH4znxHLHwafySalVjlMFmMg7Z0xoM7yKeoq"
    "Q6sAkyyEpsBCZdiZ1toJdrq3TXeLKSsE28Q1xlHVjhx9McyEXIQ1VUszFijS3s+x9XZ/5VrPX9fTFYSTTWNcJEA8oBuQUzIPFQD1"
    "iASaCg5nl5OjpZ0mNF1aWpCHGncAy7Y7kjHRPZIToA3wAwcsBjOOkC27KGq10hXclPENaPKzIjR7RCMXz18unVzRx111LtbGXJN0"
    "6bJsk2VVGALWNpeaHacuTjjdHC4EZev8HESSrGeFeZWHAeu3HnVszxt7RwCIppaZ2QUbOYOUXFkwzWaq5Xa6iuf9SUGDvFWUdT4B"
    "0ObM2OSEloyRR5a1Ua6QJvuqSqLgaSJI0U36ZOu2hFLK4MmTXGqnUg04osl6ZY/HETks4y46yTjHN4v1QGLdmVNLUvKThmzGTOXg"
    "0qhkpdjJkmXAQEsEp1MY02R4MK9c6qyt4+D2u2bsV+CwnkDQc5yCwRyHDWXBURavDUAWfqwbspZc+iwNiHz2iLIfcEDCTMerrKo5"
    "7ZAKCKEhAc8I5pSIsMoyJHQ4q9ygqmFSsnKBSsM9FeNYElrQLOjfzLA2Q+0z7I7UMcemSyOhjobshl0H+hm+rfPJGbZLJ/bW0TOm"
    "9ZXuVLVPXImp4cBDipFJT32frnNFyWzNb0CQKpNj6tjD1jvP4AI5evOaBzu8aTsa8rn4ClpBgwlXJ2IooudDySIDO83kaoPzTnL0"
    "9i4+hIBUC+ocsTgDJmGElmPNijOszzjZg4XgwBB33CdF28FXCLPPZlwfXd1bnY7HFh9QEdxQG5qIfALS+r1p5Kx1tulEsAqPvVD2"
    "GDOcfnXMOre3DtjVOAM7KLbgsbASr+KIrGSBOnJ01lZuynDTMjyYIGZVkRC4VQpmWQnuuHZzsoF5Xe5dZ7TMMxZXIwixrgf7G37Q"
    "o8WPDKKzVY1AHjX86HsbmvY3DFZOrbSf2uNBWguOjnn8jMBFsSOBcaZagq49s95csiFVh1NBNI1bw0d3pbRGe7qdOY3zRzLdrhFJ"
    "O4eMGR9obu3BR1AGrjpNIWHM6/IOS3KMJI9yYO5ndc0cTtiIAkabBTSqkLafH1UUHXbTyOi2Gh5dFNCwQRlLM1r8SZ8Ug4QsjynC"
    "1btaVZqMKxcdyI2OpLVq2ni476dZOuJ+0W/59SzXpuJAF4f24MIuxWrdM8dyvZPXV3gVFd3GrzNJJb280DBu5W+R/YwGJ16lyjNt"
    "HcPuEm3F0zhn8QyQYhnY0jKMs2xb2cDCy25N2yyxKcDF3FhVdcqiqpA8Z/R4u8wXIrVYlZikTkqtCZ4p1s/sK8idJREngCRtJZfr"
    "40ouicM6RInoEi6wRIuKlYKvgcxk25EK2l6EO8Wq873amWqwUkZLPPtcwnA1ZhVWfzot4LzC6eYMA6h7cOXMbER3qGmoadfDagHh"
    "C1Z3mzMPgEcpQOr1tO26fsdxAbODwN16zunNakoh1qYdrBZDkUuzZq2zADxKWFFBOUnU3cns1RZir/Z2JWdpagJHtuTUIY+0beok"
    "6GKfgs4UArq+iKxapwi/t+Dkkhe5njKMvHUqs+52m+ww5ZUWeqW1LTBoVGxVCEDQ8WIXF2rn5Jy8BiuDBREb44HMpmDTZBeScBwC"
    "pKsNDUDG4FKmOueye6Dc2lT3NMPNLa1d+xrSRGdgRc1EczIZGwLpfZUoW7AvS7wBVnkeOtmhPl1zNMSiIK5zva9Hdl0ajru10XPe"
    "gDjAK0GRiVivJNg2VTotwjolargGtUX4cs7Mg8GpOBpEIxdYikW1wj4JsoNQ8NdLBPhVgjTTmKMkMOs1D6RyXbtiLpzI3HUyKeFo"
    "6Hi0VYiGTudqVIBF958HtXMxd5Rr0ZvM4ayISHA0Ihp3IRjkpEUJKL2V7HiMlPhyoIVEoPTRLsjrwhe3WFDjGop63LK3+KrKFmNu"
    "AF6SO8dlYJo5fgUwqEpTAWql9Mxt1IOw3kB+oeA4IQM7wiGIy3q2sh6tzoKXOCwTnWx7Gvl8L0Hyqt5VV94L91cRE2wXbXFY4A3L"
    "NDz2tKgh+Qi5oX9eA7OnEHkAwy6K20fSXvRT2QztRmyYXstjf65VOfNhwUAw+Jiqtlq1zNlw9/PiJ3QndB7CItT2HN8GOVWZe2Mb"
    "2Ins7QbjxEPW9bTybboyjhxrmpXKHI6bKwdvHMyd2ZIR1nqsbiJIbTslL7bgBdba1Vnj+upo7LB15ZPwNTkdF1BY1+dL1a4qv7dP"
    "p33JM3tZ1TMiDRrJiXgWR8FewebyCqnFJRE10ZDZExz4Ol9DkEhhhxnm5sFbHSqxDFGqSox5Y5STGiNMXJbcWpTq8ehZp8Q34t7f"
    "rsfLcGbhpKimCxv3JHfshjEQTWVxE/zr1h2P3QyymrCBuDwvt2KfhxNeX4q8ihTDddZywtrAGYa6lrKPc3cGt9XIn45XuQ79ZcRx"
    "k5yxJOHCiwzAx1OyWYclq4juXvJEf4pZPY4BP6cufuGXmMD7gz0d4zFaMfCibM5eZrkkJ3UBlJ96b2Mhdk5OxI5xGhnfHqT0QIXT"
    "hoQv7FBftpEP7A6qKDgbEicpYi/Eh4JT09BjpYmcJYzabdJLYGzADbpZXaXVQcVhRCJXpYklSYIsbcjgoD1AAO2PO3oF25BVUpFH"
    "d5yFASx64Y0gia62pOveiTwneLYmAptcZIy66sy2oFmUH/Ym0gUHVm68iQ4DFdM68DT7g06rzppxCyD0gcWvME6HAN4My28UEtf4"
    "WKqCnbNy5DRH1Hkxjruhmc7gKrAbhNw06rWO41BEGscK2avgdwkzAXOJmbYgFxpqZ4FYEilAjY0aTsoF3tb7BeB0+P5EoNFWphRH"
    "2O/dIPR0DNR6X4Eu7CSuuP3W2ANXSRZIWQZR87CZeZdWyX6j9XLEe2sUlMgEpBdvoL6s2yOTrcOM3I7mzKnMLjc6wmjO1dCtJtMR"
    "wH53thJ7l4KaeGhNeBcLiwCCZA/ttyx9Cf0qjmCByWtlK6+JTLpSG6+8Zu35yo02RJvduTtImyTt04nOzqkYMyotzcl0cBhThMnF"
    "k7F0gu3Vqygj+oHK65HfnVxNL1mt3UqdRneimparLBaJU3Fp51CJRsXZXxysN0R8J/qMwAwDB+L7PhiGAd8OR8MzkYrLZku/tHbE"
    "D0dTT4MBN+QVGpmrHducCjxLWFpSfMISSl/Yjzh16eCk3FjCxUcXeaD6FUkjjC/PggzUTQeWZy+IzSRTjQUBy0fQ6ZVrEZk2EkEU"
    "sj7Eqw1Gn4JBoXCABKviBAK9jCBWNvUdcRzUOCiKQ9Ydrk2mLyo7IvB4wf0h63Y5NJ/EIKZUPNchj2668wJxTZ/tSdjSobYNF0+o"
    "Mf1Lj00Aqls7ye/Q2VqYNxRaIa6xbX8+h756cIw+hgJ3jts22fM13+6nriMVBPfySFELZA6IirXnLZ2xBhusag2BgLWnkeIJNbkA"
    "aZB0iJqsC1aZsiUNJIgC6YRmWhRV5BUK+KBOOjECT7t1FLaxz2XONtyCM+DKGiDBqrOR4TV4lOX1KAVRxnC5jC0u9VzuToS2eJzI"
    "zDlFJ/N0lwO2svj2xPqonbYJUNIlAAUheM11AODt2ia3rAhqNAlaCzG1jBAuQ8QzDDEpuMJPNqRd8MJlN8vPhQZbg6sIZIf2QiIz"
    "WCfgRux6MrVH1LZVXeOJHo7Bk7DASggZmoIGyxygGc+KWjjDqVRdPDuijwb8DIx9G4IuuapPlwu5+PzwwEyL31pE6yPtdFh1SoqG"
    "CEGcWPhdGDnKHVKEUAH4gpPXGuzRpdrJ1sC0nq+o7SEE1G1r2JucxA49Wlr5m52o6gv4D3HHa7oDiBFxEJFBjncAPKl4KGmo6qmi"
    "1i6YxZiVWACVy7wIUAUYmtmh63WUTjthHCq/aa5Ed8KFdF8dYF9thLq34RwHSR85DWdbRaLNXCELcItmZ01bJ4oGHCJwYFjTqmxx"
    "yopz1fTa9lyboyuJ2bZJ/FQnRb6TaNPrUwz2oS2Oo1V/7rYkgIW1R+HM5Qz7s9xIp1OXshEyl1AUqTsoaJHmUgN97q4lvs6x4oi6"
    "9tVdFa2X1wW283cM5LvmZAbzOiZ3J7Jb9R0WFVe9HBu38xp3yHD6PF5xfBGtgAx5W+zGhR8Esdif3LIOnJ966KJLlirarac2Zj8l"
    "K/MKIq3EggAQDzaoXQE86JGwOnXisOX74NJg4s5ADpfrNVxtq/qogWd6ss4kZCkFyxjz4qVAZIuIwrSex1rYh4U7ECMqzroYsodw"
    "7aWmTXrHLTyEJ5IEkeF8xMtToro01mmDNuPrnjMupyNezCCQrE4NKu86DBS1opHNAIG5fWf1l6kTpSwXrFQXbXBApzZGzn0aply5"
    "5+Sd0liT05pSQHQmEtknGCxBZDuZiyc8RFa3OpfXoxWMKFnkQYDRgytEXnYeRgwhMUx1mDUonQwIyzUkbO1+DSpmXhw9gs6znOFp"
    "jt6kp4PrZVc73rta5CS1VGqSEDcmVre4tLrWXelvgQomMXgxWiB5QcIhCqvjqpoREl0V4549qzPfyeCgRUjWIjrIt+j2DAGFRXhF"
    "G7g7F3Yxf+8VNg/GLRXoJ/Zg742MtxXkGMu6w4KVSdmHXObMkEr5TN9JsZTKx77KhAoifRMKuzq6WFq42scqWY2wXiMEAoJTXTMn"
    "X9LYDXbpkR1dRmi3Ig/tYJjVYvEoHFw1zuJWbS9L4w65iRyGgBD7gm+kfps2R7a2w5lN97RIZom4MYaprI2sjJ0UInDaI1bqXJAt"
    "IUcAJnvlrIEFSE+kBCgsa+Cn0TNKLW+mjj9vOQddn88524hHZ8WldXE4kh6DWDZucYAWIvTaiA7xFlwGfoN4i4s9rJzFUpMb3KNm"
    "XTK2PdjRDFkNpw5M1ApggBG3G39NhIPNp0UDY1XvRsgxgZxJg2Fyf3IOZ7HbgOYkmfV0mvRwoJJhFVcJfc3lPKHi0UFOctDPO0cN"
    "PHEeBTeESoWY1nVwErNmMK76tYxjsSGlcTzTvKDOqj0qrsK5orFASv5iqXPmSm7BoP65l4hoOnCRqXVZ5B9BYBZXzIzjMFMVFbOT"
    "gyGEEoCAtFPEy5APkNgmqFazAzPrLYp2WDC1WAfG034eZoAi1YZJVgHv1h7J9ye7DA8HwTvs6E6Jrxiv82CNmWomYYkVBbS0EQ9z"
    "EVs707eqOm1VKzG8bF2Xq0tvdZywE3oBNsBqMVdCuqlC0ds4aepQSFI68PHspzuDy4W2Ex00VZYRvhMQHwqKeu2q5vWAEWS39a4Y"
    "kYCAU/TOJBaqAp1VYA669SxwcSyrIVzwAxHhBIZ5/mWViv5tgQW1P5qqIaEbRxC+fz+y4fF8+v+flmvkxctyDZgM7cSHETvCyRFH"
    "0A6NxyxOhSO1DH583JierOSSy7R7/thL3KGz1rEHIR7QFXIlHqFud8S7xb12dolsgCg7dGLBpZUFAR2UgyuREwzcbEOXbQ3XuOxx"
    "0TomomCFEhBT+9G5evMyuHs1Qs6DcVH2LLVJKdYONyikjWwcqiEZEmtyAog2g5lC2Is1jdErajduR1kjBn2rU4uc03Izd50OT6Fp"
    "DjHi+cnUdrSYV6lRdr4s6vx0kNExbb21LvG0ajUMw26UBWul9IbiKZ1NF/4ulGLbmaaETaqnNE3RlEiXRzZmJY6vy+vyYVCiUW1X"
    "tqmwieaZYuY2Ah+YFz8psmK7hxVSatk2nBffabOgUErXacag9yFQ56SQl3PJOMxB1lrMEnjYKcqOUnCSPnlshU/EdaKkddBiQX0I"
    "Brm+ICgAemnQ53Erbd3dihflq8WZR9o9sDVVUk650sWMARiXFWgnseB01SpjvBF0TqYkw6NIx6XciuaDYiFrvbhsHKepm4W5G8kR"
    "Nvq+5ZrDXoEKWriSR35j2bGn+6FqxSk9FdZesL2uPrMoVRbLMDd3I1L7ux2uFvacjxDW6wO1gvbHGkSICtCrdsxPsrEVVetIseb2"
    "RAWV5FIcRZ2o1BwBGAhaLbv4YCTFRNjuxsn2d/2V5U8GzqDGOKG6JEVJlvCC6CYUlQgZH3vajjpuqDQ9e664a5pQ6GgF9EKsHcQN"
    "KnAtci0gkBRRu98s1F5EZ8eyDDvqE5WKFFUZ1l6JQz+/sPkFEnFhcRkLKMRwi7UqdvSzVYah6m6LoXQdRBfhMJisQQUdG7AAFCGj"
    "xR9p1mP6WCp1+3Iwt7iqF8EYaGR/rYriDK6PBo3vCdVZJTXVmtP+SF8YQ1ekQNQraiPttzPmVtgCjMaebhG62wgpI8TcfopbwYh1"
    "yFynewPeWeZcdxYXSP7xdMygwXZNp4/gtAIviXCuvOs1IcRETK76dD0cDza7xQ9Nz1xO+GqvgbK4I41yj4A9L7jz+krpfX0QE9M5"
    "TlAoRgmwU3QghZj9aSMM61adZE7f5JqrcQvTaluBO3YOL/A8Qs1JmybocIymqsPaNdV5QWgwVcSsIwBCVBRcnIoFGGs4fUHPzAYq"
    "j6GqXMplWIhZhJ60qtuX+3gt5t6xpIz+PDveKjglXLOvQGGrVTZMntVh3bA61Jt07QDRuD+tgCFtrFEzajVaVSewhQZwT61XGiIR"
    "J1jXxWR/LhcKX8yYxwIiDa+71DkyR7PMOC69ROAmjnRly2JkjMlrvBBa0D/oPkgIXhn7SbnDQ7uzbZgI5Sym0rJMBeO4B60EXxMj"
    "wdIATsJlFkiiKztmWXTKvhgOW/V8gOlYNbqVXYuVlq1h3Fpf8eIikT6IgMipE+zNpkdUi5KhQ6LeVPxmyElCWvTouEaZE5kq+zpd"
    "nsWN33kdTniOd1hsMp8Hys4twK6mUcB2jCjDx9W6ttMtA1127AWH0rpfgLmyIXIC0wQKFKNNhMCDHxFD5BNdQyH5htsfLhZDD/i6"
    "XM0LjNhyOitIeUtoW7skrQ3RI3ShGhxwgHRArzdEuqP9Xcm7K4A5NbGxQdDCIcANc3XRk30GAHmSAJ/XtjMc8BSvLuXnOD04fHsp"
    "AUF0oiw5odPWbZP1WfGSszrF1AJ6Z93Cg5YxiGgFqiYOMBR+aLdk7LoXRNx0JRxoLbmV6NNuVexWTH/dKX2/7/D+TKpWdzKHBfLV"
    "VbXoPmhF58GpjobF81mdhCzii2ktgcCFRQm8y8/gkbPC9eoQQXxFs64VEthsgD2zBcpDgXQV0W8WjJNPYnDNV+AeV8qNcGRAzDge"
    "PDuNQ8BvziJYorKHra4lvSAllIKu5Vn2UCCSN5E9Le84tdApFlQdMvO69NVEkKOLEQFYWQA3b9ZtptdJWnR8jjlhEl2O7L4+biZe"
    "XulbE1uHq2CRMxJFkOnkVtTWgZANZSdbk0blAPV2tsacPZDwkKQjrpKRpHtFO/ToxqU2Opdo8kjWA3PAzb4vqrPTQvhgbOpecE3u"
    "RImr64X9/1g7j11XoSSKfhADoglDcs7JMCPnHM3XN/fNWuphP8nSE7Zln1NVe69tX3Dx7RtMKotbrjRhiHm7AMVTokf6ssOy1lti"
    "21uaILlqeFhqHm9YXkqTbT9rQ5blueQEhG7JVxHsexlLoqvqQ/Yw3Iq5sgeR78r1cdGZEOUnIkZjErFBNMdKvnWW1mKHUCNNNpzP"
    "PsThQmfeMggI8JRKIzvoG/ltRyy5FCpMVKxh9npzIg/psQwo3QpllAy6vQ7jXAGvMlLWhgSbzdpOu8oU/AzQXAWynlhyvetGG9D6"
    "2J8idx/56wGvoA0iNCFUCH88GxiVkiak1CTwDypL609ucCdwmL2paYkBibOW6loFhFmwXf5qr7Uk66mNpsg5gdGSrEurtJCV9PVA"
    "uaujOTn5IBApdg9jw3qbhVHK1yRDQ9n4+keS//KNAY3xIHyj2QcwTzq/o/LzBHXT6HCfNPgK9k7wJ/190l/tH44tHwOb5WaqVKZi"
    "AT311qUa+7eB+u9HU2XP7i5Jg9msOoFHdcj2BMuh/QY2U+gXc8GvGBkH+aOFRh7k9Nnxn/Sk+8acyJ3gm66b2Hedh06vbbkNPfMT"
    "QorK0EPq9O1Xu5JGNpgOEebSF1Tf0GTizY8funhRcAZYr1vSlwkVV8ZTcvv25fVjDY8G5/KjMGwActpvH39OI7YPKfd5an/X/IoB"
    "mjEDtf2KWRtxjONhtD3/xU7sVjEkd+2MaOYb0tV6DAYUZlqtpw1aEhbfFK+Y1SPiCZoZNuFVz+RtWqqa/mJJSgsDmYYR5HHfNUkw"
    "mAknt4HXCPxBJM9WjKBnuTKwXLqwKtfz06H199nML8Ve86ZWP7By9ypv7K8GNBg7PWMt+qUfV5/ogfH1a+4mS0mX4P/8H8OIlxOM"
    "bH5Y6cbBPtXe2Kp0qZgXlJOx/i0JuzUFCpvTlSrIdyV9cXMpyKL+bm/sf54Acaq3nMtFeKm56yB8C0OQXFm7PrcJN1irnMtKRx8B"
    "LSjkZ/nsTVLtqyJpKyBrq+P376dlgYdNmYZEijDJQ0M1Sxf5tbUjptIE4WWdSlYtmy6pgSUXtI7d2dayspTxVTsHz1SwUDiJDCWw"
    "Ib/czzSowhBCBcPLs3BFsaxOpp8PO2D9FEhmfuVGMyHDuGAF86ojiJPzZY7H/axiGFwNKOyIrlVJc4QZZGD2VoXWlNuyZuNe0O5x"
    "KoUhJh0OfSYjG3ceoykD1wb99RaXrSsPxPixRtPmYwBcN+6jkiourWESy86cSJjfiU9fZa+nwU79fRJoxt1bxOrZ4lHfBWnYVdgb"
    "EmK/7Yd724gnHF8QxxNV6vagYY1CLQ19Q5C5mlpppDu6h+qqi/f5zjW3hTAl9jvXjs1i7vKMzRmNtsc/dGUb826niin8TfEofVnm"
    "keqNTDnOhdcsgIdX56dw6k0DM31vYyeXc7n59Bc+maiCaVj8UdbMPNQfKKI3TNDLx5Q6zzYLOr1t1P1oaT2+IIf55tnjPI68ZpuJ"
    "GeXtHI7sAs4EhCqRedA+gFBlL7WkybqqtKBKIsNBvzWDUOjRhnOxeTVOKr1ddomozYHX2EOvTv8mzOJeH5b/pkNbsDpamXzF4QZ0"
    "i/U4OAJP61tIh09Si4oX5PwZY9KyOXUf184mOvDB1NR2Xlf5E3C1IS6kMJYY7WiHMQLcUfrnD6RyT9UenPjQPHEMpHuTlZepahYE"
    "zS/p5bMMra1GDfGmg24Uip5+NJvh95U5ejvVJ0yiS3oEbkrqvugESO43jdqgcS9gB+Mwfwv8FzHjSyc/oZrD2Ax/m/34BbhalTJW"
    "tjfA64B+RkY7f/lut49dYOqxsTG6pv0aiV3gI4DUdZQPv3rsWEOdLwtve/IQKxVQmjFjsANsCB/nxS+o6EwLvsTB8uXY5YvS3ozA"
    "ABRMRv1R4S1fO6isOjpiVDliyoEQPmU7JgglHp9dDHkYsfKQbJ4ZNcLuu4aYRx2BhR3I3KFswAzyTDZHDgPKuH1KkSj6Cd2okHCq"
    "oWITYeX7OiImjUD2goHIjynY0RU4UV0fa50EX9pW3KZ9JtfRVQULPr8cCX9z2l23ergqys9wmjfikcAk3WfwxKnewu22z9bX9RLw"
    "4fj24JuyPTDZu6681zZ2dapZ5X2JX39pT/IBuQVNkGTCCw1lK01pSUvyeLf8WsWUlusvXNRFSbWcNz53iPM/FKPUFcWwJMy/9YQx"
    "3zfoIswMo/bx3O0ZX0fcJZMpdtv2GYazuWIy8oXY/twOteOpAMMytWaGwMAHkGKxMv4NKG2zF86TqNzJ+5ulo6ayD4GLh+PHs+mN"
    "qQFKjW9KnA5Bd5KNo39eNa08Ccm3LDO86DDPU36/N+2s3Q1jp/ktmcbiTILfr7issSn1WHw2GPZNvNEgSEnUQwTKMwwM1J44wwUl"
    "3VRaeH728dkFHCUD3Jo4I+yXhGce6G0Z7hebnjU74Y8uSoxhewVDHrO6isLKiEVR6JR4GvAeqVkX6fwJgqBKuO5n1GXbr1Cbn2W8"
    "8oGjaEkcdVJyxC1LTp36oR0tofUpH6bOtiCwaZzlQ66v4f8SDmBNaoLumlenOfJ896UihdEIu2aGN8qqcrcT2g6Bww+yq5dTmH6i"
    "+Si67GtnbMjEuBonRwvf5QiyLx1AVyh3xee+cLG7wl/T91OkMArPR6YQsXlZ0oztMFzKW+F+XA66ixerfLkqZBYJKCaMZvRrqiEx"
    "uL6X4qcOQKi61hgEMfiiEwKNFKX2RAP+VelkzaldX4RYWFcaox9mSIj+VFfSG96FEYu4a6woqm6iuMKQpVLsJo/XO2xc1u65V4JK"
    "gJPwOroNXuXTFhtwPA9x+dLla+YYf9QZO7Ff9tgvkqiLy0JJl2lml0ZbtGW69JNRbQli3X1Cs8oqk19Xixeqk0H3HNu/Dl93LnEN"
    "2s1fdCriBL8CEDlMftVqU6+9EvyBKvpdtg9nX5vV7Jnh8INNHnEGp6PGumJLlC82+wp56LWk3dfJFB4d9aKgBR34zWVip2Wh5oUI"
    "PI0GavDSe49tTWNLdMfLh2qqwvQt3inFNvKjkjYSnALDV+yYo98oX/Vld1gJmYrhnBszMbG+3eBwa5gBdD+islIYLOM/h2f0WzMu"
    "PZUX3zOVq7waU/pi6XioDbRtByatHyJmi0IsOyXoae9XPzy80RDk7qA2mrSQu3wMpcU1Fu+keOKb9YQoE2SzwQrzZTruKKTOkBWG"
    "izNozFw6l/EmJg7xww/GpeahOasqGW1eIocFOCvyiH6wMoVDA4DYRdz5b05+ejO6wrsmskd5xAqRmlRjykcRMarS2IeG3NQdUOks"
    "e4kmQBDDgdaS/JD4TXQNfSGejO7MhETit9BgfrsgCJggczt0s6yracyVJl9ARMnnZPRYZMbxuOXswJTwOn8pdoGrMteXUqspK5tr"
    "Wl3QGYrss1gK7QsxIb5IQSAxaJDhL6E/1GRMcNNdjHwqOmBi5mdouVhLnFzFXHEZzUpif6RFkFl+lrVFsH+b8yCX3DGOwOn2JfAJ"
    "hvtzaYGX19qjJTwFKgfDxxUUb/zikqk69g+scxQkjejBfJB23S8rVKGayQmvM0sqkqam5BQbP6Ji+L8jGUUPDl+JqBId4pn9qZrK"
    "PZTagANm8nDvRs6q/oi/DjlWgbkSFZcgApw23wwakv2xjqmMPxdsA6I+rwdOy2pids977TpvGJ2+55m/WDrKMN9pJVvk/QnwyZLZ"
    "Prlr9Za1Si3CoTfHT9PPbN6Zi4PXjflIiOpVZbcDaAP2U0doBKMr+NOX29gvnm4PRyINTSnziiqrR3EYWYExNISSYuOhdBX0rd+0"
    "b4S8OWMglBWKY9nGpCqZrNBh1nwJYmhOlavXBf/1gkDECl3A8IytXBM6GyIiwVa8zHPSe8OpMFOL54xUbM6/v1Zech+aiCfD+Rzf"
    "UYhbMyyHjNrqWEAs02XlGcMobimsFEsB1OR+tN8j9Bw6sBBBHC9+W1mBXoBWEZXIJ7PxyavJBEha2xhTHkA2yMR89FZzuekYemO2"
    "GQOrz+YsshwbQ7t5BUVH0/7dtgBZmAWTeXs0Dr3LwmHgH/B7OiL6rlDeFYO3mloIEP/FEs5jPYl+3O24PeDtGYTkQm5hHFa5DFcB"
    "G4Y/TlAUiuPS9k4cEUjQlTeAw1Ehv6ETtDhMOp8defZLlkjXqbeupS2LhNhOXjMM3iBXzN6VTnTTqFqE4XRyYTa9uu+hSCzImVEL"
    "zvplk00HtfjYPEqg6/dq1GoamXCn0WqpY7e6Z0SrVPO359WnrKuzBR7JuACykY4Dla8Xg1A6EOrCV38cRoHIHSr5S4ErhJ/XRAiU"
    "rn4KQ4eWFkFo86y+mw2sTNocsQNnn4SOgFXCRrZopK+h2u2I4UTxintKPaRwc5piDHErZz5Gy4vy9ZrcYdRANGdquD/ftsFi/k47"
    "Hs4vdnCjnxeD+JFHtb05nSBANuP69/rejeBN1fqqF0E0yymeRPLFmW5W6L61LXAiq1pZ6uggT/nI5r9tcn/9HQc5Fuewi0RGF/cv"
    "JbgzxWZlefVDjRqZ/qiOGmFXe2M4HzJ0pVS/YAG2AxaX9jBM4i4rAc12wZn8GrFbfUX0RI7ln6pM3ywXBA6PeqPVkqeRO13eVMjk"
    "ub+aimR2UQ/Wd6VaHqoUTKnf87PtEU3XSbtTlqz0hggMq1u7Gp38gPgJXem8KFylWcAmdMgFIK/daMIbqCKMdjfUQjS2ZeXj53Oi"
    "UlV49++lYMhIA5rjBT02GIZH6Ib3qaRyl+boZHlpvo2kUPyMeQfs3OB3q3C2D77dy7MVtpSGF4sqADrw7r6xCgdrkcwK5jPfn9NJ"
    "RxIobie6u5exk83V7HoPdeNqPsdCd2YBRDcZIFucfMydZCsnzh+TpKi0bRSseOcMG3ZihAJNrdCQ1lzVW3GVDTDnidsQJPhbt145"
    "2PM3Ocf7qKWimFwPBg9DECid+3dyDnNMWoAlX+okNCvRJT9wD4LeWKoa6yVzQ/OAr34pBi947iH/TrQDA4zM1Bq/HK7m7pn2tPfO"
    "56jUXCUE2nVX95zkNBHJSGxNRyu/CSVMnePHab3OdvFykuzWZkw/6hmpmd7nNBUa1AVH8L6Xj9nF9iWyX5883mkoyj6qaK9H2oQE"
    "MpqFe01ql5UcAtAM0tYf2idVjdPeJQnZbvSrWyp+72nLa6KsHra6rH8mV+qx1IpY9L7yq/C3rzvwl0YwMjbUw0FtuuZOQC5vEg1d"
    "wQUDvOJKOiQJ5rcP0Sc0FGHi6+pTSBQu0VY/Q/qoCckAQV11eIAWCtwcboof2GHz2jJaf2IGDGOqoO8I+I1HIbRwBYkXkEyLk1Tt"
    "BDNfkZkV6/N1NnT8GNukcD43PAL9aUcbrJCbJwcGZ40hOM4vVnPxyN/YXrr3QY/8ZV1pUBvSB7A0hBW6nDa5VwSF/iWP9tXPdQOx"
    "D9NwEjb5HtNh25HHAUFMWHUJcXxtrR1PwdZtn2+sxbrzJRiJXnSo7hZveOFd5+fvS4znbdObX6hrc2ak3r4pQYuhpWvoYnJjJYuH"
    "CbOtmx88EtPx35Pwz0+Ql6Dp+Tgd4699b13F+tXcc700qCZ1vv8Ev+vF9Qed4edn66scKXzdJFuO0PKRc+dp1pc+N7vbS0zWfjIN"
    "GiavRxKoQocstLMZxgLWj54KZN3rJutGGuCQfJDpbmH9yzo0Z4eXozfgRLzAY5lIg7wxvcJDJznuyrRJ9rJfWYU3xiO2CUG4YmFp"
    "h+fkNmaOzy/MJnDIZVrwfghJRMxU8ftG1b0GDq/QWgTRR7Tq+8aQfjFruM/csrbg95mYCRbER18n3mWKeK6tgwKbbq59xW5nxcNC"
    "zik6Buu8mhYcqGeYu0EVQO2Quh9nRcEkU07gPKsVn3ucBna8VtSM3dxtu9pYIVTm+SaiRcMkHSMQJo59UALZjpd0lWnQuTKlgKGb"
    "bcF455boSSWx8MtGHl0ftR5Lwhp/PCQwBOMHYOvnmH+iyYXP+Z080XYQjgXAsQc2FmailMbabRLGIyvY5GccjFZnEjGh/kF92up7"
    "Dt8M+frGt96IVoM9hZI6ZS5zo7TVWlbKqw9jbX/i3IbJ33UghdOwNvgOWNbWU/NKk0lsAfaGuMdDPld2C7G7AiX4tHbGP2Ltqt8H"
    "IftXDxV5qr9EtiH1p1R4+qwQW7dHEjl8sP4lwZvSP+go0iybVR4d9JJeWXfdM9n2IpOYDX0x2Vz00803popso0cLfdFTrr/+/yzY"
    "m1n8GWj4g9LOH0F9s8a2E4BLWEE722LlJ1mOMppFiaeZQSkOMNQdP1H62vr561/WEu/F4XWBT2uVLX87k+W/OBc+b3cFIhnC8nTF"
    "/o6VpV1J4rcRz0lo+KrxlID9KuaH1QCCdAoH8seu+im+4PzIja1L18mmeggmv2zQgEJMCsnOC7bnxYo+wwoQEivSK0bmt2Lv9m/D"
    "0xK0chYD3qThMrRFq7JecgRiHFSa8ULZa/TjyZc8NEOwuSrIgHlJ6ieBnkNxZ8B1NXSlpGE0BPHnjFRJV4QmpjFny4JwYD/Ah+JN"
    "bFu69AgVHpR9Hv0tRbmLIVloNnILkMUY37C5zI2vzE4cNnPoM0KHjMgqIz548qIXjO9Bsy0jNx95ApAZ2soB5BxQyn7cjpGdDVJv"
    "btIZP1wQTuVrR9f2VVrRmmeLb9X1dmqMxXHjUI4DotrAj1P/lGQTbf/lDfF2jpYheNTAmE7uR2OK6A2tJujLlpnjM7b7uvNlA+YZ"
    "JWv4I999ctzoLK5QiyoJrO28Mo5w5D9cHZvYjGavKa8ty3/7ZTkgq/sZ7NCNr1N1fZ+Nx8jPSW/ObKNEbc9Xvm5D38sm+5HRJ+4C"
    "NDH3S5KbMwbmR0B3++TSOHyzGS+A8W+mCFhSVvnZ1gRb19/Vpx9ty5s0wO83e2dspMk+WO4aKoTYqeoEOx2sgP7cp0r5BTCG7hMJ"
    "50DeahEs9SrpcO1VVm7XDUk/bHp9iqo6OQLgAvbNHcEaqIii0o3hEHGQEOb+lXtY5X35Ag+J5kC+3D4gf5pkNdhWOI/tw048GBGW"
    "5dwGzesE7YTNEbV4jKJLpVrtw105IAr+rl6al/PuxfWrpk4i3+AYsUI8L0byAJPmAUUGhh31+mPac9eSjbj8/QFms0rYCenB7pSd"
    "T5A/oCNLBeo15U1w+o+pLO++KS7dRe6nBqQ403u7QuzE0LWKzMvN6tAHj5gYTy/eIsZNwvsxiCDKFaczGHOrz1Y1pEa5MCbcIxSI"
    "qK4val2S7nVF8CImPmM3f/EB1lLh6dOYPFUeL/q430h7S6XlM1Ig7CWCej0yrLn552FwHXDI18Aui2px7fV79RAof62WeGeDkazi"
    "cCo7n63M1UMXdXCnTHG1rqCO0MRw8KV4g5v3tQIylcvjGAh2e6xCTsZUEJfIEAAtUQa4sM8s8/jGr6669sXLvbcljon1wyKmbKjl"
    "mqK0F7gzZyHVJVhshoR9dfp3/zhzQlfVnaT7mjn1Cr5m2ZTFTQgkZBCQ8qhvMOfcvjCw7/LCtsFG6VcKe8RnyeCQXXpJltYn1O/9"
    "0Rnz73OsFHlIx2l6P00ZbEDYOLEe7S9L+9zVIxTAk6ROdVngz37Ceqtg4Lg1N3zIViiNxXKHBaFmuuaNAr+eLJ5quKvzA7LpgGKK"
    "lHXhR7aalt+Csl7hM6oqDK0itUOrEnRAEQF0CVKf/orWgD06YaeU7IexWdKkBUogJKT678z4cPrzwykxWqXo8pGHLOz6MtSLAQMp"
    "aK/iM47AqFwcZh5pmBEPqzmhymLoFubYIWDzwDcoXklXx4rm7bE4CboQ0oqAQ028DO09y4y8TfIMTiGV+PcsRBznfqvJ+9gaAODE"
    "fohoYJRt/5d/nt1WBV4vaT+L9WkJZ8irEItCel5K3JC9dDk+iZN0xpYAzNVpOyt2Iza4I/celiA5FLTjO72SNb7r23BXHEuAfnfs"
    "sHWk3y8G77I+MmjawIVIHRJqUO9/gXvZKE2W70TZKmR+VFre111yD8e7DZtvHHtWMFJ9oWtsTAajAPrv+lcvbZ4QOcyKIfPmtSza"
    "8/bN8U3WZVHa8Oqvn8a2Qqd+/dNVOe/gOScQHYWpKlmB1ZeqMESLT+aDkUAzH3jfWMMzoZip6AqlmGzzYzsW2RBznSv3x+zqVApC"
    "ujuLPGVHoTcH9lEruwdFr2EFLCvp7eRW5E1fcmcZOWfOoTlawmKW3Wb24PJ8lhsL/B/PYmxxdDRZd5ks+EMjyjxnQvirFZKPixZx"
    "wxTrk2/ohddhX25r3d72Lr+RFHgivGYG97RX86JBgo4RwMtBqkIT8VDRUbeoTrUyB+inY0mkkb7I9MvFKTrlWDnoufeVRibvcgGg"
    "3qrg17z7U6bq6BAbSR2/e3N9WONYf4rte1sQDY0qyuJ+F1KjW2nfdnpe2N1MJFqc+uoDYS7UQQ5rXueyjwGSe782pa2uut+c+ut1"
    "oNenkCH1KtRfj7gkNn7F9CevIzK9768r0F4psbpJP539mS77o7xoMsaIe/Kz8baZMc2613vDw/J04iZoffiDrLPX40zym+omz7f3"
    "4Gf1hIpYG9TMAqS6desn3nCpztImFqasodHZEA/wRIgnZsfQTs8yI80FIV46P+qwF6z0RM+mMaKK3SeKus5QrlaOOIxXP0gwLylX"
    "HMG6f19zrMNq6hzONObUEhBBuXcqjHzfbv0gtRH78UdJBcMunFV8nR/I85yZqt6hoQgAQK0cJaZ4in6ld0KK+ilMgALgV4qjyKB9"
    "Y+zLc0A1PvnhhEvDzMKRhfCxV5MUfspnfAVrCwH3CosJEVvbzdm+Ww2s7RiHBwN2yfdRuGlyBfFgtKacm1Jn/xBEWzns4021xENj"
    "ye5tjEfPAXvPt38z9FED2IslcVqswUbnH6U3haXUZcLObDtjtwCujjKt26/o7w1dywxnAJ2pymjHJl/fZDt8pwrJINMYOim2WVhf"
    "7MtQ8hyUIqq/67MyYuPuSBNCW3elFOeInF3YweK+UQQ8Mj/3JTC863bmw8YEliVxpjXUlevgdzlipWJprTaiMfbNC8hJRntt0x4Z"
    "qB2zclmxWDbbODMvfirEkMUPB+00/UO7i2HeIPt5vsv1s7MMOUqt41nJ44CeOPiKSfof6rIeatAqmhTfXca5Kj7tpY4T1lnTXl8y"
    "qts5Rb/hAyafNw6JzwpFFHCqgO3rhHaPX3pr7tTgQkAW6VC3O4ktEBI0Wwm41gherCB1oJS1aTKOP+9Dsht0Xrpp1YyeRT5/p5C8"
    "bBo1krvLHs/E1d9GuF4x/LaQvoRpCWrmd3uUDe5ArQ5n7rS0xUFtUydc6SHqsRIyiMcMAV7XKKYH2YX0L34t73ffbYWiNfAmuh/s"
    "DnlRWob3Jea4OCl7SgBLsLlsb/tFVHqkQ4HSHVc+Wvxa/5RvUBZdd1z8fP2d7OWiafTB7d47HNe3fy5JkUORF3hmnp5hSzywit9i"
    "NLJESEGMWwh4A1d1oJoDKMus5IR4ktaecAz1SeMToHYEtOIaPhNg1JG+2ceIaYsrIZ9f8RjJ8B5bsvR3luB5WHe7IWlsVL8G+LRy"
    "IYInwdgsPFNGmYoi+jBeT7QJ/7mCMm8+us+iW7+fOcVkDGQlMlwxC1upRXnOM54PiFcC4IFST2who7XfjrtzRp2pPpzbdO0Svm0z"
    "72AkRDR9D/jopPJkFXQB0dQ4hpyiUIkqAW9BZldrwfJcNy08fiuEHkQOfE1qUCB6FTyDubiGzK4tvyUsdXKhHz4FRwx9fgDH+nSA"
    "iYEoPjcWGavL+/6QJ3EEkPqpgJU3bkL0SJ4mBW1DaS8vrXiyzFAHEVMTF45AWN4kMXGCi6NhD5IaM79nNjjaPJ0aAA7nBBKo1Id4"
    "X6LUGg0aQedINQ8Q+ciQVuLLV25lslKUs59tNyC/nE5pPQnuBgAi6YsNRVd4N/GExFSqfvABL/oYNq3zKErUSiMEoQxwuO7KPR8f"
    "7GkVh1LVtkazFBVMzhnIWItP/2uC50GOAIwBFrjYYiEkFKEhr0CPuTLMRqVJrctLaoAKRMMKdNeum0xEBzO/po5nE+EN9d7mm1+O"
    "3wtMxLegv4+1W9QVESm1VhmCPlmgYJrlthKsLVd3liUKVUZKbPuZigOYoMgPA/d8DGDTLN3dNbzP5gil+QCA3APW4Tz4vhzPDx5K"
    "wmqBe3iIr01thwuWBUq+i/uSZhDQa3hGCHWs51mvJ1wCGESRxMYzD0ktGipphdrTkdPwQ+1RgeXAZkxZL3Wz3AL92vUDfcIZdlKN"
    "+n3I/fv3iwUoscHkQp0psqw4YH0A/T6FrJty7WNLUwGGVMqAP0W7UeSmMp3DAFpWBSfsst+88UpMnjL9euzex/S8IhRXnBlh8DA6"
    "rZaFel+BiKUhh58GRD9LxHgwzcu4MYYTkYOEVCDfnAJ+5fdrJChFTkmAY2ssJNDAq+KP85Uh3h0/4/IBDNM+a5jhs8rG1bH81uzJ"
    "E/17/Hd+KweU372HHxAS4BIx8Gf1S6lOqp/3E3+bIb5zfhwHY4GfUzxTrt08kAghw+NnLOkHBjU8nIk0WmV9RW/mqJmGnghfAtJo"
    "VF4EwJd1bI8iW2IKBZfg0daQ2UfhWViKsMkR8OlPYn3QFhmhIakng2cjaGet/EAXcpHewRzBIYW7UnTGWWjSY5/Ub+nN9Ao56kD7"
    "yyBDNElf7NS8eNBox+xr8e/Q9UL/xNnHbjMtrss9mX/WnWms7w2QseBcbCic+6hCPMZb8mhPNB9fJE3DND+B+d3fT98EJAdRlkF5"
    "J1qJDZ+fKQ4mZ9h5gdMwtPGgj5ChY1ObaPtxHgMpSOz8fjDrh0/KIOjyzx2xuDw4rm6kSJ8coVG1tP2tu7yYL+bL0Nfp9Q21lYZ8"
    "NyPEz6xJxsmMyEfHCXnXYRjlv/u86AdeKVXVyIIiuew+RYeMa7Oy07/GtbdqnhWU3zB0OfexiRViIT9NCZB7ahFzlCTp7z5hsPhR"
    "TKpXydTbDUqkdWkRSP9Q8XENlpQ/rwnO5ne9r+WDA7Fah6eaj9XSK/axVhHTI29An1jFTWiZYTVf1bT5B6c6X+yRb0dXr1LVwx0J"
    "TORkYDBLqgv+jKqd8T2bZMlcx4HZxhBkQbPdjp+ZBIJaQb5mU7TrV8Cu28WRebxaSW9w17aU9ft0eNJR6CzJJ4rfOI6TBfwCyDcP"
    "TFRCy9hf0Q9Ogiji8QQJtQy9Bq79XYOWoTzPJjYhJMoUQnsBZvKXz7A3qOGbDuRW7pRCfo7h37mxECMkCMk3TyTymqtM2ybP8SlE"
    "L//Ymqsetvx7PZ6pLoZ35EZ2NjqW7Ti2ReGdzSaaQrDfGNu+Zczm2WmUlQ8TzPys+oHoqTVT/xr+maJqaPOYa0dR/KqwVaiOFRu/"
    "oSqIDd8kMDOR/IIcCBjGAl6ME6dqeXgKDgBa3QP3DQNJbu31hCmXdAKi/3G6zzQX699vp/6fzvYZA/6/zvYJYXQciQcdUREEFVXI"
    "6eHeHlG+MKll5LwJGyPr0kPp5OEek1gZ9AHP5hAa0rBMctHGdQQZnyBCt/KA2seARYScqo8VZbaKRJBLVhs88Mob9ekDkuluf03r"
    "tIoitwCCsrq+qgga2LK2LGLiafiS/vvRFupBT/DEzCljuSH74pTDrTBFrcECJ3FO1MQd0mpFw5WwgbrCLpJTJetq7R4fNKaA7glX"
    "FJ6aam0e1QgqNvsBi69biRfvmkTkQlCchk4l0nAX3QPd0Lp/0TxE06KiP9mweSwk6TTd8v78BmHV9tfaczdbCZmBCf19YCrFV0N2"
    "mmf95idAAFx8rUPuyfir4YFtVrEZ7mM3yGkZo3E6vnq5zbDPa3TGtYn1+fYgYui807EnLNQuja8BAH6XT7RlMkWc+U1LpiUdcJot"
    "f9+XaQW6Ep+zfC3seE4Jr3KJX3xlVubOX/rOb97bp+/0T9fpfRd5m/kSEJP3CBZ2xsqFuj4wo6grDWV5rOg8pPYohgCYOtLaNS/D"
    "28hYAyjcHAs8W82oru8LCqtOAX3xGr3VtPpGFbN+w2L9qkPNiMp7M+rRid3vbzq137YQChmOOxzk4YHMiyoFQSDkG02wYYPlklWC"
    "xOcDB22E64Pc4iunc38fTvR1kBzfNxbY9MQEwC7Uz4Snz32RJpRya4x+pQHb8AL5IBV4rDORpS7KQRZ3Qc2oo0wuIL/IDhnm5mW5"
    "Y2k5vfV5J8eOQJ3jurqK19CnvtmctyOafE5NNEF0FA0Z/JXjYOhRvOliyrSiyNQDPRkyzw49T+OSz6jWhC8/evXhPmkOdSuh41iO"
    "0CnNwnpzkWeWB8KIL2q6v7bQSZug8T1c4+C1TYji1Z0hrJLfNRdqHLQexlG6iMxAdxPNYMJ5KOLdA8IuhYHMEz5HvR/o4p7tuezR"
    "T8ob011X8WOv990SOzQkcwQBmLdCsbhDnUo9iz5tnKc++PWYqN6MelmG4zZ/mvZikwBhKPsD8g0ZmZPr9g2JjfLzk82316uxO/lD"
    "hMSQg5M5WgNYNUn6QFPxJD7Lcabp3iIYRs3ejhB66qAtRn/ohHuhOOTf5A5krS5yXXl/+V/zNkEg3/WFEe0wPGEUMW/VfUFokKwl"
    "Q+1TwUUGhO79AFesC5SjeU9hTP5IC+KIzsO6D0hZ5ii8ghjev4lHDJ5MLFNpbY68sepJYFTepn+P1rdf5vKMZ6osOa5g9G32DEvm"
    "xEkOkS76Ebya4WnJ4QTybGyAEnhZeraCe9GbS0yGzyksfbiKNF3ix4v6pKkNBIEOSIbAIoWX7taxXuayfmf7PoYKWdlxDc9f+m8O"
    "+Hg1jnVRf6C0enn+5gn8E5QgfO0DzEFipSzpAAz5qXFeXDGD0DndIAzAfg5Gid44GiUnWP6+yUdQZwrGNFaN7fgTjP2xFOY0fv0S"
    "A6Crs2m78BYHUpg73FGQFMYH+hw7WBp+0IB41BhXRvg4MryY+stI70S8fCNAAsko4Cjw4fMhwNHFlRuyN6EX8Ed+63xi+uGyLbdk"
    "jMi4mhN7IdI+UEbvqGSOOLIKb+Y0oyMa5Hpe0jC5E6r46BOPDyQ2yIM3Ag1MUtTnkCQQFLYNTtGRU3/QtKf2TzdmPc1+g5nZGz9d"
    "iOwq7rcvVPQhwIqjLx2dbzNGCePRMtd3FemH8o+tE1WEpDiQAEVYWtdEUNk+flNuyJMwGvrdxQpgNByZY6s9S6CtVtbfJ0IlLiVl"
    "3yTruT/TsJ9pzwQnhJ9QZDTuLRbzfN93oLO0ASTnJwRLKzGDpwCI2Q36YE4OzFelOpUUGuWYQ5BD5rNZgNNtB55FPBOgJ3Ejn8+S"
    "irfPPSgE0cNiK8/00lKowsmWCdQnLs0xhCmMiDFDhD/Ir1vbfozzltp/RA/f46J7kIpr265ieyhxP4hYWRzMSXJahwegos1X81fl"
    "4VLt/vRvl6zRG9KhmTM0Lcd7pTIgRdS7MVwcN/A8feNZBVebPAIUNY4PuUS7haQDOwMIpWJLZEpsXWrrFwTwMG27ZaQwYO4MFftA"
    "+dFXOst+RIP+WMBLaz29dBQfI9jA8RYqWt8STI73+anaz1FgdTRnPO4drv09I/tavMP5eaHsJIzfjUAeF4UDRPoBmMWfE0IaLuGq"
    "LQeIKH2jQ1ruagifKar4a/BZh7iOxoLmNYGIbNqyluRzgrl1mJbNn53I+FBug88H4o3O4YvzPR4J3y9xTt4lkHEhsf3K65h1KEDH"
    "oDkAcRSIdk+lS8jTRWxXe4IFexXNR1fA0FLbRs96oucrsJVt5SX6dRwvyF8BoV9LIQgYOum0Oq3zHUK7TExES/IAjtz6VfBAH7+q"
    "k8MUDG6sBWDbdqLXt2KeIWExkhFb/4HeEaPWzdxXwLB1tpkO/oULh5ZFzrnKBC2+FAHAqO5ZZYHgFWNz/p/FN3oDAICxku1EmOoV"
    "SfVTZdy2Op8gfeUFs9TIzyTmaf7dTyUgZaikkB1fAvkcaR2xyeuIm4iOa38QBbj1tACRoGA47NjWL1kW5dqvH/CTnjmJsPs3zFuS"
    "s6Ucfd7Ia6Ww7Z5tc5J/1w6FmJ7RfIgyNeLAC/GSyE1F97KPXm9CksG1UNAS0LWeEnGSfb/2YPDjdLRf1XfO2bw04wBONZ+qcmbn"
    "XzmfL3mlIvNbthBJbZy3J7di5kVuaYZ1xgz9XSZjP4lpgYNcVCzE0tyEm3PW8U1HQy9CzKYaJbVGz/huKoL23vnJ6LNhJllkrizg"
    "7KuT5fISG0BBvMAfeF6pErZhIrIQhcOPI4medA9w3Pdh6rmCPnXZgixPgz83idRiL/vaD3t5TeEKiH+F1VJHhCcJ9Y9tUjbRYlb5"
    "yJ6h7eFLSdPsqz3amhXe8b3rgy/AC40nZTGjz+EarkL/nfJXBUg0ydnYW/aetmv5y2Xs7I2gmyqcGfObJbV9NIGLpRT7jsACgCCw"
    "Q69XWbfChmDEgj9UqFGaMgWrlAUSBOafklq49uCr3if8ZcxG35ywdzYf5HHl8qRBiOYOs4Jt/JtsPzEp3Sy4bFa6zPhiqF5m0ExE"
    "MSv5SB2hmM9OAsHjzzpm0BlzvUnXyZdURb5Fv7zcnFpdIVu5XBCBT4gUxZvhp/3ZZi/SfUW6ffy9GjaKkhVNf5BMMfMaG4SF6Ppu"
    "ROPJWB80vdsTsHQ5bnT70mjYxX57j/SEenvDcSJYauFeZbuMmIgYsmBrZbTiW5SQw8nmLQzLSpQBfoHUXQK7UWPyBItqkJ61s5+7"
    "YePfW34moMPG1aszVuQbqfRZThxXzRyuiur5e3+jqnMzLdRSIxZVpuYNZoWP8Uvlj7Jh3HSkxs7Aa1LvduRcgaz+erkimxdkggQO"
    "6zMKk9w309hLVg/J6NGkp3LwpvHNVvUsQrLcK8U3KlKo6K8re9YFR3Y7DESz4H6iz1ayUoRRC1SgMbHI93s6wLp/IQN+BFWwVZms"
    "DUvWaW9f5btSMStLgoFzevuo4851uHqzK74W6RiKdxEt2zAvilriGtdhq4JWHt7+x+6+ECfVBGaw3ArNnVTLKmfuBEOI+PcFDtzp"
    "8S1PCwiK3EQcqDS9TIkdgC4X54ljXnXQE09r/JEbSU/TzLBjXo00bywV//5suIRZlmtMljoQPUE2QcjLw3a+XwmLPxuet/G6uJ3d"
    "8m7TY7Kpf4SA5fpDxCJBLN9N+FEMBnoa+THI8kKOdP/pGdtIqOfbPELizblg4RdE2Q/JaD+C7U9moyqPiK5zQ/tanPbFxJKxa9f1"
    "PCqwdSoQEPcLR+Tb1j+TOLkM+xvsK/xy0+tOHJEjGkIIncxUJtBYWRUp9RPy3wK4+yFREcddvg7y9y0G9b44C6c5whGvHWTE3zV2"
    "HJutMiaObKc1hPt7A43YUs/tDPn3QcIjr37MzTppZjMEa/ctZ6gxpy6rOnI5ORxXafTuo82XsqlOJxa2PlFnhMoEh7PrcpUgiVBg"
    "JWPt960qXdHPbohyrWvY7z1OX8VXD2YuhQT2EmWGnGCVOWiZyyARxvMR+ygGO4JUieJywEaG6jo0Y7w1SRFAGMHPBwV4MbfekJy9"
    "PPbzzpgcP+klxW/j58xz3OyWGohF1XNpZ2nlyQG4f2iwKYwkb1heNro5mdYEyaYiK3KRTH+ht3y1s4rNkn0zHo+/L5nfZHSZAKiH"
    "BCRxeQ0z+bcI9mqkfhZ/1eTUQ1s1XCChQ1KXDR0pDVpIVhN3UwP0G8lcWkWMseBQ2AuabJBJvipa4nSzKBXPrrhQ/MIRqia5YYNr"
    "SlMtTPBvmrT135XaJYiXiRXlHRygs3tl5e9yx4EsEN/vZl39ndzVnSO2rZrw4zP2kKopLZw3z/+gg9YXmrb56O0SV+x3G785tMeU"
    "/Ye9BVSOrzFgj4GWjPrVYExWb+4yyHxNmbu2X/XmEFkMdI6dti2cNLurR3tgf7ySuQffNftCBtos257H8AWmwNCKM0qhvipdB6Uv"
    "Wx+SlSO4FRO/39wL1xRtim1hTY0P7olF/lII6LDTip9CDIC4oOJAVnVFUV5KagwIDQgXwun+jbOHx8vVJbyKkQT56sYpg3ahyZrp"
    "U3CDeO8XfCOlIwRC/SVxU6LehamK3hoZDAW75wTN5lbuz3mJRAwZlf6UAy+wydUatAKyaCvQ9pLfAK8qLsvyr+bwCWZEK/ODjSC4"
    "vlLJFmTYUp0vN9/x+RyMdaK+BZ9Pk5QP2RMA0+vKl431lUvdtX/1I4EggLQRHSpbMn5wo0XBLa5c1vYY5+ySnjdr1qOdneO1Wldc"
    "V+djjo3CLTP42CVprF+L2qKJxZQ9M2TmGIvk7CGUr9vIPjce8mx/3f7dV+F2FceSYvMBBGSeF8uqz5Zk4K/fzMrxwnCdaVvsSgd5"
    "eK50GUYVl+ChjJm5GypEd7QjX/PJXn4V6epLCCR9LdFGh9qsuW+thdAy59mduA+jbEmmh1plc3ddy6orCtUuZJBUmpItz0Jqa6jl"
    "1fjNm0wptgyKsROMyB1pd2xNa768GH72G5evJy2fknk9V/qnWYAUDnBE8xJW3VYl8nWRYc4j2V6SSp5EpzQ0ppFpMHmKw1J06FCt"
    "HmKX3nv6Wcl+2MbXvqHZYDqRpBXVpvc1CC28nv2m18F2LNFO7ms2YqTb8KgtmS7H8gfyx75vqM/SsyzuoTS9UCS5rYYoKrrAz4iF"
    "8d2yfmC2M+4HVvojN8WWGF3Xke2AuUwfNEgbccEwbixWmH2E5HivREY3XL5FqLOoPkXtqEstBP7KKUBI2v5GR3+/eAMDsneimeYv"
    "gy9d2WzJUMTRomg4w/H9u6LbrAksyM0ehYmy48iNdq/m3W0zjBg+28g9TMSNKdZRVme3QHN4GUiYrgo4hnP026pa/+vgG7x7ziZh"
    "BMYSpjpP4nKmgLaRPfTICi2W0kNazOOVB7x9945Php0DY7KMOyNlkZ7j3rA7P6oOGedC9qcen/lwnrugB0RnAB907U5aA5ifYD5L"
    "OIB/NxZkj3dWNZ0SVXZy1AQWQXUQ+/obTKyFRGzD335Bo3RssBD9ofwiFhZCdmV3ZQbR0N8ZsIhS+xAslWeng8A7F2uKojp+d4cz"
    "bXM89guxDegRggNtrt1X+6pjX/sqKcuu+A/EVSqHY1+wymcxkOfzkxECy2gTUqP7vrL7zdBcVPG5UQm82yLGFTEMCHrl60m4KcMY"
    "QGsEo1zNJhZ4WE61oPgMxbNpe61VAQ8CcE2MJuQ3ZUMtmDqHrbvM+jHsefFo0pCf/ADzBoiKcFp+kGD0G7yCUmR4hGCwlb79pnWZ"
    "6ahtGANND/tFc4RnnW22X9eZx/WrZPuPNblXWiPqmJbkhQHicwnQrP2eewU15CD6s5J19qfJziupDvfeWDtyWbSy5QEm0moFPwcA"
    "1quXWTKzGB9Zn3qZ/DubI6pKg+Weark4i9UFnuFJTt65b4aiUQ0QaH7JNMd2kw2APWD9/kPcm3e5bV35ol+lxJenkI8szmMptBbn"
    "eZ6p1nKDIAiCBAEUAI5SrSWVYseO5Wtn6KQdp+M4gy3HHTndSSdu24nXuh8l5ZLsv/IV3j4HAwEWqyR3cteNIxYJHJxhnz389j77"
    "HLSGiTTtJ49rTdG7CicHLU8ZnwtwzLhbE3u3VYjn8nXW3s7nqc3xMFj0bGKbyrRdYKRCaTQrDqVlNb+OtYs5utfJZXopNi1XGAAF"
    "QTCD41R9QNfG6dp63O+MXBPa7gpNQ/6kmO0M3eHupLX2c3I2N872Jnx1Ls4C7myFS0kjwN5l3jvJZN2RUXu8CgeGXrAPCIN2XbXB"
    "slStZfvlZiyWlYhsshNvBCs1dtWJyY3UIjb09r1xbzKWDU2DCTrGco2JWwiOmQWXmGx6gUSHLNV6xXR4k+3XpEW91U7HezU6HivF"
    "m4n5aDzmPEOCkcVemu2ATmlx8WGywaXsuZZv0mklhEbT7rdns9JI4Bbu2jTDAIjOMf1UzZvlB+OY2IkF0sF1eBFbjjpir5XLFfN1"
    "O1udbChPj2wyrRqQK5Scr9v28ZAsFb1FlyuXI7IpX8KTZUqZIikn8vFlxpUCGz6aVnqlUDkbbzNyrJmTpETWLccXoJntI3ci0ZPR"
    "SQaR9WS2tFN5kGe6DXwSKw/FprwU+rI3PJLofq4R7tKltCccTvgBjQeLY/tcqk3cVD2TCgXb4UWNoPyZmL+wHJS5NlUhfJkATHkh"
    "3crV8iluDC6q3Mo26GavU5eK4oKPFcUJHZsw3sgk1OHigS5NMyuYBJfXFWu45pFk0lt10b0yyuLtJROxxoRjGgxXnOWlfitRT+XY"
    "kiyEO8zGk5D9eTHOTWK9dqFQz8S9rchsPkqGNvUGPekHufamMi56PPw8lSukirmxfxDmUj0v4a2KnglA7Jk8kMBHbbkmjfQmWAwG"
    "Q6FUvphn40OukmlJvfkmUxEHmXF9SDKx7iZgL6SBDnIyK1SLE7bd7Y7GCyIkNpN0dZZYDO2LMTinRUoYVWryoGK3x9euwnKZqEkp"
    "2rXoxseuxCTrChenx9OWf5HqFUtSYkoyo3V6s2bK0xBLlJqNiiuYbTbXU7+/urS3G5VN7XjclY7drWVv3en6m/nxJJ5ITZEfspyn"
    "anb0LhBfxTVotbyzcLfd9vjGjU2imgyP2My4QE9aPT6b6q2nZFKchajKMWgLPhbhC61wmoylKwv7PFhIuOXlcBUg7bFg9ngpZVbB"
    "0apaymfoYJYc2quuMStyHN0IDKuFRc/V7fM1ehjP1Rtc/bgUrlYlV3nlWlITclXgOgy5yIyYVJns9cTlJtZejeK9eNLlWsQnDQAM"
    "9tKgG3L3guyo3xtMViH/ZhoEg9wl7UOKlouNFL3kplwgRR7nxkRuEJuVJiQV8FKhjT0ijgdtz7C7tNMrvltazFqFwESqjzuiJ5jM"
    "BwL+hNBl031/sFTZiMOsfeGtV1d5Ty+VjUfalI8kff0yG26Rw2CgslgS1XXwuMRR9rC/MCcrmVQ42M73u/7clOOk5rGnI9WYcIeW"
    "yWDR367YSzRTCQYLM2EseoaD9jJLkt1cvZpMx3qbeiI9D6zzfqEV3hQDTJxMMqVqoRmuZBqkh/VnxKBHLvtCQXd4WOuwIjP3+yfC"
    "Wh51u3Ij4+XDK2ktuCR3yuNKjgbhdYQWg4WSRAA5aqmqyyf0vGPR6/fUKpVVXvZlMoliR0zVAlmylC0F28ExUUu3YslSOC6M+US5"
    "6i96yqP2kmT87U4EEE1wSAHMk4lEszzwFrhcfFLquavz7nh07BpH3IUFSRRq4Yp7Ep6U7SlhJk1a5GiwYletVmQi+ulUcL4QwwJX"
    "rR3X6HQmvk5HhuV1LNFqHSeOj+WC6Fu5OEJal1rg+iy6i9GqMih3VgBRFuvgPJ4Gz8geC7fFcmq5Ru8eaFU8QoJiiHitWSOW1KAL"
    "MrPwTYarNbUuTkl2tlp1gH39Lj54fJxiCwWmOVpJpWEmTk6XpWSl1WJoodDLdvrycjZu9jJrsbAkwZ9rFLrN3HJGDjeV+UYmV0F2"
    "PmVTDOuOMO5gt8Wv/TkvPHPc8c6TU8CrMakVd2Xjy1wj4C6nBqF0szQmKtVg5LjVT68WxIT3DSnXYDrbpDPMzMt1+Qiz4bzt1qzY"
    "5SZeAKRzd2TKD9LB9DKVzhXmhWC/lestA+HccYCfckWBjheI5mjWrNoXE3qcB92SzgrByUIgq4PWQijNuLzQTLj7wUkj0W/6N6Fy"
    "KD0sdgDftqa0X4wtNkW+HY+PquA0tXqBwTEJ4BcFfQbJ2WYQkSrTUSrkKaT8hbg/Nh6Xh1yvLFXYTKdc8GY6xcCyvZRJfkxkBr1J"
    "ddVkB17J189QrrZrUFr7h8VJnZsf5+pMkQ/a3dlCaAkaLFMiE00mTUSOQ7UO15xmUt2kQBJLn+z2bhLDZKnU6ifXRW+eb4fLK1+5"
    "WiiMhQle00tHuomgb+jfjEPE1M+I/jhLsaBb5pk6OHHAvCty5W97u13at0x5wgw9LXZcg3ArTK3QOmvdnov5Q3Fp0knl+EGcXnbX"
    "YW6ZLDAxGuztOptKsiCcaX+s6ydz+XZh6QMzmglMeSFEr9ARqpVVx8P1l6HyOLZYxJuTbLUsZnyTMNMptkBzMIOQPdZmOmNiVmi3"
    "xvaJN+0ZNjqdYnpWgnLcaiQJAtFxbcIUeNmtWqvTKVcjw3VKbDEJtlXki52iOA/Mp2nXproC1gadECISM5kOlj1re3YwlJudcXGa"
    "KSRX9plcb3kktLG0FgzzLnnQdHulWXAuiptZrJJm0owwSvWZ3CTNLlzJSSs7D7Vd/UhlFt/Ey8yc8cjzeT0zkL2b7EIkK4DR8lR1"
    "ljruxnzSKFxu0fy0teZKs400kCOrcMy76k7Wbl+l0gp2mbJoD6aT9r6/6E7VBvExk0j4UujF4Hy/k3W56HJOqBfsmfF4UKxyc7d9"
    "ITDhfjHcd7n81RJf6LEh/zBdL87bgWrX1y12pBBTArxazXWr/iHfqLPkAsxONStPvWinRXA6Tc6XrlilU3QtucVkmSq44xMm2F0v"
    "etVcLjl2zccZcD1n7hwlpUY1ZiD2Fj2WdMU4n2uVjOdycW+212nx4sRV9m3G1HISWh+n6IoUjMXBE65kumSJI+fkeJpthvvjbGpA"
    "53vtZT5TWW7G4UCMBpQAo2JyTD7S67V48C5AfKkpK/lC/DAGkItsip3jRDxRmnkma6qYtldcIxfTL/i51DRFT3MpNsCGulM2OaGr"
    "1Xy7IhCJ6XIciYQGETo4bHdzAXadq0zcU6BiJlaTUIxv0CKPp6PaMc0QrdV43ZeO10wIIEkt3Kw1Un6aa4GWmM/n2e4wRaZW6wY9"
    "nkp0YNYsuJLtNilFFnFPhQ4k5yuhUSAik5VkX7jXdEvkylxCtJd8JXnVT+b6m7y8SYxCPAprhukIOZk2iXC7NeAihD0Vz7jdo4kw"
    "2qxLdC8VL2Ra8dCyMBhuhGQineFbxbhv0J3y6VLBPhotah6xV2RWvUUdfMeY4Kks+Vw/H2tkWhPimJiLK58rFG66ko1G0EXPqCEh"
    "jSKxSqCYF+KRUq6/LnZ6VbLbWoBNB0A0EGPi8tieltLLdKkkZNa1VHNBrpuTXsbfotHOktGE84UiTKqVmLdlmi+kaXrebq6HcXcu"
    "WBx2Ft3eKMvkR7EhLZcqzXEsL2Tc5Vqt2C0HNwBESWnVSyXjofQiFJD8owJYjHA1SaY9keY4PWrw6V45RwTnY4EkJVba5AORElFY"
    "pY5r6zKb63uW81q4K48LUiTTEYderh6OF+NrOr9ajJKNVW6xYgNM2lsnYo1BeRZKTcaeRa+UScQRbveACpPtxTb42tPZNJdrpkMh"
    "blPiBuHYINlwD7nM3NeRc/Xs1CPUfMkhuyzlh+UJnchX20E30VvF8nV00Plq0ZOzmYlvVWeaUiRSzbdSpbR/1K6lCrXQOph2pxLi"
    "8WIlRVqyvRRy2XPBUaxSyg8Kax9FsKUyaw823E2Oi+XpUpnx1EPuSZ4hZq5GYlSq8/KxZ5QcNjuJWsueTldEMTkodXpFunkM6n1G"
    "Nsiib0HMOWAplvMlK8VVJVuLr4otGpRDO5DnXRsxnU/G6BHD9mrN/jgHPn9uZS/7+7J74y32PZ1QgJzQQqoQiRQ8wQLNN/sjX3zm"
    "Wi1c9foqlHaJIy8V6CZEJkgyPvd8ssyHeQ8Zz5YGdtk1mEx75CiMToWOENlSLtNlG23WM4yMi7PajFuU/VSBbSUWC29IAjwWDHlK"
    "2YQ7y40ku8sdrDaXTHwIbkgs4nK5SD+1qPG0lKG5pVual33MWsgLnq6rssllE3Exsil7ell3udtnSP+Ea4Or2m3ZO+MJR/iCxZ59"
    "DVYokvYMcol5JTwa+SeyN9Qbp/l5uZ3iu6CTc4VEuSiw3Ui9k+r3krVjMU4O0GvkR9REDIVL2WqILtXHMt9t0K7h/LjmW9HJQqOW"
    "WDZi1LzqynqLiXG60bZPw6tpqhzhYmmp3xeG2WkpXLCP67Pw9BjQadsfEljOP6QroUXouNpPdGoTYpBtSxnXxE91xDk1y4wyo5HL"
    "X/Ou+EGrnScIrltp1gpMUYyxNN/vs1QHgG5k5s/mGonIcW40Da48MypfZkKDtcsbGs6L9Z7U7UWO3eSssZ7VM6Ng1+2fxWdEkgIe"
    "qIohuyuZDPnC1dmmP89mF+uEN+Sf9FeuWEvMURmOld2J3KTnO0576K4946nx7VhuvJGCUjULPkZ8iM4lKYr+3iC2WocobpHeBOj+"
    "mJlUu4kiEQd5Agyb9YVclJd2kfHkiiovqxF+4663AkQgx6/qxVZ3k4yklqk11Sw1+W4K9Km9Pg011u4g+JjLlSsT6rvC6YwoBoV4"
    "RbBn/elWphnjWW+SXlZbJX4zmVbHJbS86cpuyp1Fzb5YLXL9dqIUT5ZSPte6KQayqUaOicvBmVfgNsB19Ww+IK2r8XB3EwoRZaZU"
    "TxTi4UV+7ctONpsBYydrnePj4GI8Pw5mF/NukvGk5sfZgr1RG7lqvESCsNZiUppOpXghUm26e6VqMODKSnNAhyF7JFuMD4qhMDdl"
    "ANFmcvFANtKtcMX5kIkTq0K7nrOjN3wVI2GCqJUnI/egtlqDHWdb7XR7HBzmRSnb7JekNTHspuyhuTfYHbPu0KJJZ6u9IZGvu9Ot"
    "fKxAt4sUAMbjTq0QX7rmqzDR7YYHmQlhZ0LAaONEqS4GFgWPaxSoLOlc9TjECFkvQMhMYja008E5u+muOgl2kq/m6QpJJusZIZdd"
    "+CdMZdKtBSedGAjedFMMJ8IN+3CyEdaBWTIQiU/FosCkyCTHdVf2+jo0J8mMf0lPxdmc9tWCtD8T723G63msGorMQ2kOJMw9ynpz"
    "ncam02sme4ApCzLVrdQIJsCjfClwCcYT6jjXoP3gnIwoNh9zF+YDsLrlwqzVd3mOaXclm5wX5LJrGE/k0rl8rtBws4UWm+8xad49"
    "zsSERGCc2gT763pk2VgQicpgDY5mMxPnyXg8SfsB67Rzy5UUK3RidIammcwiOwfMG5zyi6G70eqNg4lYaiyATqzOybV3WOxXCGpQ"
    "bPgKRJpOVNK1SpYS4yMhSEWyTR/lzTcmAd9gQ7K+YKu9FBfLWus4TyQbhMfuKoWy4cmk22lkSiNXbwiogR/Hx5l0OlUaljYsHSj4"
    "/L1Ju1EuVboDdlGpHbuL0Hi+46+uVzHfrJXqTDLlKvhOjepEcrXTLs5TinH1UqLFRuq8qxURInLBL2ZmtGjP+qbrUrVaFQuNydDb"
    "aUvhBN2d5fONitDOV9r1NZ9qc52qt5z3pZuNYz8/mXerTCUrJ/qsuMqnuu1gPjUIu/wwVXUmQ/a8rlQ8lku1+sNajJgXg6VNIBtu"
    "rwY8zcamqbSY8LPjYTu/SYT8rlqx2oqv6DxdCDXADLbbneO5nM9XagmmIfUCgfayuwrW0sUek2JjlXZOrskDcTIeT/zj4+F84Zu3"
    "me6QaHHuZWwcbw4B9jFwL0GnFrPiiGuTiaKnNRx6yvFU+3jTmMnVOif2G41we+IONke+QXXei9GxtpTt5QvNICEu3ccTZiq5ArM0"
    "m46BtJGxQiyxjM35coFod6nGcSEvJVp9OjmJtVsZoXxM9f3xWqk4LjdqqViY3Xi6vfmkl0oJx0Q9VooXyeRiIvgC4tqeDrDHrdA6"
    "s0iXSaIyCy2mXK1T70tiZVYt+n1De5H1iZ5QaCQK6U1j6o6wAa84Z2qrmo9w8wRd6jdYhpYZIuLyd0dV1waYsc4TwIyx5XG2JoXT"
    "dKy0JoSN0PO7ZE9pJlXidCk3dhersWk8WVtW8h65D1KZWEliwUO3krF+a1BP9tfrFB1bo/epSwAY5Fqy5pWFY5IhXLlEYUOWph7R"
    "V/cOGV/bO+mmqVKyFXbZ2XahMBe5wWQz8y5GQqIfr8Umo3SKnsW51VRiJu4Ok9oUZ5kFGwPYGspkcoFMbtWo1uuRcX9Sc5dza/+I"
    "8smh2jKW9Yy9GzKbWpaTQ6ZVQ4eU9jvLZaEZ8yE/oJOud5upSWk+63I+39gdmk5mRCC4igxmwvF0GrZH2LGv0eHyuUianxRr3vmM"
    "9jZ7XkEeZutEblVoTCWKGhVWq9AxPCKuy27XzIcWfle9ZaxwTLUX3BBo0igWqys/tS50fAy1jJQ20irN9hvdfnA2a/uW7VixHpRL"
    "DXEdDzW8MpdvtgLlsJ+fdRYLblMMLgr9Ym7ULLQbHZoXGD4bD3ua61Q47em2PZ02+CuEd7EYeQfDqT/sLje7eXmxWJTX5DIWS7jl"
    "QStOFyfCSup3x/5+s7uie9nccjNP0xOyGCBcbGjadK9HXTkS8faK/UJoKHn7eZnwSgMysK5OXONVy4NSnCY07fK0Pe32aOYJjJr+"
    "0CRTyDEu0pV128P+icBSXbcL36dcyXjcNQeaCJVgLBZcDocL6ONkzPcy4LJuCB857ywK8YQ0XLFLdzk5EQvzCCXPweFLjNKy19c/"
    "JmbH8qxZ4VyRyoYIuMKjaTlJ+8RgkBhW6YwcWnnjVconhcqblmfdiIRdk7IYsYcGI7c7OA3MBo1EjTzu1yRJSgZq4ICEuaLI8/JM"
    "HPi4EOOyV+nkKlIuV2e+kTeVcs2qtYI/EAjNiPKCmgwidjISGXhcAwDzs3ivnGR8iVay3mdGZDibzS7blUInzknuQLrea3vW/U2/"
    "uF735q7aJBKxuwro3NBhYMwlNuIq7Ctvuk2Xi5AaCTsUISfhebdsb3mG3b63tcnUvJlwDWUpAERrukd8fTmbhTl+LvJBwhUiKwPX"
    "iulH+MHMbw82UxECQJQ86LRngflg1aVc87UYGvpcvsUqHBoVGptmYuYZZOJLOr5BKqwViKV9E64HXsNyZW+RwIWVWSoyXnUT7tR6"
    "OO1210vgf1991HbZ3XPKHs4MXZFFWyJ9lU2n2D5m61yVmJfthFwZch5PIJBNdiPLgAcsBl8d8sUch8IVuRg5TOfANASzdCIkHs/7"
    "HVC6baqQyDRLwb60llyRwWTiWmXX9hm5kqt58AgQn0udka83kSUXSQ2rtXWqncwBrgl1O8t27bhOhER0gpXLU8j25DUdTtWy1XSt"
    "2we+KSerRWJYmTE9ebZpidU51WjY1/ahbB9vqj5uuQrMCSTGIfsC7O9GInv2mcAM+m65wMSohNh1+Y6Fuic74YKbeXDEbeQQtRCL"
    "9l6YqjUIMr7MtxvTcSLhikuV8NrXqNenqyZfKNVkyb0Sk50ZDf5rkikhfNZO91vZwlwQOSFc53ztUS0cDpcSc7+X3XilcMg3GkrE"
    "jG/Me6PIuu0Kr0YNn8+3Dh0TdtfA3lm5FkEW+45cfJmosG6vRGbHYyIxy9XoGpnPUqvwsEvlwff1hcak4F4uiM1w415mvP2JN07P"
    "Yul8genG/JNysZESmim/TyCoEZdhFoWCB2Ro490EljWXPbCI8Uth4ZP4UjMld8sb0suA8iiT/CpWr06Ccijo4QvzjT1MjHv+ki9J"
    "h6vdQDoHRodreadT95qdusdcT6a98pAKNI67AJ0WzWElEmhQ9UY5tU4mSCHWCLiPU1OB3fjG9GgQLFRzleYqkW9nB7NF2df1JCvt"
    "Wj3pzs3HGdpPc7HpJE27wZGjJt7wfNYeBAcZz3AzKLnsi5DP6yt422y5OfWsl71YZrSWE4NyrNdbtALJmr8sDTq+Nh9il6HhscdN"
    "UFRnMveNgnEXCTirm19V+naCddvZvrez9paFapkVjyvHq013TJX8ZNrdFYV5KEk2kynXYL7JVF0JUSC79cW6Fycmk5bfzq8LqZVE"
    "L8KzcBw80sWoM6j46p5YjM0VshshU2tM80K9Jq39BTadb7C+dGyJDGRcXCT8oySKt7vzK6I4YMIL8FPtXq/XFyr6WJadN4SIKEph"
    "d6wXbCbsi65Y78hiuVbigkx5lpZdkRANQMkfdHuWy2oy0gd9E5TFQcUzlAmBZL2+xlhugsvha8fnlcyxe+IV6GVmVWakTDMZ6/Q7"
    "Y9639oSKvUAiuehUCiU+v4yH0wlvOVlqotfdkHQ8Ns0m8utEO17mU+5EP1OvHTfSbGIqFBKzdkaoJ5KJGTuhiYRHzsSS2V6a9vS7"
    "1XQgKBRD9uU8sBi55uKi1XQnj4Ehmj13JB2f9IKV/jrDugRX1hUbhIbN1njZ58oVvL0pxaab08a8NkskLCeOKRntzm8NxNt373bn"
    "ziUhk+MbozlHohccHQxoq+0OyXOSfEBFhzw5n1Gc7CRFipCpFEuhX1YLy3BTi+0G5RQpNmphoLjFQTnltUDBL223FLo0FqlRdEo6"
    "9IrGFDF0EoJAccPEmGGHVsp2orRWpKN3JIoQyfHRN79FMiLJUgfkKmrxeCwH5Fr5K0YtIYvrhW8JhDw+GEYtM6/7wOs+9DkD6B/c"
    "+aZjQLEsVKCVKAUPwkTwIHjghv88Bx7vgZt0H4QOfAcR9C/rk3yH3gPfYcRYbcnjdvoOvB7C44z4D/CHG//nc8I33Aw5psip19iQ"
    "JwythA48IfYwcBgw99J74HEfhpyBA/hX9PgOPEGlEp421gCDCY13ewLth7K4OiNNQipNQpgmvp3b6t3tTdQUK0FbIkXKB0tmKI/h"
    "4bDlYEwx9FhWvq9Q2YM1/hThh9fUESDXAkqZ+hbQrn3TwTKSbBwLEGPs8ZmKh4H6e66Fd6/54FGn27NzDZ7dczGsXvymQxrzFHSA"
    "PpBFgpNGvDiLWiSSYCmr2+mO+EIBm+VgxLDAruRcFIEVEzzLi5YDSRb5KbAtx3OUxdgz70EQnsyG4SMWDDvdB/hD+Q9dPPBEgnDf"
    "EwruKYCvKhV4Qv6YB93xGG/7DwxP+7xwB3+oXIqf9mzb3y2A28cVhL0XKld73t/lGW9YZQsoijlDmU4XDdSbMdxcMs5fAE+WH5MW"
    "hNXE6F6QufEOmwZBMnzOIOF1eg7QP6WfvgNfEUQiwh760bAO/X1lrpaEYKoxeOBj/Qd+KOU3VYskIuvf4RivB6o7xMVNd5CkjFXJ"
    "IkSRX4r7B7SVS5BEpBqCh/APPzbi2SEl7sik103AiFXieg+97fD29yH8HoNkR/RLnkOPMxg5dEaKEScMyxmJbR+GckCRrN/4/IF3"
    "4fEZGzjwKkSiViaBQsI2Di6CO3rqABSEFwhtvgxi5VsEDX2Cb9mA8bdpGB40rLGmk4S1piiAa8JYI8CnpjT8BqXh36coYBqCJBDB"
    "g6njjOC2/KQbXUK/cFseN4lLQAecETRmTakuDGOeRQ6QUj3E/+kFisYSQBVP+BBPoFoEJF40Em7m9ThDSFMchg89RsqDLg8fuNlD"
    "oJXfMEeInMBFhhlBzx/uENh7EFn4dy8B+2naiOFG/I4Z86oq26vInvvC08HF4YUqw4YaB/zKxJlexNGHQRbZr/GhH/4e+rLmuQg4"
    "/YGDgNMDEwyFF0Ezn5mHCdOyQLUBXQKHQWfYyLgg3qHggT8bcnqNJATKwBRB9RtFehiW2mFZbza4y+wXOuHdEa9Qf9cCehf+nYdU"
    "xcReprRMRAwsVEW2umCvgwdmmzbDlxCxFDAxB4jCcLQZUHiBn3dkxyRLaJRh8yBQpRfkfpcS3l0hjoy9O/VGzDI9PvTu6oPg2H9B"
    "Rbj3XPPvuRZW6Trkl0aND0SJaIoS358LJhkECQooQqqqUYHZNRie0CKwAycAY4WCJrUJbIo4ikV8FTYpTpjYALBeG5gHyhzodhIx"
    "j+HCoWdxaKwU6xzP4bbSQ0Ot8FxA6UQ7pFeCjBSmtFql+9CfNah7rB8MZQ9UzqdFRjCLe0SR9qAi7LumOHDV3YhZUVzy7CW3tYfD"
    "Vz+8vf1NBz/9GpoK6WQvJpBifr/pkPnhM1WdirIOh4Q0BtNMIJDp9B4o0FTaYRcvgulEBHhOmY+g0+s9DDsDQdUsCgQ3NPJfCE0k"
    "/m8HdoegCriG7mgYmCUEiTI/DBZ+W8h4w2+oFJme6Q4uQFKxRfug/ljCpCiAUwISYic//ANVeBDGVMO/2z7pEAMi+BcAxR2Gf37l"
    "92bHmnpBLYcUbURwX2em/GBZ0T+PH0iNPhTZZpBpv4As/LsKzL+raXagEwKxiDi7zg6qDnSdMrXj4QWL9X/RQpnU8UUfAw0pqNtb"
    "gSXWZrXvZ8EUIRBxEFaknqNkA1IC5ImgEvqjYqXgFioFFaSEG9Qe8H7N8hFc3vus4kZrCJDCZ9ZtRo2JFdjiArLxADTE45tRM97E"
    "KADxwRKbNfCOFQF58mRDO0gzsGMtQ2wAGWWPmcU2uwbCNw7uXgpplp9fmnG6BzPtDqgKg1MSBKdkq0s8Xmco5HQrlZAsT06/JkoD"
    "BA6eChalE0PQxHqHO6KgQkKSysSMOuJObHdESp6L3IHknEgrq0Va0BbHnW0JC2OxW7mblgOLnTuyWGyOBUMt4wDxLJjVoQ2/xWEh"
    "RIY4HDPDIcVZjiyyOKcsjiHB0ZTIzyV23aDkHMdRYrZZKh7defHFsTxjj4r0Ler23bsWy8mJFltJ0lGr0+mkbNEXKCfANJkSrXGe"
    "ZymCszknPMNZoR+27XiWpPUOI1MzCQa1INg5DMjBc4kxavlIdrDEgGKPRMN42RMtaMREq865RNWpkZWbs6zNcYt3ELeViw2ZkCnl"
    "8g2VOvh6kVjzczk1GgGnW63QSbUuMso4VW/9pvN4TokwYBbK8KLVMpjLMs/dwgSS8FVqGEUEug0DIa9fJ6x3Vkekkx+NJEouUiPZ"
    "sdR/dpAAAXEctzgH5WQpjpbHt22OZ/SFo5YHdUpiNlRlIFHiAmhouD/8n/Z1qPZ1aO7rcKevOsX0Zq5fh/EoPbHqF20O1CfSOWQk"
    "6BeHBoHGCaPDfChZLUNmAYwoUqMjxjCBSRpYlAIW5a9ft4wJ6ZDhhhYHTJ8IXAKcRwxQhEfjSMwAFsQBKIYH7R7dguc0TgcDbWZ1"
    "qFipT5LXUNsdrMCOeOfSoQdrjv4Zf2WBQbrWb9zhnasTYWX755O9InBig2mbEYKVjL6gNqqQGJpFQcgj/afee4uDGcL8M0OHzMhw"
    "jXTiv2r12qRYjrhoNEo6F4jbWQa0A6KmbIUrtu1YSSce/4kDXbbdhsnRBafHWe8IYF5NuiBqGRCiRZcQOVoChQL9X1ndDuUrCKDH"
    "7XZQd++6bTYXfL2xozx2ScqpIxNEnhYpSUINqGPB8go1Wo7cpivEynKEGjFc4/il5Qj3ANQJN7TK/x8UMAxUbZ2BptWZsxweCpYj"
    "GWkWw6iPWVAXMLgjKmpBcTiLSmRuW5Wszr24oxh1hjSwCzUT5PUBwTEz4IbDETGkgHs05jHynNq/CxVAXyy7oxg4kIpG/XZwOqsO"
    "0HNaOdDZDvm2rjMrdPQOw5H8DPl/tyznb/z4i8/f/eLj3wKdZ/zQclsNFr0IagFuP/nR7758742zB/9ydvrB2YMPzx7cQ/NBklCO"
    "GA6hwJef//n8uz9HF4foYagCPfX2H+BBvUboBeo/NPbm6+evvn7+q1ehANyF63B3CDoXbr363a/e+hVchJ/bTuhPGnuAajFXoZZW"
    "ajIVNdcKqodlOFTfk//166d//MmTH/12e49Tb53/5YPzj3+nj4jkBYZCgzo7/f3Zgx+ePfjs/PHDLz552Vhg/SIlisYiX753/+kv"
    "PvnyN69r1Z84joXoHYVkyL1Xn3Zo9NMoJ8B4FLI5NCoa6IcCjOqgHWZiamTEAU+1UYdG1NsIHb+4p3EjqfSOoLL7KttD14vzZOrh"
    "/klTKAZllWDmtjMa8RC1Blz0DjhwBpI++fiVs/ufQzl+ClVg78w4J3956ez+u6ivzExtQeFvvYTC4uIc8cuSYGSd95Xp3KlAEsnB"
    "XEK9LMca5/f/cHb//S/+/PnTHz5SqlkSIqpHLXL+p8dn93/85O3Pz+6/otejFgH6YO5+/ez+46evvvK3z16BOYXSZ/e/DT/P7n90"
    "dv8vZ/d//rfPXt0+Qw0BpJhZ7iUo+r5CwLP7p2en3zWUVlnv0dmDDxD1HKCWhwqz64wOD5/dfx039fbZ6Q+0MieOHGgDAOKLI0RW"
    "B83LRxb4ADDGgyxY0Cd8F3kBvsOnRXOzLMpfiwP14UjpiRIcxPQDiC0TytcTR1NvAtH703+FiVRb+uKzn5z//A/nb/zo/C8/xleV"
    "Vp++9cmX7z56+l+nWMqU1p989sOv3n0IRWHoX3z82tn972/7olTzFOkDpTtPfv/oybff0DqE6vrVJ0Djs/vf03qm9OTs9E9np/99"
    "9uDlswdw8zFcOf/4oycPXjr/+X/APJ09+A6Q8+wUZvXDJ/8CcwZT8BuYNjRVJ440rYnzc2rAy9QfWjK8yKp/vfee9rABj2etd7AN"
    "1lW7apBkg1kWL0L0XStbsgJ0AExkkQ8tdsoh2rbVGIzG1g4uReudKTIyqqXnohUFi9+iVGPwLLtumQJOOphCc9wtz21DM7fcJpxR"
    "BoCuoHAK7CKMbybRYJa1hsXogLvFoYY5VVBv7Bjdiy2TwgEpQMMialgZJ2W3HB2gK+7bdqsMvspf7/0QfsvYX9maYYSZkFjcNFha"
    "CzmeAuTBeMqiahlzART2sTiMKBFdQI+Af+Cgtoa4K0Qp8FtQRUjkblqUtVfLEb6EJAauQfPKb70tpT7lIpbPmxYUodGuICm9CdKt"
    "F1EE9ab2BVAjqE7LlqfyghVQEJ7dZ02iJDMaBFqRqjO2F490BStlM9Bg7wjAkTOhrf7+juydVBH49wDx7i5o+nrNO/RhmLiwAVxI"
    "GDpyDQDsNcrJ3URTeKT2SnKmRYJGi/8GrHWLcqI5+RYU1sBYFrC7qhX1YpYv3//lk5+9iWwJdOIa1A1K3PwA0s97Hnj9/I2PtGcW"
    "zJDS3JPL+oPLIa14Ze3nv/rRVw8enb/2L09/+KnihSxGUOTmhUeUyVc1LqjMDog1v5QOqglknl5+/ekP39FMDVKV0NkvH/z5yT24"
    "8vCrD/8VXfnzL84/ewOeVBqD64o5w6bpLVOfcAGlfDmDBAj1Cg3F1C3F9Kj90mtXwBfUfv75S4DFoDd72wMt/+UH752//NaT//Xo"
    "/NePsBHe7QE8rpTRZXhL0msqodRvF+mMLNDFKlULfoJ8LDyTBK7jMmqfPfjN2YPfn50CVAA8BQN456t3fn/+y99hePXu2emvEMK6"
    "//DL98As/urs/mtnp68q5D+7dx+PE+bkI8WofnnvJTRVj2H2nrx67+z0+08efgeDkfdQ8QtzoLWjtq8xHkqTka4eqKHP6lgdimiA"
    "KGLhUH69oHK+lXKSPGOaWIRHtvUlKjlE/4szbyqCh/1jKKiSdS7z5m7uPvPldxBjfAV0UvqInuJ4ErnIVwoMGhga4QP48vTb755/"
    "97+V2VRVe34evYOhiNsB4MWjIRWvgkh8BosuydY7NBg7cGNxcE1zpYEgIxbs3G0bDghYWQcDHvstFkyWg0WWjIE7Ei/K2i1rfn4L"
    "3bh986bfdoh+Mdqvu3fZW97bhwx82G4wI+s1WY0N2VQ9i7j6hmZhYW60+y9wN2WnBMSgwKPnDj22I3nH3u5XOqLS51ss6qUeyrio"
    "xUfswYgF08xonP707cfnr//ub5/9xGJPWVmDLUa/ThwszKuo9u1bWid1BXhpAzNe1F13bTxaNQp52egL0ALQ1qaFDUF0TFjAYoca"
    "1GcOtYdvn5ijJCKBJ3PXboiUwJpMh8JS6LLWrX9WAOn5X0C6P/zGHeWZk/O3f6ZBfkXwt1KqlXlRlm5akFPx03sAmMEkViirfsdm"
    "175L8xkqBnTdXkBox25BOg/Zwn82DhYcGvBmDlCmGyptGqQMYBBnRQFCm49GjJlvFwwyvWJUo5WDha9qZJZmbNpVJireNARoWBSg"
    "cYm2I/cz8RxgVxQcsjhAa7CgTMSbCgo6Ym9aYCAbSuQtNjNVD75xhz1xfeOOaBqkwpU9zoEDW8zJNpJ4kY8Eo9IAtra4oH0HpwIH"
    "E3leFDTyAFWQsF27NnU2bjpRwrgEEjujrAxIK+OkYeiCpIg4vsxHX+Cds+mLAAbv3sXf0MBstj1SejWdGVqj8/NQE5ojt9S8fl0h"
    "p81s6nUfDflF9x7qP8/uYb8Wi62i6c02FPnYqCiwkko1E7E2NEA+hiOprXNxy8GZoupuc0j9YgBbji4xCHFKaNEAxr8gWHyfs4rR"
    "F0S7x+bwUD6tFhxFZilC1IvKxjjyfoWWFKxJ6AtYhqXV5oLa7DClhVTnkDIB2C5rvSOCWNAmiYCiME9jympDRo8ZApVlJy9ghkCq"
    "Fr4S8PyCMv1AGahOSSZEWeow8tjKOafU2g4UtN00lMJ4RB3ZNc6pupKARsTngKrXjE9cGrQUVzoOKccaZ/c/hvl+8jZ8vv7lXz47"
    "u/85YFjgifOXHn3x5x/ArbPT/0KA5BT87Y9w+cdffHzvy/fe12DJR+evvGyCKABOTu+DtlViMUqQx1DJo6/uvXP+yXuAVBQ3foe9"
    "LjUt4oAQD3Bsfl/UF4dLr/IudlhYD5HqFHvBoyxxab/tli8+/SNSpKjIYC1TEr7ftWo/beieRFgRCzg4G9z933/CBbbXQBu7JK0O"
    "PPc3r5xApQqVcTe0QxUl7WGsmI40DYUk3Cg2bFR0yrxMsIoeHrE8L4JVRMKvKGPlLqhkUNZWzHNDSpJVhaVqGlBZ6JntdegAO4ff"
    "Vh6GZFOMK9Zr2KnXjeuDTy22G88Kl4urAxRxUpgvBe2ASNj2KvCdebc4kEZnv8YUMw4L4mwt/qJoq/9XIa/aslMSWEa2Igl0Crxg"
    "xQskSJnZrGYD8A0BB2m2Xix18/JugEc9o4w9mcnADRICy9S1KJLhm5a/3vuBxY6vUzCdZ/d+imYUS/62UWqs+M5KvjKnmh5qr+ng"
    "tNmbkbo9FgGUSzJyk1lQK5a7d63ab45ayfBbvw16ULRgVTbnZIb9VtTnRrbn+nXxqmEuD+dbL+2rH712/v5rKCT64NOv7v3nl+8+"
    "BNnC6uAxCrX99DdqdA4UzWc/BI8FO20XvZNbFr0oTJOsEUXjK63HSozkSkG6POCBFkBxDHQL/dW4JHAXwkVHJro9RzPSZe3gCoyj"
    "00mjwLCZxg+ILZ88fg15LPYeixHeTJVzc5fw1P0PuwTAAHUKV+EwzDXgA4nnOTM2fvLv76JOIQBw/5HFAZ0yrASqD2N5UfrHql5S"
    "nAY3B/Re9IXKYAJW3QmdExlQHuAMEkijgJ7WeNV6S0auxDW4R3AEmEo0wGq1abFpbpDsEKEAivIdyvBh2zouhgQAbqy4WxfyGPaS"
    "J07j/qneDDSgezP7I41jRjggwZ8xxFHRU6qtEPEcOWSbCTSAbb/DDE3BVRGwggPJaUPx1u7eRehhr7N26/aNEehtVaUf8KMDWUGa"
    "WAGwoJoFcJW8NiggM9ycunHL6XSiBf8GhTxHEwjd6nQegQ1deVfAP3Iol2y7SRa22wr1OzLc4sUUQY7RI6JTmEtjcADBCtgtdy12"
    "3mFVO6a5lp6b4HGpZsFuOXAdWLA/krLyNvDCTrTBOtupciuFEI0CksFTQ34azL56C1SR1pp6xaH+VRlA+wVggFpVRlbojg1AIfJ8"
    "Xnn6xl/Of/pIiRogZHF7619utRleQ4eZRrOkh2TuI7CjhcHQyoK6yoA02k+evvNri5ZfovZJzzKBARA0jBwsNE3JTlzqolWz8ALi"
    "DmhVqcZiCj7cf+vs/n9jb1DtAtJGoubJ7q8BRw70OlCkAPxp7PFetCYJUudJxIs3NMZMSpgxk6KV080391z00tZg3jo7fe3Jj3+N"
    "HNYf//rs/g9BXyCtb1gn1CJ0r+Fbr2O8p4xA3hIRgH1TALv8DyIi9AVRkMMUFLcivvO8cYkeUIHN0ZDgE7vfX3z6XTws7EsDZUUb"
    "EAq4ltsiItm2Rdk7FcumimWbYy9vnuyZqZJxVxvWGxxY8sYFv48i1QZhUiwsNZJNKxSgyagD9eozkxCE8S6m3gfelB1vlv3xee2u"
    "htAAlHPCXOUZyzEYc5zsImPjI7AESY2VDSwWFRA8+PTs9FMcffvT2YP3caDx+09+9dOnf/iFxYGCfgl+JrCUDHXwo5HGP5Tz2JDs"
    "BUAYLoArZuQhBLtmDEotUrGdnlOxb4wyKEHpwhChpJJGtAdhaMNUxofXewb8CufwWHiOXbcsygY8CkTHiS+YesyJVq2Y3m+1POor"
    "wkNa4PsxWiu/bYDA/+M+lXf7VN7bp/LlfdLhnKlPugVVU3BGLLU68pwYUbtBk1iQmdnOJPp1oRtKEfnragWUuWDUDKpWv8BjX/38"
    "ZQPH7tYiUiSAB2M9+jr/1Q/OOZEyB5e303j6/S8+/i5gYiW4bCDdRXkjRZ5llVlTjLqhRn1Rok4rvq/JYalfokMQ9uBMRttmVivH"
    "LHCNFrj95Zfv/WifHv+uIenAABn/9tmnXz767fnjn/ztsz8r8YDz376HKP/m66ZawO/Hy+vaIsUb2Nr+C17cONV8X8tAxE6941Ig"
    "P+M5Xk/TGwEYajAb6sjjcQZQ9jx6I+KCEK2Hh0NmZrOcGJnhL68dHfwT/M8T8To9aCek0+P+p39C6f7UP/2T3mdlgnQXKwUw9dgG"
    "HnQR5fMmCAmo6gRsO7OimN21a1YZeVRYlLUvZQDHAOfA2V4zUIpHVtZmAHcEAnecAdwx168zOsZlTPDGdi0aJZADrsM+UIYHZNRK"
    "7AN84+gLWc6KyjvGGOVdv27FXxDEBtdvKloJ5Y6Dt9lsN8CuWckoaXg8pZTfHbDB9NmQR4vHe+HhsVORAL1IeU8RqP0a6s316zPS"
    "OkbVkSrsHzvmNrUE7u9Nz9F8++PQoyoLdUkdiehN6xxwpyS/iFwMt+0QOm/4efeuyCnDceB6bIYKVFFFgZS52mtoTqnC8BO856ta"
    "uNiExjjDy2fISILd2TJPkGMUHe4jr+bqC9HtgLDqu36dUPyEF6LeG9hrwHD68rjM2Kyvbl1e0vNcsbohL4N7BGNSUvCgY9fAY0KW"
    "+0i7Bj/Rkj3Kt7LYrhJ0kbUYV40I1cOAR4SrForkwZ6e6rm3hoL0mEfJ4PhkAN0XUJHkVz8C0PqGxZRj25/D3Fzz2PamSViUTT+W"
    "E8OQvm6jeHX3nbPTe/vadV/SrrZjyKIaAyNQuDiL3ou0kUWHssox1BaBLAeKmd9auhcFrQxcGr3gvor+JCfvRnYUE3hgcYzMpm/P"
    "6oxGFcKJtjRciPgOhowR+CCuQOVsyuAdwNAWO1aXNsc1UjN1d4xicFkyr25SBGKIk7g8YYPx2GHo/Zl4R+JNy5cf/Oc5ip7jxesj"
    "yzPMKPSY0jp8Q9PwJ8haC2DHdTccZN80BIp33BGPCAd9NHaMGQDT1zwnDkJz0BVdYqxQUUkzvD2gRAiOFbJO6+idE0dZv7bUvhkM"
    "1RgZqqGGKObRAaVpJ9uNsnNMSKAcFxS0AHqwjBZttN8OtS5NG06iZSe9vW27MVGfliipALXdvTtRH1cu4FWcifqIWkYhwNjmWO4+"
    "uzQ/u/OczbG+pf24Dfrc8Ct6Z0iswcbApwMuHeEbCE+ZKUBiI721S7Y7K60zuzQ202i2Q6PZ1TSa/eNo9HcOGYWWZmgMktUQFtoy"
    "gtp1q1IOdWFs00N+2hNW2rEA9bVioH36lvv2bdzo+tZC+65YT+0m9EO/Cd8RMNDYZmy7iVrSfijuAG5oxBLg4h2hu/MLlx2J6FYo"
    "kDkcayOgo9fE69fLnDVhcyyiE83G5qIv5HZtbAxu43AVvqkuEdkc6Sh9/fr2DkrxIKQxUFjCs6a3m1NRwbONcclqWSjmGGq2oGRs"
    "iyONvqGKxxbwv9Cbvg/xjaOEQyYGOYQTj9zqPgvN2iibJxRzhLaLXKMd250RC9JyVBFVzGE7MdkZVrImHNcwUQC0cjCWJNpkDaO7"
    "Y81pzJ9Ca62AJPULB2gFAe4LIgV8KyepETFnEfGN1dlOngc8LBhyfw6iRdvkbjKveyrgTIhhfFVhlHwwROnR12JAZGyW9ZXy2E1z"
    "rvnRgmeGB269Nt1kTq5uYEAMafBHry0MLej9W+D9b1eMBp0kcQk90O53i2bzFhY7mjHatqOLGtEWbdVk5u7duWNtcEJugXDeBt02"
    "10QiFgVBBGWB9QNa3wTlYEHJ0dEYFs1cdImroqGqBWLn9N27MSzFagXtrbDRDpbSJKxtc8ypaE4TsWb0heauiHU5uI8lCd/VZaxI"
    "RVnq+vWFfu9SKWsqUuZIctGxbE2D5pCjDbW7zyd6kiJ6qD1V9orUVvigPrRagnKsJ7JTks3C2P4awshSuzLXxkLSNslcE8lcc1fm"
    "mmaZa+6VOb2655O552GyK9ZeJVM2DeaH69fXspWwOYfsC1H3FTvuhmiNxSSvCjtBe4i3wMwa12nxuk3TUd+u2lT3roLVX3BfucvP"
    "2CJKFv/kAMlgytpEolS3XYlOtyqjy13QGV3ueZVG7vmUxpzapzXmlKo2ktyVThB7Eeh/Q0C5aklOb54ao4jd0UR2aP26rWgUyWJH"
    "/MhSW5Wy0MFo+1Iw2lbBqNsARtsqGD05Wf2dcPbk2Yt8rCkHfY5X/PTkHXWp7IaVMvvlaqfE6AsLUknfEJUIiHaHjb4gO8EpsLII"
    "k2RYjHrk21D3trEWbW4ML6+IKPAjo2CQQOI1TaSKtrmO11h9HVBF3tr2ZONS4C0eqWlKq5qIcnAFB/SIu3e3lRFIdq5Fo+w2UKRt"
    "CgaNSGBEhfYcMwrh78AIj3iHfESe6IRlVNjGOwgbWjgERXdIoE+bY0xaGcNoKV7PjlImzLitYwrjxSlOBvF1MMolJZJDqTEKj5Lu"
    "qK4DGCOFr+CtQd/V1pPUxGhlTQatp7z9B7xx6OJd9harZXZ6bjv4KLtdo2T1CNuhR8tega4hW0dEaXXqcS9B3KLXronORqqIViTh"
    "D47V4XRnZqhdwkyEFy9RtGa4s6f8xoUUNzRl5N2714b6PmiF7uo8raKo1HC7QVsJA+c4mW8z1NJ6Z4CPArBwFCFSoBNObDdW+nre"
    "OgqeQZOZUfxctq4cfrRFtmy+5gm43cbMuTs4dU67j8Zs/F0GgXXcIm9rDYyM82exHBUlK2dzCGouHOckhZs1MEBYTa+iL6ALt1ZA"
    "rNtqHniZdKibgVZKGAdvCdJLnTjQH2VFTM3Mn0VH200wpu0XePOaIcR+cTvZie1otJMvoj28mwFi3J+mPcZdfMy85UNfCLHsJKpc"
    "3MA+dJgzNEUU4UD710FsLI6RhipGwHkKKkL2a7uQgO6jtR5xB/lQmnbk1MChglR0L0G0HGF+Vn7RliOFSzXoAVPUg4lymHj+2UFA"
    "k7EfaXY2L2AzMroSKHBGAt66BiTgr7JfgmhKoCGusOkLbJIvuDh4aARa/XPMGCsPhFGs/W1s7hls6I00v7R+1R5vV2DUh66C7gTN"
    "m55QQ8Y3R6RV/2HD25auWghC+xsN1VzD2V6UhNeiVZB8dUrQzGEd6RvQ7t4dafvT1K9KdjAS321A+gquN2yiVLdmaIm20ChOlHWo"
    "g0M7BK9fH13TZEmrdgkQaHpkKKRX0WUd23zb29rukMvHJajPiYTW9G5XdnlruxVQoaK6pVk1HnvWMvUnUOInOlJj6002QJsRMA6C"
    "I/Rr3Bi37OCOfLuE+LqD31nUWzLWO0hweYkybxhdMkOUcMAMjRtFL0mtZqMMskG6SyGRhIAmBvT3iaa99BNwAeykkGNRBFhIceC1"
    "WeAx7A6g4zawndKKitSMX1CXlwYrQt2+gsX5IcEe8GirvLJ9E40Jpw/hYQHWxSVQQLzEw8CwdwSA7I6WdQODYTWb2cRXlDGZt78q"
    "NGih0xJGvGJf0GFZ+Ave+H3N45jwA+UCyuMUwZPDZ34oZUVqeHTnxLjXZ2xYaG05UbU3jGmad0BJo0q1EL9h8zfejvymst/o7PQX"
    "6MuDH6OdXCBUHwCIUfOylQjz6fe1LIAfox1gBo49f+k/nvz0VSiAo8mPUOb1/feUdVi8wIozLE/0fB+UWkjy4tAhozVLDmeFomGp"
    "KFhBSfgq3hFmvKqhBjwmWdt8c/OflcQp1PMPUTK40p/7j7W14Fe+cYdDugVIdhN/2nGyMNJ66okNeHc2XpxXluU/O3sAwO9DTJFX"
    "MCUeouTI+7807pY5u3eKCfAWShWB8vcfgvU+O30DF3sHJaOjnXI/wP9Ha9F/++zT85ceoGTUVz7F2wT/jBJMvvvZxVXof/6/OE8n"
    "HVATW7iGBVdhq7t344BTCYFx8YKLo8AZdMpjirNShhJW5UuUckzVpBfQISjxErwXXBU6SMiPdk4Q0pojD7a7nBAby+JarSlKoNMU"
    "DnYbdCh3ATMPwPa0lL9W/De6vYWK4Tv4D9rwICu7n+cch0J316/nWRBMpVfgz6hN3qFEkQft55xRkkTQ1MmJNoaTnc6WGauSC91y"
    "IplFNaC/0Wtufdg3lLGAbO8digtnsyibBgz9QMUvdkOr3aPXfrLVyWgoZgTdcmK9gaiAvxi2smhF8HjwfKBuatpjb0eBghbbDYXE"
    "FPpU+nsHrQ1dTWbbHa27DtRJVXZPlFbQfF8yTUPVUG+7W2YcYfAZTvCeG0NGIbi20AbWyygxGcBXy4kPs8a6UiEn/qp3BDWrcC0a"
    "PZpHTSWzBHZ79PpMzxn07Ytz6x3JlFlLOfkpWo1zqxvr1Z/gUwIRUCaQ5Zm7ElBFgKCfJ0zGMfuDZPq5AvgwAeUn3pi+sqgbaU0B"
    "NLULlyFtw9Zz7CQ9Y0P4vhOC1CdRutbZvXsY1gBPS7S6vw2dd8+gc7kuJ4op08/y15e/j/cOoqeU50ViibYMwJ9ryCGGunXwfLEy"
    "8UBJ1zH0Dx7UFqoNOy3mVh3BoLwlhR0wgAQGM+yAsi4Zh46GWELBQKABULIUFOUvBjPbaqLUtrE2bTVlw2oWHGWp44SpoRJQxWnr"
    "YDB12ylGsdA4WGRDRRQIuCh+jluMgzdte1OkA24QDnJnP5wxbOC+JGbAIFFF3dP+6t0zrMc5JtE7OJHpRXnM4FU9/cc1JBXaseFz"
    "p/IFH/eAy2hl8RVoHpVBf/BvAWZyCSOHa9pX5TpFiagV/Bdf4XiJpSgBrqnflGZBnbyoV3LtGlpt3F6AyRsx+Cr64kBhDZEhZXxF"
    "++EgaJGiUETwhqplJg7eOsF+3SVQdx6dwPfJBahrncB08UJuNqOGDNC/KvICQROIJVDonEBa6etA4TlOyvgaaBg/gHco6lEVBljM"
    "MG/X3NpE6dPD7U6PcVr0qTDMANRhprpHpbPHQGHPlq4OITrXaQds5HQ6Rw60nrpLccdMTXf7GtDRsYqOLvDiGm2JZ9QALMplL0ex"
    "1XAso/tM5Hy/iYRBzgWUc7oln7EpjZAjleNVcqpFFFKOMKdvyTnSuVwl60jhcJ22I427zSQe7WHr0Q5Tj3SWPtEM+xwrE8F6R58L"
    "m8NkvFWQMrfdSVrnGjJxhJA5PnGMDcQCPUF8a7uvFRSDYZerPQAPmMN72xikQ/+6B7DgHbZITQU82+DhCbpy45nTM4fKMNIyDfa5"
    "h/dM4z1k6QNoB/48V/4alDscX17SnLh8ERGMvUYjC47M64qXcvbgIxwTUd0f7DMowP/34CqAa7PPg0Aez+e4EJT+sJo40H0Kw3qw"
    "sNN/SiLNp1Z8HU/lQ3yayG9QBhLajfEaysX9zec460zzqbYF9O28j3B200f7HZr7H+rnsajezI6L8+5DfMyWWr/FnJl2aWqckvbM"
    "SdjAb/PgwNLv336wQiSzfPUj6NC/wti0HbL4LBJeP4dnl5pw04RJcOGrEuc4yby380pAt/fQLPOGFc1zfqycI2aY98G+bGdDV0l+"
    "JsxlbJ/RwWJ7E/6+ZndyVcw1r549+Pez0/+2PDv5Wn/UoMf1wzbuWWy4bz9U+4Z3xqMgwD+OZpgDn5tmuPUTZScO2lOAEwvxYRnP"
    "nXM+tVwZ3DYHSm9BXz9FQqZ213zy34f4nEC8v/7B94DcSHjRzvrf7myeQnKLz/QxBQoc62f4BDABpwpPnd1/f88xQppQa5vNpeeY"
    "5VsWlDUPbTss6I+smNDbGoo3hGv/D8zts6htUQ5dNERU9FiRkmK5mxQ79pl6aPnr935+YJ6ibVzH8uxUXmmmqaw6Ol+RkYgBSw2P"
    "lOiBrr/Al9abVG7dtCgRI/WAQKTRQQm//MXH984/eU89cFTpePlmWVFQN59HmZU1ZQbf8G5+bVOf9hNnUswdky1gToBxBrAqSM4R"
    "QABrLPpCTPOmbY5GNHH9esLJUdQQH70GwA+w9NyJBu+go9cS6IfyNE7TwU9PlYx0CZ0ZjrAdPHRLeQRlGGHsxWleBmYmA6bljK6G"
    "cvOZaKBkBfoPLY7ETXy60xGND5CheX5oeb6FLWk43pc1buSUue5ZP692nGNVc9UD+OhGvTz03mCGDWnCaDzb+OL2sqVSUHlEmwI8"
    "uTFHWj+q6cU5gJuj2AlcgrnU7GEBfGI0G0fqPDIcIx8tHNJcEHgRnVeKDs/Sf+GkEHAAtmK+w4EoOKAvwc0IkWa4Ji8cuU9MStEk"
    "Yw/NYrtzJhIaHihG486iv778/bN7Dw2aQtux+8hU8T20zXTffiKDknloceybYMs+EIXUs1a/2s3T187v/0EFaxY0WzjmrCQkHPz1"
    "e+8CnHsfeq63B1hLHSXaMmsIQL+lbDeG4pUCziXHQElXp5eQ+RI9snP0G+gUbFl2UR06AOhNdFatB5/eAr38AJuq1zAw/AG2Dzvn"
    "6qGkC8Wca2Qzq1ALHvMehLhdCsAwGaj4UwR8H/xeJZ6Rx65EaldyljqxTz5458sHf0aWTTvIUKfuF3/+fAeK7gAmRX+nwdc17qVd"
    "YSUCDp+ioJ5DjeDwsnRA8uxOn5U3JviFleXkf77HVCSGDKgXTtVYJX5IabsoLZ7tzs7VdjMl8t/QSZzGAMPehL4rFZ/RPO9s6NNm"
    "GjG2RYVYz+EAYccEuRUXJAtuIl/k37A6+Bn+fN9z/vbPtrumHf9Aqrm3VLt2Ndk8fxfZ9MWxHytCqJPK5AZuyWKAj6ffV7Yiqcx8"
    "7/Tp43efvvkyPkpFPxrzo/PvfGLQmxqprtwKRIvM0LtHtDxeI4uuni8EvUsQi5ExTCfOX50kIon8co8dNs+ospdck1kU2zHtgFeM"
    "sDLDevBHzYqhiOEarRVoEVS0x88hCRTLJhAfoLiYzgVzzAR63NS4E/m5NnlpXawyaMlJA4LPE+AS8BN3EFzDAntDARLXrxv7o0CL"
    "/SGUgBIhMkzHG6dPX3pf9xevSHYApafMHdoJizYDf/zk1dd0XK5sj/2HzmBD0a7afCnROZ0rV/jdIkdeL2j8K+dJi2VfmKbVVWlG"
    "u44bWu0wOW/qSWcHlitdTWUkLc4UocE+k91q8tg1lYBOa8R31QGrG4qhxJbONlVJ6Few4/iB2rH3wV04f/Mhinogl/LHW2N99fyq"
    "DTz94SOkkE8/PDt9T1lI/0fPa0tCcqlNK46z7s6qJ/CsWVXXIy6TvQuDU1xqNSj34NU9p1Jc7GgVBrntqB7E/fqdNSyWPKvDVziz"
    "l0ywamGvmlnFUOgSC1x2VcO7M/psOqFI+BWaVomUm474wDvuS7Fc+bCacBzEY4lCq3qIMbUWonjNHHsC+/blr76DT+j/CGeCAGf+"
    "7PzhJ+evfEc7j/LqKVDXpXbpf4EQVzL7Hndmx5c5f+nXyunNGBSZ0llQFFTPi3n61qdfPfxPJSnkUqfjO2jg6BDiVxSAhOZ7X0aM"
    "4m/cewjkqyaAgEAOUFaPLY6RvkS01R6oJD504s8/1aE8Tp3REZfmLmDQdf/hl28CeH4Xb0F+pB36/QHqyr37mJ/ex+z1bfTQtg59"
    "/yvG1UjXWp5+8MmTf/+2yr9mRwArMPMjqrJaXbEgfSmovohW/q4DUsAUoZWdLSTcLvbscNl2rdN8SArmM8tXb3/65JM3DTF3TAxM"
    "6K9+9AM1nr71DbG++g2e6h/jPKS3tVdTvGK8hQOEHxmEW7FNmmuzPX9TNQGOv5cWlFxdGmlhWuHaNb7GxbD9VFFUmSb2j3eMD/Y5"
    "38J0+tB4ZJS2+mDS6tpRKo/PX37p/PF/o5WIX72KqICc61e2+Bg5H789O/2d4o2oEdbddj8yOIcG9Pz3kq+urvUZKagvae9QT18i"
    "3E85gzpR1c4p3voArIOiDniTxL2HF5Q/Ps5XgS+KG/zhV2+9qZBoR+fef4jod/qGRvWdkMEbOMRhVCGXOC0/MHss6CtogEfobQSq"
    "ujSl2/2DKN1hRoyRynjVdYfCeEF2P3U7zGGaOTCrKyVMAzzxXcyUb+EFrW3cDXuo/4Xp9DIwEEJTf/pJMVbWXTTDKxWg8r2a4ItP"
    "PlFn5/QUR+lfwdRRGnnZJMlG/fg8kbcjS1hYoVdWmg6/2ZUhdFLaL5TgDDYeeJkQCZu6lHb/HXRo2c//AOM6f/N7ShxFWylU8TEa"
    "w6m+cPjmxTVR/Iii7rYHtCmvl3jl1/oCiKFPH+4/GsjoxlIywaCTusxQhhyj1wIKKEnevSedaz4D0qwvcc71VzGhaVdUCn6diL5e"
    "NWf35myxjHkdQQ07bQNhSNW8hz3fz/BbHT68HAQYeOgxOkBZwX0XF5lffsnkl+DXIGmxhHsPL1gHjSNfR40/uH92+r4ai0Fkfsek"
    "Yu//24XncCB1z9IvNNYoxdHdB59iIIKYCZ/YBhcEhqMPcMjzP87f+Egh6pfvvXH+6ncM5z9pAga6GUUFkH1D1dx72OgclGONg0o1"
    "VY81K3XUc2C4PYz1+Omjx1+9+zMUEQYmevAj/Q0Of/vsDWRIH3ygJQljCHUPB0kUK7FX0+9Op2VvPBMdZo0q/IGybtfAb9iEQXd4"
    "cYoywVBy2XbVHcaLX0mBFuL+60/4Cw6HnL6CRXwL6i/pwmWemobqzNZOkTWsZZ689firez/ZY+3unfrc+LDG9w24waTf8axs16G0"
    "MPWj80//eHb/97jNV7EOMBprYNbfKQyEK/kLrvxlPHNb+/v0h59+9W+/wNj2VDtCUon6a47rpYQw7ATchh4RCXBm+Da2prHxBSP/"
    "4Ze/AeP/uXLWOfI+sMRjlff4yaMPsGH8Pj7X7ntXzshVWO0y8bp3qgBC1Ul461QXrsvbuWjMLzoZBourv7sHIe3ff+fJzz9Ti5kd"
    "kOf3NIwcphBfA/APDar8ZTx1b2Cz9kvjgJXD4jVheRN7Ch/i99ZonTHKoHkBeb4XAvwfp4+qkb5uzy9VHvsofe++uccq45pOCPoY"
    "N3/VlFzR6u4qOkbAl1gjlIO0IyWKw7erJncyTJ4HfwQv4g98SuDuPoz77+Pvb+uqR5Ppd/aT4MGnhnl4xzzhp0/++IoeBsOqx0jW"
    "R4a9ax8ZSmpwDoAwOnj0cxXSfvTl5z+EarCr8uHevSLaIiPyeBVtor4W8rt/fPLSawoVMah4jAXj90gHPfpXAw+hPoIV9eA52oFB"
    "v8GFHm9Tyk7/ExdQ9sQoHsu3jf1/+l8Pv7r/vxRLvm994LFynDfyAZTFBMQJv8Tz/ir6folSNjjoF0D6lgXYAXvASTiF8ZkBwl3w"
    "HtOe0tA7rmYXvivpkfvxu9kTfN8s9npimhHiWW5fneg1kDnpOU+QE0RGd/jQofh69odxZfPuXfbu3WuGoeF1gKXhAGeUSE7g1HSU"
    "NqHktd60nD9+RzkzHqeHrG5aLl1QfmXfnD/U1oTUFVyTuKBF82cpmdn2FcSXJr8o73nfBsBRyudlRNCHPr506DhnFC1A6Hpid03b"
    "ckS8sM1svWnZD1ZMz+O8qSNjpej1b2pamjAktovPz7VEgN76+fbPdOY6OrA4GuC+c7RVr86G37REkJTV0rQ40Gkt2/U48aqtFxLa"
    "9uMwvXzLsLvCrHoNew9wwo/l7l3DJZLgSAomAaiJVtCfK0UDt4ZOXxGVZBLDK8uUdCFjRskcZYSgk8ovbCC6ylAYh8ZPb1rUrXsq"
    "+sSoCXQOQnz3vnrwyAwxtgftYeiJCgPr//WnoI4ff/Xzl56+/di0C2+/vr4oaIgDgVILGMVNc+KeIQKvQXaDLXhNSfvA2WP3H6N8"
    "jwv5W4qN20m9hVv44ft7HF39DS+mvTEF2qok61BKng5nyNPRD964JTpY0+YSbs9OFJTPRURJPfFriLP9RZTtT6Jsf5ynRd2ODh2s"
    "dWg7eY4NVDgdTF1dRd/xwucR5bj8tRTGTMWHFgelBKovgHaja7ZvTcIYIJ5rixCims9vXIM4e/Aetvx/RAlCKDB+yQICUIVQF5zI"
    "S9dvntUTwbvtynYrgbk75hWqq7ujB1XJr7X+jO3SdlLQhGy1snz3LrNnOZq3XjOl9ZOX7KDEE67xIyaXuLOLYjv0E9uNpNWq9V3P"
    "RLTsYHUzukaCjV7pu33M8KYh/GIJqBGrvG2FZ/fuaZW8v1dTKBWqT+2pT5oygoAMgf7VWDd6VrtseNhuOcA+t6Iz3r8UnG5fg4DC"
    "ehq+3k12u8RHefAzHP8ADv747MEvlVWXK7Scsnc+ghIAlNQAEqUGkHpqQBDd4bEm2G5wRTsyT/bm4xocyPumrFR1/2aHxvs30TEw"
    "+GBqQYpaDC8kruFjkfCRmXCHQ6dCozOLeeHu3TsUpzKkx4FO10FbmPDBl+gLzlQ9unUbvUvzxdlAkJChovQXVxn3HGnXorfUA2a2"
    "i+wOlCOBqtObcp/ctjkECb/jVa8Mp62K0RdUMy7i1ArlADJlWd6GX2qqlb/lvo1LRAX8bie4/OIQ74xSihBr0w4o/RxxSj1+HdtT"
    "UNboBTdOBuW4/j8WO2u7YVW6hAoBXJS3J27rl7f9wKcRydAR3Mutpcjqx7/fonbevYdP1nHgF98YLyNmwe/23L3I43k1CL9AMKK2"
    "95zb2VyOjj64sBmPt263ue15rR+vbEi/7FV+I/VVfntffEWoW59GUWgcbX8C80IsKItRfwkX9RcegkNnPMqpfsObveAn+uMgeXSo"
    "xt27yultyDSOYICcVQCwgymTtAragzctX9375ZM3P0G4+fN/O//tvxp1GEiifvfJb3+BLb52SxNOAQmnYN76xKBWQBqN27usltFS"
    "HR1n3TsuFxRAy9qof5bLY9CP1bis6Sz+3V6NUK9Geq/Chl4No5RygIkInq/5RYqH+p1veQLP9W7Z/dmk+zMGHyknNaFVPLTC/m9n"
    "p68rS36Xb5naG5tAeZhhcx6mxZixiEIF+9p//MXH7z75EXIxjb4XKg4u96vf+f+pe/PuNo4rb/j/+RRgj4YPetiCSNnJZMC0cGQt"
    "sROa8oSOl9AcCQQaQIsAGmk0AXJIvIeSnES25HHsxPZ4mTh2bNOxEsrZFctOznk+SmxS9l/5Cu9dqqqruhsLZU3mfc+xRaDRXV3L"
    "rVt3/V3+CaTAg1++JVwjl25RqO/TaJhXfZdWX3bOm4bCSyxBitak7ElN3Uj44KjKMXkBUee/zlEjAkgNz1P5OrSY4GdRi1E4WN7E"
    "8wqFrp8pvw7bvnJs7fp89z09/Jxl5+P7z39IeqPslyytIT27Vz9/f+fzFybz4gwJRkQ1Eol5yYtGoM1rx1QmGSTvG227OKTNArt3"
    "rq3FjU7FbEQJbzWsWIqitaeOntoY3y5b5H9grYyMb8oK7hkRjzosmAcHgeE8cREWYn2GoKqidXKq7nhOK5xx3MocLnHSWlpYtUbm"
    "GyWVQz10lrUEYEakKIyNbpNkOI4eRk/OKS1KODLmBcP5qt55OMkIvJCZgdheO5dVIIL0reEOU157Fs++evDyD/d/9cpnt99F25Xc"
    "WLtS07xMIT363IZ5c0Ini2cSfA/kfuj+JtbP9oCE6+VO8WsOfn48hI9WH/61Boe0dtEWxfNW0yqmmgaubTlv67XnzVPSojznpVIh"
    "6KIeDsKBlbY1yRed7Q95TSWuNJ5ye+7defNd+vA6Gv+eB3b0gnLvCGV+55LKExjusY1Pyz/8VguyHGNwg0WdIxuRdPQ4WX7FcUdz"
    "IrszixuQsTmDEahFMtTTKuUzJOxZinuVlDTDZYCpvPjG+VoYtEjPobo+v35WhIBJkxyTdGoFUjeSJwGDYUEFU9XL4bOA89QeR6tL"
    "nMyHES7i3D2kUJNSjEDXIx7782S3gLvU+grHBdQ9rH855GX8Jt7vQ8w1T44RwjOFZU2aQwyJyDtG4DFD5O0RonHkWo0o6hSPHZs7"
    "/i/AqIFVF3Gu0V40w+8QL7Cc0F1e5sqijmXKLVflBHGQx4sJKYJc584yojTCQW7NwU3CsIpXuw0MLLU0oUe0QoYPdsw/E9ufRWTh"
    "8/QsQvNlPAu7jK7oXnkVaMQPikSAjEcTjmPtIbRdrncxVlIOl7cU0qQmQ2lzI/K1YYd/c+ncIs3DypeQdUHl9Mqt3GkQCeA9WOqu"
    "3OYgAtxFBz9+7rNP3rAO6X3LkHCXLb1pDBf7BkKT+JXcg48++ggcq5xc940zj4pYEZnO9p1vL1CWjwzfkglcGIv2zG9ASKRaJ+9p"
    "IaDjEohoYXBwInsOWaSenwVTr/f1ph6ngxEU14bZdr9x8tEzODgRZyDW+WkV5CpP5BvUjBmCOhSeUJNLedd8JzTKBIainixq0HE+"
    "beBGM80Zq4QANLj34G+CRh45TDKNf5jD/atOuenX2w9FXqsLsqtH0PFOy29zFPtsxllfIWFnwhJrQc8La82gj8RXrXpYxQgYyDl1"
    "1Ws2/U7Xh0nqN/zIW+qA6IRJdElBI5gEDIKSq3WxYrGbDzQkMVB1mULNsGalzzripqyIZcM8aNn2EHyJStDZZFKVbSiej+iWSazO"
    "b9TzZjXiLG0n6AjsmrEJZDdJJLwkt+SzvHW++Bn6InJ/feFnn+688dcX3s7pexR0UJayyPtwWEWs3IzGdytDQRa7Gf3IuUdOnj59"
    "7tS3crwjdfahItukPyUeA+UExHqliJ8ykvqNUZg5gpzWC+1TAAfOEYZeYYLrXlYsBnLAz3/5OirMvwVl+1XierdSRPQqRdqTcv0D"
    "dslnRYXd/OzWc4SDwnr0M7HXXNhIvaqsjb0VGwOVeQ/zgOzt7WP/vnzy6HfLR/9jpXisEHndKO/ZJfytaB2z4jro0rF4bPmpp46t"
    "zBw55qABO5ppD5x2wBajnOeeSNiIyK7aLZHZcJpsl9bMGQ/eYNtcbKjrHHG3pBW26oddxj3trq8WtwYOyWmWhsYXBfmtCpr/O8W2"
    "0ymHkQEAjybKefGtb9o9ZYU/afdct+f78VSEbObc3haf3L4wcTohdxMNyRI4UDWMmAVUfCOf7zsNaD7fV+3DV9cVzTq+ixUpSuK5"
    "5eYKDzJw/ZJfkKbiFEibMJw61SR0W40B2/N990R/Zm4IeFuwvR0hih1135KI72gp77tTs3Jds9aJVsgv8VDQ16AtXGALJtiA1/Sn"
    "pyt5rizRkKvJK8Z29WAQg4Em7l9eoTsbytQXP0Cscws6OYdA8MFKBtoaji9E4/f29mTjzBuAVUdoHeChYHpafHED50gByY9xII8U"
    "gACxStkRVBVw8Z0p/t1GS6i4lUm9HcCsCPtlw97iJ+KBwaBrMRgm9hxoLGmrlyTccLlpWbNm3T1xsZ1ft+F5esbFIpDsHWoUxa2y"
    "tsD9NrvM4Zm8cEisC7/GOsjfwCdtgcX5CGhWftcrlJvNvNEZfJx3ckPDtBNrqxVVgM2BusT69PQUzdTy+oqYF/4Sz4xXzQew8+T8"
    "XLTjexD3tHgxRj1FCzIuK3QHltXoF/lJqAwljYt2FhZsQbcEfXL126F3Jb6R6BdXIF/DgrQETptPEBjRkRMoZLyO28dfES+OaYze"
    "gY6WPrZEBVOpiMTX7y/lxUdX/J2Zc/zC+dX1VgehYeH4p5DXZGXyuYO93++//Yo016BnjiL00sVvKb3itf/c//U7bLXNWTPyTVZO"
    "y74kQYIcbHZxSnaS+gGdT/Tx6JxT9bCsdU7cgv28m5drUS78fsz9FbPstNx4QZwN4VBgJqnoqrXcX3Euuusp8hIkrdfKIHITqw+s"
    "XDDlBtK101Bk2NDJsJEkw4YiwyU7vofIcCkmQwlMI2+Yvzg9fTIMy5sFv0t/86dshKVRZ8dFpEKjRzMXaRoGCDeYMeZ5efN61sai"
    "Bho4qJaqA3NRA8y5mPWQsyT6ewr6C6QLO/MUzErGvXMryeEsQf+X4uE0bMKr5B6e4t5QDXMc0KJbxoIvoiZJUCpzDYosuwIWnIn5"
    "MuzoRQwTIp4tzlQ6bVOc0ChN0ncXC3heaKVogR/CQsLhLevPyE//fPyEvFv+lO9gaAESONdYThA4aZo30nuUbFB9xVjvY8Z4xjY8"
    "8Hn53hP3lSzGUcKzksHDpdd9TwQG7lynt/yEQyFJPLwW486wUya5ndElh/aWRTgBqc5uudqz7C/h3YqFzL0vdt7c/+i9SRwj430h"
    "3BZN57NfvPqjw3sH2uutVRnKF3QeXsWq4y1MfEUffHHOu8/BoLDinIpvka757e3Z2FyNXDv+yX0YRBb8BusHS6kbsbF6MlEzOQce"
    "fuDYnd0XYcVnc25u/+ofMCKfwmAzcD8643wH2gwf/JpMspg6fHV/75n9778vInI5uyqNEYRh0Sm0NlC92Nkl6hJx7opRUP5vHz+f"
    "rmPESgyrNQe71w6u/oj8PEZCbmYfhphRSLm5QRrHzv7VH3I6w+d//piMcnG4NqUDYcbD5R0tkecyVqz5y1tsGMuouYQJ12riXv/0"
    "0musTZHSyRY6c6/oljiOH0av4XU9LHmC+d0dMtTRLzTsczHKJczLszwpBkwWp01flhiRz8hWycT28od079N3nsHV3v8jUMcrB6+b"
    "eEFZwzDvfPPglV1q4aY5PDy9z+u3ku3wOXPib1CRg1fGGtESLZumUApqf1UiON1MFRpmqoAF3b/0Owy8x9spCOnyZf31Q8GzUgt3"
    "54/vf/H6D4Q/2SCGm0w59KLrB6//juaYo8oxWYaybZ7NXCrTHPdgXQNlfJK+rHCsCTFiCsaxbKVohio85zAG2UktqnOziaAB3oxi"
    "I7GZQSQYXCeDx7PDy1Lcytp+eCqpfLG0KQI38NX/Pnjjzf2ddxI55JPbOIwXCrf/naffIr8YJnGp9+tMSmR8ZUZFmKmDNxQsQsIG"
    "dOm6NMfoI3vVOJzF3MQ5zhJeNknLuglLB/CqotBh2GY1vEM2PAxHByYsDI6Y9C3Q2CZypfP9ayBziNACPhqFfmS609lvgDkuiImh"
    "Ik7oFFKnJ0qYUru6aByX8qicqDdoKDDiUkFbyOlgHQ3GQNU7uA5baraUkbn01FM6FUHrp4vmpVzuWC6HYDec1PvIKfhEprHEk8lh"
    "kjlj5ChHQCuNglO6OA5O6aKAU8qrTtB0kM6kNOTT+YuT4SndfQJ7vGLCBxuHlTTSQSU8a+JyPHHiCSVLIf7Hs3/SvRrj0zd0E/uW"
    "3DeoroDkve7MCbVDG/4zIGO+Q95pMiscxkGVAoYMjZjOr98fpxCMgdZaPX2yWh3SeS5yKQJCMwNBk4MyrP6d5nrXtPrjoSf9y7CL"
    "v7P0QAzajXONQaV9VIPwVaBx4ffJEMJWT5/2aolh9GWEaXLmx+1PI8Vl0nlc9KJTtbrZBazyMmRysCIHQXqI/W6azl9Vvjas7cnV"
    "kUBcErlsz+CeiZ3m40u6SiuvsLdNriiZD56Yu1sgu5TKOj6yqOs1PYT+2GJd6tsBFiiUahP2KqkvkX2rQ0HZ0vJt8sXY/u0IE+Ty"
    "imEqNcnEsLmz7UN0LeigAR+6xt3RLOXx031ptmMqHJDJxh4dipLQ6emsf+Hg5T+NRhXToX3uDSxm0DndyoR3FAZGE+IRJpwImdY4"
    "h+BvrOjRx4SGR9dYcLO+LAyl0cs5PZgwu5uzyW4evPIu7K7TJ5/E/FH4c5zgXp9JDoFBYEcbPTQNm15euqttor1DAPNOYoGIhTeY"
    "EaBqjQrIgF8ail6W0Prp7oEtjPGKS0TI7ZO+V7iYYVCJuP57Omo0CrN6jgJWcvh7Q7hE4l6Wl/kJ5aVMzJl4SFSDVNdWg6qBYtLS"
    "d7iybvYzbZMXM65nmHgdaXNdR3NmnidU2P/pZnseHQ6aqXKdLJd04K5L833dTRprS6fk88VlpaBdhJbqpg23zi1djImHFkCJ5o2M"
    "pctcN8WEYymrJvfcerzDeu6JDdAOemaEZfolCcZp6TF9sMe+wMz9PwhQgCValt4wptvTa973gG/37MQ6TzqgnhzQRWNAm/d6QHVj"
    "QN1RI1rGITlpU/2UZqvv2RQ7iwBDb7yv1SgwQs45ug7nxkEjerrF5DjiIFENAugUM4Zx03toIbklxePGKPGYBOSGPDyLk3Izi+FK"
    "2LInEsAH9j0AYZhYsC5vZorWJHgUCoWWE4vWMmdrsDKRQI18T8rRdI5iwOUcUcCegKYRttYXmQQ5xUIl5tI9N1QWggKUk5hb1xUi"
    "jTJmsDkmI+Cre9dwWl8OaZAOu9N+GB/8NLfngdVygayEeCh+i4XCpM6XsFln+lJQWDDAiWIAHRLWJDKClUA+mwBSVkVPwosnOfYT"
    "8jFMRiwek9/ZsjKmICkTm9TWks4pDMdgAZYdRv3hsi+baZJy78CRz48Ebk3uWSBjZdWRWEd7+398jwEqcjD9OYqdfFnhvjGoqTAh"
    "C7M0V4NNVFU5nCg2XKaYTF15jFyFakFofyeXg7WRkQuyOJEgOcEpJML0zGBuLIvCXsbRa6wftX3oXp8wC6j7cKiIJrQAJPrFjk0Q"
    "ifbkdOjHnXzImeBMo3IueCRNeHwtquOrmD3AVIeUV3fYIWIS10Qc0Ki2wCwmx7gHuxke3VFR+Fd1BDjJ2dnwm+D7f9KNz6aiQyHM"
    "CpFhpHIjunf5MrxI69WbEg9HvNrwDFOYhdmHq5kRJOmThp76reFJoSlnofih0NWqVHoyKfb8+UdPfufbD50/r6L8sLxqJQjhL54e"
    "QS3HX4FOe8Ga57qWDMSzSsYvFAYwSNZ4/l5dK1X+UJgnD4pHIRpmIFKIgYXLHjCEpl/1ziOcIlc0bXt9eVO+DVstLhDYdu6bnQXp"
    "VdpN2/ymoOkV+uWwnWzKacN5lejeE+O6Z3TofK3so6HUlvWQk819M6u5RKYEts3fp6bUO+qIYeu321rj2jOp93y3jrWjZTFi9aL2"
    "mBfhlMQvwkq2WNQ4633JauDGmJBEzC4nE0RmpSr2TRfheSOY/m4xzrmfpRR7ivZcBTGO0y5a683IR/teH34DcYduYZpS4/bLcYCz"
    "lrSCa3NMvkcvUf7Ngrzqeuqj800y01Kl3W4U13tOjiIx5//mYRytEzkh1wGnHLJmUCk35ayfzluyXMae7iUjp9UriN13+UUzjUDi"
    "X+/SE3/R8aktylB3pubmY2LEzTQvI1BTidg4C7CoFEXpOfUwoADZEATliISaRtAvAjufV73NNwv9RpncmSKBpWRlpaskcq6uWjNN"
    "mjqKdLGKcSuUe1OyRmbaGI0hMEazgGapGSvdsHXIB+wZGFGrWy9d+IcLM/SJ4Cj42r949xXvoxmdFeyiqUgJuYBzGh/Wks4djA18"
    "HIPnMJ3wVD0vw6hx8WPCkj4R9NlYOGkIB3qDbOQfSEDGXUkWwj+driwVe3KNuZPlVzhf+/IHnPySPts4UkgGmApKhSXXugk7DUhc"
    "ks/5ugv7Iz0KZP5Bh/8tdEKvW1KfCrwzizrCxpF6fussFUbXClq33bhdJ3J5t4m+TbXlm7a3p7wCESl9QlCOqUgrtZ2durDqZxZc"
    "zVIp4dZcPTDVSJwZtoGLd+MkMdnaKqEzK9drJEk/F6OXal7x2CmBEreZiJnQTsub1uHr+2T1yGimVW6aymEkdA4r3b2Mmj1D5nSS"
    "CSWGPnpCExP3SND3wkcCEP+0crRD5otaP/R8jUrh05SU5KS1C3QuUUVBPplK1nEQr0UCNdVf2//zdZF4Crq+ACO9jen0xdStCSNt"
    "RgKn15Nb6h7vpjFQTUGANkqRxyhWTtQ2i6NMjLMhEQUiCYrYsiA1EQuJc5M7s9FpgrQY5hLbZiKC4n4N8wmKnzlUKCPdUpReFdQv"
    "VCEhF7d77rJV6HQidInD3674G7XEd/E3El+tFadddbce9MrV9EJpa5MbzlzbsYugYYKSad1tJ7rLopBzyms26b0OYrGplyvCyD6c"
    "NKIwRES4u12AX4HK14ywUmGnHEieHrrtQgW7Dv8CH/GrK6X44/LsCspyTTcUeczb2/TJq/oRSIfiG6yR5fguvLADajMewMeeKiz/"
    "e4ESiezt7WXLorj9QhQsIDc4VQaBH6GA2r1YR/YRQq5JqeREZ/nV9nK4gg/HVqg/A62+xW3NWGbVkesS8g/VP5rsF+JM8iTgHM2A"
    "0EVHpxMujzXjwu4y9hlJvLHS3TR3XOIAUXxqphzjD6BQXuhGQQd0o065TvDfMF3p/QPzLTmyrknHrC8YV9Q3N6oQ7cN5fYjiKNWG"
    "yvnYWUMdnY9992PlPhhxC0POSsF7B5Qq1A3Jma3lmfUoz0xhHILsb2RhIbuChxB6JN5x6Mh0fS0ZF39uI5CTP5iHuwMnwlQh2Cwa"
    "qBd7uIQJER72YVdNTwtEMD+NCJYNjcgGtHOgBWQj2CRiwUeLnAlgo+EmmXuKbxMEOrpNOx2G5CMgiVIk/UxYG4VElC2NX7nNNygz"
    "KaFnZhAICOfwk2TJn3Ck4HAx4oUMdP0Vw3EyeRXErETpIRW34szg8RhEpq01OI3ijDC1tlkZTkw06eB+AlDncN48Nk8lZONEkpHm"
    "QBDm1SZZVv2hPj/cIVo//PiwhKPT14qsrwwcvDfh48yIIMlU3GKArL97KElwelXFdIrzIt4XoMyR1k6XjXgNXDRlU+H9MELyHSZ5"
    "f+kQE6P3fASkes+XM3tPP43o/eizIzmqPRkRdq8HJsXl9MKIH7KXRkqrGrMaIrVKmXkCN5iIdd7NnUHQhZys8vy/ScFnGP4hk4bz"
    "yNy5LCXLJsPpme4zKFpzzKAFTZ1koymdcwaY7d8bWjAHmCRz6vdwQhfD0kj9UMMaB2dzjwfXHjK29oihtceMTMcKlEcmFrZp+LXo"
    "bx9fE4SMIfhPk0MLwZmynhi7NzIm8NJ1XTWPa779/XfJw2hfiOeZjQzaVJP9YWoEU0kYzjlab4hJQt8PemYQpQ9dj58SCFqCdWAV"
    "IAS9+AXWaERgs2uY2nb5kvQbc3ExWc/JzEG7B5RozlCa6SoLzZgZMhjvMJaLo8QMkBdFHaFL1xDbXXjX/pBR3loI1mkh7mu6CsL+"
    "xf3nX97/M0N5xAV7/rdE7W8EkR782S7Ug5QACJdGS9lYwuiDZIGvyy8SGh2X/TGvyxwdtAgx5mdmOuCNT3euG1NGKO2wEvvPfQgc"
    "fP/K88g9PtkTrO5/Tsjmd+gv/jLQlzTpS2HFMtNz7vziI01KeW32/vP62AsXO3UGqDl4+9dkF5UiO6zO+W5YMUNW1MLhT2nhXRo0"
    "CJDJmpud/SdrkGH/HB5qwpX5GOuK10HulGRBN5Ph7sFTB8/scBISjBIzeXhen3pq7l8yRkxpoyLC6noGPexc588IDEdf+QZGRBQX"
    "RVkhQTnURfSdUH4qgdgy4mXK+D0mzXcEzpiq+mK6a97UMTlhhoS4dlNsghupdNpXZdZkgujnDn76GhMlaLIqsY2ucA3Wy1yeU6Rk"
    "4lqIwpAqii2ZPSswd43s2WTFVPPsVMEH9N7nEmC9WQmcen0yRFUdtfcTvFKuncqo51T5XZVerYLrHjmFacYItcnLfl08KmbjdawU"
    "Z/Zk/52X9YJD5q+qcNFudqKlOj/NREuZdajWxOwF+e52VGoqZRcaqf+UF6nX6dBKe+gdjNGeJs5OT7inxwPmJfPR06ZUHrhGHgKM"
    "S9TrlEncCQq6qXkARAUCseqYt7v32SdvHLz7K4KvviSXdJci2vS85xv7n/z6izf/Io+blxKFiHXTL0MpJmzEiufK/lzDxPNLN2L4"
    "1hFJ2FmpWZhqJGo9JUtcZgGjiUg8tbhydd5XFXXj+SYK0TFeJcpXIkqh28tzeEI3tLcSURzkyP7a7KxyFMuojsxQgjigwoG25icJ"
    "pRAmVGfYe8ULF9ytNW8TzURRWN5kHKyLwSp/6ATNZnGWwL2oqSj0Oxgx4m1UmkWMBVryIqch8KNCT2CFIfb7N6EJi2AjPMQNU3En"
    "dAMapCkXz2tXl7wmX6w1y/J3/PjAencTC0JsNEK+uN5dLW7J7L1OGTYHR6Q4PgEcQge6Xtypauj3PLw6GDjfa7sKpWoBIRgzwFI9"
    "l34p+Agfdq6Wt7YtuTIcxME/SwgSzxYxHfplb2YOc0PPVOh1U1P5hQK6ABcKMJ/T0/QnrpEUrrct23mYuybDXmJ7d9jTgpfWCktn"
    "Fpy2S+Fg9F4BXTYD3ZwRlzAWoA2qCfVoejpPf922s1DAhWVaWCjgyrlykhawELX8BZcRc8monyKVDJpZDIFeTlbytp0ib/xJ9fF7"
    "7USAlQpAoI7E5Ri48EQa+Gr5gfwFBqXdOIY9ZuyzI1tnpGPBHkzTQOU1+mIPLtiO9iSOIggP8fAK9Zr6CJMng7bmxaxFcmLCApEZ"
    "OgdExEpkb/EUw1M03fTAFlpGiBox6q24vNXsFa1VzCfCCJhIwRqtOFEQlWFzAdd4GMNlE3OLM75FdTDk5l0o4G605yedcHSjRK4K"
    "PotchQSoJgsWevKJwsygVRlrlzVl0jk5nN55ppG8Ii66Zu6GLZwIh8ep1QmRE3Cy4tyv8UsEfzDaEFXH0AtK20CwoenpEFdKfHPx"
    "ZycqrEHzVB0taMHOo8dgL4BqSkuJ20JegA4hF1tur7hxlYvkTqpixjg0y2WFsDWjLNH09Om8uqTBGHGuVe5YDlgBBg05vES4seQw"
    "w+npLPoIyhQBpeW6awuMv9ByzcvZjscPzJOmGQkspmTsnlF6JPm+ZiPPL1soEKNOHFNATHRZFQ7xbHXnVtUnCELYP6BoRbw7aC6K"
    "XgzzRYMU4XQ9jIfypA+uraFltvGiRzFnMuzi2L/nnypUu+dx33vbUWO9tdqFC6vbcAquRUHnKeDpvn3kmM9YmhFmIBHVhFH3cT9q"
    "5K3CeSt98f85AmPRGLLfiyMO5fGhBcPm4RzSYX/xtyceXngwijrf9r63jtEACwU4y9zACQp4ouetR84tPWo5ajOud5pBuTrpfmQI"
    "SLoWEQ8McKuIV2E8BEyc9cTRpcePPhqsYSjiQgfv4ZcUgnYnDOpA37COqKGWC3jZq+ItQRs/84mJPKTsbg047NFFoOsCHL0w3gB3"
    "RwcG6z0KCrWKwQ0KDKQNW+v47GypmS/bRT+Pk3EGFxxeRAsPSjLCTeesGfkAImvhu+lnern+mEVVTq5no/XiY+XVIIzSj4GkifV2"
    "DCRgnqp2Nd+2MyS2ACk3FhQwjlBk0kgzaWYigqWzpTN4WtKTVG4AdCdUK67cNtXKvS92fkKmUxTOrYQY2HabQG8ikFhhUppNXsvS"
    "AzWgn0STEZ0YDgaPhF51HVhQvuJUsdrSTJV3Vdf/Dw+jhVFscbd8EPww5Ipf7iB3hSt8aoVOZZ32dL8RsAjkcJlJkNgGuliBu5pO"
    "oqY7Kw4IH4SM+RqsDksD0IeVoJYjK3boe12cOjom1jsFbtNeDb3yGvWq4LuVmTmHf1wP3Sq8SbwkDsyFnQoMmYbk8A01IGV6Bgfh"
    "Nmdq9MhAK3KU+UafE1CpjRmuVKBKIdmD5oyrz5vW/kAyAboGU+SUXa11nl8WXSWYwen8hSNb8tvgs9t/UMUqaKmvZxW8fA2fyD5M"
    "BnFjiIaXY2sD5lEOLlBFuGIZj6Ss/eFQXK6UbIJSfCIVM8+hnh78jhmBHktKK0YIhTxu2b0k/cl+oe+trvnRN7zoZPcMrP9mKX0p"
    "z9FWiLnHzZOEtYIlC1aM/YGRUwRMCi1P+bYU8iOF2ojGOAEHgm0UfYrH9uk0QbDTMJkv0cz7TkDE4Rf87ll4Rg61LKEs9SOAt5NP"
    "HaQviBKrva9M7wtm5BsHXrPr5UTrp/3Qq6DoGr/CxyqccGB+m9k5b6TKfDXYqmS9vurUsNwKUGu5ekZsJrxmx7stV83BXqvY/HQT"
    "fpa9QVxJe9BvUNclwxkM4id9fLKtnvQRbVqGvoSDOqgmeU0YyIr/X8hUWhcKqA2i0gp/MLcxGfrvoOjhNOrUhiS0tPozr8Q0vRrZ"
    "UXX163Nf8+6fno4TBaanZX+7nharzzFMrFGJpgdiENVU8Q0sXtNdX+1WQn/VM5MzQIxl7TZbRn9Sne/zqD20+U06vG7knojELpSn"
    "PsmmotlM5f7BZBCWDfwcu7lsVcNyHRH7MfQtDDrWitoWMK9C2C5Xq2d6wIcXQOPBqhBUsfFEGyPO8fJpr1YGgRhVQabFk1EiSqvc"
    "G1rwBLsH929BF/zaJhoR1jyvc56WAr91KufZxWSR+n9eCI3l9Sg4Dzujh/fA9o+JaHt7C23loJqpWW+6XHoKK9kO5uFtiIbSHFa9"
    "lko5bEwUnsVmr5HwnPfEG2l6hcKNx2iyYseQV+Dpix0MMPgoLyc1zHQOETzdrVj4wEPkZ8KaunOJcwPvCDPZe6J8+uUX73x/d/9H"
    "V5UfOCMP2PmSg/sWrL8+tJgeksPTKCV7iPFRKSygyjCMQzQMlZevsREdnaxYdk+VN5Xwh68mRkuWyw9Q1tIslEkgR9ketfCSsFyS"
    "Of7g+de1iiYpCNN77CFjQiVrMbsLrNFIcbwSj1S08m+8D02fGCHVcdtzVnJ15M4NU7XeDmMN59b3f/3uwa9+R+W2/ouKzb6kewTY"
    "aAvyeDGOgk3HBTC8nWqaDxjhvwFO4vk9r/q3j/97KM3sXFotV9bWO3hP1jInyf9eOzl1F9MQJJnJyr+MLPUynBrOAvslSAJJEpIf"
    "Z9AEgv1ppQBnn3qq2yiHnnQmxpVjoFvFOaNHCSpSTD88VH1rgVXBo5A3jIIEDNOWC0QFrPrsTJgPBSKg2SVCv5L6QoiaWDgcEpCj"
    "E1TRtpUxZUnT3txdozrZ5WvS6ba3//0rTBiIjzx7nvfMwa2r6KPNfbrzRm7ua+c5vubO7y9/9tEP+LqG9BC7/M2Ii4PrP0xUMhWe"
    "nisvUM3pG+wgUc4zUUIPvTvPotuOXSyofe7qFZUkFd8UPmi8/ufM4ipxWual65ov+w3qTzaSrUqrHlqzST+TU7vxq6OCOQ53kp0E"
    "IUU/yZTQksDwYEqPRZqhhxlNr1kQFh3sYrUz4y+ynLe3tHqTV82fRL1Xs3w40pooMnv5cvy6S+RgFRn1Wlg1erFfpRW/Ed985bbh"
    "MZZlZ5keUw5kdFtLmjTBETIdahXpUDsZmQK1l97VsccMhcKTkZIwT0bykBMh/LHACT/Jz+K3uMzOv4OyceRYHfWeAdpIspQZIRCT"
    "yjJACfm7Qk7fEH/9BhZFT4zq0SifymJGW4+seXSTq0FoucnSsallKCtrT8zqkpMCV2t+He6EXmmmPPrYpfwGECLziCOA94FCvNEk"
    "ZyJJ/V3se6ylUZjL49PT/1bPf7fpxHehh0p+LgSd8+iK5Kofa4VWUC03XauCAJMq0VuZi0/nvQRLVRNUb8IEyedpHuPHGemsh/UL"
    "cU9Zcv8Q4arQf1CA6hhhZYR+pW4hD4KMcpYUa9yAmhO+4WVGf//0EiLVH7z0oYZ4/IHAJaH7SalXrwUpG29/4wO5xTnMQH8CvUZY"
    "g/G37x88jVz+i9tPf/7Mb0SQGqF8yjupJySZvobb8+af9//yhkJDJ1bwtKiKSUkW+89/SL7/F7XAcmiFaktyTIhAi97Fsb/zkTwL"
    "kFFYKytOlabYb1eCFuE3WAwi/8XL1/Z3GQVf8+7zpF36kVZ79Zp8Iwf+nW97CLOsQNfT7ItuLiP2lKUbOiVeFPwI9JD4keM4EuGU"
    "8sXAz2HPJ55AKZk2E68Xcn/zdwbw0jpuNiM6azYj7tRak7fFrQW1WtMncgP9jMFRD17+Ff/Ujn/Z//Mv9m99iKUl41SoKih8RQTi"
    "oZxDM1NQZZUI4S0+fCIszTwTJcDgRP5X1umxx8VmdHBiqjaji+1zznHnPud+5yvOV1fIqhcNzRKJjNgXahqk+Ghl4EQEKhrb4Ksx"
    "rgRmsvO+x6Bb5Bzb21PfbWrJtPm+j9gZp5pB1yvWm07fr3oGcA7fVes5ZLCJX1OLbRWOl6zo1XaBq7FDwZNlvZzl0GkaN251KNWS"
    "sDOK96GZxXcCs2RYwa+3EZaFjLMX/uECcNVUXTG4qxL459e8zX4QVoUNSH+g6tSMB5CdLneclnERIWOXN5xN887Vchezvxddo+AW"
    "CLQyfY09HO/uP/s614NAie/yn+DQQVwEgXH8iZbAIEJlWBXLAj+4/yumk1ZOgesLuEkclMRq6stuSGvxA0HQ9MptWAFjTtzyIR8G"
    "OW+ti/mt9CGuptXHYlz9Yr8gH3ZCeAa+459B3BQ137dlaSZuh6S2xCWM021j8qCE434cE3NlMiGb8qgxlXcsUgn76VRCRz57vtqK"
    "qxnkuTlVlycuRbYu4XnXJfBUw+1rv0+tZ9UbYq9SX3mVavkMzFYMblQx+eNdXg29NQO+SWUa0DFHL9I9VQQi0pB10tSArEykJTg5"
    "ocmDZ39KACOy+s/OJUtlYQ7QHcCzBYyiz9MfN4yxGuJnqlUmv1B5QQH1NmhRjaIa7jLyKsGisByF4VwOWrr5KwqjqizScHmqDZ1D"
    "5JK+WNhSXy6nm++PWdnp6ewVTNWVEyl3orocPwPUXIzftbwiCVd2xHb6lAGv6BEuo+2YSVL3hf8j+sfjG7D83rysj5cpYjp9ex6F"
    "NqdB4E8oG09Px59jr5d2LRkLUUT/VMxl4kqums27yqhTQojsI/X1Yw9di1Cd58fVYK0267lYWUjbbrMeONoYcWfKmHzcROUjsd4a"
    "ahUAxlHRWn+8ZCGI3OVrZMc10zUl6AMLfVxVWaBfvm8ERe5c+nz35wc//RHaEK69RHq1XlJVhjEW615JWuKotAy+03yhFF1lO6pl"
    "0PSkdSCrZVnSjsTKzKEcvPMGxVTuoREOha83MWT78ofw0xc7r6Eoeen9iUYxHjolUTqi3hyCZbFB8bOyXNA1abzVPT19dwRkfQrc"
    "OkxUJmmbmPZtHa19yamPKlQSmoVK6l+qUMlSVqESVgRAtJW1ShhDjy7otUp6MBmiAdcEG3aie1mrZIlTiRPvpUCYUa+NqiCCwsMk"
    "vKLUzM9xEcaece89Lt2xlM6Z53dLWaGXhHGNDl+6QwHEfHb7WVW2Hk19b3508NHLQseE3fXGB3fe/oi2yh6oKvvXX0ah7rn3KaYd"
    "FTi5xzSF1ET9RalhCdO3txRnphy1G3rR9lgqUKYYD2VQ1mjYx4qNDMza3Qe/xABwaY3aHTUU8Rrpiu3h8z3F9E30ZX4Osd4IwP/K"
    "Veuua6HQyRa28hc+3bl+RJL79jbT34BBwZjFgSr++a/fErl7wjZKrOkSTPObXHorKwyfyrl98hIFob+im8MusKjCrEGATdcRbDrK"
    "20OLsdRtuzjMLjq0tNXXEpWtqBc/S1cQI0Nlwx0P65pZWLzKNZYmdkm0H0lyBp0rgC4Tb68l90Qzj/a+0OkAnSXSrQzuhq4LPoce"
    "ekTWKQLWBh8ll6NyRt8tJq8ceyxorgO9HVPPHFM3ZNEX4Wg/QpWHRjkmlrJrFQ3s+SXhktBHZjgklnBLLk1Wo2ik54qX5vhh1mZB"
    "P0bCQjNzLZpj1sI4aW7fJtPXM1aCg4cF5KN6s8BhjXTDoahatARpHHM58bE6nGnuJX1pSWAKknZMjhRQmTP0X8X/5IblACBKXFhy"
    "WFyHaZLaJ51CNDSjIFEzbVuIJoBUj8HUhaSyPnqP9p0G3nVxrAwzSbFNrTqxm8sqYIwMkfCQ38syN10H3new93tK8L2hZZel832y"
    "y0TSu++jadAkFTMB+nmWjuFDumjnkPyr2dm589xdsb1BNX2eq6lkvoQS6W9/cf03WVVFR/T8/jE9H9I9xEOWvTr84EQRG+EcnwhA"
    "GdcDVJK/vvBWbjhc8h/0Coa5+7k09gdK57eyyqRQOuXe7zHUFu3pUp5g5JhUyhdP2vGiqHGTmKy7mQBEbd/Z4XbnismaP5OtRtxc"
    "sr+q3CbWYqSQG3Yi7H94GRP6cSreo/iDP4gEM+H9fFZL4NVuuLQr6mkJBvSszFW79PkH7xz8+DlC9EeIBi3s55JMydtjx9/+3psq"
    "M1DkbZ9y76KOMett96Z2sZQAUUn84uUff/HaT75c+WJMJeHixXNUvPirs2bt4jYlm5zvehXj3NqKr7szS5m6hZW7s/uiNRLogsRt"
    "zm48ePUyDOfLjQVtFITNrEox3zebGg7flDWg+JfDDml87YMRIPF6lur+7jXa1RhvAzNyB+3Mu8KzzfWIGVuXfEexPoKx/79HKfny"
    "RxRFjz4e4B/QAtkSyQCy+yJwDdBrCFDwGaL05+lflQp8XaWFimxfzuJMlflFaHqyMtz5/Y8OfvoGgZ08x+LIyihwCAvrwiarg9xT"
    "lIiw39WRNkBUCcLoPMXsYvZLp6MrmrzoWfe4S8O0Th0bG+PCOeOZsniBellxRL8zg+j//o/A32kRbsi1SuKspXiFBgXFk/y/g7dR"
    "bpf1mYSvzc3/8JKTJy4Pny8Y/52f3MZcZgzBeIeCZT4mxLLfMrjdqXMPCWCAay9RCsuzlPgco5rdefot0PPRjCUMW+kZHBMzpCxi"
    "nGqdI/RUUFMIPTWnMBdgc33+EUEVmecP7QJZ2sDIT7mZ0ELhlPiWt9kOIg+30Cu7+5+8vf/x83l8n40RkaT1kr67q+xwzsSVJVLx"
    "cRbOHYoif6ExvHrw8g/3f/UK9HLu87euU5UgzO/e5cv7Hz7PH0Ane//z3Rf3n3sW/sVeXf+IalMKowaGrOxcPwWqPCgBURdD2h9C"
    "YCOvG3FQzefv/BD5yCdv4xh/8id4lba6L9G6CjQGrW9xwWy9ahuoSOXQKwsFsBKAGtLteM3mKSQizGxmll02qK6SN1nzxHQweZ1c"
    "1Hwq+fxGs4QetpSzUdMa4yLTcSXRoTtbxaglqrMnw9RgPjMARjS4u0OWZMowWyxnu7NV5Bwt15uEjvSDTy//isC7MEogCZGi4E4Y"
    "eZkIDAudxKcYi8YYxEToOirqeJe2D55BQwRFER7J6AwCB+XgmV8raH0E/dApOYvW0eL+i4/uvPoJQTNcP09lvW8fXPvl/se7OMqd"
    "H32680Ic/HflNnOgz27jyNC9LyuxHFwHPv8W73uQbeErfNbCBuNt9DpGNu9c2v/+1S9+hs7iOy99sP/8H3mV9QfIw8cThNYsnq+n"
    "dUgTHfDrxv4nP6a5vEnRgddiHIiX/og+QzHxewo1iwyOT2eU8cqs89haE7YK+pDcMalKimmfccISP6QMZFYpuSyridGzfmzb7qNI"
    "t0B+gOL9swleYVhLEvErMvbommKRbKynw4lL7aaM9f1si3miMp4BT3T8/tRxrIWbGKMK41GhWz35cryW9f649fUeT/xyzzm5Yk9Q"
    "PfEklQf8EqX9NnJ+BX8xoJ+R/V9+UVhVTdORIJKkOTY1Q7EfSdQArOvdnBDcqDsxY1f9YqtTH81HFODAgV6TmpFo3HplvpGo06M6"
    "MsIxjidQvNOSPcs+frAzj5fuQkllCfWQh4sRN28l68cAu8qEfUQFJo6njV2zuxKa603KKhkG+CNk6cuXv3iTpA0Gb9OM7wxEJQGT"
    "ZbQexulJGKNXjLpTh6gglzlpLJSyz2h8tLVGvFW5i4F/rmgM9NAutlhSB/ETSGd5aSURWd0jilO/DnWs1WEHLtnDpRg5YuFf/ntn"
    "fHXbVX20636hG6y3U1qdvD5cM+FxEAW9+MVvf0cqsRFmf+faL0EtQSkA7tm5fG6JEtLlQ3D0iode0sJTv2zKVzdaS44uAn6xmTU8"
    "+mHc+JBJSSsjwXmp3l41oaM5lPXPeJtI8boHwwm656jIkzGioEvFyTKGJH5Jj0n/dXs7T18ryEhdq9zpWHasnu9cV3U7juXOIlRR"
    "XMDjeWk0FFluCfRzdvDu37pFbAvT2Q7+8/39d98fNhOCEXbK1Sqw6wWvFhWP3zc2jcjACq00k8tNo8JAztUAHXoGMuhWctyptY4X"
    "VBRlF6S8/4Pvo8RtCvtK32X+yF5X9FXf2tm/+kMJsTeKtP/nZsBVMxBXYsgmntTE8GOHmBkefu5vH1/LZdIOnjMKpPgw+Xp/3bmd"
    "2eLN1DG5d2fvrTs/+oFuGuBeydCdG0SrPxcqwOXff3rlZ5h0RPItgs9djc0bBG5qQC+zMQMzBkFoEdY+NJo/SkAwheoqLP3jlN7c"
    "pRSop3OF00vnlxAsBn55uFzhxChBHaIQLqcyvaolHxkxi5iKGAPk3cLjQoHf7V0HxU34O9AE+ao67xP7L86Hyioilolzh3Mu47v2"
    "7vz+p9Ahaa1BmDrmhUIgQHPGTZYSMILzyvuoQ4oatLtGvdl0vSxODtqTZdE0KYLCH7lb5Z5uGU5aA55+SwV7JdQVZcJBV+pfyGAG"
    "J9ClfwbaeT9XypEj8C9GyuxQowpGGmbZVHyD/QbDbCqTQ4tOJvMGbFXhcOfDGlbIASV3xN5dZbr6Den3lTGPE4nK/Yop1tTqoESD"
    "HCfqeqs+6UQjFbyNeKY3JRDfFiGedT0+JaMH6KNoDGvFZkYoWgN08VtcNpGe48NVPDekLAo9U672xCMn8ZPs9i9+e+d3H1qDkfEO"
    "MFCYVOhew69WYUY26HCiDsezNPV4Pa+KzH+jHlM9FfGoCJVUaxVdMpVyWM0SC819sjx0abGNtm7nZS8vB6ykS+1aK4cxtrLVDP0V"
    "RrSPikuKfdApF60K6TbSAwhalCOYUti5AlGUUH5F4mGcuZmIfxwTrKDW0YvKfrOb3Ayhl+ViXG/BoDfNLPmr72bOYqz0YniT0JvW"
    "79lr9QgJmqx3uKAmvu1i4vj9+xHWcWGFVDCzolh4TFFRAC0U2wgDGiHyZlS0KMDc+t/qMkd5GOxjZG8pFSOVjD0ZNwiEjG9YdaIe"
    "vWM01nlmc8SskmPO6DLehw75u1fe0xE42OC6c5EaHdj54RPhhcLlXKFPsUI/ari1IMi0XB3eZ7zc8B0r18MkUVAEHvPCLpCV8/j2"
    "dt0rXcB6MidPnz536lu5pVPnvvNorndk63sbg9ynV14l48ufMGASzV5W7v/+Mfd/f5FbOvPYmcVHH3z8zMKCIeePBVD42qiichRR"
    "dorwvLLjyC30LFz5ObmMbgsk5hHiRBymtlTu6eXoOqr1Rb2CAckH2UUry2UdksuTwcZYPJYSC100nZQoAxEzMEUcya6OAG2tFLW7"
    "MdkO7l9d725idiyFaIgy8ngfAhKBhhTfocKL1a05hGkS960UMcMRGyIChV8tvITPXXrj4Fdv0wUHYYy5A6ULR7YoKXm9HW1vz9pU"
    "krBSbnoib8VGuDRc6yNbXqFbKbfPt7pT3Oe8unBszrsPnzzrb3jV/Jw9Y3UJDQ2fQWTM83hfiUjGmlkI89pVm1DTEF1XwAFjJWyn"
    "VYy0BOWOjtaLOYsI1ltYglFQLt63vVqeMczC+MKs7Sw3HT+dwxc45dTFits2kgNa7olWwa/OtETSksie2bawtxivSM+fqdWAJ3O2"
    "gk/thAibh9DJLmy45cqK7dCNC+XNYD3Sb+fBtNxIPjA/1drebm5vt2BKw6DZJBwP6AQopvArfZuZm57Ox28w7nR8zKpCfpnqWfpV"
    "GG8JbxMl77/tIcDeudWuF/a88IS1bpm5/xsEtmnexS03p6dVd6anjb6ecNUvJZqa4lQTb/lyg5Ny90Yh4I7kW7aDXdkowIaG7rZx"
    "1DZMfXMlYyZw3IE5uJa7AT9sKJsRprl2o7xFtNAJOk4hBK7QKZTrdcve3i4bKU/VoLKOh0Ua2AvEFng3KMWwEUUX1c2h1wp63qj7"
    "of8B9D8ucT/sICGCtZzQq8F2kTljVdeU+k7MOTW3JQkBt9cGbK/NgQuMrIWpq2fyksyxhOiONbOxPLcyk9+k0uIIXW7P4KcWBUXP"
    "wM0EIlriaww0i/fAD+3zmG7WhZ9E0QmOCtDOyBw+I26bsYCzIJtI1XhMnWkP5y1aB2Dc09MIKtwpo1uspbNc+AFZrsy5XnQmEH2q"
    "QZTD8c6ujCyFNLYeRjyF0M4U9jHH0zi63ZbebrVkDKc05OgoyrtK8M7hXFtMLvYBVMd4aYgHM/wBdFFdh1Wgc85BtmdzkdCOgH/U"
    "icnuuMOHI5ZosnknGTMtRB288YFI4EM9WyI4TgFnnKrCy3UmXePfFYOTv4k0z0X3xGKcFbyoz60tUVc3Rj+UXzRP6e3tRXnM2qqN"
    "TdWGxH1ddPqw4Rdn8v14gRD4dcTcSQLPIaNxWoqW2bkoJRoQeR9CAP3irGEYKSNbi0vN6pb53axA8b3Pbu18/t6uNfkOybdK1KHi"
    "RomlkCLKGPYhN003sWuWM9Y/ZyWUVtxBLZJLj2y1BqDUZW4LIZUeYrttpraMQ1sm1mDYa0tMmUXAcZmu1O3+RDmuOufW7u84U4QP"
    "05b2kKy6bPCzrq3t/+A5nhIhM7ISFkxPN1Ujma/vBJ2MTEkh/WQfFuNyfZGKO8PY8t2y4yFZv8P57whFVxswcsZR+pZJLEkOOvR8"
    "S/HUoVqgPvvYfzxdsfviTB2+eLo9RNwstBTBvQW4E/LwJyP36FyMbRI0MgVp0F2WCoRBSuDxiAMvM2aX5cejcyvQeHF2/sno67MI"
    "Q7QE/BGaj2wHpPmgjvZEeUXVKlC/bG/jY6XZYlty2qZ7ogkNnngykpw0SV0jzMKkyS0EiJNTDv3yUW8DFrvqVa2ieqPkhyKm9gqs"
    "14d6cqDQotAM/18yncSIsFAtuVNxozg8GK9ARxoS6EFJyKMIcdUIMeW+4QPhidkRG3+1XK17csTsRiuGdM5T+JxA+hE4OXH74Yl/"
    "/deS9a//OgN3D5zQVGYbGZpVQqeKTJ0qCdICp6lcuJG6jg9EpSsgvimIB6KGTIEGjIIx8sGo7LeBEqTAZ5d8U8mIYvWjSVqGb2gY"
    "fkrDUA+4xp1OkzWM+UBhTpSz1J5AjbWsVBCf5fuyqYLEnKVB8NKYnAvMvu0Y3LJRhR9CTaS1Jzk8gBiDrIjsVj3BwsrhGhY0qhTX"
    "Kk65GRGiPAWb3Xe/0/D8eiOCTyOPzKZxijf8+FZZPC8+zDVLECn6zhMbcabc49PTDSCv0khVRj8778VBKC17+Q4704hpTeVFX6TT"
    "IWuKG10vI+gdCIUsU9I8K3b4qQpfblbLm0YaA7p+pL9ExBFlunm8Qs/3+kZZw0odCUtz+TCyAb19wdfT0kWC1u1URtVtVcmN5T1O"
    "YMp05Eu3zgR20AlZXHPVZHEfcBiwkKTIsbQakOGahvQAf5Y8+/vvK5AbLrn52a33Pr30JwRQpmBnTF3/7SWMxxCS7CG7Xwma3UN0"
    "X87xG+ROFakqo11fjdWo3TXdXEB6yr2bnWnR7ftRpaGmQcabqXDfJKyois5RURicm8ZQU3NfubP7IiWW3DQd0gp/4HDhRf2zwC71"
    "0she4ey5hYVzjxuEuw6EmwjBGSmURWG5spaOG864ESMOrIE9+cGqO+yNfRk0iB2klmScxPGop208jEfHXGVQt64yuJ+MbruOQYWU"
    "XssW2liwWKwPERmAFJqHEhl+wPtJxV1OCMnCmdrIuVUk7qu8sQ5eeZtiPSQeo+rzyWF9ptU9fphem++y1MnAz7d6hu834QtAVEvR"
    "Z2EgMMQ1BPkc1k+QEw9BNBI+aIUPDFXOYGyMM0c4U2//bd1XhPJ4yUj8YtxLCqF779PL5MBAn/t75HYnIByO6sdkApXad/Pznz+P"
    "yjzqvS/EkRuEJ3QXjXNrxDqeliloqs0hDYqwo1HNSkhPLWFHrdE3Otmh2x3MWLOEymKIpi1dNO028vYE+gGIVILQvUKj3AXBCv4F"
    "oYoWZdFTa+IV6K9BQae6Qymo7R1Onn+O0VA+vXKTfGY3GcnCSgxwIx5gm2TvwhJb3La3p0g+SZdRjAhfbSzkVtChUpIijrKzWta9"
    "jMu6VB5qBrB2lYvG+FhKJuLqGU7TDUug+4dcJWYSQ23QiUimDUcYZy1ZzFfhaVFMlIR44axUTltFdrp3XdLVmxmpR1h+WK/ceisT"
    "AXtcBMUz1kyejdpn8qFpD28WuhGZxJuFFt0Bf5VZPBRm8VAzi4exWRz/1+a+WRpj/KB3zSqftCDARnUk/a2lhRVrCBzCGVCBSHzd"
    "3obhioFmebNRBvvkxxb5lJrxETnGqhZOZMIWE+rIu6VnEB1A4yzaliwGix52GEwM7yfcHbOjOht0UEZXAtYEiAx/+/g1yR/38H4N"
    "gkFhBzDaQhoqISZorR5vDLI0iUlszTxA447oBCGzhHi7ny5vLqFkqUe/ct0PgRSLcxbLbIyWrVd5MUsExKVFQYdPVs+l2dyCf4vN"
    "gT2PCC7mXH26cx1oGveRXvWZC2xdtWZ8psUZKzd6qugo+UpcwfGir6CtfQSO8RU4z1cT4DxMIGTWDIclOoWasQQtJKK0xlQGdU1P"
    "n4ZjIklqIygtceglVEV4y79FeVt2T1sBsQ+2Bo7vAt8J1nBPIAfyqqAUVsmlEOAvwGnkT8Bh6XoZr6OZXv7QDSvyq1NxjT26vR0I"
    "0355e7sJr+1swm7Dj1FQDfAvTri0+scbFqaPsHPcyXb8BbWmjHifO7LlD44d2QJSw4p30LPBka0y8wGjKgjBOwBrKHM4QcC3fHr5"
    "fYxXvPIxljikAIKJTibQMEedSmNY+eQW7MpI1VK3zTH/HXV7KytAKOvGTka6ctU3eX8orcxkLQ7ZWuxEhTJIJD2sMWaIBvI6r1Hp"
    "YXi0UGsGQZhXvyCk+z/Pzc4eM++1i7NjF8QiF262wNXt+G0jlZMuGFFpFPbinIm7EnpNDca10Ak6CPnLrT7ZdrY6lQi2t+2EjvVP"
    "Fp4c31v38BictU/MCbfoHvD/Z/Ec0n89OmfzoYMnjiHA1YcJcIbkxoWCsYA31iaQOzzhdwzcE0HsdwwMZyVwAGIS+q367/jOx+2k"
    "p1YKkVgsl7IVhyKjaMGJuwyFGocQG2nXe6acxTUlfiYDmF+Kz04tEdkaG5U1XIuTsdFxQPLdpEqacv1o6dyx2ljB1FfcHghhvd1t"
    "+LVo+Pz5xL5hWS6YmLDXgV2J/c3H3xDP5VWKVP2AJlTAqSjDTuZReCHGZt6xxk5JapITE7L/n2/uv/4zSvX4C6rnoPvzVFRxKoBo"
    "qWYCCIFDJyU9J001JUe2zuQD6Zsr5nBK2GNlDgJeF4jXYTXv2PNf9+wkXY+l5xEIu8NgxWRa/d+doBXN/f2nl8oPB8BB5hNh4tYi"
    "Jnr6IF+hlOS3c1y/sKRfLnS8sOV3MXSUioNzTRKrNJ7ZDDebyen/9f7zN7/89D/ecdJZvy9y69rEF0eOqu17VauU10eVAUU1akxX"
    "Xkb/ngjHSIwJM51ONcKg5eWO5c5U616OmCyBMV25KulwNzd3/F8Ks1gAjH7fuS5ap4xEOV3JDCfMSMRU0/fZvSj9DzcFsrOBqiJI"
    "EGhh1i4KZQH0wzGj/uLl33z+3q5EWBM2aDiWcY9dfffOjZsHb9zgVARhW7xyWw5JoOZIJDVVgYcx3GSqWSpjy+zo2FVhkxUuwC/I"
    "WPUHwiQZtlQ3uMZLnFyuUV1ykTgn9OmxXRy7G8agdv/vsiS0NZ3HYMXqZAehLkjgVO9cl14cqqJz5ZdCkEAnytvsSgEaVkV18Llb"
    "upTBqYNGsTapPVLVyNg8mhuS7C9D2b9x8tEzLD2Ymv6bKnswlVZJI0ievmLCNdABfLn+lpzZY2M/pt7xPmMdwRQdPAOLfeO7Dz2C"
    "OY6/fonW4tUY+gbTPv+L8cIYF8woX3bphuYE1CW0PbW4+x/DI8/d+cOrn176zwR6gQMqhiTYEZJPer1Z7ilnyT3lv4PcIyUU7nh8"
    "fE54epbF6VnWT8/ymNOzqY5IPEaLoI2ScIQaqCqHLe7IRy5VO4seRoyGwCljjEBp2cg5dfDvTBnGsFKkkN90Bd3VcruN0QOGIisv"
    "hkMM1mHJKje9MLJiXJLJbNcRWT7Y1hvrOb27CL+nC5mR8hIVeK1QI3/it7xNgQAsAkK0H1zN9l13lwqYBb1xrkaR+E7P7SGelyzR"
    "Xrcd+aU+M2fb4jOob8uzK85Jt1fC+uYqDBv0uxDtZFQV/GSzmbf+kRzSuULX6y4T6DzWmVqx7BW2jZ91T5yl+mxdD2ueN9FK3hNm"
    "8ZPT05Vy/iRF/yajtuO8LVpPfAfnLelMGi7k2B+u4rib7pm8V1j9HltC+154Ct6cl8VsQCmcmsrDKU15HJvfkR8WcUOgjcopu6cx"
    "YMWpuJ0K0Z9TdTd9Uea8htXd+T0d/KjUUVG0WmAyYcg8MP+qmuSqsQT2lOsSZL0RytNzN6P8kg1TDquj190WCuxD7omHsPI25mtZ"
    "09MPtvPYhkPXQF1dC+Hl9AX6bM/X3BoGgoB8BvMr3nCWYnNgY2ml1x9CtLmTkk4fc1c92YzNRsb5s+gSyj9mb2+fRbTO/GMOdMo5"
    "W6jjZ5tP6odsLLczBTf4/+HZWzC/HYH147U6EdXVDotLTugX6yodYWB2AqnsLL4XFmGl0A3CKP94ZMcd4xc+xOvQ9NzH5pvAbeFD"
    "01MVajz3xBn4l3tvLr/frjTXq14337RtdFDS6mc1AI+vt7FYvbptMXlbq2KjmRPePwUXRYT39LQcMrydiglQHfiHaOC94kNOj9AX"
    "eoVe84Q7W3pIFbfoVdTFc6FYU7voNZfr/+RJxrnidNdX5W1YjcnMVCgtSYeE5dSwBtljTr1bxMpRA7UvWm7Pz9dsZ8NtyXHUfS0a"
    "uyU/LrqbbLMKEcwlv0F2qk27OOv040eX3BNLKqZbPtlI/C7mUf687na0n6fyFtEGKkpLNqJ9w37CtT2FqhVQU6COpqmKveUVY3JZ"
    "QpoVc2DHl+t42dg6qAgjMUxPN6I8UXadaQN4FZAWvGl2fhX6uJbzBskw5UPyn0kC0FYTHsXhNr44dCJI1KMm95KU29KR4azDw+8b"
    "jnXMcjZHRnbDkdgJMRoUJmgD2PJmiWtNYrg6nIH/4YVBhvlWGgUXoelFNAomc4QzRpPrVoRbdfVUx8RnNw2TWeJof5L212UMwXfa"
    "RvtcYOTzD54b0nhjTO2BWnNU+mgyTdMn++LROFvz+OAwqGm52qoYBUbNZsabkCRsRqwpHcTQV77RzF90KEkv01TMob+ikJBEWnEO"
    "0UMqbXiYLopqRRhtxc5ouPjaz4TeiFTwW8LeIA3z0o1UYDGPZ3Z4tEqzWe50vezSSEOXt+uVw0pjqD2df02XCqIZ+J4s8M0IigYY"
    "ovS3307PxME7b9z53duWgwWXTwWtDlY/K3LaqwxrXP2eidSEV9wEOraKptYjtKSfbJX9ZM6ppKdN/iggRTQPTBLB968/+FHus9vP"
    "so824cH9Yuc3n791XUQTctwWu2bjdHcR8rlqxnzeLajV6jk8rvUQOjq/jVlqh3kr4NuWMiLpYk7AxYq/PNIWdWox2anFzE4tDu+U"
    "Kl0mOjWOZFebXn3UKZIaQjJYMkcVieOa3uxazEwCGt9WXaSkJSoY32Vrwo+aclndZXNtPM2Mab7LhkTF5Higd17/3Yi0/aBTrvgg"
    "9ha+moXMlW5ddlMv8ZyBeJ9s/V8c5DynvUoQkhkW44vh9IkaIAHVG5ZZayeuDW3d1RSwMGcZOwl5+csf3vnvHQOtLNPB6+sOWUud"
    "AFmAeO8LlDRZV08g3kvQNCMkdQ0hL4Jmt7jukBz2bcoMa5d7+CEckUZEd1M8s6Pku1RiWcLA34k/oCkEtrcmwpZGAo4QHCPXZMOP"
    "CEErNASJOGEdPdqrWCj3w2++JvpnkFBqNL2GlcakT93VHnbOra7DVbHvhi5hr21kXuEIZO6YgQyfzrswiwsOzc+iqYzvwxdMEiOh"
    "30f4CiYWRHYV6etZ1cPQqOdZM7w2MpJsk0BVlhzWXGCSir5z+uSTS8XAefR0seKAKvEtUFpBEipeHACTR/1CPvu9JpyClSCWJFQc"
    "3y9+Q+jSCNNu7AuSDWJY78tPG3hql1/EWhIYi542oOvvFG/JSmJNDVx7O4InCXC1T0ShuCG1hETRikx8OJlHp+xgm708zKCnzWCb"
    "ZzDCGQz1GWwObBUzteYErlcInTLaRcggAwo4rK/SXt0T9aSKWc26J6mm1jLMIKQ78rOyBz20hQRCY5yvkRWkV+DO2tvbNTKGyAvO"
    "Vhm6v7zi9HzKBcTQrh4FjMHvRboLdkiNbBiqkQI8wzaDuj1I9aUOui3dr3VDPQmvkU/G9qhCoVAzLSj5utOLjYcnXW6wbjtnxcde"
    "DA7h509Sh89SHeLt7bANF+B9zllSlzHFElX0RD878XTJxlF5j2KD+FS4vU1TMeW6oW1jepqPdiXZp4aYERvNgS3NhlJ3ouJJIKSW"
    "MZZ6ISp0j/bwX1tBbTQqiMmwSQu7BJ1gBg2rL/vEtZXJPHVizlmUtoa+biltTD68Hi2ALC6tLnA/TzpnoZ80fWiNO8ssAZVsOQ19"
    "rFvsMn00TF9XRm5wteuBzkx3iyaAIWL2WxSgmK9rRGfyPS4yLSpZHVz/oXQcvoKm31Qbw5yALPmriIaZOlrNaJnEYtqKpgJp6qrP"
    "L/JYNIPjVHt6ehFmwnYegvGW45254LknFrzk/n3MPYvdw/uoRjbe5aM7oNtAFkF7UL1vwRMz2/RiInLWPXdDUvkTbVfv8zyVBB83"
    "3XC/5UA3LDRWW85j+Ak7ANx73YMv3eioNYO1ryNbnOh0Y/GkjjNgAhAks22nzoqD4Ew+L9ZkCv4vF6pkBqRLM1R0muKln2jbMxdS"
    "6MG7R7bOlqTyXtR03gH6fAzdudkFopyidbDhB5jK00G/XcTZ3crzNKLf/gwWHbG2t+MrOSqxDd87IeU5n+Z4hTzMudZkRkZvVt5h"
    "w+tZ2dkMAixgZBK6Ln080dZD1gjNe8FzTrdjNO9HMnPZTrdHxp7SPov3QO6vOx/lUCQ6A63jRoAXYB8T9LmgMKTsEW13ELsjBpvQ"
    "VBto8aFJEphl8LWmxorCbnGfH4oV8NDZQsGrSL3FYHRvVIB3lJG2eaQDkgRZkUWbXgN1kOK65+gtU0FHaJy2BBJN0+95Fn3vVCLG"
    "vJKjQ9uh/lYyiKIxkW9mdtMldgNMVB4VA+au0sly0j2h7+L8RZDQQhDH6lhvQXGHk8wc7MFAnLFwOi5KxrROlup2FY8IwS3E+RqP"
    "AE3SI+9qo9kHq9PV0e1QM27wuhlBlUvuohYCvYjQAeFmfrGdBvKZRIWgTZrUHgq9ymASU3SvMZHF+strDJLPQc/Q/2HrKoS8Bm1U"
    "7tUOwBhifZan2hOkoFVqRp2NCxxxoDCN0za8I1tLpdjgqXiwdkUx4wtJK+aiM7VkZ/JBaFOYZQ17psyp666vjoAmaVrm1MLdI3Eg"
    "u5MUPhRGkzRXYVFZXT/fSV6vjk4oqXTqXzqIuSqryZZ0D3ldHP/rLLePy/lqB/1mjvb7GKwqkaIxkuCNxPpT+XVcgDoilxlcMHNC"
    "2qHptqCYast5spmnBuw4e6d4MXO8Fycf79ihHvzyrcOM8+JoRCNzaC1kkl0Cln6Dglkuf3rpfRooOR1b5Q0MSgDBMPKbts11VrXB"
    "twxQ3mELSha1dFy/Ocg3finKvSa296WbwgJHSAi4cCuTWzdQb5NdbExs6/Clo3mKP32nhJ6+/R+/ZVhoxW3fUbctlnRmeDOp2ifs"
    "DCnF/CIo5iEo5nXEjN2SqZJrqXgUB+PugbpSRxroGZbjuwvdfBvjJ6JCNSz3PVArpqaiwtKZBYwqgj9kRYMT04OzWV4iLy3ig3HE"
    "gotB9+jYrnRKKrWn457AC8sdeG5FLPiiwoboCP85Al+quwZOh2w31G/616m4Pp3WSBKTAI8/iFJPymCpDMiKFLrwLJoyqOQp4+HS"
    "i6ph0DnMi0IDUCrbUjv8ZYcclbkvTIOzellYppeNevnIN04RWpHXxdNXysbT0z4GrghDujzHMudaS50QdJvqVzm7Z+LqEtBImQto"
    "qmvtBt/ZLh7nU6MK5Lrk1Nwz+SZnpOY3Ksv+CpK0PZMXIyhdYAhX8XWgFw3gX56AWynohcBY6Ul0r5yPxLPCIX9k65wX/2Tc3GmK"
    "O7X8LXol/jTYf/2n6l4Cf5UNH7yxA+vGsEWyeXGD1jzr1/IJ6QrH1vmX+M5aE7dfTYXqXfgHrgZYzF2YoetiR57Jd5ZnV+w40u8S"
    "Z+vO5KtasRAMfhLx0IRfc+Ef0HCIMcU3ElosC08XdDzLVOxbYCCmVsox4qkE/Uw9EmnRcMx5SCtocziI1lo+SsTNOUb7aRkKfQRh"
    "IrAQdjDbBXxHzizKP5ZwmiCsnEXQOFHCmGF2zJa2BkuaFkKU6f2q+Fa3iswvh1oaWICtKZkTFuxJWDaHGuF3aAaADur/naT63zG1"
    "/05a+X/Qy2sNZqj/3+yQpuiPFCJahsRKGHT65I3TBjQvjaDlUXAp9YSOwHc+0XTiE9A4GysEV+0JtKuH2lHwmO/181urQNVrCG1Q"
    "DgnVhCM+4gsq3qrtqphJEM/OND38+MDmQ9W8cDbZRtKbQirwNDRd1PPgkPUcxBuAVh7AiCxgpqcInuvbBJkFh/PQF1U8WlKMelxT"
    "Z3Oz5GMYLAF4HaXs167HUF9H544Xw0KIAFfwkQ70IS+dD/i2E36pLaYISxHNuCTDVTy/mRd3HPXtIkZy1aKvh/RnZu44EJX+1FHt"
    "KXXPUX7I1pZkDf0I6OvzYl9fW/r6IiXBhG42fBqNx4BS295O4hqX3VFIaPcjfp+MueMQtRh2LQrq9aaXJxDxsu1Mlc2WQQoZuoLV"
    "CVawpq1glePzWsB/KzzLjrakVX1J7aK8oyON4/N+RhAvk5oysSgoyxyGCw4jgg1BBBVetPth027wUteO4pcOIjznWyr6F95Bxyvi"
    "bGb1oUdAuEYvWhkz3PNBd+0Q+4zbrgdRQI3bqcYxRPkRYGHQssztV8uM9Pd193jWI4tk3sl+ZCYBqGdQzdHjg/k0pl84FGN8KMQf"
    "J5rNKtrks3B7Ox+4oQf97UYn236LXP8ghrU8cVi6cCgglB7yZbcGV2qFShQ2gemj1yoF2U0KDHAZoqnyajdfK1S9ZlR+0j6RvPQE"
    "nAcjNgjsa2OSXNmSU0udIdC5arpz5WYkPrW8qCw+ipjnk2EY9LFdkB7Ni99GKrSyBkfhO46sz+Qw4oPzj3JXbW+vFVpBlbK2ahk2"
    "7nxNHoXxy0tH54pzdoxm7mfAmPMcAB9wtjpAvX7PK07NDjBNJH1vv+ERZp526xzcyrmDGfeHBK1ISQwjgNSh2wyLXmWYxS0/G0Bd"
    "9RQ7l3mH7J/qUuZdWb3KvFHr2ECL2ffVbgg0jl12g1JyYzKnmocfuO8PbOa3kOcU/X/Ol0vlYcyq0Gcwy+PF+2ZnbWfVa5R7PgIU"
    "dFsBVq8bxCs6PPIKzhoRLkKfkjDEY+2M7Z6OdkU8SWH3YU1vZXK89bePr/71Bz+iYh0fp0Ihm5idke1JQSfLgjUyHAOZrIx6EZ81"
    "64U83vCoQ4lfX5ieD/ubXOS4MhlR5BU3iD3xvuGJr6Ev1vT2TQJcy0eCFH+Bx6MRJG339snuLW3NvrArIz7KpVt3dm/vX3spgVLL"
    "Q6pptNZxa9PT7EIfdjyKjBY6lrQzDfiDL4IE4MxD5sSU+WggKFMzbHXE4UxyT03/MvfVbKrMDiAjr5Qc58gI7wos7/R0GToJf9gA"
    "oHuMyxQnXlkxTLaTSN1VctbwwHV6m5T66XhVJv1fvpWi/heHUv8o4k9bufqYhkXpV2FPwdR6SRNXCr93OXJCA7GXU7OGnOGd8SIc"
    "ne0d/WxvqbN9g8/2BdZO862ZGaCUWPJBMcoC6a9eR5cLnp2b/EDL1WirhVyhhfpb/CTzYP3hgbPo9jlFqZ8+8qBLzujnnSnqJcIH"
    "WZQteWP/j+9pYKm7cXS3LMqmRwhZzv3efSoFKOhBJ3ArPRqW292aF9qFqOG1893ALjBOUcM9AS/icpoYBYXJnDKjFFvGfM5izppp"
    "GFBGMTPvZByOOBheFGfDdobd0fSo5NHmsDvQbLcoTtdO9mGXfNHQm/R3DbmJXzcYUPZVigppTba3JcJUuHEsCsubXUvMJyj6ISjy"
    "dM2WU0sPIodZpqdX4tN4krpeMjIaD0FPBMKjkcxyWkBKfqeJMg9t9XDjrIpyVJkSHJobx0p3tJI7yIU7UpYjwxtm86zQebThnshv"
    "4bXiBpy/zeJGAVkgCLvzHSM+3rXgnUG+RSVpM7rcNrrM3Tw9tJt9b3XNj9h4GYRY3OVe9Jxb/bbXLCMSzyNlROmYZDxY4gOZCW/E"
    "TKmFByQSlmIYveHuwHAj6ZMwnHJ+G8PeD1lewJKh7RjXO4YtUDi6xkjINfRnSta+mcARJtARk83EuHI/pv92Yxvy5RehF59eeoHs"
    "6tcVfkR2uot+zlTLQ4EtO831LkdCZ8EqimKNwjsZoccjjbGXsQAN8iQZBegeDTrFueOD8a5JRDsgIIRb+99/V0M74EILYi5wThG+"
    "4ZdowL50g4qO/1zh9iF66qU9s7LtupEUEXGoTcdpxYE2VtPPpIPhIENigAJI/fhXnVrQjpZAe4CRFr4yMM76Bz3gWug9Ar5IHiMj"
    "fkBc091SbJTmyB2y3VIqOjzdhk8J473lPAFNkPHemeoUvA2Y/+4ICajcWvVCw1Gxs5MZW4xoUJijfy0RYYyVJmwF2Tovtf/vtfPo"
    "PfPToyEnG8jaZypIiu6THoh8jC9aRWkuX0nkCYNwCtxI2m99OWU1t1Ja9fIVR17JBCW9a8ZBCTGTFG/ZaEyE3RhuRKZDzPS7ZT5h"
    "xqYH6VAyHpfhqq2q3TjqoPsum7IXunkNkJv9TtVE5HtWx3Rs/lppuUYxnzVOrXYwhri7IlWkB4IA5IC2rXla7ARFI2LCkKwQzDks"
    "zg0mw7P+H+Bz4jkTjDqr0s0GyzJl1EZ8iTIsr06SRevXx55SljwIzLrsV24nEXCvPCNghq68MrLqTHfdQLb/ztIDKcwZAkTV2pOZ"
    "jZfPfQthV5AbM1zHj2O8lxvx2UScWGS+yBqVMsAeQ/HhdGMGnwLifVVULR4+YwlM/VEEQrg3CgK1rChloTdkzhljl2YEp/cZWRD7"
    "ZZFBQO5sktx3ss/cjJchWXqqECKaGCtrQ4mUJDhac32ppVxwqHe2J34npXnGbzUrUfNbs8r6Cu5KSdcJFXaRdk6cyYlfHZbwxKWT"
    "emn7R+hLEvw7rGqQI3iuzC8U1julPP4LUj/WhXVBKl8obDTC6Wn6UyivYtS6bRe96WlNf6iIKrJbeOAUPT6F6fjAGBf8O0gqEqob"
    "i6hyg4SKr40TOvAbnXMpXEw/BsT0hyJhZpwniYkcUfpl7tDRZhNWaNPAm25pguazHKLmF3yyr/gof/zt49csstoAkemkMQGfDqs6"
    "UvWtXx386m0jDU7m5AeOYbEJc+SuHMkcmsf14Twh1gIxn46RhCQXBPt/FXrkWP9EJhm/0G8EU65LJCoQaCWAICrkOFC4Ix0GG0NR"
    "S0JdgENulTQaD/FYumhuQeN+uN62MtDcEUUnRUIapmoMpkr1etdALEITfiVotfzIKolq9VmSm8FbMTa7OIKvGWttOaF7GrpdaAf9"
    "vI11fY9CN2YRB/7EXOkJ0b1jylozh3jJM9Yxqvf7/w9Kjwgx0xMU7WkU7f0PUnT7y1O0l6Boz6TotqTopsRTb8YkqljaUg+U9yIo"
    "5sjXYPBlE64oK5AJ79LCATAktyWXGusme2FY0p9GbCwdYY6SXz+79RwDLxb12CZYzzkHRwV/oBmg9J5f9YJiu0B/nR7ia+E3aHN7"
    "G36twQf8XlMX5B30AS+V8RagWL+91kU0Q/zrVAIfo+sCvzQHvyFkAcZVwR+nHVT43GwXxEeGzW7Dhgu6a3g/2ioSmFindEysBTJI"
    "OW3WgFIGV0vYTL2x9Xw3sJ0JUkyjxiQVczaMVVCWR+IIskCWsMB4bOSRmWCin14B5xQ9KPg3EbC63kypCIiFppMNPTVU1VaPdgpN"
    "XSjDr8g1CbpMqrG89RnVbIDWxVa3LtXQosZTmwiLhRujg2IBlcHAqBFUPLe3p2CcCGSOmHHwkZA+23XQS+XwhQIDOsvUAujRlSY5"
    "59GUiSG8FbesarzygDozLdK7nVnUZMva882SVMTPUyeK8quWvfkkRdKhGjwB40xQxnDGGTXGhkWbwvqbhl1FSQF7ysSim1K64wht"
    "2SSlbGuF5Fwr90QJVEKwr7gyFTXg+Llwc8usWgAyIZumpUzY1mXCNsuEDqbBkq+bCUEGncDX0OtyfB03uxiqWgQddCZ0lAH/K4la"
    "BMYpJtQ7ZcYCVekXH8Xll0yhO8Lx6Usor68G1U39upx8oXkre26Kmp0NdyiJOotuHn9MIKozBtyc1OThUpHb0m5y+u4ii0dJko5C"
    "Y+1kQWErg1ijakwIol7h7CDF74YhmkgUk6lWgjDYyt2AWWkkEExKYnqqHmLYiBkqiovosxJzthZD1WiUSd0dFg+4vDhRXRLDYnAm"
    "vxjPsY1Sygq5SfsGSVQz6CErWdHv5CpHrRlQm+JXwBfd3pMawbo+BGVcHDHmKMOUsQSaXa0I2pWzYYZJYzyw8phyXR4BhPqj5zh8"
    "wNCAjVR/tBHwPXeeuYqGj9gE8dlf/nv/V/+lmxrufLIHUvDB868T1IAoBCRe9YPv7+/9Ce3Kl58ZWhFIN95pQc3WILUQJrXen6bW"
    "4d7ksGXkbGksgeXzd16mWjH/I0wOqLqLBy78XVGsztwGaS7XQC7XGMrlkkxOAFJwa/zVyRQsNK/93coWY0QLkhqE0OAEpRGnbUaB"
    "1W6i0E648TBM76OB5unYoOix4v3HgV2JWjuGe41cl5ovLKOkSKI0jWUkOezeBlJgZN+E14jFOSdfw6iNDMxNaU3HWEaOOBMkYItc"
    "f57EsM1R1E6LA6LlOZLdOb7V8GMkkmsSXgynw81maVgj6RtF1Ig89UPnIO2JU875zN0xdm+AhhBBP+U748pFlnMfViJ6UEpvTjTk"
    "/E/WIrL2r74bd5sCehhrTEtEmZwYhxg9c2RWjmcTpN6ylMWMyCFNkAnKmrmMrQujZoakhfMgYhczZG3kIOtVr4geZOYnK4OhlbLj"
    "EpLVksFiVaVXIQ6ZLliLNN4R5g8QMssjBdBKnJDniBEkIdQUO05Ywt9MVNAVh9blF6l7L3x66TWU4nYuSfAnUdkus5/SxzmkHNg4"
    "EUdMeqac06Elpt/dTkLe0QUZdCxeZ+MHTAN9fS6zRjCPRPSYJdRxybHtIPJM1M/hxzzmwTpY4i2HRQoMUpAHtzr2MUMwcezH2ZWx"
    "Qe5Mz90K1rCObny+iwxEB2WQcgWmzCA7+WuXuq9LCpaDimPR+uyTv9z5yftkKEN7haUqUcFDayBDKxPQvDIVnDRNBbDrTGtAwiJI"
    "lb8crPSIb5wh8wr8i61T+kSwNsMpVdh9/AH6Ok5/JHdViHggUclq12E7BWuT1RpvVIeY4aIYYzzexVHpwpGtcEAl6W+Kso07l45s"
    "ReJSvBJZ4U9Zbn0W5mLxDyFBihckM9DLyb0m33z5xRGcQdtx+NgF3atiBgks67pUvun4Y2MFMoA4ct2jXNNROyZ7y3hhBWurdaNR"
    "TteamVcEclk3onKMKMaM8O/rwjvdyxGOhANda5brGq87xDgCoxQh59RZk3efX21PWuoMuVKcM7xDO59eiXEw5hqqWr34gvO4T+5u"
    "gFTi7u6HaP115yfWxMMzd8IHKOvHFb4Tms+1uErFsEmB3WaEy+ixGinn2iM6Q8ovFDBex5AW2+RBRD6k1HjPsP6NivsZG+LzY00G"
    "2hOull+/e/Cr3w2N1/EU/vzXBEpOG4Quo4htXC+x6eZDVS8xVJwSvyfZZII6KPU06spYm3ahU6HEcP7apNMJKwjKJkuIZaQfH1jP"
    "UP5I4EUov4eiFGMY28m7k0TlLFNYzhsfMBuF4zEfakUdQ1n4cUXYP522ubezQ0GwTUEyfOrzU3zs8wGK4izH9iRM3qvmOYbPdaXN"
    "O3LXCmczjjW2LVf90B5v4aQGGep0kuia5uohNysDAxthaUXdrmTABmLYttxstNN2+Q13fnJ7/8rziZgJIIPZ2fNqZxYuduo5VeRo"
    "//tX+CEuZyORzAREqBbrRxYLyeOEMHn5mVg+VPGSHlcp+f/AlCZpVvRMDwsLXQocFMgJrE/ghRg3gT6VooIfea2ukWbRWpuenqoV"
    "qvRvJy59QHYxpvqmwkDMh4KHiaS7mhbTDk1Rxt68MIHadPgivh5FITcJeKQjakDAq2wtqo0p/QHew64rNCaXy+bWSMqWN2BIghSt"
    "tbK5HTelfeITI3UsqrFQo5q6FLWN3EZtXKxbI67aAy4DlpRrQEYi6VWeD9cJ0meXDMy6NHWV22LDLyc1EurafV+ZnR2l1uqDnnOq"
    "wAMGTlmbFDlyntqajWuDtNtReIpwR80PW3lzWDU1oHdeVrV/Pt25/A/DZTrcN7kjWwyVeMbI5x9gOab9Z5794tV39FrgGjDDzYM/"
    "XNWrO3FZpAu2PX5ZW+llXW9PtLBdtIrCyl6IRZp4tEISPrLVEhH01ayBpRaphYvUGrtImEopwSVB4/NacFpFnrntgjU+ZekLQ+Pa"
    "hEiadfsU3T8/IS/6Umxogv5qdIcbXXZ/ggwtUJGwJEAHawIj0mEIgnutgKAEdpbtFU0onVJZvaEYwEdOYmLDQad0YTTJCoLPix0i"
    "2mEepq203A8anY4nYdj+cj9xp2Qj44wQF3Q/rOl7rTTWGENQdhVEBdm67aC5p6kwWzXyqPBC2GqJRtmvaqs5vDRkvstY9kUgmx1q"
    "bieb1QtDjVRy4DRk3AsT+XSGyBs8gGq8w2gK9c7pMiBWxxMs/H3Whj//4LnP0c3BtQAxLp7FCzSgKJsXSKp/w9r1SYFGtmV6WLhK"
    "m0BqVpjIEsT8E90KozCsBKuXwuF6GYRD5I0LhfXuaqEa+j2v6+ZTHJJ/gAUQtwju5dnmg8srzmngT6aPIfHKB7v4WMyP22l+vBoG"
    "/a5XwqLXrjVzxoMHKJIQXkTX2vTHkVcwYpKuUSIlXyWpBC7SX3Gt6yl/sOh/G7lv2+yvMrIl+r0gggpT+WeT2rNTnTC6ClOnjRAU"
    "EJ4VXCBHn2NBKyDRzE1P8z0wo/ody7MrXC/cEdnlrgU/WrH1UA3pdLJCHIup9BCGcuBjmeYueh1oDxTiyVb+9G0CCEO0xwKYqhpi"
    "sPZ83+fcl6DrFUOn71cpeWs8ony1Wc+FG/BvxgHVOG4osBMFCGtWpU7iTV63YtpEZbAhBaFl6cxY5Dw7pUImhlDgRlZc9p5uUNND"
    "/ZRgxbHYZFLF3JuhvtCRpTyqoY6Iu9w2SaykviPPa8ZHQFaab5UU7zJKiPwXwyjDqPu4HzWAnxM98hltH6YikZkqAIQumhoZDN4k"
    "3jymZpORXlJAU71D4XcUzvEceRuahVroeWSlaha8i14lGo/lGSfU7z2z//33aflw4aQ/ONsJLJWWFCekt1qIzRA1ijx2EkF9tA+C"
    "3C8axwI4uqcLGZnjg4Q1cjXybcVs2jEXaussSoqpPvI73xRTNQaltnUKSI66xkqwI15sDw97ADlRHb0dUJQQrN+6v7ORmzWqidBe"
    "fouq0X6Q2tTZ6U/K5EM7/cfIni8/Awftweu/O3j5QzhozcSzkWFNE9FrvMBj5ol7YN1l4zH1NNPU04F7qz7VLLXnm2J7qjNDLIdY"
    "4SaucHNoeEAyz4DtIey/XiHkLG59KK+prIcmr+HjepIdlWAB8lHbqBb1Qu6zW7DctzIMHzFDbosh2yMRNQ1zKD9SEhskEUw5cYCX"
    "fDzBSTm66n8mkIr2MUnxkmcqJ6NPgCyJYCq+H8OmxP2iBRFWIhvx0sFUY2KpmmhILI1i9fA7hvsektnHSTDoZSFxHK2f6suwoKsp"
    "6tAIR4wKvmrqwVfNwwRf8Zgtq4iniBGFNe7JczjVLdtgmAQEOwLL1dC78fxKpIbtMguetAnaSHsGVx2eNj2yeGEQRBOZDsbZeJkS"
    "cR7RUxl/E45D6NvBsz/97NavLshjh+W5Ucl3mJp36dPLuwwEaQ2tpaVS8eOiil8bjADdUQkG2oRqcNwJTqk9qMoYoh9IK1RPudGJ"
    "tMGdS+ncv3jgMi8vgTkTkiaRGT3itzpBqKJHIt0AJmRYBzvdZb6NRaGMI0xUSE91acyhZub6TcXLmoWV0yRwA7pnZf5eDKVpjkHS"
    "9884D52SMzUZXMVP6K45GbGw6blbIQaXWVRuB4QoOO0wV3Y+oUNWCdVRalFrhSXGYNzenjJLfWnapVkUaVepHSOqIMUqpwR1JGdP"
    "6OJRgbV9QLXDCJN23Sp5xajEk1RcY8jkNQWZvL0teoUapV8lG+qmhznDGRYCuNqFIXZL5DIgrT20bSpFQNeHixmys9A0TKIbOpuU"
    "0GM4IMJShi4lvYtHjeBmy4r1XjjNOlmK77lUafTlthMlsz+c5dBpGhe5Z9kF0pvyVyfChwfOstB8HR7YCp6dSrWmnmUozT6VaA8w"
    "yYAfw/z7EXo0ZjcoYZCbqLptUW2cqKtKxKRvTqynFbse3hsefSdRqtJReEKsJLrhfjoslBWZQJS7gL8CAVHZ8FK4va2u4EqRv6QK"
    "0ilKx9DNzz554+Dqj3RlBnP5qgTaAzsewZyXQDsxXsybW8RPDthezsRWw6HXEoF9wy0P5cNZHAwJzUI0zK8en+1sOHOzs/9kW4Ox"
    "FolRSe0x4xxthxDJhEkI+VQgGMe2Kfd94qUw67pvaVieNztZRua+1WFBjmeBiBiVKP1E/fCJgBCGVYcAXqjL/DLWl2NdBYkoybdK"
    "eAPVYeG8smMopleHxc9WEXpYUyqqsg6hg7/YpnaR6nRiqbDro7dMcmAcxFxewrAw7pC+qYyhNoePVLxz9EDNUY4IEKZRF+9avAum"
    "pwPQMzpUS95K1UPYG1NCMLvS4N6d139HMPY3dPK2Ri2NySMz6i7r9ZbFOuAIuZjy2aCy3kW7Jc9e26zI/NmfrxVzs3PHzx/89A8g"
    "o8vCMRlVmPUVjFIrGKNnw89bVRM8e3q6kqjInOQfiTLL/+epp3LHcsXcP+dKOSv39dyJ3DYGcmrOAwr127n8f+5ezr/nonVZFz0R"
    "pO/nVBUHqObGJBKnWLhvBLF8XNG1HzqCEnKekhweSkkOSeS+oSjyS3VRYkJBv6vPCrGx484axUxUISbstEDy0zOSESgnp65rMZA9"
    "3+sjXTDWd9Iug61VG165OpF2FlnD7EAyyNiaLOOPgBdP02Gr7KR6YfYz3YoBt/hgZ2QW3iHKrAuYWewAl9VjDLa49bosT5bv6zAX"
    "2nzhc2zWGZvnW+v2y53UfY8ywgbIbiBglzwlZhP+vhdXJSlaRy07Hf73qE55a06bBEUEGDjLXhs2h5wJsfxJNC5lOQm2pj2uUouh"
    "Q6iYyKbqXgnpW4pGWOfVtNTiOf+vylOaLd6wpm46Ugz4xmtf7Lx25813h5VmRker2uBs2ESwnf8e4lTeyy7ljEeIwOfhms7SLSvR"
    "bJKvyP46pMy0NBqbsGKGyCYtLHrQqIiy1tLehN1aTM2V2/u//unBzi5FX2KZc56OR4K+Fz4C53HEQ6RC7hR3emmPk8el5wgLvLOV"
    "WwL4HZpMstPR45CxlI7mNFGTiQRqmO/GAWQg2TSnp5vxsY/FvDNI5ioBXCSnC8dRZC87H/LpX8PlUIhUR+dWCHzfiFSruyem6hSj"
    "Vi+01hhRWGaJi0qvM1jTE4M1MU+8kvpdgWnA10JL3lfNeFFdVOwTtWgs+dI4p3xrMB+oELg6wpIv1wsYxvrZ7ZetFTdvfKVQ0rlB"
    "XHm3XQi62H7fb1sl68xGpxmEcCAU5fVWuQLXz/pttJcW9cwaToFoufWKWCQnkqhtGy6sD4ZiJCHeaEAsdqibN91qyaoEnU0cXnGj"
    "tNDNb3DhBTKXW1h4xhJwls4iPBdg6GDQoeB4c6q8NtmDbDSj9OHOltcK8O1OI3Nmy7ZRnjds5+uFDixIx7addfWEKMeb31orfneD"
    "7oC1B4Is1ge22cB5/HkNGlgTsS/0Fh+rMWa9XlvFUwkEFmfJfbx0vp6P7DTGyghFJ1PAmqxcYiVcb61OUFcPPdOydroTampYaNhU"
    "KGSbZwVIoQfrvRnlm3ahB99aI0KiK11vKESawEge4ZntCaRnE2H7XCgJtDU0LU0vCnkmX+cTFLpfvAddTfn267ZoXRe2G3PmTf5o"
    "83i5Ehl+aLGdSO87DDjgpp6szdiAG6ZElKSAZQWUbuV0zmmNUF2fyJfNUplZ7VpcF4qdmjnLOeflK4xDimArlTW06dEHqkU1qiFR"
    "uYqa0J/Jbq0t6VHPVTekDK26leWoxxxr//Wf4tFD3TbfhuWs4oRDDlweV1dSsED91X995fmcXjry2J23P9rfe23/z9//9NJboo6k"
    "A1tKrSBXBWo6ahUfl78cqTtbZ4vRKKJK0pR61uvJZ9tcGgt1Eb1i1tTj8ciUEE8i+zn43dJC+LTzOBbtjmx1BnE9LcOEfzF9umRv"
    "OVSsESYGZTrRUjaAHnXr/2XvXdvcqK780ffzKdQF6UeVLsnq9hU1so7T2IMn0DjT5MI0+uNqqSQVLVWJUkktRa3z2CZhDJgQCJA/"
    "gRmGhAQCCWQmmQwBEr4Lptv4Vb7CWWvtS+1dF0ltmJm8ODOhLZV27ftee11/awMmW7dxbPahIbKZMdxpfEbKzxduXvsT8ZR8GTR3"
    "CQaijeWin4HNei4Z6oa4DhnEAvvCoEHibdEIHtpBTw643MLAddCxUrt0hturtUIL/nCiuw2Pa+YMj5vIRtlShRiCyBoCWWqZM03c"
    "OEWYN0oL9QpV4/hSKAFpU6lSiuovFq6QahX64Nbzfzl4/R2xh97L9NVgzt/A81LQKUszJ7j0Nw6e/+CLJ/8MvDDXSFrET0TLx+LM"
    "4+w19xnVIq3wbYa2Ze0tgpIMAnnaTdw+nmLHZxsD2Re+MdBjRYoW/a7d6czTB3PdLQzlKVR0wL568jrMTjEchZKTh44rFzVwJMD7"
    "ZYd7YXcKWCS2VB/DGsDeYa8DUbyCPHWONXSdC0nXXrz1+tVbL/+SEUT1Yk1tZiGWpTsX9ug8smtm9rUEXa4C0YZ/GDxtjZLeclY7"
    "M01rdycXS/uI982nb8J84/bTXO5uwM1w89rzTAIVAuNPI9dauBtaLIKG5dmdMfvxVrdJokqPqv0ZLgdVOzfjpdD1BU68PaWtVhEV"
    "l/v7s6VXNa7quuJMoIhWU5ZXOAwGXj07I3Ryhm+//F909lA6vX3lJdraMOy3lSmVh/NVoYATHNbmV3c8NUIx40CyHQHrz0OiGYzA"
    "tae/+Od3D559GVcqfp1I68l7WtR0zCdztvuRM4yl9N0UYgjX/gwrLYZRWd3xtvnH2gxIba3ueq7hzA/3bDHxAHo5VCEC8ZpCedLf"
    "BXES/sgHCB1Ypb/yEa59lf6WDY4CI/shyiDApiI2qqgpw+2S3PWp6IaRbMmwihlcpk7z9fStXxVgNTAZrTQmI377/K/zHEe6/VvR"
    "7Q9n222IaFKr/RUevEhZlWPaqlmn79mXb730MbntvEv6/Q/g88ZDF+EvO4C3r1xF8gwFFE3hrR+8efDMnwzRdX5yWCN2GxjHEER+"
    "vB9MLkdQApr+nY4xPkQUf7749AXU0RHLYhzloMvOxMKm1aMP60RKCKaPEQWPl8wFsCTg9OOVMsDEsIvBSIQpmOj5vcCa7AKJQGBb"
    "nmC+15mhDsByud3CPJGM1UPy2K3X3o8krgXhYYkFoCjwXN6wmnXxzTQYQ7AHJZ3H+jCintOY4fy319eYgquvH/7254wJS6xojJ5E"
    "+t6peun2B92uHYzZjswP5U7b34cueo/x1SyZZ2ERo90XA7UYMh7vnHUh8vO4WHmit30OON8abAaMd8f/1azvVPAZqf18tPzAt07j"
    "MXSr4tzJZcwaHT01p7nPnnoxxx6KVNLsE39B/pCCFbwoUoPfy/kgrVwEys8FyYvbazXLsAPXLjDsHvZE1nURbgAtlO0iXQkzcR1U"
    "rDExC/AZTbT7++IBs3Q8xp/PTl5+HobOfFBRsloMshVmk6hyDgP1zxVDn7ulnhMUdrF6vkOk+AKWT2yUoyNlwEFeHAs0kgf0lgvH"
    "SzAshFOoReZR/bb40qyZqoyK+hu/HRT9FaE7PE6gDqzbwH2xeDnY048LPAduIRzEHLiTFK+O9tKkI5D09FZ2G8LMpOFgMsPqJFlH"
    "urd3W7/2SOBVqEzs91vvvH/7zX+N/85pEDL45zpuC8pRalwtauLmtf8kxNKPsitnarvDn/7y8NVrM7rwzB8Pf0i+rJtJDMBY2Ygj"
    "UfVYXqN4P0wSV0hppzrhOj9IYX81N0Bh5LHOxX9h+WsuEL9cvdAiZplxytZFeIjxPBsF/Pfe1TOl0hzo0wfzZC4yyPOtRSAHRnc3"
    "8Pfwm27fqdIno3xhefli1Wh3UE0DRTDHfMoRSHOe1y2rmKCxfGZl+HXdjQr6UzU+e+XDHLHOQGBM3q/ZWCI5ea6Ir76I89LdhUuE"
    "cdhczaceRHQYZMFy1986fOW3jC9lZ4xC3h+OqjCmTCejBDq/IyS7Dw5f/p1q21Qjdw1RHSG6tzjwg0hisQWzC2u76Mi4wEBI1MIc"
    "fevVj0DOjOH0rN28+tbnH/+SdFEaVinqrlDVdIPkUZABfwf9PfjLDTYNHPz0h78UoXvkMczc7FXmQZSXJY14Wg49MoEW1ECNxm51"
    "ZnRCaqD9AmiyLTWgoXWUgAbete/B0vRnvBTq7+iamfRBX5ihTwemtR8C4TeQd7iAvEPSlCrlR/VsXUBXODzZVdgUKw8EefzMUz9k"
    "0C016KYNV95Wz64TGN5eYPdUQsrMxkwq/w5q3OqwMfHv9nfgJqzxldusWxPia8rfYcI0nOlyVAr71+231CercJfiJ8b3mjF6ueEA"
    "1UJ6aZEIwy7enrh3ZwR3pN5o2bb+WPTdmuqRNSu4JEWpoWdaO742jXm0dBr5yZByGkQwes0uS0LupfhGh5VtRIzyQhuE18ASyQYw"
    "IUDD9WEn3H7j9we/+B0sOH9kIeJeSoIr7r6IoJImgfMNIyWGX2ggL8qfkeYCHyIvLR4OPNR/IBpfAWbJQDAbtYaDp5679dIbQpzH"
    "SH+prz546+141V/86uoXv/7VwVOvxqo/+PPPDz55/vMPnzv8vz9CHE2q9KFvAr29v7h26sSt32IewgQ7nmJOhRnVxS6qmAhtCDQW"
    "4c84VJaqCZIVKHEsHbId7bXHi/nrzvOWCdT4Hqg1BgN5YViBrRM4En8yHr5DFJtoA64CHCeWFwB1qqkJ8Cy+tjXL3unjjUM3whdX"
    "fsgjrlGHgu42lO0Rn72N+GwzF5O81WS1sK+Jg32OYEev33zyA7oCPxDmMmyAiuNmQk9dVMKobxz+6Je3/vgzVDh++kPYF1FZBZZy"
    "2BGHhry+RHYZp7vjNAxz7nbQE4ltP+xBHRw67eANmK+rTF9JmVZQPoJ/KOyKpybBHABCFOQL2wE2jjpUU5KNXBhuYyIdvMNJOj14"
    "65XbT74jNTnRyNa/TI8ztqyHF4Xi2ibmiE24UXWKNh00ohEG2o2oWzzY7feMiqAyUX/OFFJGOfG6GFX0onjCX5HSoMOdeTHNEEOd"
    "QSfql2aIlvpYPBKBUyaenxm3UXEqZwneF449AnXDP0VKy+HvGtiqvl+Wl5eoiPhlSfkF1w+/4xk0zGgDfn+YdywE8pMwfg4jxOSk"
    "04Fv3mP0nWsP5Pey8DQhAt/he3WbK/owyTqynwZX21r4ck1GxexVzgaCjrcrZ9tsfG02PhjQnnTD8Stunigx+nTBR6Kz6L8Fn5G0"
    "oouWrAqq3YuNXPHKmlVseTm/x3kRTnhgfsUTIDCIlcIr6lW24Xa6nEJKiBSDmOpPL2NCwsvyMoBnNjyr42vKRQCP6/C4CY+jPXb9"
    "n4FVhV+a08tZV93NJz82MLk2rFGT6+nt/f36/j4wdTQ/glkeRWPG0KOxNgVLbiO/ZwL3VBEreW9ltVQNmG5qz2pLPPdhB7fm3tSS"
    "0f5Zd8Vo9svWOE0z6wAH0OnH7jkEOkVHhjKG040i7OyH/VYL2JA9dKbfE870WDAFxp3r6lT2VNRUvXzw8vO337xBnD4tHm1bmHfR"
    "xenh679B26G8qRE3kNm2ENgJgdz+hADZ0U0ef/fpyxgNMntGePLW+OHpWpfZhQgd6kzvnvTIodJY6a0YzFfSgH0zcyU2rc7ZQAah"
    "LEyPI11RpxBIpQybilS7MRsBO9ffGCK9kuyfwASU4KXCIzJPyZlQ9elRRHtgYmwiIgEGhAToEWBUwJEAQ4Fs5dW4OwV/+zKIqh4U"
    "mxLscDi99faLlyMIpyuGqdyzdjuPxgLJnSYCBJdWkXeEy8DiCctnSl6OKnk5KHlheiOg0z1yxQ0SGb1SPHs821ggQk2Hfu4sqC11"
    "5bWSZmwLKJVYTeSdCoR5/W+wyxF7WXQ9WCxi1JNuWUGRP1PdRsjMS1L7e9w8FdUSma6Ea9KzEXCvwPplbzHPLtj/PEBBNxqzMuxQ"
    "ihxrv5VAGtwzG6Fw5wKF6rO7/d88vanp4WJGyzmmbRB4tSUg5wZSGinMo1/ZBhYjIBajxnYbl+/4BxkjzYOvK+I5v6k2K2c3k5f1"
    "ZuKy3ky7rNd9RkO2uTBpWGN+YfIbMiKzcCgeo4Y5oyO/l/WOAjUeM/V04soeC/U0EGfxkrDpnShxZ7BNay92E2xO4ZFZE1yfjfcx"
    "pssjDqxewY7Qd6VjLK2ezK6ALJAfAmtHAJ98zMgPiNsOpZLnie99gbLeR4x7fBrq8y4WOwEDPbY2Zzq3JVn+ccTyj4uDoFObQhXo"
    "i3rmjq6qeuFMZMiwGrKDJ7+KDkp3gpgFhgQeTRLXhaI8jo0BUTGjJcoMY86xwIAN31jZZAxAOXt5UphocbKQoa37rrrkzWi9Nx66"
    "iGLZLr3NROvmnc7GNkxHjc0HB6wek/ORBKzG1cNRsEaZf4jsdDbcu54FmzkDHFz/9a3Xnrn12ocHzz9H3gJwtn5B7hAfUAYQkMA/"
    "pBDBT2799mmME2KAidk4UQIr+u0v/uMTgeTMqfzBv/3h4MeYyOLwrdcJ2Uqjfty3J4rLCChVJc23ANCFwwjXyWOh2wUi1K9KaqO6"
    "NMgZiQ5ZT/KJ//qzy4tO0DeGeVQQ1jAQI70Z2iyXGb5Eals4HeRRQcC1iy4MrDlq/nF7vkEbk6CxKQUHgVbeIMn65ShUCfvzJyFo"
    "Py1Cf5lLzAfy5rx95T9UVypj/tDSz0EXKaTIGbrN7xjKGmrK2lJ8Six2BRoI66b01jjKtPCxPPlTQhb5hNQLT9Ee5dHOeE2gp+e7"
    "bAeTMeU5sUDqdKnBcTQzihMh24VOp+/kYGzdxIUpkIT1vciQmFHU3S7VMPwGJb2uKv+NifmGq2d95jxtStcsdnHGN3M3uZkXpCvd"
    "SHVfPbIKMo0ko+JOb2KTAgo/0FyM0L7zrnRdTE4/Q2qJLwITdciPUqtN28gSm9Wc0nrN3oAzNvWogjlc8CZrOH2cWfzWdhsNdO0X"
    "n6Qsi8zpv/wrk89yTCriRcyIJVn/W2FA5/grjO4s6aZP+328EBqb6s6ktDxW9HEpltxh0juAeOmxptQbb69hJePt4zXmUIG1mtKy"
    "IyVSkIMToecsBpiyOTPXMX5aO5Wz93v5Dgu64DF8pvAXM4sBlA768AmD7ILK0pKHwSA6KEdCM6vFonf8FsaeJ4PROwsmCu+1c532"
    "fNhW7vkPF/m13x0lyvwBv8XjzDUsKacI/cNwFkRWT0FjXDjKfE6QuT4LoTh3oQAAlIifrXp8lRZy5DOguPDjMxp2aBdcoLSdIsM6"
    "icbbEbEbSCtACrrfiTdn7apTIqCSknOysHvgHEc9wrcL+zPdoHb3EvZK5nTY4U6Hs14O3Vj+JXIAYAmY7txT8fC1Tw1egfRM7BzJ"
    "qVDgu137OV3/7yquhe998Z//RYzkG9zHMM0DkcvW2KgTODP8VPe0Y+XO6Naw4YcpgZZ8h7iUZ67r5nmTsze/jn4onR4tjPBGdW12"
    "oEAjTCTMwhfI8a1ThDuG+bqSKOJbtiKKpBwNHKLP05QaezooO7nKgCxCmgK0vZRzWJhFRfhFbMhQNTgop9ggZQbZfQ86sb7jzD0m"
    "YmsJwpGc47J1X/EQ++2spty6b6Sna3U9BP5UT0U8dxNCRIsYqg/i8DlI5NKD+q6+By8d3HhFyWj1jkROIPlHACbUxG3FNRJeBeNS"
    "Ma2TbzcQ3G91ut5xwpzfqFwK/K7bd9Ay73eGeI1dCislq2lXSsLOD2/zKHB4EXag55QFZPqg18BqKavfZJoA2Bu08yq2vBODLvN7"
    "x1qw5c310BNx5pRSnn+24DG2pqTawK+0//A3aBxuXPhLGaskrByBjU0SQPcPJg1lBPXhYfA89gAHsR3UlLBxPV9Jat856Joj85Ng"
    "Mlffo8BOjjTcJiy1sEopIlc6Xt4zydq4YrCUAczCLUAkogRtLO9yFKNQNrJKxvKesNSqEcIfg4zNRUO0VMy/04jlFqWyjDTuDZwv"
    "MVuhOluIXcgrC9HGCAxLsbv7WAupFHyBAxrNYSG4d3XNOb68jDh7fEFJbomyoiFECtDFWDeh5glMpFvVXyp3LJzWskt7bwkI2dIS"
    "2wvwRmLRG22WJeCSwNZYFzuxaa9nJz2Axe2HMDkGwxYEetS0ofsiK9e67aGy0iOTOmw9G0N48WCpOW7kPowyxnkZOxCmcFIsFqnW"
    "KbZIilCYPsNs+kGeMyc5v5njcauUIaRjmp1tt8bVplh6edmFXgaIEwE/0Jk3GhQHGvbLOhrCFPZ0tYPbHUuFKQXKfD2wkMUG3JGD"
    "AyKxsgJEAv4ADfEbLPRmERR1ObXxk4MOWXBq1i+FLJmCCy3CSFjL+EXhhhQUdOFJCMeB/GBRtcFTmKcH8KCrzYqOnQ6jKRT4ccUd"
    "Q6ObNl3P7nTGE/xxGvnBOBW+ipWz1Ldtvoi1Km2HPJz06pabfwTTZMD5Mat4NHAVqmwtyO10LDNuWVsuVQjVOVWgcAl8j7ByNuT4"
    "Hp65vz9m2VgcuMhYu2Z56LuNXMmqNyrH/s+j/a8/2pisWsen24/2H3u0ULz55Me1leLXH8XY0buPwamBUo8W871eONrv9fr4J+zi"
    "J/wT4od9aGy/12iaUJxuiXYfAVFwSeHTP2w9tImI3yCuUNj6VuiDwO9gpy6GTjdvtHAb+QFim0B3jckU/4FjwI4D1RUdiWZ7JlGu"
    "tvu4RUOxF+kr9URru5/StkUdZbiqbnOcb/dNeSSTCKQ9m/XDCkwJcAuH2u0zEcGvnPUpzQjQN2AhvIYzeqiJFMy9t7S/L5FnShb7"
    "6KKsJ/2gA9OEU+kSegt6Q4PI51qryIrxb7Pex7etEkyQxacKTn3U7X/UQKg4fm1WSly/B7LpIyLfNvnzpiQLgf1V7zh2AJcern2A"
    "6Qg6mIjAhU/r8HLDHvPtyaWoPJRByQNnDH8UYi28QQ/29zukwQJB675+HsctrNr4JgZhgJBWuQ8YXUooR5t+q2/y1yI7lMjfoedk"
    "H1XOjlhOdpCwQ5S46CvmUwjQ4kT17+/vBvmQ/YIpXNEXRVi3Iwo7QgrrR3q5HUe8g6q3MSI0fhN2pU030SZ00Cab9yaIQs64vMnQ"
    "U6kYWbNiju8w4aRNjKEpou6I/NZgpuBl+GuF5XaYp3pgsmALlreR1bfp3G+abFeSWmoEW0HvfVjsN9yAzZAcBw1hxTj2mEHrLeZp"
    "bLJUfGyK4B6lOaL5Qa9O1xs4fO432VTANOxVNsU0QFUIacfmhzLx2EIfSd+oYFQTm6s9Nld7bK6oCA18Mxr4Zmzg0xFcrn7fiXYN"
    "mwl0McLnFf47rBSawasp5fC5ZCJZMdgD0/jk2QzUEfYojWDEZppVx5xYsB3RQHySxqIjil/UAC5Gpx/m22wn47SMM17fS3m9rr3O"
    "nSfa1sB6vBbFnW3I9TVW2tZW5djhjasgLVW/+Msnx9jr5/PoutOq0NRvWBQoUy5Z6DhYHljd0IWleNwaeIFjN+A5EMk+MvVwmSN8"
    "ZrNT3t7eqhqXNqBiqJQc6hh2AjyFg89NsbWaxPIds7SQobijNqwWtA93O5vSylgdirWhDGZLG0yrIqvYsoaVPFJJvPjxAtv+P8Xa"
    "ClxRpoi2q5nbq7Vi6D+AngEbNqrTrAtszFt8zKtzxrxNjoTwhlE1vnn+EaNM3+EqhO+X7rsAI7106WGjVl6dWvVeeWN/X9y8PfUb"
    "nzfuk1EW2xLPRtusrkJrvZ0xLEz8lwG/yOPT2LIuwEgQU4jNHt+XMGHQa9je1kg/CMoGWtI2IBxxfUfBm82OHQLXypmbOqG6R+eg"
    "FqeOdXNUtAejChwGYM6+MxQbbEQSTTKzkqDejUpdIdhLI6Rd0B2qzERlaTBmlBwvOijL0FhGQHLgoQvVI3kg6gjrnafXcCbNAtBJ"
    "8Rl+aFTht7BaKq/SL+wTvQC9xe/wodgvjPEvvEEvBR7vPdRPTqDmelN6OkGfJny+WZeY9R/e2aS7ZI+onylJADAocsvSTq6tj7Fl"
    "SZP4Gn57mB/z9cRVqA/6od+FdTAVGDmizXC+quqd6JZ7dUqjbkHxjiROLpTtVdv1fFO7F0NGNEYEtQYHgV2AIfwbRkBrfJajmcGs"
    "sJrr1yQACQGvdhC+kFq7+PdBv4FO4wJQvty0wk65q/B23x7qAiSvExO8MZZq22fSMu5EdN3iPfeR4cUz4XOaRw+QlMMDq6OYyzTW"
    "jPErLqlWlW3r47b12JXE8q/w4hPhreGybLSwVwKa6IvI3uXrQH452+2aK6vrgeDWbGDHfORiMDcLq2vqVujDVAi0/Dh9Zwgceb5a"
    "3n60gaz4o/3a1034+sXv//nwlVf3D37477ev/Gz/809eOHzq1/uff/TswbOvHvz7lf2Dj96+/fJ/wYPrB9de3Wdomp9//Mr+4Y/e"
    "Pnj/rX0GxLV/++qzB6/8cf/wzesHT/1w/+CFZ2698cv9ut/t+t5+1+3X95k/yQ4QuN19kLiazX2/2YQB7O/Y9d1BzwRZ4JvQPxAY"
    "oEskM6xNy1X4sDaFZ9uF//fmlddvPvnJZ9df/OzKTz678lJtRcgWstw+/3r46rWojoPrT1XN6twqUt4x4ddj1vcdzQkRnfLSaUvk"
    "lxiSuYSlDM9/c4ieGqb8fmz75pUfP7qdR+bryo2bV35088pL9/71k9dr2MWbV154tGYys+7NK8/fvPLy2b9+8q+1Y61YHY/2J2vW"
    "NPH4/zAhq7ayLz7cjWVQ4vEU58XvDtU8E+dRMAxxZ2yfK/yTXfh+DeZk+9G9AuwOrKZ488rV2kq+iLdb0Rk59bwnxxpWJ55fDtFg"
    "RRxUiMaqMj4T6P3elG++jqfNo4MbNI0plUEr2MsiXF5VTxl3ke7Zu4/hoMqe6pH5LW1QDmqGYVRcQcEvEKdY76HwJ/q/tJT3CGh5"
    "2NyxG+g0avN/pQOAh25oJnQsVDJVwyOcU/Sj73CoBb/rgPhwNuDYJcytnA+915Z+9yB7I0odetQzDRX/hKK4+OhCiRCq/7YHI4oG"
    "eKmOA5SbDEsGiGuFf40yDb9qkM8cBiEkaq8aqB8sK03AhUdNkJs/7xhisuBvRrnXpgrhi+MOnYZRPt+nBztjHxgPEWDHR9imEUqS"
    "6VXO9jB95v4+vORFru73DysTUaEA6D/88LphQdcoN8/BX35K31knhIbxFto8oN2ywVk+ycwYh6+/y6oxLBp6GSOmGOQL1AIzQ9US"
    "BuyLxtR6JL0DN69+yvugqjThB3ZI5VdSkAo9J+nJmagU720slS97ztKzCOCoZ+lNGpTgZAln8Deff/QRT/P4NlclaeGy75LW6G10"
    "OriG6SGpGjkdXJfPEtwn4MySc0T4wQwf99c3n3yVJUI6eB5R9Q9//87hD55HH3V0hNLSgLBB0+QefvLS7TdvMCgsMcvRlj3nIKQq"
    "OkmzbZt38GzgPoSNyWCAaLPxb7i1UFB2KtG2My2HwTTw75F9btiKGVtcw0Jc82/4o7JRypVyqyfgfwYHkWDuC7Bzw2DgpBhU6m5Q"
    "Z44B8PZpKDCmf2CyThnIrncEPG0/DPxdtI7ZQb5QaBVEz0zx03dZxo/V4kk1TwepFSaw6R48UTyRO11czZ0qruXOFO/J3VM8lTtZ"
    "PH7nrfAnD7ieU7dhTQJ/4DXUp+jCLh4zrxOaU0Yr/uYmlLq18Gyezp0YHi+eWriaUxnTFVWe1vF7ivdQ1/Ef1vdYM8q0klb1f35W"
    "T8d7hv0ws7bgcb4FV/kWPA1bcC19Xe5qYtqJr2zXdWAbR2lLvprZmTs5JzKXTXSrF/itAGSHv73zIHp2hCNxvLh27njxTA7/o47m"
    "TudWS8Uz/xSfhqhudQMjQ/E3Nw1ohy8cX3QSusdzq7C3C2eOVlFNwUn4H9qa81afh9Jkn8D77H7bDgLMlLIGV8qaoaSeu+hQdrB/"
    "ICD1atEF3vZbYd7cLtXYF+C25WW9U49ln0PXMQRht+H3oUN2QLicQ+DGO2rCYEdoyIhJhh9hDzlC570UMgx3/ImBuUsu+qKDChlT"
    "2uXCYuiHdqdKNodmx/cR0xuJ2NdXS6Vj/FezLIBYgLEghEArVGBkPv/wtzljxV0xvgZMEbBk7nRKcdBiFmVjZHeAsUnTAwaGVvt2"
    "3kVVtJPaTP6BOnHA9z2ArCDwSQpCGVq9BUKowfNuvRc9MVewE6RmI8iJ78mvJtnfQreXfGn2Oyt5Pwq79k1YgL7BnkMxWh72863/"
    "vHH76o+g1H29vG5SXYE1/ub57xZEeaqWJozJBWY0A2xvhkIGUDjWGGtKgUskB2CvEz9e54mZkZN8gQU5xcoA+xgFDtd71eI27hMZ"
    "CB5UAwExif3CeATZK1oXauPH3PcWnamevPkk6xX73ZiWqQan4YbITka1RO/LROtvC68YwepPMTivJ3tFXek0DG64wI9VdV8ePE3y"
    "wtPXuVPNkx8fvvI74st/QA95enbRJxGHVs3a27LzIH+KNuFypvLkfR6Wd7ztAOFDQArfRd9qN5RPodelGrym/6QAZApRfcOtbLNQ"
    "Dz5LFg2tZj1Q12R4kqd7KGPWe2Z8pYRoic6jG2507EFot77tSXHR6WPsrupHALXZSDBATGdiNUiTHprOMLuFad1XZ0qsSxv733W9"
    "/QftullluxEekk8086D7TfQz2pnP97HJuMQOVd9XF0pjDJ9X9TSP9m9euVJjChRTEcTbdn7S0oBJlGpRBxhUzp7PB7NqE4JyELUf"
    "cIOM8MJORTjxpKLh2J7rHXPlq1UDRosYIfL3rl3XfoeZMFIQ+pJufy3KsFBAYUx4Jc6RUIFSoTvRkx8bK4RiRUHFILYKYCOZpjYS"
    "iZNnNM0tmN3B+qV7Cv63KLMRsJx48CqIV3A/Hkcel2dkXC0ZFseeoZt4hJdqBgvM83Bt+B0QmJISRSoXBjd0bnWteKq9enzBis5k"
    "iia1mR6tqj8oV5AgdukMz07VST2M+ZH//TC+u5FjEBuWvD9cjJ2k61vo0bzILCmIf5QNKhVwsOFriQiYEj6UxAWzBTFADiByS6tV"
    "onNlfiNgD9DPK6gSXWPutm6lU+3EEYg7GpQw/pWPFFBiRgv5P3oCUMON+aXXkb/g54KnScHt/jM4A9g+5i2NCKqpI1jOLz+1QgGX"
    "GK1It60yZts1Sutle3ZkVaBMtJi6V5ChiKgFmTQIdZtktu9EeEMTuEzhFUvcJ71yaVruCMOP8is6WPTKq3CVRM9Y6GevfHwa6YeJ"
    "YSTtapW3hsHCHLz36vsMvcLQ2jPL9Ap2CLnGIX6gzHix13MRNpK1K8KIoE/Fk4Tci5pc7S0WsRuLso01De9xza/2alq0Tfw9B1Or"
    "Ke/oEdAYH5R8h4BPUoZmxKbTQvOqqxWk0MhEKQwo1Huhhb3p5WXaibh2PK7pjs2FQKS+9o7IEKWPy6Edpw+LXORzCHRAML67IgdL"
    "r7xGb/THnt6K5mjMApqU3p8grCmy2sPWN9GeWCwWA8tFFCphSGS/BMVeoVOEgQVFFz64ysF6gpE6q2uPyl5lzWqCKNxGgiiJEB09"
    "pDQyBthDPyLx1TMXStzUEZbBLHL4YN5oITNW5QbBEKbcsAuesycDOICY+cVdFeB8l+lFYRYRjUeNXcjAPxSLkH2VsAgVBYgCa53y"
    "BSXhGPo2Rad42DxuCvZKCjcRGtEIDJZaglFPN7KXhjoSjdLnFUO2o8F/PYAu5E4fzUy458tLpem66tg9wxcQXjPMdQco0wMeZSt3"
    "rAc8Ojlw0UifPLlJPC9mNmbm94iBWwqELSYie8rUhNydAEpecOCMBShgBsxt2ZT6QjGuETMVOaqvD9lnNF8f6/EOFhvh7oQrF362"
    "B6OIQb0QxlylZZp16SvoKeZK+SPb1OHKKnf1xMHR8ANk5B/v5MkQhretkitdt0rJuqgC5NyFtwKwpaF0UaVZIK8EYvrJV1X6GJso"
    "USQqcoohczUlX0xTvEHqROgdX6ZE/77Hrf6RBT4gCzzzdYjWbnk5uTpLYnWWl9FXWv2Rr5pkzPmUry/xrbS8zDdXpeIxd0C4Coew"
    "ww0LkWEQ2R+977+PNIQ53l978dZ/XqM8Eu9pzvOMt75y7fA3byLfzN8K+VsMX5F0CJgEPRr3PyTGHSrjzlgGdZwhGyeMEbrN5jyt"
    "2yDesm6jAgStQCKRzl+Ee/P1gx++c/CTN6HA4evvCu/o9w6vf6wXe9qIjWBIK4pOKJPkQfXotHvVGX63eM5Rk6MVCZyuP3Ti1CDb"
    "EbfV1q3KYlvOF9WineCxPdysnG1yDw42HpL3pLdrKPUeavno8PRSDk8v5fBQvLqoNFiPvIdFpfIgNbMPUpMf+CZjE4/2KnVBALjl"
    "OtwPprC67kWITU2rR3hNorG8W+mZCsiLe7ZSAo6RUSRXUqSmoEhKB7mbGjbqi0b9deFNM7fzHmYVi3Vegi3Z68IRzRMUH7vAGrbQ"
    "i4w7HdfLniCo2PXl5QYn+1Bc1IxkDbqAPn/a70v0GG9+1jNeLuoq7ykjOcvL6BNHJaRbHNshtGHUotXGdiNKclpuoFpI7ux/SklV"
    "jf7b64nM1MIBjL5QPALGEE3Xe/kIMmEPJtnfoxOI2aahZ/kehf3wWcF3yY9b/oyJGrdrEQX1qi10GWDCHAk0KpwWy52d6FqH/QA1"
    "Ae+E9MqrkmueU3xCVu1C1Q/VyRshZLX76P3uVR8b5j3LNcsTkMpF0II3El6Plq1k7mauYqa1Xbcai/Qrksx6Vhcks+1tH5N5Wzw6"
    "BGW9mgXPvJFlAGE3ajXmEdaLu+GOKj1ivvb3S9a4YsuM4Lg56PSb62MRvjs6C9dMg3nW9Zg7YNsvd7x8jwV4WcDeOeWuRSHxVlRX"
    "X9RljTCmU8LByOFPHsRwGOC2QguPetm1erYblP1IzmuKyiqZZa3k4jm4qwqr6Dq4ao3Qn1/4LUaROzgrXTVobzMZwINEPXSqfRBb"
    "nIqxosQv9OA89+6F4wjkEx25n2BeeXvQoOKTt4U342ax3m0wT3VsM7+Fxe8FqkQr06vQd2sLS0mysb8vv/cCZ2hQ0b39fSXcrNm4"
    "93SpFC3rHsZkNRtKVN/07mGeqrHkLHJuEOayzWZxwGbx8WlFlrE2KrGQkglUV34cf6/CotMHtvDkjAX9hR+9EfvNG0U/8TutPKjC"
    "vT4g7NahA30tt6vn87vFrSoaSugJWUoIrHt9A5ijETqQVjasxFJgSFU46POgFxadswFyGYuTonXF5Z5GITDd/f2IhDzsdh1/EObH"
    "1imYumnkgJxneZEm6Jo6JfJhZVKrLts8u8Wu37Dh/HQFuGMdA//7YR6Eyd4gtNAcaAeODdPQQXWhMHusEzYKu6+N8/263QOKOgmq"
    "eU5zrG4R1xxW4j6naQ86GIXWLWKw98Vu12m4sL6XgK+0gcuAyc3DPbVbfAImDP5iDIuMXDtqNXwyptQ9IA2OHWIedvgvxEHWw6Dz"
    "TWeMH7tOaPOPdiekT4EedjhCM9/5B5aXd2W6eWJYkcGohkLQES6o48rZMZ+Q3SgfvVmGm12dK8/AFvmXTcNMGeAYKL0Vqhg0Yp7x"
    "djCQlOEdipGbSzRrS8nVYxAPlg13BZC1Cki7gxr/HNo7NVjHSbJlSWDY4LZHNQSxgSt0Hea87TbZLG0Kbqo6FuLB/n6+a+fHjA2+"
    "hAwxMcljxiQzzqusFPmWEytiIKbVVAw4GvG5IPD37vP3tFmjh9/u4WXPxx/MHE1KbdVVXBckdpuV0cqYqN06H/VmDcVS/lGMcN3c"
    "XKmM1SL3yzFEhcm9WB7Ihl8foJoBfY/PY9cegGKOB1wSRi00sB9WzwIOno6tLM2Y8JkvTOef7C5HAoBxl+LbOr5dqkWJCQIy2oii"
    "Z+ROKqIggNZr7RluKL6f4BR2/FYNiySJFOOK5ESQrfx8x8FvFSKRo+JOZxAgjggMa4GZI/Xj4vOmFmckcQb+AY3UkjAny8tGv+3v"
    "IRxJEu4Wdq1ymfvegzAhZeDqusAmVM528pNRuWeNgZ9o0SWCTIU0UwTquwouS9d24/oh9ihqvA6smTBd9Hg1drlu0dIQbEkjLzIg"
    "QMFwEaSnTqw7wB4W4drs5k3uiOTzAjNHOVISKbiLT86Igx9kgzy0MlAeGH4DrJCTlWjcq/I8uoc//SX+TckRy23McVgH4a2KSHcc"
    "P+zlCMtORX/ISKwKTTOHhbRGb3C9N8OEuHJVwkIw/vf2vz0FBT7/ENr6fYQSgVhYH7PO/PWTP0OBHDSQQyvBb38FndVbkLWSIfJ9"
    "PphrL96++qGIro4cVrH2WG6V7pigv5SjkIWs0dLRelixehtfnxL6h3y3IbZriNkL5H4VQopuZ3tsOEuv6INY6Eu9IgIcMDnWV7WI"
    "PF7FlMI/2cRCqeQL8G5GwxgK0+F2ZwWEwFn1SH2XYDJIMgpQKHKVQJq71Z7DgDmnH0wrHgvgBfIaKFyUI/llczJsww7epM/W4210"
    "JrICK1SZGkfhpoUAF2hz04C5aURzA9KcwqQ0aGAhG1iDBtZQJsiu+GdLVXfbR4HYv7dURWHarUWQV2x6Mmth06OoHJZs/e6pQwMV"
    "aqEmSl3yRE22wi4genv0S11o26z7Ha20nJpIkYOiADL3ZMDDz96IY+Yj/gCBD78AJ4+fS56kSAGwFCIouqOgUvF9MujHij1tqOL7"
    "9FuyVx3Bz9BCoa3XqLJ/mPcgy5+Hz9gHImAw3inyIo1GpQRiaIVEoJKStkJTs8kLD25wfpV+Y3yxgdEQLFyDTidegfxKBO6hR86b"
    "aBXym024nsmqbqlFMT5KllMO4rjNtjNMoSK3NRr3nihJvqKhCmyWsoml+oL04NxHjlSnS1LzK3TTqAmM9Hm65UCHKPHPoip0AhOl"
    "tIrKV1qieELka+TAf/WD21f+44s3b/CU4PG47reT0D6I8ideIYs01yvzFF0sP3uiHo5jiI2+i/inaFqEwk99/uGVg49+dfjMJ6Jj"
    "Efllml2xlWj5H0e/QURxdpSVeDyBvjCLKHIkbB290q+E1QthPrS4Jmndr+aHHo+LwylkOz4+LK7U9oVS+70kfo1ZpgVInRTK55x+"
    "Deq3rnamxIlWw/wEXU6l7pySB4ySBzolT6fjqIllspSr2gJs1HgEpniR0SU7YfCISJZm7khMMux5H5rItH1oho/D168QiLrgVgQQ"
    "Suaey7aM+JTGQLeMiDWE2uL78lVgG7D16//CiR7ULIlhVPmrPCWCaZ1UVgt3m/u/u80+EPOgpUKXHou42RCBK+XFxMmPkXex2q56"
    "Qd3vKA+VY+qMUSPoEO8rWWbVar5LFvMtAifxe3BBn8/nXUWDpIb9xTOSKHf8416+YcrAwLxTRXaFJU1D/xW4y/uojK4zbWGuwcRC"
    "h6c+4iHBElDCnDzcg/osuReVhe0UyUhkRlrGZkLLCPWhZ5c9LjemZBOLmfIaaWtKSTbO55ts8LDsOdxzr/3ii1+9QpmpkwniuRmM"
    "o/887grgpnwTb/emhhM0jSRxIVvYfbcRS0TaYo8WAGxs7aUlLHW76ITXD+rl3bpld9DDj/vQrZWEB91aKQtd7tK5++57aOObub8/"
    "9/D52TlmCc+XuQZ4Y3S7iHriSO48zR2L2FjNWYy8uqKnzBeM3L+QZfdrc5LRtvqOHdTbmQIZ+zUaMSkSOfLpEzCGcQ/d8pA/0P2/"
    "DHFHfJwkcYdvvX7rDz8HOR5dtdrEOi1UHgnuht/tIR5RmbzkLDILwfXwBIJ9tm2v5ZTxbMCDSkPoRaiMFUiIU9/7pjNGxREVbcT0"
    "nghew9SW4g1L1sSUGwQGGaCqSuyCFATWkXQoZb2nlPQ/YNwEnBRojPa/BlEaa3eajnE4kikGHXSGIdifRA7H5DpjuSSWqEzNaDCp"
    "mjzFnmF+/mJ2qY1ofuuWvn3gxFBa5DLvC3q6NNBLaVhuEAIsNl0AosEnZKsPpKlqfP7xM9CkAWVYB+YknyYCWS2G/u7+PlA2qiTr"
    "pIQ+ETB9P/L2eGoRM1LgpJ6Ktp4tQd+SIA+IcATFeYOtAUusKU6LZyePW5/h4rJPkf8RpRkTdfE5lARaGkkb7Nbtwe5WuUWEJN+L"
    "xMRupd3Ow7+jCrHjlL5qaYSG2Ign30uxse8lbezWZmUk0NPGmDNLtYNX2T9l+ZTFA/LiTc3sXI3CzqKQ6jhJlyeJrR03/xhlr8pP"
    "KY2/ynygJfiapvWDSdVLLy8bWCUMH0Q3TzqZ4fSXGxwzMjqEcNnxOWa79Tx8JWiSlct/h8HCinckyBEz2bdX6ag/r7iKvHoZ2/I9"
    "pJfEScAiTPaSNgNMz1XvuPDse5b49AiTzVMgms85CAi8Octv2lMxaYEra5gzryctP3nXAubF6kWeaTNe1JLebgPdrHZxzyKwyQr9"
    "6/BELMZnV35irPAfMYfizSuvk7nNGmXn+8VM0moKVppqYzonr1o+sW3NWU58VEI9/FJuNKxmzAukiTK5GFHu8H3Mn2Gs0NMV4+D6"
    "UwanBkuwCZsxJ4zsHngjPU0p8NdIbBjLa1iKybdZHHih24EtjY0lWuLiTYZS0zh89drtV34iZ1Fmsef7bDaBbPp+mMZopaKR73Ao"
    "8o1mS7/yHsbdns551P0W4fEyJalRm414jicfWiEYNDjo8BdlSGxz0wnFVWwzAGytBxv9zB548Cb24OCH/374OqUmsDjzPPPmb+3k"
    "3Do+pOa/NXDDJOK1JBQES/crTNOC+S+eps8vimRZv0KpDnUOknX+4ItfYDoWSo36gsJGixH9fS+dZ+ghMJfgGzTVLLGfExW7ULom"
    "oA9YQIGRHBS46umsp0jSqie+Kiul2MmQTv+Y2wt+5tS/anBMZZgMUYIyFkuIByY9sDDDCP1bXBpksNft9UCkL4MM4jHRiUTPK8ZK"
    "uJIXfape/ru7J6hV8+Hk7O+XTEItgyV1tsi3ALiuzz/+490TuBnrtvdYty9PN133efkcgwrx5QvuyGnkV6EpCkmc4quwF8LHsJx4"
    "7YEgrzwlr4LLZdFdVGyGbayaArWr7BlHr8AYR6/oPYYe/3346Yt3f0uZNSgHh6J/yeE7vNiKgemcKMCRmxEblQl6k5P4rkBWhOM8"
    "urPmM+2PIflBKS4PqIIFQZYQZxG7v9coYsUKOu1U83xAqFtpuw3SPKdCVfGQ9JwKNM8pp8IbZGCbFIHD92YG8CZNejBSVY64cgX5"
    "y72rJzOZEJ28UALDnRB+WCJEdZjqOsbSxskZO+t5NFclAr/QfvOOqpRmnxksC4oIV//l5rXnMMZWUXoYeBA+PHz6WW4Aglvm6Vtv"
    "/BIVknDirt44+PdnqKxuzaLgWNhFtJ/oE99xrK5yDp/2HCdIkYLTBE8vJll6czzwb1/5xeGPP6JrM01YBtIyeqwZ+F01ED21Kl4T"
    "ZZbBoR98+vqt374kImgVP/nNsAIyR2yP98cMhXrWNvdY4DgcfrazMTRrE5Pphsq2FrsENqnF93HSno254v36bqGHdl6PmbR54VSD"
    "dqw8s2lT00R2Uja1o/iL6QDa/9TKL+Gr5ronk1xQVV7kgHMfLuPBhx+iKfP1KwdPP3f7X36OSRciLbvQsmlJqF4kQ8vz3BKp/gS7"
    "D+N+Iwh8pk+MNyGFX0UBeLJUMs3pkQ8fDomx9PyCv4RzJ06hI69arlaM363Zg2fs+nV2iFjUGrYlkmKLLNgv4yGCUf6dNg+YbQ2o"
    "8Zv09T11xpSmPvj8wyvAdN362Q8on8AraIO+cpVKYkKlW+/+JDmfN69cQ3VSjruRk5FZ7T09fEaWvZzBy+AGm7KtVTXk+6imidaI"
    "BqcxB4Gq/ZxG9lsETAgo144qhLqYF1kKoWVKgY3xlHOTJ7V27EDlJb3FMlrFVGphIdSFHI/IVDGcmRcR3tJkli4GXaC8gm8mxRWP"
    "iysipdVCfXGq5/NSn2sm9YRLu4go6s0IYuX7X887GnGTsF+eeo5xYzKDKtMOacrCmbFLUQtC8MW3kTUxmdYx4k7kNzIcpIujHHEp"
    "S1XK3SlSGUgWVqdwUfFeK6LR61eAj2bcY86wgM/S3jSVdJYWBlyJs/7BwfNvYeLq5z/44sk/H1552xCZbLhaDU2vCol1uclTeL0j"
    "Qr5i9qzOFH4E6coxjiGubeCqdU621Ax/mQZOkUub0SzCRntKDzN5NV2CXdBYmn5jq9V8yGgRR5GhK9fMz9A/9HsGSU+o13KZ7cJV"
    "d6Y5/xaIdii7B0RgHWOeXWV7ugrzfPnv4gnqfvTGwWv/hlP47qeUhVyald4iluIGRfFraYpTTReX50uR8YPgMgKQPrmZRyFzTjve"
    "rpYdKTYwvjoWgrxExszAsqNE9t3K2W9jJkHY7F0WbY6FRVQ5edhqDzlCRoRxWNfqWqLKzCixrivErMnUalbyDUougkIX6oL6QV18"
    "JXUmTBN8ngvZIJgBkPVR3W1Dv0R24UIdVXwDDOvswSekZaa+TWA3pFkb4bInPJTc3RN7euzuiUxX/PlHH11eydd5ymINu4XS/cLv"
    "PEUg7jSOp/jDdz7/809IN8i3DePu4QUYNaqv2fjZZOI3bNJlkD/wdQotNmEfq4g7LAkT1NCcEm8msnQjS5yZgZtYiyjrtobgI3cx"
    "kzB7VTwnPMQZ854y8XQRyQA2Snxr92N7e9smDaKvaBA5Pg3f3I941gQRjESJqk0wSOJruaRZHMLArlOjzdnRuP3Bzlo8d1l8Rg2r"
    "id3pqTXF7nInZgkQswSbrBYdMMzQpV0YgeLIsVPP+yaPYUbpSSTYlkFUpbk3s7HIWmDlOLkajE4quXG5GSQ/q9uXsNsReOKddJvI"
    "dS8tN16cOKpYppk9tow9Y8Vl/Q4juK74Za38RB5zCawtN8LaciXWFlFGMo3UK2fdOPJXXSJ/mQvAytDY7XoYMVNUYZamsU/yn3Zf"
    "Mn49uwktP+i2XTVQPqGk3kn6Rkooi/chCeZci6eFldX6lvE10nvmaUqfGDioZyuZZ1ePdPCYYhy6EKumsFqL9iGbj3AcZanN99Uv"
    "PnmhauJJu0GQqwqyipBRtkMr0GLXUK7uKFFe+JpnoUROGdmY85CMEtulhFNyP8kf1jtR7JdWQ2lq0agedOsBbKf+Lm1IOkXodOmL"
    "U2VXztqsdri66AMwkiaeBPjXgl1e9KY1ETsR9ceryIjLhAqDvFD14FwZDBhz3Q9oGtZOlRL6NlHKpfDCGX71Rn/P1k6zKv25fOIE"
    "m5eZIXGvl/MH4TxkI5wMSvWOc5SZbxEYAqgPM1KK2aI1AQaAjH3K3rAcfft0MqRbLwoGQlIQ+Q4zx9W64qUW99qD4kv1yA7bqYTV"
    "QMlZpLgo645tqc1Erm1AxbhfJTr1VnkAPvPGmp8jtYV9tXxp/1zAOwamcpFEjB0tqXcU7ykPbbuBezuskpdo2SioWEzVGWk7/YWS"
    "qaqlYDZRwvBgllkAaLYtVHuNveBHPbatSYsDRZX97D6GYa6pB3No9xqtG93F893bhEoMWwy0nN6p7WoqAB7voDk9x8zUN6/c0D3/"
    "SGhE961nc3/9RHWL/vCvn/yZkP+kXmNu81/ORVQ4sszahzlvtHP0vYiBxrFd6FZJaC/DXdkvGyt2cku6M7dkruF21468L6Pjj6ks"
    "2BZ1j7pF3ZQtylg4GM2MLRo3I6eKPob1fSdvq9qsOav+2ZWXEiuXYQjdcVuGMMOiVbvh9nky0yACfOHkDL0rfbjcvt0rUwIQTs4f"
    "Vl2vNKGbO7NzFsuvZjiiRtoSVb39W+ThNzksJz8/mp8st8lwH8dfgTQVnZRMX1qtYmXyfQwTEUebjzerv1c/NHAw3C5fziqVUNoA"
    "RXVFnew4G+Qjwa1J+vtR7dk+woIR5/b4tjNU9BG7Ow1doWfMOcqId6ntx8+eeuGzp36SwyCmq39EMCQLg1NlOCqLj80lSRd0mv1k"
    "rOTFGxR2gZp61WrBhvqJEJGfhxfZBwwM+a93br/2FK4SGomf/HgLA2L/+smzmY2S+jBGWXOE8PrszSd/ichgccu6u4jrcAS7QHHW"
    "rsqiAnliKV/dxqicimuE2RhYiDop1CT7GqkmRWujSgxmKBHmzIqvuwqHq3VgRI2NzlaiduBx1UAbXgFDX+hDRwKr+rGhGLC+IrfR"
    "lMNIPGCPgQ9MGuRGCsuN/O1IZ2zHlCprhIJEMN6iUHY/ONfpYChr4O/1c2dz9MEwMeTZlygCmEFPGazVTklEOMBoATltj1cGRfQW"
    "A0a62EIPA2sDnrCom4f9HnauTZgSj1sbprW0B8d8s9gl2JM4usVWBX9BH77Habm2uIlvMkgJ8RF4aAMtwmcQj/DhxdZFU9MtWPcN"
    "EIcHRUplXgwD2+u7uB0rHOZT+wWG3a1cpo8dkJIeyd892SpsTHsj83Ki6WSFaZXRw1gvmx23h1FIftrW6pbbUxEAvcB2qOqLLlac"
    "p9NM7BPMGWa1o5oGWTtnU8u3RiAZA3OLD488wCsGuh8L3xjcGIHTGNSdfH7LakEL0i1ri3lo1R23k2/hgn8DkU1dr7VBfnz/iIMz"
    "WZ2YX9Sc265oc6MiU5Q+DoNaMXojY33Ey0I7iJ3gBOH4O+i1m98z2V4QBfpRgfwe7Nbp+pjPXq6I/IZRKJCcsLpWMi3lpy77qbun"
    "eJ5BGUtRp4y4iyJtla8Xj5/CDI9c57xtW/UkiozV0KSskSr+jDg8i5SyyJuT8Nvn7JJGNXOfXKbhbJPnZ6ti3D3Z2NoqOuTxjc6Q"
    "Ru0yR+MZV0bVCWZrk4fcastv91MEwJQJXvX8ZuXs5vLyeHl5s4hEZVykj236iPCw8OPSuLpZHpsK0owuMFJGvkhg7KHjbhMdeCdB"
    "uWf1yk2h2+5ZTllNMHepnh+lKOem842t2HyuX2f4h+SJTJldDStwmuXOQrET7YZ2k8tAZ6ZoEn22DOApDMujRIczjJvAVxtxs/2i"
    "EsWtH7zJjOdM4Z148X29/Hu3XvvD4Y9+GQNr5kBtugEfajv48XMM1ZxiuN9bJa7qZzevvkXR3H/SfHQU/hjDtBbpq9re1ZconOm9"
    "ZM1MIMPoTkpUONP1MHB4AmYtrKDZFkfLs9jpk6m7cWDXXjz44ZNpKHXX1f7DXLCJIJ5pKtcLfR9+TXP+O4YhT+zmG2r1wvXjV2LQ"
    "8SqzbZcG/HrrZXSXZOj06CEIe0zp8Kuz1aQdp6V7DW9nGpM1+V3mYCIHUJE7CzZ3txikuUCn1yIzh0ElMnsXVYK2A/jHSdOhL6wp"
    "p5qcmoz29xhyJsXeKml7o7CQ9tgCuoJenVznZS15OvrmHNyGXL/LaAa8f/5OgRxmHXJCOkCdxoL6g0zEhvSpqBp3RiH0s4q9/PzD"
    "Z5g7Go9BV5AdyLfh/bkNfWVYErMFL1QAEotkRYw7cPKqGtCeQZzhBnZZriNgIsoTyemVdbbRLo4Z28iD5Oxie5qq3mXbVCR35wlQ"
    "Weu7bbE7WyBtACUry5uxWoLLT8g9I3Nl1XLLY0SxKi+BXE2wToEK68TonXhIF5zIly0lMasR2K3yhGw8jFBukejEik0tYMSD8iZ7"
    "HPqVzeq4PF5ZnbJkcEL1zl4xJV6bFweSalfOtrnQwctyVDaqdX3z3r3l5b1CwerZEZFmBa09k39C+DD4P54PHe1gTFjTxE2fi5t8"
    "eJq7lhVUzufD4hOmnqOZ48KAGKoKh7CkDzL9vRuPSD/Pon5VExJzsCmsCVRjNJDFWpEI24G5v/99B7VZmQVk1llElXFhI/hT0zS/"
    "BFNzB+wMD9i7cgO4EgmeY2HEK+NvOjp/k+2gEb97sgIxzvfrOTjX0qeGHejOPFUwP9aRopAdKTlxli2OVj9/KT00Bt0nSvv7nW27"
    "sForjtAeZc6IIYRN0o6PR1X+aWxHyKIZh17eTQQu0S4AgkRwv1fIs84lrzuCV0pqnWoK3pJKJnwiE+4MG4ykGj6jGjanGiGjGmEa"
    "1Qg1quGrVMMjMzRPYzxDY6pcl3OXn5JOvkW3SVI3zrUpW1xohukJ/XJJcXDebedxOmAyPJqMEAYZ0CA7otMuI3W+tI7GZTL09WhU"
    "BEICE8w9zAZ+CbFEQSrZoX+7lY6H/44i1U4PzZfbY2tTqw8jztMMlSNxA8FGgzeXl3vMK8LfRRw8qR4QfhKTzfxSSUhOrbg1cxOb"
    "sRBwUpCHqAao10oYN1vmVCsxtbbhrwwu2Isp41IQWIFURwImozYXvdD/juvs5Sc7Hb+O6aOgRaePkUNQf0fW3lZqFyinmfizrYos"
    "g3qNFlwhvFmlB4K+Dyvy0fowRZcUAEWHY2taQ02jM4yraUS5qWys0oIhsJ7IcQwwT0CEXdCqnG2xNSR3K6JA9EzC3O8j+pEOL4sZ"
    "xAfVgbhGoER5GxORb29YW7qugBU2M43fcroya7WG8kdU/bRqoufnEHVBckSISHzOZIjIj0fjh1kiXd5kKz8UM3AuvhG3ZD9ReZJt"
    "XD9nIo7nIGFdR7l7z0pwbLlWgGZtxK1z4FJrKBF9Rs/uh/wRqkjgCeluvAjhnWU2tHaLtKrfdMZ9GqMjQn09nrXOELuDRcVSPmWg"
    "Aexby+BaOs79GYWCa5SlFiqA8VI8PaP6sO72ON+yIiJixsJdocSklQx3vV8lPHAt5Fsy+rUlo189fokgKWuhEQmIOJB/7z74vkU8"
    "HKsdO/4wcalOUHRor5zrdIDbaFQMPBAGoanHysGK3gff84RkcKzXIZw+3iJHbfWrzB2IIQhgqw8hg9jiLhgCjnu9lQVdOay0Yjat"
    "DN2gda4ih33vEHil3sqwyPjqY2vr9fy5qhFiGmxjx0doMb+InCruLt6vBxx7yNDY6kTZ8SmwrBmTz8tUi7hhosGd9xpKFWw7NL5v"
    "lO39fRF2HVm3ZnmuB+i8tkjeSHbhU3nltk8zrwYqU0UpDWVxJiw3Z70e1Ic5Y6XJNRiPDLebtai2+/ErppeRQY+IacVStugkx27w"
    "TWvGsihlRLD4Yd2A7ex7PB69VcSoHQokwwjRVnHQQ6cV+It+JYhejcxPfXfHH4n5o++Ynhyr4f2n9zDU7OrNa28LL2cJj/O24rV6"
    "I/J/vPa8YDU4GNGtn39E/IfQ0ihoQmrNrOVqPHP4zauf/vWT6wzA8L1YxnDM5iDwiDDkhcLZ1PdJMI6aSFR07cVbf36fjHZKnOsQ"
    "FmJIyMEaYDCf1P39B4d8cawl7DHb1f4A1lO+n/a63AY0TC056h1nQ1XSpB0vruVOw38ni2dy98B/mKY2d6J44siJ2NaOmpFYOumT"
    "q1236PkzRX5lFF3V82AeskCX/BpijgrebMQAu6VJaerBi44YOxzZRAYOpB8O1Ow7LEUW11LO2G/aYUH95PzzovmZvPYHSnOJuz2i"
    "Qk8MaeA8ydLGnKR2Lbs309EfAcbVjSWv/WykhB7spxyxBOnuWeVGInv3rFiruFOT6iFh1OYBMKT6KwNJ7NURVmLXQoQO9BFOEn22"
    "fL1i6Cpx7fAVXbaLvXoo4hx1N3L6KekyjsKYbOHvh3xr1qZxsFL0KRBJfv4BOYMQ7ue+jIHXHgEjCdcPQ4SkJSHkx45P/YpkNGCL"
    "YmB/Hd/qVDyWjoaymKCuqgWL0tHREYvhvSdOlpaXieeydyhxGWON4LeRee+ZlJ8egZ/G8JM54R2x6mOGQc5RwOAxDL5jhWUFchFd"
    "DATXNZafH5kid4YvKxNkpwJYLm5wc5jB7b8D4LI+lgCX0E2QVZeSS0jQoahuffIVMvVo8UEibpOreVWU3s+eevHmlRsCye/99BBZ"
    "ym7EIkYj3yENH/K0DjWKGwOkeqWbjZ2OzGldrxx7tJjv9cJRdb/X69PfsIsfuyameh2Mswvso9m012hiwWgvNrie0A6BQDHgXtUp"
    "JeaQst2xXE0km4xAJBhZaL4fI75YZctl6JbFFjqnRmZcfDDbYDuuBJqXx1i33m9Wxtry78nvzAxrtSuUbeFCx7dBuHdChAYbhE5j"
    "C4WV/DgF9HxsFr/v+104sqv4ddUaCEgC1/OcgNo51gZxVX3KWjvWXndx8NIGfsaSchBMCLw1KGwWzoAUO84oM8aaC3tYBiZuHHdk"
    "EJDt1WITTlQfOfFtnGl4MTv1w7jSJtwwqZRATxAQXvr5Nscsw0wwWNcmxbgjw7+36DsL4Ld30WGPQdmPZ4TFo/MeJgXILgEHGeRs"
    "KjOjOaHg3ZN48ZPZgPGp/UstGe9iaqG0XqYW1Do6VSEsMLtSvxrP+ab5YfVVzOXEwi8h+mh9eZlWddu36rA72LMUtIBGZQl/86Ps"
    "00lyaDVZoQcw3MfqVXatbiU/tjZho0ymkQY51eCMkovbKO8RdLTw7dwrwkfJquNma8cE3xgdb7sox8bzDOBe3cRB3lPSdMfQWN0a"
    "W3uoP0x3RoSfGMs1qozlUdkk158gw0GEvMfYCMueH+bLYjQmEortWo2cx4QuOT0FgrmeH6eluhinpLqAkslMISkSyeZ2fm8lrdrq"
    "anlT5rsyza+JLzVJP0xrnIQ2XLDZEFEOcfvVTUlpKAKhjoBw9YVg5Baw2mDeCeZ3EnCRlz3h6qaO0wzLHaCB0D/4d6xCN46YlYeV"
    "n+8drpl4vu/AuDhYVmwsCore8nI3bywA8Bbl/Is5DpPEiluZ8jLCzE3cejmVocahdLec/nkS1qxNbHosXID1bIOvzkwyKOA3sguw"
    "Hv1DokeRueUBtUf/6Pg9h0LRullQvcK/mtU89FioXHrd0qohctdV/8c3R3/e7tjueBiu6fmWgcY+9gWKIUGxl6TGNULnpo2S5jKM"
    "8xElmfRVvGFY/RRvZ1i6z/75bfbRim8WwpwTS7OJsgbvD1cKy04onusz+sEji2bvyfv4l8QR93kOzS5iXKfvsUSLxrz99o9On0Gu"
    "LfUofZTG6FB2SiA+4+o4bmOHc7vHSR2zzGE6IJFHa3l5E+OtZkqom3gzwlBWybfrGYqEuS5dLuQ5jmz0Yz6mTaC9iUENuAJz896x"
    "6lxTWFXaePYIbayktEE8jUi2EsdfSAbcOT12hM/3YTenAVNJASaB/cO96HmkxGwHexrBt5z4uls8LYI1gVu1vNTY319qWrEB9Tr2"
    "OCI8WNyKjgh37+dnhCctJJKU6ro3rzckr8/sDZWYmkoXePKHlC5oHjwLNM5SRcjmE02z31UVePZ6Cl+jJ1/AlUHBk0d+s/Y3+/kI"
    "xoXseHbdyR/bfvTRY7WVu49ZhsGxXej3KBP6o4+CHIJ/VxL+HsyohwXK8H2FW8I5cBa2SbJ1vDtanBvj3LFc9LMGeyFh8hH5PEEy"
    "/N5Y3/lStMW8gBfKzlRNYkvQxMLm14ELvlNsiKTpINtiVKyX7xR7llvsQWthBebD71WLMA8hy5CovNyRKgQrqCQ5aQkRFvPcCPHX"
    "OH5mmFQVhzt+Y6x7saE9taOEtncYJMdFJ28Cp7ddqoEEjpnjOnAZwT9L7vLyhhutpJtgwsIgpobrcLBQ4auIyjh0W0mLEw0bySB0"
    "EeAOc6i+wh+wfs1Q3Ko6W5bxXvVnIcsy5vYzEDD6/x58+MHhkz88+Ld/J0g8NA8wWJl+uLyMf5e0cSzYKqWVV1tl8wGSCTT6xad/"
    "Pnjm3wz5tOvjU6b1RUaLPISZb6roSuVOOsHU1Qqay/M//fzTN5myVlEexxfAG3RjE4ZAAN/DRTWz3wpjL1UfcuCNLst2mfVSXfOm"
    "4huOefHZcoPWxQa1ETMGkwZXd7ztOuzTGnOvb1Ya1cb2qsCYYZiC4gE6fVTpr3yEXgUc454Zyvg/MZtbGmJhU6K+EjYJ5npBTDds"
    "v1QrR6CkSANBnq5Di1Uj99mVl+Bd/EIAmpbN0D2y50UDt1hS9nsWs3GxXgxRLYXnQ+yPCx7W2ZfgseQ4BJceTyhkAVUDTrhTRkIV"
    "xVD6Ea7s7Gs5HROW3bhyZNl9oLtvXh9mtsXvU6lut3DwU3M6y4WKwgI4s484iYQIe6I3ypVyZ3ojY6qaNn79UcK/9m3mGx7dDj2h"
    "+EzVe0o1JouCw3Q7KfoUzPUREWDLreTxe29/H/8x5XO/0qHNO+iPYfdeQlfHS3BvhjnCDvq1WJkfSP9iFmZw6+nrEfqvcAEm8xJc"
    "hj/AX6++h47J127oRqlXjbIrQZtcBakJKJX29gdRFrn3YvBEbMJuXrkW6xnLfEQPn7v12h9SFNplvZH4ra/ESMxXCNgdJwC6yMQ9"
    "/mUhfLmotiQitQ4Zp+MgMfDU55Soh5+h4wd2AGP338/ht702yIKY3gQ+e5Zx8Nq/wuWDDHEt2wHdZ3Q7n74wCgJ5FmC25ksZMZJB"
    "nKfWE0Vsp/HUhrJ8r6qdnglfLc81345Rl8I5iSmiM3fBy2OmEMdCwuIRNQmBkASMkKB7qKQkrojjjiq3LRRGy3Xpt9iwmgm/xV5k"
    "skhxqEs4YfWk+5yilO3qSbgb0gORGySaefZV5lxliKuwKgH5jsKqkLeo1UErWzM/4li5HuUazWhefqykJ1pt0vBG1dUTpVKZkkNn"
    "OZrwGY54OtikPmwhAkHpY+oNM22exXJ2uSMDkauyHHzS0SfbI2enoGFhyDoWMS7PgUCqVw2NJBEpYUDiDK+RtYbMxMKN1dsEIFbf"
    "3xd12HQZRchCY+ZUG4eGmeBqMw85WnDmHjcFaQAJ/wJu6hiLwh3U+ecF1FOdzPQ8UljkUXaYIvVfyKVBIEEpkjGJ9gtFvwhh/8uG"
    "ysxwjqfbfW7M3PsHb73CAuCU+Cbm5o6WScvya5GOCKFxittBzaqnyGYoHNnLy6Qwo8xBaBqxdWnJRpdnGzlWmwlX+/u2yijOXd9O"
    "U/D0TSMZSpkF4yUlKEV+wm8z3W40xv97CNyUXRohktBdlFMlYqCVtuA5g+MjvznJnh6BOQ0ZPVfYwvr/MGs6oweLMqZWIm1tF7HD"
    "Bez2roXqhAuYD6H6CGULB1LAg4aDCmZnXl4GJjJEwzflimfEhe8ZSlofEGD91vkHMJupCC8wgNAu3e/xCuXbQneQluSs4YQpURgL"
    "xSDMCtJLJghhJ5IlGr76x1hIWsbKApF4Hf2nkGC8c/j7dw5/8PwtKAmclgJpLUI6ykcbZb41tiYXgJEIYMFb5QB97Nm8cZ9mNnfR"
    "Co7GqqvKthrjH2KsPdcPRWJAWLQZ80+ALf6uOSHPHGI2MZiwN+i389vGF2//4vBffxxHa7UwyKpnckmTv1VT4BmEEEHlkkB8Su9c"
    "SlpZHMK0+KSFcou7wCUg9XK6O8BBLi/nXaGTcPt9VDYAiyl0Fzt9w6yK3kJBe0iPBw3XB6Hg9hu/P/gFqS+effnWSx8TBAquGzmt"
    "XPuAcoDdMCwmMqvLnEMstj7XAVqGyK+ByILMcwC7QNmSambZLTa7ISIlwz/FoRDmlUk8eOq5Wy+9ISbxXRWPmXvlgWDEerhIX/Ks"
    "pb32mAcVye8oyddSZpfm4w5nVxkHm86vfgbXgdd3/f6uXEgj7qvE0tNG+4+1x4GLERr8NzevfULo90+RV6MEfSKcomvvkpb2A7hg"
    "RZIdswwcrefXkS9kyk8RGJzah1s/ePPgmT/FfKEyhi3rjQZfg5MaP4+67jWMrm84MuQIyTEPYD2UB3ijm1onY5plPTeGFWo6Ibjw"
    "eV011FRFqR4kfPgphaa0mJYZaJBntSIdwnZgdTThhDkxBGPhS0iZg7ZCH3hTguu4CJQnb6BrUrHrB45BeH8lg8cb8GujhOAobgX9"
    "nTsYgoL1aRX1kxVZw6qxCqe7ZMjghSmqJBDqzrIrO+TPR3oO9EIBbukCXmfA0rKw0xBjwYhwImgz1Ol0fU0RDp1ZGlJTKH2FwHji"
    "z1a30lNKDIWSr4dCTOKnJfHTuMLWHF35rM2KsgGYZwx5arvI4iOHDZeqUgLV33sYmwZdbqfwfNag0ia/lhBDkM738d+NuE2AGgDO"
    "byvlBxgmMo5DUuoNxowxGqKhgFsQhtY5ZkGAh9Y5siC0KuPl5XHRc/YcVEsrveoOOqG7pKQNF6XKW/yYwShXq1swrGIPaFaM3Zwh"
    "1qTd/o12YyHhQvP23vbR7l2P4oru2MOYVZKegUyvJVkDdyzWNN/tNZ50tNXAV5WXfN3pPDnCnbHu+zHB8mXbCsvtEHj+OYnO/JRZ"
    "VPnRXuByiDtmtYxpbUmDwRUwigd5xKcOOJ/arg6qj1eNSxuHN65+8ZdP9JzRyDMdvv4bAiAh9d2Nz//MFFiUCAq91ykd75WrCWmM"
    "+7MTnEfc6ovxGaivm8GiPxflIEpFSVngXZm0GTv+vkKaET6BRM2Q+adVjajch3rRGwhkhxpP1IqqkAsopyo++wlQPONOPHihHsqG"
    "wrXIc9Rrjy8vfxtp60y7epbxXFHHKbuK76iHeo53IaGET+6dWWZwmP2EAlpHJ0yVhzL7dAGIl+gSo2OxTiHyEV9QHdUnmvc0i3nG"
    "LpnR1chQzvFPlgZokZKujpmx2cASKnW2uYLpBQVDFQ1FbE33iqGc3qvv0al7SkcDuZFIOH6dcAF/TiryFwgvp5zSxFewMWHMA+KM"
    "yAYRqjYIuns7DWP2NOQSdkfNEKGd4YQpgUHPRgaFZN51djhm5P0ZpwH9xpJqc4I4Q1Dlp08jkG+LNfupFDqzSCMOJnlwaYZx2PPJ"
    "LqzkTI+aP7M4OELbnN3FtH68r3ZUG4P0l5AgMJgPb+QCazRr1tmaH93GkjCxzLS8pGT8ydEu+UlCkXgjCwEhUzNx8PQzt199CxE5"
    "FQM82qMwC8YbihipHk6a4BQDGI+C1CF+yNnyp1kTzWa7EQdY+u+d7gZTfDKe8yhzPwSOMnsykR0n/dc5k4+rmRzXzMiuFP+kugYT"
    "TeSQUnbMGILm+tlNRQDv2sguThQt6ZDsyNZQ5hRdVOGsOliUh0xVw5N9LVqFyMWZ8FqK9Fq9wNGmuojx5fv7qO5WbNZSP88U3bgQ"
    "dJiX8j25EkjeGSREWLQ92/xqVoYFRlLP3z/44C8Hn75uzGSGu3awq4Vrdhc6AnOJPN1qPyOfNtohQ5k8YJ7jjOZ+AfsBtro5tegf"
    "MYmjrEmkqxP+FWo29qXuu+IjIn6a5pcbmWoOwcBy6kB1Ru6QWc5JZL4+fO3TnMErEk5w1uho8ybEcyJOwsEm5n8Vm02L5qTKJmvO"
    "ANQOkwaPOiynWvaaVwlTXp3Z72g+Nx66aMTexlVa9HWmG7uNIe7PGFHOt5oma86lZ/wS0c5KJ66+7iwkfqfmWQi1LZRk7tU7IuaO"
    "1PVRoOfYAEpAe/V8vpXUOJeZruLsavXy3RP4MD248mwM+JGj3JEFgDJGSWENceA16SvKyGplelGSukV4UYo9OxHIKoqqp7pXVh3A"
    "L1SGTEWH5jn+saZmwIAL9EL1Qty17ELStezCHNcyK6SKSrVopJEJUD/QYsjofD3XODh/pdXRRypMOKxMW6nutoYxN8KaecGdw1go"
    "61wxtJTaZ2Xv0S+5bZbB2uJdWMx3JNfv5uq9sdiGl/WEZSneypS0e8iSTWqOL+TAzH+I+RjPq/NLuBynipuq3zHc0UOe9WspudPn"
    "YmkucOaj1b+jVacIOAtkV2uzetSl3pRLrVBHS6go1dRPyYHl6MAsMLxZxCzmbjKIU9Z4G1spZCTuJX0BNcFLS+d0g/+5xKnt4Gyy"
    "W7KHB683Azk23Yo/jPtBD9NMfZaiJIZDCWXu1EvaOPjLDZ4Ym8uGb3AaLCz5wztwNB1qTp4X/lccTTP6sLA9fyh9TGtJxutODqXq"
    "OjjjXLKWyE9QsGmPhX1KIsny1ebunjzk5OUv5pRnYqxFQQ30Xn2I732pHhPicOYJeyDIy3aUiIo5iV0QzYgZmgLEMsL4QJ6K+0F6"
    "yrzJnBHs4waiFQUaSXfRs3YRPGbj8KNXDq69euuld4C+f/Hr39/6w+8EayLdizYiXN8nP1bUnMw+byBcolOkeNe+WpI77OPPhu7H"
    "GUedxCHOcFf17M6472oEb+NLC88DLZNRclTQqw2d27fb1sQNy0O252fnYdGr3zZiHmI4YTPMYDK7a2zemuSY4VDqZm2+v6ppgJPz"
    "xacvkEeYCLbIxt4cqsm3RX+ELfeMqU1e2hwt5pYXLpQMijHksiAc/GEx7JszQZHiFzOtS7PO3oxP/V6AyqMheTCQKuQrEjCHERm7"
    "9dr7RoI4pK2Z2m1g0gfdrh0gTAj0nDYVY5DESqyusaXIn7MuRJz+xcoTve1zwFTVoDSeUPxfbS577S62HH7OLxgrF0EG4PfJxe01"
    "Bf/tIjAL4q4kWnCRdGezXPG0TJzYb5I3HDQyGvv74gGzVjzGn4M0do7nVjdynz31Yg5dQIBJ982y/IXusAtmxG3OS5bGkMaOviUx"
    "RJC3uBhzL33Ds6MPY0w8b+C/L0pwAZY9tm15ZAnHK187MWWKXcRv6jYqS6sRYs5QdQMMFD/fBDbHd4FKdoFUOsUt+lMkVw142Cah"
    "awkdNBr4II9NlKyHCWchE93Fq4QcXTIvkjoJKIf9/V1Wl0lYR7vQUgutheZEfoQxWLtFp+uGssfT+xHhcRFgF2iNwaZ4bB1mw50o"
    "pQnrxPounwMc9yJu2f80VNO+NpQvdw/oi1N8YuCG2cYs/NUfZntFzlbSpSRjVHM3/urmtV+QF9XT9FlE6OhxMGhcUGATuaWQm4go"
    "rwGadH5688l3gZo7I4fZ3r/4z/+iJPM/TdZm1JIxwMhlhT6Bv2r8GH/mFOnDg/0WA5k01WtQ/DQVxbacJ0wFvC0tc4DdQ/DOIVBM"
    "p4gIiPAq310ISws8O3zDZhuBDVwKoc7iBwM3gLFbQOVsy6GPwSgln3hbXfaR+qWlfIGudQmQlYbPPqrUzNbzcLKeIs3F4HsBkvdg"
    "Cyvk5GHIas/HiqJzERuAlJcuqp2qixTE+kb9rijM9yqOmD24bxh78NDw/9/N/727eSoplfjA0XlkHje4g7pOZSdg3mlOYId+YFSB"
    "IwqQH+rgdWCsz60FuS2oZH2nBdR1BiGtM/hjBkXiADl3uKNnBE/mer1BaGEpO3Bsg3zc4ig9UwSSWl+EYDvK9QEbnKfOiqVcWGe/"
    "4BRcWF2jjV8Pg843nTES7j4mQ6TP26hdMh6H/+rw365Ri3Qnnqm9tW0g/GY/WQKjt3m9diet1oH+DoIjJccPq5xAKeKTstOL8Jhg"
    "XvlCfWN8ETHNfYRINuHWAlE0yPPTT2nFzfVLuHT3HuvXA7cXnv27XO5e4glygdOpGPSx33ac0MjVA7/f9wO35Xpny1glgzWkLSB2"
    "UG1SKLQKO63yXaUzpXtK59bxK3BeTgeeXFgtra7Sk8B2+075rtVTq6dXWZk25RkJWjt2fu3kSUv8VyydMOl3BjGVVuAMK0DbJ+33"
    "Nfb7DuWEmlEBK1BA7FivlVJulVeEO7R814XTF85cOCMfFNbKd505d+bCPcqj4+W7Tq2dOnXqPj6AOqxH+a7jFzYunDmvPCqAmMOa"
    "O3XcWiudtlZPrEFrctxUpuN6TrLQSVaGG321HojMTeW7Tpw/d/rCBisY+C3EioTur23cc4I9JNe8u05sbBw/w5aCjMDlu85/4+Tp"
    "k6ejJ0of1o6ftM6cxv8VT4g++L0yRSTn1jA4mYqVLPz/4gmaYNgTQzvIs+3BHqzJJ7RD8GHdDhrpT2GCV4+vnlg9Bd/ZZhHF6BsW"
    "w2wP4mE0t9QWW3zZAfoa/bAW+4VvAizQjLqNi8oeQV827tnYuA83cxexFrUyBdoouKrJp3wX6L2MfsDm7iqdWj1Rwk0T4KImi7Yb"
    "QWyKpgTtiEgqqGQstwK3sY5/oOFuD3MTFep+Z9D1+uW1U7g6XddDXEYQPZuBmYNLp9vLHz9R6o2stVPDPevEKfhoxmrALCvlE2fi"
    "b69zyWG1VBq213fs+m6L0Ja1xa4jeHNsHptwI5RPlEq51eO90bFV2Eg5VqBve332c2GIKjT41wOyFrj1cmjvDDp2gN/76z2fZeAs"
    "A6GykTis4z5odvy9MsOiZrOSK5f7hG4HRSdK/+463qw3zzgn7+G9u6vZbPI3mNg3oS407a7bGZddrw09CHmBYuBOKCtleRWmU04B"
    "fm52nFEZEax50d2dxiQa6ipMHxslCp9pE4PbpAs3o+sVCNprrTcSjbZ25Aq7Hh7GAja2bsNd7RVIr1CuExbv+uODfug2xwW6daFt"
    "/rhl98qnov4eh1VeF5AC0Dn8yvd/YDfcQZ8KU+dP8nXSlihtVflBw3H2/Y7byMWPnLIClDmrZxPw6V4bBlCAb3UHZm8vsHvRqMvs"
    "uOt4hJOUrcYJAR+D3j39YEeVwxXrptUljltqZeJHvnPowDb0Oud2+q6Ta4177tnRG+APlapQ18D3mr5eSpkdtyUE+BOxNT3BV7CA"
    "iJ20Q5X32nZ/kjq+iN4rMyWHMQHmo+6G43LxBPyKIWsTIhVAIcqrxwqrchOxU5G5FcRmpl2Mf4BmBuyglhm9WgdSU+AjK2UQF+jC"
    "Xn+i1ZVyInDrn4m2PtKx+DTxXu/4cPi7M7qtnvC9fm6H0Yk9VvGpUil9L0PJYn+wM+FnG9H6oCRUWdgBbncXCgZdu6MdfXToyKAQ"
    "ypICgUhpMU4L1+lN+dDpdNxe3+3TBLPdhRuqYY/7EmQEa87RH5UG9Z2WPtmcDpZKX0tbIOLKFiELGt05raxOrHFJnHEVVsV6rp2R"
    "C4gbRavsJPyUPYuMtK0VT8aIWwYJjfYM0kbcVVh9OlFL6fY22YTYfeQ0KpgqoTZJoaPaq0X4AxPZmOCmWaOB0hZdS9DrWF8icoXX"
    "I07yqNBv2yAgqTcUbyT0YfU5pTkZnZSTyUbSV1ownNG55pcUJYSCttqTaL5X514luD5yJyLPsgoTjpOOJMeJHfh04oGrs6adc+Re"
    "cKfIc0BHTCMybF9FU7MIU7Wa5KnE2YXfC4L2AH2kzzD4NBIlUkbim6LLp3mHk9dytNnTL9T0GaV/qe0ykhh2AmK8TavP7q7sGzYq"
    "WdR5qviGS9/ZfUynPblzmqXSW9hNrMb6JEYTUyeAlQ277MJi61NeO3ZC4UbXkBs9FePTBId3KpOWLHoBaZstybBS786irWJCh0dp"
    "WPyaKyIE6iTlxub3AmdZlfMVveqNwtibQiac9XIThH315qI9yvckfs+m6/IIl/hlok+U4EjVOxUbI36j6Qb9sEDKrok8ln3HDupt"
    "3pmo2lxp/YgsQIz7VS6QRW+pU+nUll95mfuPBlAmdGq4esO2602OwrGy93PUirgFlVs840ZMJxJy+PMlNI1c+4OQlAGl1F6VywSw"
    "2SZT3yRrHrT3iiNpgSJ+hsayphHvuYPJuLGz2hcM2SLbRl477Ym+oZFOHIV3zGRhxWz024LBUedj8UmYx+jEL14c3QmNw5I94LdA"
    "Og3fsYMEDV30ACp896kjzJ3OqkIHYP3CQsi4ilM4uDgP91WxxbKt7mTG/IrbQ7s4UmUBVl8vImpA43oLbcTTEf1aO7OI9D6XpKm3"
    "ZjGbVU6ZSpVm4wBAEsqiIvptjYWLO3ZjruyZwT+I9xMNsktQlGi43UziQwWag04nvdNiREgg1rLuSznsopPVD3amWH9DjVPSzuwg"
    "6MPbPXRugnVWebLE8iQqXYBXY0PpeLuTGUxhw6n7AVkUygM0EuACsF/k1wJLO1M+Tt2gDgCjN1EvH9oTsBmJ/1UK5YpNb3L0swfi"
    "8KggLoMSNUtnhx0Y4vr77cD1dhWOnZJcycNEwge/T84ouroTidNyzz33zJae4t1P6B/1LhT7XS5NnVAJLMvB5cY6GClRv7Zot1Bt"
    "b6rSd5STvl+3O8738qxkzyqZZvRjgRlwiP3PccpCP7KxyHKcUDQGQeG4yb84dh82wUCKp3ftPOBLzdPamTsjQPNYE0bZMs4B9SCH"
    "xKDlHFEQ0Xj6aM+tntJbKxFRTBIxWs1enS+xolU9lSowp8nEEQVNW19mQjKjpor+7iRrHyilgkGqSKaSLVGUaHCyqE6+oBx2MYt4"
    "KToF1wPqkCvR/0d8hjoS9FGYLKj2kyRAEZigCrh8FhHJdWk8RTYn5cCJdElc8ninBI93FAUh6yQQ3J0jKzy4iMVbOBGXlmZyp9Qm"
    "XCUTjXfp79m9I89XUi7FauA23Osxpg8N9OXVY6vribaoUBFW2fbcLrtO+nsgEs0kJzkYcFt9Hx7qFcCDXHHtRD/9zf9n1xk3A7vr"
    "9HPU2KT0NamjLil0kT7hsB/Jnyp9zZzGXsRWQ3/emwX2Kp/wvbafK/qTNCPJAhYepiE/E60fVef5k2yGcr7FaLWk1Yd80FomIyRK"
    "KSM481Vx0aL6MMxgPMQbBay0bHvjPWB6HPGaN5ospPxW9BInvowuHNpF9ydVpk4qajhf024c1eJwfC1F8kkh08zkvbAt4qgaVcGz"
    "gKhc3x2vMzPE9wuU0au8RiMDyuW0HC82QlJcZtDLuNFCqyZHyqxFZotd62hnniRtuxE5aNoNpzDoLUJRqLJiM/C7hUAhKOzBESvo"
    "xCvoLFCBQmB4L+aRpjzyUTpp4s3PfbPAXxWsJvS92IS9PblT/o5VYRc8Z08ZPKqxFyLoyhDYOwvQ5UJyCHDw7H67vONAWZS0mHbH"
    "MKLNbO/A6RiEzjpxILpy5K7mWv2eE/W1e9a5fFVgcRCM71KWFBsp+LnV4qn0W0aekgLIGpjWcJLK093BvdcKE3Mc2qhHhCtvrT/n"
    "pbLdDElLs8i0aGypEDEVDi7Ju3G9srL6QL9yxXuS3SquQl9polImGvubPNTqDmEjztohJNHki/ec0k8GdkZ9pXg68c6qOc240/nv"
    "xdO030hS7fm9oy1CQgZJeftU1ttwO6FVL7leREhL6wG/fBiRzvRRYD5Oabtb7NjS0SQ818NOWuzimlNKO6mtYDEtFkl0QhBfu3ON"
    "IFecNJh3ZIpDkJiA1Swpc9BHDTuZY3WTKB/OwpYwXr4Idc2QQxPFPcK770xmLy67h4DPDBpc3kRliGrMo62i2rMX4hpVDR41ENSH"
    "M2QWrs0oxew14s2isADH2DZpGFbLcpfFTL5UFiQClKVfk6Uw/2BaXcdlqTtgqiPxPBJzjqu6HFZxdxLTDnwJvbOmP4tpoWWbfaVp"
    "9jPrudfdswiqRVRT4tVIJdrxU19Lr8jXK/JFRfrAY/V+GU6bmgUS2Z9k2wPT5iHRQjS4E2tfExVDNZFynZ4QUMZCJmJVF0THbB5F"
    "i9udSKUB2ztp3Jzl5YYUoWf3Q1xVK+WhP8eQhkXxFNCuiGt0iT8J20BgWu31rGOiMo3IcDHGIslKrdpTVArpd2Wvjh7AueLp+SI6"
    "K4rXdspdffxkyuPiSbrEU4pPi37DD/upfpE4/ccj+ZAu1RNCxGBko+WHlkpFSA+lPtkZ+zOomXCAryB8UG2GnSBc1HFT6FKzbNNz"
    "TM/Z6s7ZVsDUfSlHB5xNLYsCy0J+L9WRaf3O1YYJ+7dsixCfZk23KIjh+bUMLUKWzxZi8f5tLxfrI/IOsxxX476plAVhEeXr0f2J"
    "ucZEzABxCHP9j1gdomOLGQ+Trqw8t8OwNVF8BlTTeSq1iylaT0VVodVGNcak2B0aTigsl0zflsmfznAzi6kzNEFxLUtQbLQbE1U3"
    "vbhGuoH6mDtgge7Aq4nZ6bDB9ppimz9FTv7HdSd/7sXDstmR40fkEEt/C/iAd39nnHUF0s8tfyFXvWZAPEVkBDijqxDZvuI1ks+9"
    "6lkd339KOXL1Rs9vc6Iwyqq7Nt4S0nFJujSWUnykMo1mqnFcJzFn0lyrSNBSl42ZTEM7CO9QoYZjoPAHZcqYPRh/Odtwh4t6Zupm"
    "NzE/uZ2YZTRpeaNipFRczDc6vqXsTgdraY91JzK2Fgs6EcLbRVrO7EuIdNjA9fQ1Pxnyj1caWc1mQ6MJLpxKkfaEzgK7UdddKTij"
    "dvr4LAcKei9BdhPeDdkTjcZ4YI++3IaOxVvN2dMz/XxZf2L++GzL4POFdwwj8eh1Xb9zj+VTuscyIrmKmSrJH44+UWkzlGlF4O3m"
    "CC825VjdQUhS5HkuKu8FjhxYIqbrZCaXCa+R1Sed4pNUJ2/xUtxjmyzJwW7/KKRGVzGJGoBwZwugzCxFvUxefUoNuaMbermbfdz1"
    "tdGJ5jLR4UYHCO8id9w9pxJBemlGm+jKPr52BKUbvzNZhxrhUYfO32tEA13QxD1TC5ChTkmVa6j5Im72bHZITDdDvpyovWK3p1gd"
    "Inh6aZwU/jNRb2X1RIFGzPsdQ3/Q85kaQyNkgcGyMOVTYkcsShRP9NTwHNFAruMupKVlDDZ7Bd23UnyNs9nJO16gdP/w1PMnwtgi"
    "ln3tlBbfhrFzkRuW9iNKhgmHtHm9WUAyopcLO06452CF1HDd7tTzuAK5Qg6PmuR71TtTHMUTWV6dR3JLP4rImx4EghO0sPYbC5MQ"
    "NsfOsJZtacQq/r/evqTJdexKb9+/AqoMRTyWQBQIDskkVRUKq9W21K0ORbTctqJUC5AEk1RyagDMl1lsrnrphTf22gv/AUd46d+j"
    "cPhf+J5zp3MnEGA+qZ5U9Xhn3PEM3zknASd6uh0U9ZRHjCL1lK4KDpQWvuY8QOy0kaYNclV8AKzdi/O2kv5MsDh/RG/Y8t1NPKTI"
    "D6l7Y8V4jOVJkqvENlCrvYyCYtlkLshA1/WF2ukpYnGXn6piJv/iEkLrOqo1zznuiHZno6i3bPcLsnXPTtmukK3ileJYnAjUtJ9m"
    "l/UARmnMxkQPNjmcQX7K/x4EbHtOuoe+5o0sT9XF+5CobAQCGpCeIRnQ8XRp0Z24K3BdKQE7QgIWWipRaQLrESbZi9bsF9/dxWuU"
    "FJc7iE65JQAsJABH0Fbd1pzCZrRMeku0Vu0vYaxPpjrd1peWjwYle4nFZwPhq7qIkiMRMw2ImGmgR3Lss2lpEBjzMvtj8xJCmVWx"
    "C4lceQF2c4cMR9WNBc7mWi8IlYFYoo4wkxo4qODmR+u119u3YiVtegypyMjPvqB3mN4HmEYiXVZTfDz1lD54krqAaPbhEdpE6kcE"
    "PqOdaI6oN0Sl20iGiMJeRgL2ArWjZLO6m/OccIvR6KNQOPEq43C2dWu0G3llbtnZNdMrvZumTmHzNK9GDul258O8bhpipxS31nvd"
    "VltWoAlo7lrGyTbw9gjdMaoQuAvxwOl4flWclHDaf3KUrRQRrAKu8fjsgZmU6vpCiMl4ok3LB9oKj9H7n0bAg8dP2etnfYbGJhui"
    "vncHYBjosMVD5GEp/prXAcFqsfYKnPHbUtCAmxn+5QgG+iW4NPPpkKRHGnM7yT2TOV8mdTmihDTAGShGZjZjdMLiZctu6iVg0hZ5"
    "2a835/3C1NviP4P8+ot9sdrm0Sei4p6m4Ovnwh0I/XiEtU/SqTy8knV53UTfRJAB+CvZiNK8D4YT0kjA8RBwPhYQfyhseriBkmW5"
    "I0QioOVCUTbQeKrvU1msi7Jir+DqvCxW7EnFZYz4bzYSikXnCt0qNuCgxq9d7AAeY8T4xQpnF2uIWOzivmKUGcZcOB3rNzjmRzd2"
    "Doer/0kGI2DND0Ve4jb7yXZ/OpZ1DjpJjhSLLRui2Ga/4gbkJ+xo3uFgX4Wx9jAaltL/Fzae4HAs7KGuzdfMAQdgsoFolb0YeHsN"
    "+1yoL6lix4rOy2MmLkYv1keAy8U5RNEpRSTn3hLEA45wQhd4LZRJHi92cR/9cW/uW5FJuq/mLVBj3LGQdxCmZ6vhYvq4IP4cggOa"
    "NozIwcKJVhpeP7I0zuRjk2QPvECo4yoEA/Ekw/SFYCBOu+CMCNoOaPmz8U+bYHqsl0BFshbiA/Q25wlsK06rRkB1oGIfUSejhg0o"
    "qYSE0XU3IYPHBWMTFn1icPUhp2HQYLJlgzwzvkMYrAquRWYdX0SPSOrozzu+IDRoGATCyupEhRrgoSxvWaMif1wvH4d0/bE337ZK"
    "Rr25vmu8G2muZSZyVAf6JQB99nwG7R4BybHRukbop71rZoyMgPeRAxiN/bmY+RiqmnGLgbZvY8vrTF4bLe43AzorT0bs2xaxd1rx"
    "fWD1ISxkOwSxFgYIP1WtNY/cgeUoi7N0ED9O0ImmSzLepx3HD0D1uOEGEFJRNe6hd29TyapdR7M5D0sReI0uOk8OnCwZ0UBEHH70"
    "jOZrNbRR3AnPZb6Y+ylf1UGzHMWDvxbjogJNVYpDvVY/flsDAs0DK0PnMDZF7W2BLaK3hX6oCQB/lAXunUsnKFiIkyHOXnvtPXw0"
    "moEZvgXMMbcQ70P4kwNCShvdKUUJ2IuZRbh9esCnkAfWIUwFocPWMiu/AGx3BPZLaduFFsWWWNJVWOXVpujCUIaYVNk7I/I3nUSh"
    "Nmy/k5Uw6XXd3ThawaEIMKqF95ahki1gz+vD5UOWl7yVw3nfFaOmK1d1Wx9gqgLY1Hu27fWhKqpfIWBSuSGcihflqh9C9H522z+o"
    "37PfsV5eCDJcm3XQm0RtYn4FjTy+gAzff2JLo2zbvFrk3d14q4CkYP4xctFyZuLlCMhbOgC/2pXFhTnZdNLkreWbdyprVxUCPuoC"
    "NGVzUxAZU1ubjcdzhxQmhc+ngIsb7XJNZIvVJ+8fq0+fScvLMCl2JpvIUEEZrl5BRtEHtBZfyKrYrZVKRFVvufASWeB1UIWyZ+4c"
    "U+EWGrHQD+vH9XQ9HYxubd6Qv+E3OO/Qt9JKiht1orz5GXfqrqjBTg6uKaiVpFmx90nKQ8pLa0ZxlSxslXWqHR/R3id8u9tZdLTq"
    "IqljT+KLxdj5gCJBYkEafzb5XaZd2T5uDYcDeqeh/wKy3Qguw8LOWiCHiNNK5NFOI0oQWg3Ts0F8r6CQ8JuvfxLV+XYHIrMl48df"
    "R8kwGUb/Gv3217+P/mHLdjG7+/812tT1qZp98w0pmiyP++jrb37B5pQRneyUnmAPFNXlF9X5BNKvKvr06ZOUuG7eTxvWFi5ajz2j"
    "7F77xFgpEIxyTVq53Yul6bF8dq+xuvvjj6BwKnAJMItU5KvFGJRPIJUEhi0qo+dowar3Ll/HwgQ65mK3eIY3Klq+9fv15z5HSvTf"
    "WMPsws13c5r67k390UytXorPdn1Ms2or+ggwSnhSefquyHFJjcJ055gta5vjh5T9Q1PFhekpz47jaZNzDRMmI5UeaIzm+Zo08u2G"
    "wbjYVwnTm/oLVSS5/uqYxY213R657F/yjWzPO1nkDXfy/B0udmdrjAt8PA4QI8JIh1e+zCtrYIzbe0fZiZm8ORdih9kTAJeqmSYf"
    "U3Op8xokkVb1qjhtczMJdr9m1/wZvqWg2fa60zy8rkTN6/UqbgYMnXPBECgxI0cY3dnX70k2LtmD0qf7nh2Y3Wr2iLMuzki/5hcW"
    "Kz5XBtUzw7y6N9cShpklcID4Etzque8T3yaDceUvUm/30LsM6jZbnhfbZX9R/Lgtyk/JKI7SOEqyOBr05tTOe+YYfsvs6kSiVJCU"
    "npqtc73dbfEaTSTQ6IKqL0h+V+Cja4I4AQs2cE24p5KL5bnkmuz7qeLx2C9G3FKbBFRciWefr0wv+joCO8f9oj+4mCyUWQ6LjKwi"
    "/vZGvPC0VeGp6DxtVXqQQnFGfTB2zKMRRkrDpDvYBDLC42IpZRkDaLCE14SzYpaejT9GFkUhk/tGw4ZUZ9MfX6iu0PmOMXwGQI37"
    "4G7xQlDHApMKgnqUez1j/IBrosSKRMDImyWPXCxlcOSJ86T9SNP48+aksHrXhMv72FdxbdzlLvsso5Hz6XKXEFE2YtnXHsNYRnHg"
    "rPpapX25T899TRiPwu6/C//PjKcpoNbFhmwhk9DnTMLFD9g9sTML7EPKfwzwh336ICfDHP+OykSZYUOZoSgzaigzEmUmDWUmoEiR"
    "XqrEwXHU/8jIFCuMUmRhSHmDIEqThfAUmIWGySjNplkxREyeLAg2HP7WYAJ4xsWgxNS2pqkWj4m0urRe3OoeKKOgrAYXz31GcfcX"
    "zxdbmydLYq4oGS4lSvD58ZeBPF0qayqW8XKM923ok+fykhApvqGoyOZlDR+LRrHjiyzR0BZm8nKv26ZOeS4vCZiBhqIiG8x+2Z6X"
    "bFN435/YldxcaoylJjdKwd4/vbGjKI0Z+MXfcCpZ6WG70kNemr2FrYrjY3h6J2PBF69pKO/sVW5TGF5llI2Ji8tjoYyUnLIX8eCV"
    "RRGQL1yCTvSx4T9+DxL6P/5wMdGVOjf7I4g/zALC8FgVcfJp7tDOHdLckZ07orlOz0a/T3buE8nN7FFldFSAATRyhwj8kbQw+hc1"
    "OMjB3Ih+oIsi2WyW5bNsFOgZ1X0FxJIBYX5x2FRewSbgTaVFoMw1QYkKNwPhAhUveBwnBq7PtQkK5Elyu1iZOgOuNyuTJ8kCeKlZ"
    "JUSaLIKB64wCmCKz2VVm1ccUmQ0XmJXPk2QBvLasEiKNFaEeSWx3JTzQIC3BuADOjxW74pWRDVR+IEgXzOi5UD+Ly+/FVjJhx0me"
    "yzrbmU6qSADS/FxeNHsN//oEXu1AxFerIIQim1KjmvemqZLzpmmK76aJmuumqZznNohewVwbacBa0wTCBAN5rDlICikTEjLk4Y6l"
    "g7cyhPqxxDDyX/aS81QQgsagdnspYvmhqy3GRSyPeyvplY3YTKmPsRAnxHofxIqLiBVkIuaTJ2aLr0ss5XpSqtYX6fZvwQfFQvHR"
    "17xsDKQhZJnO2OYN/LeacKC9xWa6zbb3/KgtvXoiJdygLNEDPl2uY2SwWJfq/VDnb7Ovvv5qLsTFFWNkdoxV99d471zjx/Y1OPPW"
    "sXyHEVGaOVxrLmRB/dd8dxayT7sl8dC075o8Ih2+Dzd365EqwZ+/HX7+uvbORWeq1s9ZAaCZ8ufiuxvDQd7fapNe0x//Llf02/7r"
    "XLHwl/pGLRrucFb0c/OlpuWeYTjP5ccHo+XdHWeDysL10uyKw3O9ubUsaVOLN+bEagpDxja09qXmCSmK9jeZIiPa15FERvsaigRp"
    "X0UTKF12HZAv7cuL97/DTSaooQ41gFZqX5xQUndV6npOHdXGl7q7bL1Iw5BQNXLhrO/sq18DLfRV/NU/Fc/HIvqPv47+GaJgLnZF"
    "9HtGBZIM9td/PNbH6J9Yteg3vzN+/vI3f8+T/sO2zJ+3B57Mfv/hHP37Y73ZLnkDvy225fvxq7h6r+pi3z9vYxgEW7RyC2ox4Ndn"
    "X/2mqP9dmbObJ/ot+81q/TJnexnQs/L38cDe9hza/9viT/k/n/kgeO55i80gQxerv0G8bo46AhEdV0XjPHB8IeqMvt3B0RQe6frV"
    "EtJmmMYDpD+sh+zPQARHfygW7M9URkUXZjw6HPr6kf0Zq3DoD+tsnRVrEQf9oSjY77WOff5QjNiflMQ8f1hN2J8BD3L+MJiyPwsZ"
    "3hzGMZqo8OYPk0f2Zy3Cmj88jtifpQ5nriuTMOZquKggepgMJxP8tOMLKz/Jh6N8LgRmbCTL9bJ4nAsek+WPp+kQtMqMq509pNl0"
    "tHycS6ke+5SUfVsxl0wvKzGcPOXQOHCYrLmnx8d0MleyMzaYYj3EJgQLOnvIB5MshRTGcsMAskk2mUuRJlQosiKbS4589rB4GiwH"
    "8M2MzWUzsBzmxWouBXlsSKviCYfEuWD2vatsunqac7abjXD6NFhkcyVunD0s1+scawi+nJUpHkdPsEIgEIERsj+5+MkHNWJ/YMXB"
    "9Q5PWa/ZJlEpsEtWxWSayxTjS5USeMCD+nIsdBrDnyQd9WIE7kSAPLOzRNh5vaiMh0Dq10yCtSXbtO6fTmz9ipwt51KkvBTvZEWx"
    "zGpNFgBSXrergk4ypOXnFUx8On6aTJ5E2nbP7jI2k/k0T0ciDUySZw/ZeDLEeYGk4m0JJ4JvOvdQrvLyxTqTkCSOZLpIi0Emj2Q6"
    "TfN0pY7kYDCYDJb6SA7GbJEzfSQH0yzNcnkkWd5kOCRHclBkj8MBPZJZPhyPMnEkiyHbU6k8ksvRcr1a6CM5Xecp7ig8ktN0un5a"
    "kyOpKpMjqb6FH8nhdLFaT8WRzBaL6WSqjiSu/2gYD6ajeJCO4mQw7unzOV6vpk8TeT5VO+J8Yt3xhNV9irPRlNXFDSQP6+NqNVwv"
    "1WFdj5+KdEEOq0Doj2N2C8SDgayuTu56sVhnI3lyi/WI/aNPLq89fIonU/ifGLc8xevp4+BxIE9x/jhdrHN9irHuYPIYD1j9bJzK"
    "2vJML0cL9uXqTGfZalgU5Exj/eEoztiosyF0nvXoAZ88FmyV1AFXQ5cH3B57Ou3Rwz5YDfJ0TQ/7eDnKcUHVYVfHv/Gw6wOtdnD4"
    "QKejbJAaB5rtw/xxRA+0WlN1oNfLfJyPzQOt5o8c6ElRPC4ezQOtPkIf6KfhUlcVB3o6Kdb5UlEbCBidAWB0LtSks0T9fThLhurH"
    "aJYlo4riK0wcRJbFbNsN2Q4mMAirzHjMJpKVGo0tqIRZbALFkuGYNCUgE2Y5tmsGCTtmkxEvya6iPYZ7hL/uV7Mn/leLwsDct90M"
    "gvbg30G9KGLGSaGoVENw+aRMzmYCYD2yb/vBVBUaskIgqo+mdqFhL3SP3mx/PG7R/gR0VMv+7373+4up/8MdiHl//6s/OHlsL/J6"
    "f/t3br3VGvP+/F/++//9b//HycYtigX+3//433/+n//LKYD7FQuw6n/+t//qFMDNiwX+E3jqt7NhH2Pur2D3Otm4p3vXry9eSOt1"
    "U+938eK4eo8fcLtTJ7UKBgP5LtZ58WxiZ9fPAgQK2h/HS58Ug3Jlzf4ItDUbSn4A9mDL9u/KMYDn8WJjDP4b82gKKOCFMGEXA24q"
    "oVjC11SzUs0O4MntGvP9wopKCw9D71q9PifbACZUo2vnXLrMDl8JuPdfQjMiTaKw5U+QVi/z0wynkib+6bg9iFRi5lWdzKhn7Gc0"
    "IEbU7BEAHssIeoJ1DFtB4e5qOOH+rq4eA3/lyYl8I6jTWvkCoBr+zDZtoWYx2hmB4babiPh329NMaViPgf7RpD9gSysCHXeAnU/C"
    "8bQyN6Bn2NJKf789M4hD8EVk1drUeYtwD36zB3iaXHvzKw233GDWzQcoTLNEHVlQ2ySMlE0Cawnc8Rw/FytRHExr3RZ9xiqKZvRa"
    "R0gLON2qf/BC4aUFUp8GSBGFhiAbfEZMZdBzPBmPu5145XsmM1nlh2framFko8oGb4IXDa0XYTHgyPhNYWQ90z2h7fhKb2FQp4tl"
    "NfyD8HvVShMxa8zE7+t8gc5ZfmjpYQRxYz7vItjl9/X7qfgWLvIfYpJwOMMN/INz0bvORDufO/cAW64QqcNou2PbyfoAPJtQh0SO"
    "BSB/BBFeQZ5BbmsmQG/SCoTOCGMRly/sxjNmBcZ8/OEiDo7ntMiRjMm1PSYmD9ddvih2XW5DoA5t+878dCKkweumlX0xYwTaWV2P"
    "HJ/FXmtI1t6tEIYqgKEnxk56BRcpx/ahpMgrDBWjBDzzXkjcGupcM2CrI6vuasPW5dEKOoDRgL0mRAZghfGNosGQ82Xe4JMTXRiM"
    "a+z2B1PWvk0JzW0P7EAWVp99NuaeSNVYuCH2zsDrbrf/JhxPyt/v0rDTszyaCuDN4Corc0puPYrD8NE4Jjq5xHjfHY4GNVQFczJ0"
    "YdcqsDZHGDZfYD0nLISPBqB2eTpGEQKfSu7xyIyd3tZWFiuDqdIJo6/rCOlDy7WecMxolMdOteOmESmRPz9f7OtE5TQYI859ECJY"
    "WEAwu17HFDofPeL+LEJojIh4R/zzkchTE24JKwcNDsnGE3RIloJDssa3pOEJMknfkeknLOVS0DH8C3VyaTpaUSd76hOjxI56dyvy"
    "gmzlybREN6hwG8BHOvsZdCiqoLdG/x416kTJ6lhT+wjzCyrTnerUu6iOywhVXdhs3/CpaW2NKDnJag2V8Kbze5lU7RQ+BJ07Wn7m"
    "uoyVvg78JDASyYuYzldmfQXjYyThockqHXlX+wG44mrx3U5CCE+9keWd7Y9TRkbO2vKaQB9fem7sT+1KUUKZofriXHnkCnzsDU1o"
    "5DKOAebO4UTzVWMTCmFeFZZHQY+Yw8/QEocFBr9ePEeCA5XkuZ7gsNdJ1xmEb4/rxr8HXacIMVmsvq3Lc/HDJcR2WkIaY16kGFfc"
    "RoNRQAAXde5cXomMEFzUh6qtc3hjMj9v6+XGAS37zpRhpI7XEK8cITFtPfwiK+FyBMJyyfdn6nnXfc+6uvbdIKGEVwe7OdIpCk/8"
    "L1iGZCC7K7WjTOddbHFWpdC9Z4+ice1HK3PSZsiRFKufJY68hdguNNSQ3+rzLjVA71IPi38s6mSTe0Jz67w2sYjR0yibHLX+YvYe"
    "9eQ9tps7LvZLjqeqLren1h5qDS5wetObuXKB7b1uNI1nk8gufl8M9DsjHvqXoWWnt1juIJXkw6aLgYLZfzMVMPDxQpNiT5o4npTf"
    "KkHNGJPBC3QkIGjdxhfZ99rw10Q2wa9GVz5D32LdHcS0t7lDK//eL1l1IIcIyW/GxrnBOJDePjhtCXAePmC/T1ponlNwmFrGSfkG"
    "TlDwhz+OurhTqZR74hfx+q/6nuuml44AvKeSMURbi0Wn6pXQzbPID4ei7Eb7GyHHph6fde7DIW0I7zzh9tmjzzb/Ah7JLLRy/s8X"
    "xmu8Ptsfd2wmXplNf61i9YokD1lmRXsIeWfZ51sjUI2Kt2h6xXJkWSO5HKgt8shL8tMpee1DaJ6Id9LoWWsINEo8QtfKps9j2dLi"
    "yBanTVOyGjcHvYPV7c0DRqSurYxUEXtnrsGNt3PSuBznYsa/9CzL1XAUzvckzE+1OX72+xEPejGfCi/m4gDxt3xy04v5MPVw/RPK"
    "9adXj09vd6g3HH97nGaPhOftjlsLasXDqWdrWXtLGDR+ZMYeoZt4PKUzlhkz1s9EsBoyZVkRZE18A2xq7cn4pmRV5p/xyoBfbGJU"
    "FCDBTqBcyRp49LNIkrDaX7ch7qA+KB8NJQP+JBdoiheo1kkAKfOw2hT56vKxQFG2aiLqSJ02SBhcUcZpo4MnZcKrHXpfMsq08WDY"
    "7qN4J6O2HwOdQ+xYI6ogNVetirxcbloT/FL4P2mjlwqLD2QwroDA2C8FgIEKxvaWYMGIOmwGVE5VWAnuatUxCT3CUXAvah2/UMj2"
    "I4c0EXNlKtINqWSHneew/GuDRxIDtYjuoSXu5K2QexLdhJR4yJwd1WWkgZUTbUdJOWi7pXSVnassCmtP7ghWKPqpFy6VmZJcm2LS"
    "tzgPeieHm7UgVmV4SENW7EpTeYsnX1jRNhyMavxDcWrmmhQp6x2NqQUX+zVZHmqfjbTL4722usNtblxT7BZgpN2GtFwazXkcOfXO"
    "NhL0lAF95Wvxul2a5tjLnhWhRRb0xnL8wC7FdjnkImYEkfoRBFwky40dqczZI/4wDyigWx93q++wjRj/HvH2HBRVX0YNrNzlvRng"
    "Vd2ZjtBoxKP3csxRGCrkvw7FYKKkOjhOFb/sqsh+ihNbFIjhCeGDXDydKFbvWgdRcyEVgo7CmwHbSyrwYu0LFqHYv5VPp2vrxwXF"
    "ZV+y6gCKOMoeT7iOw1fuEGbuuw5ckfRzeboYajpY8yfJH37stPsEzwZIrML+k80WqHc6wcORGNut4wXV2SvrFqh4WGhQCB7av3a8"
    "/D4UAZZu4Y8E5oVeIJx0SOhoRESEwvnz8dIQps5WhGGdfVHnN0klccJvvItjK0peSONhHhK5hnBEwKQOZ9Zyh2A4v5i7Z1ZWB78p"
    "Cvk34ennQ4kH+rB3xfENkrbu8nd2enqGXOYxLJdhL5xX5E1VSDX4XIaojzXI5ur8OYHfF8cHU4XuT2g59tN+5nm55fH0voWgHbqs"
    "SPIAiKECDIWWRs80njuzFkIQWpan2B5RRGmr3ZXdrmIZ5KYgZcHDqzOGoPKPfIQLZRTc78dcfBP++ImwziZcb9JSMYe7yFhjpRKz"
    "jraX0hbc6kf05VzKSVztnXdVEQ0gopTEbJO+CHobC17GJNBjko2vjByC0XzRowaknPFIjcNHbb3Lq03M/7OhLgghIWJESRVJqxcj"
    "JBdkWxGTLHFvU1SkwnCWjzYfqJtw3GndAJaAkt5E0k1F45Edfdln0mDA9DxxEnhLAOUlgKaMejO3iokiI4I8H7lbmwg3gu+/IYFm"
    "f1sWvoeFnRyMwhAAVoWZWFBldIXSazfpzeoq7vjJ+2hrLQ6fqDERpo0/qK+5UzvDcS1Wt7y15MeiPHrvXczltzTv0K9D51EbWk6b"
    "9siVd1qakRUEQl+qj95wMg335MRvnuBsVXqYk9r0gmi4Npx7HYLBp166kNxQh2udQrfN3O83DJ2mBbkKPwaLe0NzK0nHj/OAkzR4"
    "aC/t5X3zJleaQNycPAS58AM59/tR4xReF5EjJx9aVeFcdgPhyacAiZqO4yZ0lvuujvS7ek1etoeV92xQqqJRYOnn/26xkKxnjNXd"
    "ZZu/YOTurjv2BWN5d9uxLxjeu+uGfQFTg47H8OWefbnshMUedqAR2yzdTSG+71wsm6OOLU9457kHGB4T315gFSASYlBp7t8LrFaz"
    "rt2PqQgr4FmDTcp3Hy42LJFZ7/7qJxHep7sg+FnPI1lb7249Kh3XizV46wL0tAhcn//gsPYgVq+XAmF55sUdNHojuhVHFRQ0lPgL"
    "36f3GlJ4AeJv94SbbxAE6QUt3xKLmVY3YamJ2CkBHY0+RMR6pH4UU96BtqUGy7xmwp7OSFo8D8c/9WAj9OMLZZGlbbBGhqeYMYAo"
    "y+mzBoHh4wF+QAWHQpx9QanfBtoXd+ede8LdfabGPanMSG+DBglxYD9jGw1SGJYZFF8HxBW81oHRU/79JXOT6njsTvdWn/vnw62P"
    "7nLdN87yhHuJN/21ey6kmYEFEZgyCunroGrhyrQJGUcmUM9egxjoBg1X7kTSTswAsaYJ/D0wKzUkRmosAl6PRYnzwSqhNgkvsN7V"
    "N0XU00bxtIoU4sEhi0FwEAU12iWY0muy2mwP5ilzxNvku3a2dUYIfzDqJjMXkQ+5IRv0EnVFTwsLg0aQqUUOWltiyFvg0ugQtD4J"
    "ccA8V3JDISgpK4KiZiMGnhGVFKOMYcEGikQU8DKNQnL9WSgIgjbhKJC1TML7SCQvDvmrgYBrki3pBUzl8rHqyfFgBaiB1AjJloA5"
    "qgOsF1jRVyR1KEbUAkHJBtpIoYVmXT/N2Lp6XbsLlV+XPdlIsmz5ZsrXR1Zz3yfJfWCJ5HVb+Sh/7Foj5G6jYQFuCFPbR8JFYDp1"
    "qh+ACCLeno7FfdtCWLsK0eJY1vSlBb7UGPtfCQPrSCPZWKLkdfMhDJJqpYP6dd5gjj4WkyiaRBbX2Qoq/4vjPlTLy3UQeqTKSKxU"
    "88VPKlTtHQA0gpUC8oDOIlkvb+4giVjDVNJAhR/4kLC527VeevJdNu3y5DcCClDcNnwLRmHa5QxUcnL4svvEnSPRTXnbvIiXvYMW"
    "V9WcfrR+UWntpmNRIcgQ4KYEiLacGXK/2X5HUtNMfAWwmw6Eu0UAKTTwyGdsNQJjK+ghqY+r/N1PVEI+p5tsK4ou2lhzs408XFlR"
    "3UP3S6wFhVhNvbieaTPcyoc9NYGGOMZb2BkOlTr8hYGd2EsIc3UDYFVULeBVNWXDDGoXmpVkv4/YbS/cMED0PN5PZ22dgCWc7t06"
    "DjqPhE3HEPU+Bs8GcN0np2hEdBHMYjqtYhvgtbiJ4Vq0xlxZ6vMP7Eros35uA48K71E8Z7yhGUcFmEYzi5NA8AQ1FbJMI9NECxLW"
    "SYTC46xTAGpPq/E5thy6+V6AhQdxNR6rdFC66XSafBPfhYXvZ8o40i9UUTqf8tV9AOzsxaLLOa+21nRuhmKYSSd7FPZglmBPft+Z"
    "nrdwIyB6YKQndQzRjpKTdcNkmgdyx6ssLq55g4Ml74Sxkt9MIa1Tr5qfCoPRV/V++/Zpy4j+8nkRK3o/Gkx+GpPN7nf96Rmwn3lY"
    "b6KNDJeL92tqi+PQfsN2fmVTKv0kHRT7gCOXdb6sq/biI88kttow2E0UBAD656bsiN0g3t0yUwwSMNtv4O74p9z3OF0JgjKk4w56"
    "UtSoyqAy+Ubdm1f3rQY6qd3c6qEXIQib9KM9lRDdr1+9Jq127vQmkpjbtZ3yeoMxWdu4EAg6RjLahbN5rmASuL9IPG/P8JnSEH0i"
    "b/fUstdrMpfLV72QkXonHYTrF6IqlvrlSdXYMCPaDDtyzkr66LEhhOaEdz6Li7DA5t7LBPytXwLTI7yzB6fImQ7h4L3njNoRQkHJ"
    "KNlvWthxLXK25lvicm/azgpTjb5JisK9zff0gKQwgdxk/steVFho807XTJTvf+6Vc2J6p6ZU66ks8KS5PUECmhAqG0NjNpFjd1Tn"
    "fGTsXMX415Cm3qNRKV5BNBAnNYkA3U0SGfTe4OyA4lUfEJQm0yVtdAfHas7W2xII6812t6Iu5FLMTVZFVd9Ds035JPAGIn2PER6B"
    "XEqZKM04hOPpI92BL8Mu3lZghOcGrgOaPO8usJbi0RDeGwnxQzTL3o2wjHZb93BOLa0meo2R0zP1wqRdNzOIV/NpA46IMPMCyY4I"
    "WfMr7Y4IMvNDyXB21145oP9YY4W3OHm7tHAc+Lm6dMeTNCrIb2uz80P+ZU8mvasz313NeoySzUesSptJv5s8GA7Av4jt7mps4O3S"
    "QpyOJffV88VjGnvDNyM/OdBADW666aWhya5dfqqKmfxLqL42EJ+2vxhtOwpWVDRX0usSWjdvTN5lIt3ScVdFN2zX/Hhs1dZrhFhx"
    "j4u8s239YJlQ+9lSvWj+BX5d7+sGqwqPSJ4aVqjL/PX4ElXnPUt+tzzI3nYjaulurrgJkvV2V1T3bQXSQFRvLpZNuLMabb7Xddj6"
    "oYNpjNDas+3dGfjNf4y2y9ku9+xf0XBqDQTkVF6GwhKPOdXOezrLuGvngaAePvWQg+O02q/3oRAhvsXznC5zToC1ZM3GVur+pTx+"
    "hknyXG9W0VNx4NMZtpQyK2x28HZ7qwgvq24F9m537YM9594qEjYOCD6PEtamNGjDIoTB8dg6hMEt2K6/eXSj1AV/fTwttlowo3EM"
    "jtukQTJcl9Fg7dcWI5erfY1MOPYJG48S6IHGFjC9hXmswDJPLAji+02BJew76a5oCVmPDpSasxE4E9fKkGKLoCv6wdgq2uy5Pgzd"
    "ag6PUrJWaTfJ8/HSZMLVuBkOHH5ltCbG7ZbT+t7HsVOHzR7GCDJhtkah9jFO0sfe3A8UK17DzNuN+952zV683tIgFa832J1uHJgS"
    "KChYHbbQxZ82sRweLDdcpQoENBwvNaDvkpfPYis/ZdIrlSxleTTBKts2utoQ2xIlnzdtgClOuAWoWu0vHs9FbrlV3bWLMM0G7eWH"
    "dlgaXjb5HOAAIduC5Xh1H+wtynfakdx6+1as5hi328RjPaQ5+7N8HM6DPA+5DgPW5cqG+HXDL1npEGdA3UvwHbPayUsPnb5hUAAg"
    "F3tfBCUm9F3EO6COVefGBFB6MjFfCRtYEVlDfErVEHH0fZ8kLwu6DxV1vlttX5XPTJYS8paGdq+QD4KZpSwyEoKMm4bYou3hxRSe"
    "Ss6XS2Yj6iSNv6nTdnxXW3TXNbGhyDd8i3NRjaWTmrDtXpa3IgUM9echB5t6BY7gaGO7ylqRHxhBwvDTSNDut9VZQ+4thPWGfqNn"
    "h3rD6flPxxV7fW5rI9HRdysdBdfv2n3z+ojU9IMzfRoOumN3C+OGwUbXx6MlaGz2JNgS+5dl9lactJSNloz4j8HTxuc7F5Vb7Zv/"
    "avKhZPom4EAx6D3Q4fBWh9eEfXbL4bvtqJHaEUJ4o9l9rTY3vX+p2zD4WJCyyUOOhcMYESnP5YEn8a/CtyB1HXg8MZbjEhQgOEVv"
    "SQ3GN6UGmSXunXDKGts2P4TkeEfOntjzydDVURF0IyMSeOoQSRJU69oHVYwgYqdfDMJQFQrIT0qLJvmutsPTGJYMOAJ6Sl2kq8dd"
    "Lj7uvQue1NAp4YweP81RcmLriAV5/mzwTX+gd3SwieaDKLtYNXTBH4dwB9fkUO2Li+OSeuLhTYM+VI2l/nAQKw5NZqMCp/83/bH7"
    "SM1D1VHzRYR/DQpP1ixjvY6rgGyAF2gwgcYCm/ZIctvpWxtEtZi81SYSAW1d7uP2fdHWib+cEC4p7uK+QMxUoGKjP4KDrRd05uux"
    "g8Ddld4fQG14sBRn9IrIRKnk+IIFPdugTsDR18Hn9AozcyeTMze8740fD2RLunnh8uK6mTN5qFac3KFalsWqDfCpyWLbCRvQNPVh"
    "rZpvUWB4wnuxES/uUFFKo+O4jTiP2JLowjk2g0z0ttw8Xyy0zM2oCV/oYtRzsXkO6Thc+wYsfd5d/Kpj/WpaPMojVM2fy6JwPtfT"
    "hxur6T7skdjYfzouLo2vT6qx1E209EP5hrEKVN2J8AWG8R7fGD99uddWy8/TGx0NiObPb9kFg9h0iy1K5tSk2/kbRjd0+dZomj71"
    "RfccWdE9ic3Fbd9WtsE0d0/9RgVEmc/kJBBT7+1zO8hL+bbe5c/V3ZeApTwPdhAx/vEO6xlDgzoy2lsvgkajydhrLmpUDoTSC/kC"
    "CekvzBaTst8ebRmw1NGOLN64Cygdx90gv5sCYFJZlgeTEvag/saR7lQn09GppD5wekEmPr9NpK9GpYcsB6rzFlt6TvmbaGA00fqm"
    "DQQCFw0lrAnDSIBnQ1SL52d0U2osnbOPQspDEcjoYl3qd/IODRSBDJi06+IpX9VBXcFf1K6QBpVysGfiFR4Zg8qCW8OjbbZF7njb"
    "l/m781h354Mcvoe3DHH5/gK8S+fIDkP9sTCkqB3MS1T4CKxHNqGlJpOOBteyhRJCnkFD6gCOxqT9EPjBLAIBD/wei1SZj4EhaFM1"
    "u9s8qlNagMKFZiJIpF6och8OCPGGjrICUMfUxQz7lgaaALijgWyc3/QiT4XDqhG8ym1uS+Uih+/lTHUR/KCQ1yc7mrzn/r4VGoXc"
    "ouFn8PkoMQ0EPDDKHAA6tQvx2m2314BLi2fsPDkc66IJsKdckZVvZVEFbi7javLDs+29wBpLwl5DZYlmYz4s0wky2WA8MyQj64Lq"
    "lVVawnjFmKtbNKrwI2KFzZW12TTF+gd4ZGQn3g/2VaWqfF8ELiNRAqI2k2aLsiS/qpftKXSksMi6PfhX1NgHhrPZVrWfobU2ERQk"
    "bPPExzYPpt6gGuWbaWva+FgapK5+S1rTypolbaFDFSP7jtCqxJ1MNqVlqF5XpHV2e43UJup8y9ePiQe4fiHVDXb1L21pOjrSRSn9"
    "FmS73PtQmLfqcvZRDEIjRIXluex02/Br8BbMxRASTMl37PAkKLuUcfq6scxSOtOOtO0P0lq6GU1vjTvTW6SVbuRQOzSn7IGdDsNS"
    "zFfdYWGvgP5ke/elbTg2A/iXzlsFk/qX87Y+vrbAy8hA0jQcZXrTUXxXl/ojn0t9PsYOl0uWOh71kZKsjznb09a34k2NfrF4SaQ/"
    "fcHF+2MA62gtH8J4SJhOEyw3bcnCrm09hsfU0AqwDqd6ZAJ7dMBLPwpkbvo1wImg/s34jGoXnPX2ECWDqT/8Asu8kEASaXC24inE"
    "sgzasW5WZSBKbLDKIuguvKGK7XbBjfvbwfjWcsfgvO6heiIMTveK0pdXx5nixvDE9B2u31BhDpoz0HEYz3S5fma3dHUx3thII4Gq"
    "YremMDlfNFnZiIz7R7gJr7KAlQWZ/PdcuvCD5ZGjqosTWi6GdCxmdORuL5SXYVrwQGiiX4CYUdMak/ygHl6k6Q3UdLxAhu5Lf5CP"
    "Nk78pPMMl+Lw4cbC8WnCsXrgM7y8nwfmvCrqfLurErRLtfASNO9OUxxOBPAw05ZPV2f8O/jIHxDcGAczIf1kSzOpqX5oWrytSjt9"
    "1ag1xBnHz2x94nmfB3xgdThuCN5TNqD8wvZiUXvJy8BoeP1AZkOzqLEGmifGuCMx96wcQ7hKxqFx74/7mIObuZ0KUGS4WKyBbc7+"
    "ywirotwuZyz3vMtL+F1dkw24gvEKYNRm9BC4vJ7XWQ9kCGRSnBxPq/y9Y/RW4U2WhhxOZchhQT9IJ5WcNRGyXZvdTnWUYkdWyqPK"
    "7vIF+3gfwWhEnTWsIDmyfCAQdPB2EtCp/vQLiUb7yDNXJXtE9qybmr25oB/AOPbW5LmFnPv6yQt2GmQjjnZiTYCr3mdUgwWXho4P"
    "FuSqQn0+b45gmF6RX5fXbbVdbHdAZgiRu6ZRRDgtFI67N6ywPFQzOF5u5jZ1b8SUylfsLjYJm6tT4Hy6Sfn84ROnemjwrWOwWrXM"
    "d8Wn5Glk1qjYW1WgEOE2pZU5/fHa7L45tBhtf+IMF16v6sj7toc6ILYp4/F1yqi8+uiUypKJLmfOY7XZ7tl9YLZN6EYOODfa1Lk8"
    "04kF1j/SDx1AbX/njEru1/d1nT3ZXSMV3W9NDAOJ0Ivkgj+ytsQJ88bW5JewoFdW57I/6IkfkiTvxfS1ai6pPbw1FhNfYRQSo5yx"
    "m2H7WtgmRe5OfkS/hM9Ry2oq3CW8ITEQ+HdPR7uPRH92fFSe0U/HyoaEhKPjdwNpNnOajRj7uBFVuSWFrg+GEEb1YaA62Vy8Tovz"
    "C2+N3lYw/muSn07Jax/9KkdCcxtjIpgu7lCbeKQD1NdNi0EqusauDxfO7TnSX9E/slt4i1bsEY+BrfhSwomKQxZsuDqV7L6SY1tX"
    "n/OTvXTnU5ulE4wHblXJffTu2wXFKzF+6B9+Nuw1Dik406H4iEgcOS4dRXkeSlXWcgOruqE3guIe2wOWYEC2hw0j6Oq5oNb7xStr"
    "uhIkmxnEsX8k3zkKfSdSAMaABR1gfoSUcjCuCsJWeiaAJSfwZR2++TZrBTwOCQ0mX8cog/Bg9gfpcGEwFlBrfOHROCFA1XgGzeNB"
    "d6excHsaY1gW3OsQm6Wn3MfDG/iT7f50LGtGu9uUyn/+xNs/xWmv555kvEGk6M/nX7RpzxuRYlAql5KBGOFh+jUPEENa2B7szzX8"
    "cjqEuJE9WxRr7kGp2ynhAWoYN8/Wi9X7hDHcqUfDuHxe5J+y8TiW/08G057p85Bco5w0Yt82dYLf+A7bDSGV9XEfHHc6Mcd9JYHs"
    "w8uceZa5+rytlxvGL5ZsRLH+uQE3nJ3aE3d/3EAneAdQPPsuD+Rd2L/glrm46y+sZKWcGKO/4i5t69u8Z8lxRcgYIcUdjLodGb7h"
    "vXewvieD0hz6qQEfyhmfqWSTV1BM8YOOJ2Fl9BrQT5BTbIlCdI6vq+9BfiC8ARarb+vyXPxwseUikiE9lcW6KEEhvTovi1V/f8RB"
    "Rvw3Y081ZRa3o49iSejEnKqIPc96rEgWVh/PcdEX77tOwCbkD8LZuaRFMhipgw8vI50fRRsFdRONlHrsJXuFUJXshvjWOxHjuY/b"
    "nmLYufwjByD1oQ90bD2Rsf/eMkUJ5I2w6CE8jMPsp3TSwgSRqkwGmEwqfRv36+0entb1+cBtSEECWn3K4j+d9ycR4ub6829QafDd"
    "3/z8GyBX2H8Xx9U7+89q+xptV99+BVvoq+9+/g37DYVE7jeber/77m/+PzPmGoM="
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
