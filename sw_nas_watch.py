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
VERSION = "1.17.13"
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
    "3twjvdnTwbHf+tmlp+8tquZe/rHij8u/z5YuskUIv/OdF2J1v/MLSIjeT5x4wCr3e7edm5/8JaO6Tw/90qvgZuFfPUwHfO/hSxlF"
    "WVqEr375pVd/693tpKTydgr344EQ91q/+77pn1cejfDn9wV24dvx0+Jt58Wfdm/bW/zitoXffWb2bejdoiTeT4EAl/jtGoVeKrbz"
    "B4ptcQKegw7XJGzux7vdG83T14+33tw3FbzrsU/aPs+9ZnpzP/i889LsuTz7+unWm9vmd+9F4AXqey7a3WfNbrPG31okqvvklsx7"
    "81Buv3n1l//yn//5P/l7/+1P/uC//vD3Xt00z+vnYNizr/GRInjz3I1Xv/QKYB+H4Pcy7xRmSyu/fEtlenBBvv+3vv+CGJcbornJ"
    "/s8/wZqF5o/boUEP3tNTxOkHP7gFGH/wA+vjwbp07u3DEeUvXPAbfx6Tnp4S183qdrT0bTw8RAIe5fMurq8XAUo/Ge8i9CQvb3+a"
    "MD1L8wtpWn74IE9v7js0vdrdlOnjcr7F1H3rQSqWul8+WFyRJk/bW1T+li0RN96iOINXH77c+xnz905rerN1D/PSt73s0+d1Ndk9"
    "BtK8z1W8R7eeOIa8GGNLnS+78lwIePXf/vP/9e7LP/zJv/j1P//RH796+/l90WH27EeuH6IY5aJiyuWd78L52SKnz19uy57u6xJu"
    "qQSLGNwedGl3l7Rv3SStfCb7DQI8LLj8s396m7j89Fb2SbrfvJcV4P0rrD/7/t9aRPL7n96n6pZxeNONp4e1o024wJYmfLI+ty1L"
    "vv3t4pP+Fo1J/cv0tl3k/bbDz+PNm3zcA9tPizfCBxP46behW1hwQUd+dpvbWd718/KTqrnjBOZhA8wFEz0O9OjBZr+t+9f3jUsf"
    "0dYT1MxeMu3z9ymf41vvm0xYaHPf0/V7bVdWVRh89uqXfvLl//bnf/DPFuo88+SXH0n7Ov1ZhPz0qUR5z4f97NW7H/69n/ynP3z3"
    "5e/8+Y/+7N2Xv/YKeHgAvPrJj/7JX/zoD9/98O+/59YDrx75viiq8oHOD5L2NyTx49V7Ct/OlfnitjHbE439G3H+uzQuX6Kpz14v"
    "dr58sPPlk/W7N/tQ5R1vdMndEC03y/Z7ZXU7pensf/yrN5/emec9M++Ll+rp5vjej1NfHP/X6X3G7vVjv6g+SMvHFRY/+MHjzWt4"
    "uqTdy0eLSng6tOTWq+cNr5eu3echF5F/CdDf74r4vLHxfdLqPUEfteANY6e3iHzavvlYI6btPT3ncauImykCPoFWt/Tyx/1534f0"
    "/Fu5+8IOtfXTx0VYC658vs17y0BcVMzD9mSv2rtm9D+JbtIQFv70uPQjext8Ei9Fb5rpvgUkdW/3NRz+3G1Jafrm6flt/fttWW/q"
    "ZYaXV4fyZelPVqtb4aW38Op/7BdP9QPl7bSqmxNzWzMS3H789KW4z8+lxX2Y3Urd47P3hX33L2X1+l7B0iq6jN3ws9fNa3wNvYXe"
    "Lt1587Z5vSbXy+XyD7nvx9K8Jgni9hTGbk9hBCaXa3R5/Bgv0NuX8YIber/xUW+/YcGeo+DLL95Dh/sAW6j6ACpvEvCR4/Cd7/w0"
    "v+EhJvH8Y7198/bWkbeXD6eyb9GOJ/20tB2+X4VzH/zfDT979V9/5+9+689/+9/9xf/+w2/dIwjvfZGbfXj1qXSb5XhLvgez0sPs"
    "88vg3n3+rL//6ntd2XnZcyrg66WF1wuiBV69eVRVSfoixnHr3+c3Wr3+qGO3Vr8RmbKqxwH6EJX6wMDeJbTttGc7+36Y3UfOMzD/"
    "qM7dI8OemPU58/oxHebdV//m3df/+N3X//bd13/67qs/u31+/c/un7/+7st/+e7LP3r3wy/fffV/v/v6X7/76l/cbn71n959/S9v"
    "Bb78w7/66t/81R/8w3df/v67L//Nu69+/fb55a+8++rX3n35q3/1w3/8Fz/+P999+a/+6sf/YankJ//r/7No63df/r/vvvzRu6/+"
    "wau32PtF0ffoxa3zPwNkfOc7PwNj3LOYHlTronkeqHUj3lvzHuj6G9X3jFk+iEl9YNSSdDH8777+1TtVfu3hRZ9wxat3X/6DG2Ee"
    "3/43//L3fmOxT+++/L07YX7z3Zf/7i//1R/85A//sSrdifu7r55tfhfeUmmezc0HCvKLW6jrybLcpfIjOxK+1/R31L9w930X/tW/"
    "/8nf/aN3X/6je/v3jjyx4a//9Nfu7Fks6Z/95Ff/zl/8wx//9Z/++qu364U3Lyblnw9/fwg+fn4zNYvjcDc1nxZffBiIvJd58/Yx"
    "Bv/2p7rKT7N10EPEcvl383y5Z2f44duTF3yfzHiYf7x8mBP1HCy6BTYfwl2ffXLfmuCWfL4YsJ8eingO84ZhsfDto9d580mXhMXr"
    "oHiKcN7p/cWDFiy8m2Z7n1v/QezSe8608+5TlB+PQb36KPrzNCf9oam7H1P+5BgXj5763Yd92K3zOVj9/ftbPFDkszvt/ufP2Vsg"
    "8R4s/uI7DwR8vPcADL74/tMmL9mzHWblx5jE+1ZfhCFuSQDvpzMe09Ne8iH7JA/b1ovDZ3Y8Dev/scrvcTXuu83HzL2dX38jJPRe"
    "qb0UypuOfDHv+1Pmrm4Q6PMXk8bQTylzfpzfehKJG6B6LxJNmN0F4oFii6vJvO6e3xYNn0zj4/kaj+zbPMS6l5vhCwvAxs9b2XXe"
    "ot29h1Uaj5R6YvxTRLB7kOK7ln739TJw//W7r3//3dc/fPfVb/3Vby8K5e/eh+wf/cWP/vlf/t5va5u7KrmN4fvF37kP7999GMYv"
    "VOxS63vU+Fj1D999/du3qr/6o3dfL2bg69vFUsdPb/L3H4zBX//pf37QYX/9p//lv/7qb7374W+yY5WVTdh8C/wWd8sgab61VPL4"
    "qx/+naWGu435D/cafueugpba/o+bRvryVxYV9JgZ+uUfv/vyT25OwX/593/14z+7tXt7ob//7qulnh+/++rLpelFp/3kT/7k1o1b"
    "hf/oQYXeVRb+4l0fmfr2ZxDvV14owd+9RQPewrcA8gMrH9cJPPPNeTox8DnVo8se0vvv66s+f/zB2214X2L8gtzNbRvZ29rx4nZx"
    "2+S3+yAE1HzS/cIahb7znfskhHdqb+cW3PdutZdn45tfIH7KI2d5NC2P3je8CNbLhpfbnzefFm9v8Zzu0/fNvR0/fa7+7fR87Xzx"
    "1POPlRX/uFeVf9tLtclfW599/91XCy74nZugfPVbD0m3Tyb9d999+Rt//ac//lvPWbvvvvpqcfJuz7762w8lFj6/zOm9yeuNN//0"
    "DipukvXn//afLgLyl//xP/3kN/7Rvd4fL+DhLs2LeC6282//xY/++Lm9hefvfvjV9+/7G/13u/Xq0/+Brj+MpRteebKbH73Arb03"
    "L3HZk864TS3c80cfNevjhpWvi2+lj7ubltG3bnsiPe6Lt4y84lmLvIRBX7yfEPkbTYPcI7HvdRt1M04f2Tovy+7BgI9tXHjTbeFT"
    "r14q2tb7MKT6OKP6mPVwm4p9DvbdZ6yG+8cvQp8tn59C7+vRbr35pVf3PfPDZun/bT+o5dePV9ckXNDDLz/HFpYOPRvvb0wmhU8T"
    "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"
    "wUkj0W/6N6FyKD0sdgDftqa0X4wtNkW+HY+PquA0tXqBwTEJ4BcFfQbJ2WYQkSrTUSrkKaT8hbg/Nh6Xh1yvLFXYTKdc8GY6xcCy"
    "vZRJfkxkBr1JddVkB17J189QrrZrUFr7h8VJnZsf5+pMkQ/a3dlCaAkaLFMiE00mTUSOQ7UO15xmUt2kQBJLn+z2bhLDZKnU6ifX"
    "RW+eb4fLK1+5WiiMhQle00tHuomgb+jfjEPE1M+I/jhLsaBb5pk6OHHAvCty5W97u13at0x5wgw9LXZcg3ArTK3QOmvdnov5Q3Fp"
    "0knl+EGcXnbXYW6ZLDAxGuztOptKsiCcaX+s6ydz+XZh6QMzmglMeSFEr9ARqpVVx8P1l6HyOLZYxJuTbLUsZnyTMNMptkBzMIOQ"
    "PdZmOmNiVmi3xvaJN+0ZNjqdYnpWgnLcaiQJAtFxbcIUeNmtWqvTKVcjw3VKbDEJtlXki52iOA/Mp2nXproC1gadECISM5kOlj1r"
    "e3YwlJudcXGaKSRX9plcb3kktLG0FgzzLnnQdHulWXAuiptZrJJm0owwSvWZ3CTNLlzJSSs7D7Vd/UhlFt/Ey8yc8cjzeT0zkL2b"
    "7EIkK4DR8lR1ljruxnzSKFxu0fy0teZKs400kCOrcMy76k7Wbl+l0gp2mbJoD6aT9r6/6E7VBvExk0j4UujF4Hy/k3W56HJOqBfs"
    "mfF4UKxyc7d9ITDhfjHcd7n81RJf6LEh/zBdL87bgWrX1y12pBBTArxazXWr/iHfqLPkAsxONStPvWinRXA6Tc6XrlilU3QtucVk"
    "mSq44xMm2F0vetVcLjl2zccZcD1n7hwlpUY1ZiD2Fj2WdMU4n2uVjOdycW+212nx4sRV9m3G1HISWh+n6IoUjMXBE65kumSJI+fk"
    "eJpthvvjbGpA53vtZT5TWW7G4UCMBpQAo2JyTD7S67V48C5AfKkpK/lC/DAGkItsip3jRDxRmnkma6qYtldcIxfTL/i51DRFT3Mp"
    "NsCGulM2OaGr1Xy7IhCJ6XIciYQGETo4bHdzAXadq0zcU6BiJlaTUIxv0CKPp6PaMc0QrdV43ZeO10wIIEkt3Kw1Un6aa4GWmM/n"
    "2e4wRaZW6wY9nkp0YNYsuJLtNilFFnFPhQ4k5yuhUSAik5VkX7jXdEvkylxCtJd8JXnVT+b6m7y8SYxCPAprhukIOZk2iXC7NeAi"
    "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"
    "T36EXEyj74WKg8v96neUW4ACn/z7u+rSyOnHONX32ygwr/ddi/oqi/PmQOH/T927d8dRXXnD/8+naNV49HSNym3JkEymNeVexpdA"
    "ImQmIhAiNHaru7q7rO6uTnWpWxqp3yXbhBhshkACDJcJgQAiOMiQK8GQrPV8lIBk+Ctf4d2Xc06dU1V9kXEy77sWWN3VVafOZZ99"
    "9vW3L7EEKVqTsic1dSPhg6Oaw+QFRJ3/OkeNCCA1PE/l69Bigp9FEUXhYHkdzysUun6u/Dps+8qxteuL3Xf08HOWnY/vP/sB6Y2y"
    "X7ImhvTsXv3i3Z0vnpvMizMkGBHVSCTmJS8aAROvHVOZZJC8b7Tt4pA2C+zeubYWNzoVsxElvNWw1CiK1p46empjfLtskX/SWhkZ"
    "35QV3DMiHnVYMA8OAsN54uopxPoMQVVF6+RUFfCcVvHiuJU5XOKktbSwao3MN0oqh3roLGsJwIxIURgb3SbJcBw9jJ6cU1qUcGTM"
    "C4bzVb3zcJIReCEzA7G9di6rQATpW8Mdprz2LJ59/eDFH+2//9Lnt95G25XcWLtS07xMIT363IZ5c0Ini2cSfA/kfuj+Jlaz9oCE"
    "6+VO8RsOfn40hI9WH/61Boe0dtEWxfNW0yqmmgZmbTlv65XgzVPSojznpVIh6KIeDsKBlbY1yRed7Q95TSWu+51ye+7dfv1t+vAq"
    "Gv+eBXb0nHLvCGV+55LKExjusY1Py9//RguyHGNwg0WdIxuRdPQ4WX7FcUdzIrszixuQsTmDEahFMtTTKuUzJOxZinuVlDTD9Xup"
    "2PfG+VoYtEjPoYI8Hz4tQsCkSY5JOrUCqRvJk4DBsKCCqVri8FnAeWqPo9UlTubDCBdx7h5SqEkpRqDrEY/9RbJbwF1qfYXjAuoe"
    "Fq4c8jJ+E+/3Ieaax8YI4ZnCsibNIYZE5B0j8Jgh8vYI0ThyrUYUdYrHjs0d/xdg1MCqizjXaC+a4XeIF1hO6C4vc0lQxzLllqty"
    "gjjI4/mEFEGuc2cZURrhILfm4CZhWMWr3QYGllqa0CNaIcMHO+afiu3PIrLwWXoWofkynoVdRld0r7wKNOIHRSJAxqMJx7H2ENou"
    "17sYKymHy1sKaVKTobS5EfnasMO/tXRukeZh5SvIuqByeuVW7jSIBPAerFFXbnMQAe6ig5888/mnr1mH9L5lSLjLlt40hot9E6FJ"
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
