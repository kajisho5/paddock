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
VERSION = "1.17.4"
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
    "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"
    "v7B8n/+/S7D98vrrYEnMWD6SB1PsfuXRKIMW9fVgvT0UTPjevW7Z96LrfOHewUM/b91g2RKfLKb+d77zbX6xQ+bDB7B5V3WLcv5A"
    "Gb9wBCSP/oM3b0f39fv1/NScXL7+9lJCaVkY1gdGjLts5vjANLFm08T6WabJQrtPHjcLfPcXnzYLDE69hJbevF1soUeu2JXLwnce"
    "3FK78nEpvywj4wYfQdj7ZuWHvTbP8zFTMfusmQHMst37iZLLezNnjr7fv5uhgJfPyuqV18/UeCHdX6Q134NQzjKvj1Px7IR8OnPf"
    "IPXm7XVJwPxiqcz0zfbnQRTZ4itbeumC199s/81P/+FDfvh/d3Dz2kke+ay9///thfWWgzeffyNp/cWLXZO7p+HOc48uh/u8f1OA"
    "PEKPJyExs1i9PPSCsB/Xl9M0UZC/XspHfNEuPH4fwqO74bPXz4ffvV98uzDPYsw9Ko+f/vSXacZ9j2bt4kG4D/TBlbC87dZNi8Z7"
    "ybIfG8NLmtQjMz7e+5xS/hZfNvnc+y3yh2z/x44eCLF6+9DTsnA/7udF5Lm7I79ZZ+9n1bZYondKvX1MB3jzsM5nMdRG/vTJExfM"
    "lPn2rKPM8s4Yd3R4WYD0W/X+eSfNi0ohwYeGyYO6yJ/URf5QzHDxh2XeoqXqRzt+mZ+5/+frj6vo7fOJR22JQEtFnudWwshfqmjM"
    "j9A2v/hRsvVqPd/6zaecRYwf3IvCLo+0rKWPnujxxudNh8+Ja+G92OZMuvdnnIabj5dk8Lvkeu99AoC34yLn3rydRcILrXzPqL4T"
    "7VF8+MFDUPi+badZJvB+8BTDf/z66S89HMyw+E659u4UeZyqh9zGWe69cNmUjzP9APIXP/f9oZ5cBO9J9beTD/xov7BCPfgHP3i0"
    "UZ79ofene+9J8967PB4bfvvtJxPlzfLruzB+L9fvM1zfV/zDycfBPCVl/eAHuvfRPL394MXnavlcTuTFczxx1XPo/xvDmgXhs0Py"
    "ySn3TSfU+1vev2/svTNqvXkv7MW7sP+5ekk/W3TMtvgu9DZtXoZey/uEvmqGv72M4qVr6MXIP3v1v7x6SsN585Z6TAz4xMmdB9vn"
    "Psl3N9eicl5MrPlR8ki5JIz8/EMy8CxmlmDZUw3uhbeXtbLwzWMEJPKur97cPb3p01tjv/Wz756+N4ua+/2PDX98//ts6Z+rZyb8"
    "zndesNX9zC/AHnp/48QDVrmfWyo3P9lLVHkPD/3Sq+ui4V89hAO+9/Cl8P00yr1Xv/zSql9Gt7woqVheLfD4Qoh7q9993/XPi49K"
    "+PP7Bjvv7fhp/rZ1gk/bt83iv1hK+N0js2+3xSxy5in8JgTIgrcICr0UbOEHgm02Ap6dDkPo1d5CununZfT68dSbe1HBuxz7pOmy"
    "zKmnN/e3nrdOlD7fz75+OvVmKX73ngVeoL7nW9t71GyJGn9r5qj2kyWZd7FQlt+8+qvf+5d/8c//0X/70z/6rz/83VeL5Hn97Ax7"
    "tjU+EgRvnofx6pdeAezjEvxe6ly8dO7ll5dUpgcT5Pt/6/svjaYF0Sy8//NPsGam+WM5NOjBenryOP3gB4uD8Qc/sD5erPPg3j68"
    "n/yFCb7Mz2PS01PiulEu75Ve1sODJ+CRP+/s+npmoOiT8c5CT/zy9qcx0zM3v+Cm+YcP/PTmXqHplbII08ftfLOq+9YDV8xtv7ww"
    "myJ1FjWLV37JlghqZxac11cfPtz7iPl7ozVadN1DXHqpZR8976tJ7z6Q+n2u4t279TRj8Ps1trT5cijPNwGv/tt//r/effnHP/lX"
    "v/YXP/oPr95+ft90mD7bkciDF6OYRUwxP/OdOT+b+fT5y7Lt6b4vYUklmNlgudBG7Z3TvrVwWvFM9gUCPGy4/PPfWQKXny73PnH3"
    "m/e8Arx/BOSz7/+tmSW//+k9VDevw0U2Xh72jtbeDFtq70n7LCVLvv3t/JNu8cZEbjK9bWZ+Xyr8PJ5c+OPu2H7avOE9qMBPvw0t"
    "bsEZHbnpEtuZn/Xz4pOyvuME5qEA5rK792Gh+w86+63evb4XLn1EW09QM305aZ+/T/kc3zrfnISZNveart9r2qIsvetnr37pJ1/+"
    "b3/xR/9ips7znPzyI2lfRz+LkJ8+3VHc82E/e/Xuh//oJ//pj999+Vt/8aM/f/flr74CHi4Ar37yo3/+lz/643c//MfvZ+thrh7n"
    "fRZUxQOdHzjtf5LEj0fvKby8V+aLpTDbE43dhTj/XRoXL9HUZ69nPV886PniSfvdu31o8o432vCuiOaTRfO9olze0hS4H//qzaf3"
    "yXOeJ++LF+JpWgzf+66D2fB//RCxe/04LrK7RsXjDosf/ODx5OBdkqh9eWnxtzy+tGQZ1XPB6+WVlksccmb5lwD9fQXV58LG96DV"
    "e4I+SsF5PMvo3n47bd58LBHT5p6e81gqYlFFwCfQekkvf6zP+96l5y733Td2qI0bPW7Cmq2659O8My/EWcQ8lCd71dwlo/uJv3CD"
    "l7vT49aP9O31k2C+dZFM9xKQ5L3f1yvvby9bSqM3T9eX/e/Ltt7ISQ0nK83i5d2frNfLzfNoV+v/sV88tQ8Uy9uqFiNm2TOy2KXP"
    "X/J7fC7K78tsuevun71v7Lt/KcrX9wbmXtF57Xqfva5fYwj0Fno7D+fN2/o1QiDz4fwPvtdjqV8TOL5cXW2Wqyt4RczH6Hz50V8g"
    "NS/9BQt6X+ZRar6hwZ694PMv3kOH+wKbqfoAKhcO+Mhw+M53fprd8OCTeP6x1Lx5uwzkbfJhKHvxdjzJp7lv7/0unPvi/6732av/"
    "+lv/8Ft/8Zv/9i//9x9+6+5BeG+LLPrh1ae3JcrxlngPZm8P0eeXzr17/Ky7/+p7bdE66XMq4Ou5h9czogVevXkUVX70wsexjO/z"
    "hVavPxrY0us3PFNc+bhAH7xSHyjYO4c2rfasZ98vs/vKeQbmH7UZPE7Y02R9fnn9mA7z7qs/ePf1P3v39b959/Wfvfvqz5fPr//F"
    "/fPX3n35e+++/JN3P/zy3Vf/97uv//W7r/7VcvKr//Tu699bbvjyj//6qz/46z/6p+++/MN3X/7Bu69+bfn88u+8++pX3335K3/9"
    "w3/2lz/+P999+ft//eN/Pzfyk//1/5ml9bsv/993X/7o3Vf/5NXbzftN0Yv34j74nwEyvvOdn4Ex7llMD6J1ljwP1FqI99a4O7r+"
    "p9p7xiwf+KQ+UGp+NCv+d1//yp0qv/rwoE+44tW7L//JQpjHp//7f/W7f2/WT+++/N07Yf7+uy//7V/9/h/95I//mSrdifvbr551"
    "fustqTTP6uYDAfnF4up60ix3rvxIj3jvJf0d9c+z+34Iv//vfvIP/+Tdl79x7/8+kKdp+Js/+9X79Mya9M9/8iv/4C//6Y//5s9+"
    "7dVbZJ6bF0H55ze/PzgfP19UzWw43FXNp/kXHzoi7/fMuCF4CrD9FFP5KVoHPXgs53+L5cs9G8MP356s4Hsw4yH+mHyYE/XsLFoc"
    "mw/urs8+uZcmWJLPZwX2010Rz25ez8vnefvocd580oZe/trNnzycd3p/8SAFf65YJNt7H/JL3+XPFc+5fcU9RPnxGpTLj7w/TzHp"
    "D1Xd/R3lT4Zx/mip323Yh2qdz87q79+f4oEin91p93Ofs4sj8e4s/uI7DwR8PPcADL74/lORl/RZD7O7R5/E+15fuCGWJID34YzH"
    "9LSX85B+knlN4wTe83Q8Lev/scbvfjXuu/XHk7u8vH4hJPReqL1gSmGRkS/ivj8ldrVAoM9fBI2hn3JP8BjfemKJBVC9Z4naS+8M"
    "8UCx2dS8vG6fnxb1nlSj57z0cEwPvu75pPdCA8TB+9rxzpv56sMujUdKPU38k0ewfeDiu5R+9/W8cP/1u6//8N3XP3z31a//9W/O"
    "AuUf3pfsn/zlj/7lX/3ub2r0XZQsa/h+8A/uy/u3H5bxCxE7t/oeNT42/cN3X//m0vRXf/Lu61kNfL0czG389C7/8EEZ/M2f/ecH"
    "GfY3f/Zf/uuv/Pq7H/59dizTovbqb4Hf4pYMkvpbcyOPv/rhP5hbuOuYf39v4bfuImhu7f9YJNKXf2cWQY+ZoV/+h3df/uliFPyX"
    "f/fXP/7zpd/lgf7xu6/mdn787qsv565nmfaTP/3TZRhLg7/xIELvIgt78ayPk/r2ZxDv77wQgr+9eAPerhYH8sNUPu4TeL8F6OlV"
    "gs+pHl76kN5/31/1+eMP3urefYvxC3LXSxnZZe94vhwsRX7bD1xA9SftLyAo9J3v3IMQzqVZ3ltwr916mq+Nb34B/ymX7PnSNF96"
    "3/HMWC87nk9/Xn+av138Oe2n77t7O3763Pzb6fnY/uJp5B8LK+mxVpW71FKts9fWZ99/99WMC35rYZSvfv0h6fZJpf/2uy//3t/8"
    "2Y//1nPW7ruvvpqNvOXaV3/34Y55nl/m9C78uszN79xBxcJZf/FvfmdmkL/6j//pJ3/vN+7t/ngGD3duntlz1p1/9y9/9B+e+5vn"
    "/N0Pv/r+vb7Rf3dYrz79Hxj6w1pa8MqT3vzoAZb+3rzEZU8yYwkt3PNHHyXrY8HK1/m3osfqpoX/raUm0mNdvHnl5c9S5CUM+uJ9"
    "QOR/Kgxy98S+2Fm/KKePdJ2TpndnwMc6zltkm/c0qpeCNnc+dKk+RlQfsx6WUOyzs+8eservH78IfTZ/fgq9b2dYRvNLr+418716"
    "Hv9SD2r+9ePREHozevjlZ9/CPKBn5f2NYJL3FEj6IMf1PbN/8fbzcolh9d5SbMN1ynl43v2537z92a1+OLYpejbWv3nnHXY9h7O+"
    "aYq8sBlmHX/HMy+QyXtMdE9gWhTkY3DgY2zi/UwwcueMD42q5J64+yLX9Iu3sIe8efvUZHl/ld9Dg979/hfJvc/17O6bTN/H8j7s"
    "9u2Hgd/PP1DZT0v3WQUtCHNxxXrfQAjP+3747ruf3wulffpqiX5+GmXzbWCZBz+/VEXZIG+jI6UaAyTxQUHOf5T9IWQPwXwkLl/p"
    "+a89/88wWibsljPkSdkbkEjWDeJudJLcJqutwXIHb3trc90jj4qFjhiOXU69f94nOxpqjs5RSriBNTyolWMhreKdwK41SS6CfULt"
    "qDgyT3xFJw4+7rigkAJC3NAiG+b0qrfh6qL1HgjmZnNTMRnr8FtzaybrJuJoiw6Yi+MoDLogekZuKhQfzHoCTmNy5SArtnPzIK3O"
    "O3Yk073CmKyoqnbWtGcJGJPwaARxQJy9ZHWWqTCbAphdWbar0syKiqKWD9yW4i+mct7w4yk4bKlCZBWaU7PmGu+sdRcIBpnJTFuG"
    "TauevaBvO1hNCHIdDQkmUj6dY6i5sxUdPRwLh6Q9taoVo1c4fu+Kxq2hh8Mt7vpBsHUkUvbeMabEzW51VFb9FqvELUpwgXsNb7AF"
    "ZhXbUmVPjynFDcwJk0fbiyi1RKa+OaRE1HXHDaUcDf5aRQ6zpoUNeSy5zdZgVuZ0qYTIO7PgUTrVq+s6TaNS9Rj4KLKGTvb+hoCw"
    "NR9sAWV15VOgPktjNwZqjasczfLx8XYzOhVle0NNoLjA/COalAe/U48AXV5bPhvMAcmwNEiEkuCd88HICGqVh1mIhITA7FyWhaez"
    "fjYRT0tboSWQtdknR6haR0dyF/MEkkX+am+nYm+hU9358ThTih+HzdjQnrzdeA1Og+tG2a/ogdwiwK1PkUtQnH2+sqESOrvmKNjS"
    "wZGkmoLqWZL3ECBBcSm5Omq6FO2RoIEaqxCvjta11yQm2kEKb6/ZLiqsfA90Db/HlHETXgHaYs5MdLxZUjXZxGHsLGLU9mJ05aLN"
    "CHN1waREw0qOLAD0UZQKLs5yUonRgVAPoIF7qansxAbrOd6gKcVVoVJ3pe2Vz5OGRUeT7BFQ3N4QYttdWSfH8iDtaGk4V2aKgJYi"
    "+yUO74uA8dQp6q2TIuWpsheA/KZO6tk1tlcoAW5Ecw6zpB02pZJRPlOdGo+hLifJhbudiGP9TbyVu5Szgt68dPi1OM7EoE2Ew7WB"
    "2pqaui0JGh8BBhqiqyDoTJlXRNnizIB2KgUPEiLBBNFavoC6fX0Rgi0r5dtJsYoyJ0qZ6PlNhjHS1VMogWwqWJJFjXct5ioZac5e"
    "CqkB23KiyzrEAX9HwWx1bjKyj00FPCsndNJLwtkcATG+koc9wxo3YN2swXUFXcJShU/BNtiC6PbcER6rdvFOFk82dF6fy43hgDV2"
    "S2CEtsgUPjsnYrwammutDkceTNeG0LP72Gup3czOcE76ZnD0yDwMy9sJTjaKJIwjv5G2rnqIpQ4GcNHoBLJ2yTSbxpzHp/1whTm8"
    "QCKCOvLXq6nfBGOqae6wmYXFOmPILXY+521nIAJuS8fzcMzYOimlltXNJtZrAa0ScFqpmr4fxksd46M2edTcp7p11ylwwzdsGQYJ"
    "cqEYEhQsq+sgTi5tXcyN1TabH7D0lbiohWJfkQZxscv2dEbFtTBNOwKEcQbdHGuJ2/SZjyVbv1T0gN4pq8DTjlG0o/Gb0dcgOFz2"
    "snnAd5yywTT2fNh3LEmdifNpRVgYFjNlw2znIWlC0UKO6a1j17qZpivNY3Z3qxTcnN1xCFyjD3r7WK2JukmbzZanAwHH1uUNuiJR"
    "ZzaqOvIefD4URtzrrL/T1eYCQZQOeqsUYlCh7lbOOXXVVDhBJM1rMXodkBZFs3HkvFsCibpbSGRKw1KwLpEg6NHNhXHTDR+mG0xN"
    "qz2WoqmQTZBkAm7d1SQZkvwRo8w9tzv4coGcY11Mkgt91KEyqfaOcGobVhS3UKI6a7EgUESb1cOGorI8Ck9aEpE44l+EPtMMZZXS"
    "zSksFrM+xlEr3fZ5nAQblBR1vDmzxqzvcss512Him4Wgt6PRQJx0NCsK262y00ruV8MqwS74uEqaWo5tIVBHmrVdray0Nh79s5xm"
    "sUDqO2jfnnXdsIxxz++nqTG0w6WfamEfGLR91oMQ0IqtsA0dXs5E6Aglms87BHGMUHCPrwRr1snyJfOBETqEA1QVnnqph4APzgLj"
    "q9TxeCnMrcXAbVqXqRgzNBb6B3bU+h3p2UK89cw469XYESo10EcHBr22ncrDoesCBfYulexEopGjAb03GFtXDVrKQtJLnGpjYT1s"
    "A/Juu+8sgA8aaR1xpFaYlKeD+TRsNtfj0MRuv0fQYnfSFFrZoz2+Ka6ELFoimrhWG7jyiSIziPQMDk06mAFGXTHQKxTAQZdQcHSh"
    "blynZVYq6AfVjQI9cINdUMcOGBn8/rw3xRoq4FmuAdo0yn0K7BEfWcOQzcnnLJjaYRb/kB4QarTxIVVyTfaKRzJDX654W9LYGr4h"
    "tUONXAHsZHc9FoiwKcRmFI9eNlpiJ5ECmAZSAU2cw648fp1n3iDhzW4UuOqaA6RR7mUnk1BUn9eyDmiSPp0mEgnr85o68FvnYsUX"
    "hGZMtEUmpTACIhaPu1uzRgNbuB381qolPIa6cqADbnBIWIzwSBtm0WQi63i4rgLFMw0NpfpZqa9DvawFzdwfQ/UsXIe9SIOieLNF"
    "zO11U4ZvUAeDsoNgvmKPNOC3tDhIw1DGA5iZDXiEQDssKsrkneBgddCk+emZ44LTNWzOZ3wQ16rqCsBhC5x33TGv8U3o7KDa7TTO"
    "T0p93Q9IaserY4HFQaxuNufrDoQjEChhYb8+jgCP5zZt2FYc+qTLW66m3wZswvjrZRwBoJZ2tBpHPnWlq0tAoXqv9oUKatGWK/Hr"
    "mIy7g0fEHmxKRCev+CN3XB2pkaEK8qZcupwn5n5QzlmvQJfUtpOWxU5ZI2jHh+sdsHNurnBI03N+BryAX0cRCQdpcdijXTaQNpFf"
    "gdIsReVaXnc6R6sob1YtVIJe2LfXRnLQ/VYlcdDd3ZybUpae4LbwqQwvshZzzvYS+lpMwKO+L0UgKsSQlI9Zcb72E0u6Dq8CF3LD"
    "RVmbeNnmBllKMGnJTrtBZunBe8UDD5dGTg5awJGyhzk5spZanzgA2rYQ5TFTbCdz2baP5gXsdpcqyfe8xVxEMiBthMLK6GQA58Q+"
    "YPp4GaYdwpBZ3WIshHDIIWOphmJohnaYNmlPoHNcO+uMkIM8R1wt9UlE5ac1oIj53s54VtQEeoyKTVAflFhHVHtgRQQWRUpG4p6E"
    "qEmwZwF7cQEfNourPnMJkgGdpCenS2YTZz0Smds4cfhZNrbrjbmDq6qsYrLam4HG3siKkXttJkYDm4cyn/FN3Lg16WxWtJ2u8/hi"
    "qlhbIYLXgaeCpcW2tviO1JWjNYhOY3WZRY/KrN2Ioi8YnUsNIcf5GXQ3WHwK6UEISXSrxaq9F1ZULKXABagOTkl3LiRT7ZGWKZXF"
    "lBWxk8dbwvpIW/EG1amZF/oeYWWnjZauC8AZ7QvXXi8UcNBr6iJIjpQhEhiPGb13ZJPiT3xDTCK4KTolZfJydOcZbcqhPVo9tw6q"
    "vWxAze20IYwqUdY3fWDkSg0TjoNgAmXTvajXriGv7REmVt7eb2auN2YYrKDkDNh4VGGskaYNl0oSqmoUuqijbONl7M6oC6dmjsYl"
    "UmxPyYS13I9XXZeyYGOd69Whvh7j2cZqmz3Hx5ig79DeF4j4PGxF0Yxx2cIvlEaea2N1844HM7WQyDx4+UmnIDkatiVCId46YEeq"
    "Vca0sjnOllXbcESs3BzNY7jbuzYPA8XxlEZ6NWg3ckpWK0thIp9Vh4thtTmuXyyS7sOkIS+sse4Lec8wYptv++Jky/Rk78xAufk9"
    "tl6dBAunBRJwQoGKZL7duwFmyGSdDKVFKZZFchA9VGsTQm8xWdAwIK6EVTTaQ4qCK3as44xuAn/YsacIEA+6SB5vLBmEAofTKwHh"
    "L2Db8yMhcv2VE7ohgLxrmKFTYvYXtWUTNB8nNUCrTg1Bnt7kw2miDVaUa1LP6TVFjV12NmgEbMOTSMOUaAhcQxzsDA3EVUGFh5N8"
    "PpCi7Asu5Y5IeahDxbvpZKNRjoQ5PTBJZUGYIw46Gw7A9lGy3icNHLNdKDS5q/nzWKAk7i8Nc5stwDyMS2c1Yx3PGSDbmJW8zQ4s"
    "htshL6YBSZlDIAmh0ucBaaBMILQMUlT1bk9hTT1Z4QjRM502aR7lPuqS/YYtNNvd2bR7HWhTwFFmBiTKwb3OZtlkG5Oy8ZTrjABC"
    "Hzjvc93iqYOyGVuOmJdjWNG5INv8hDfNfuVnXRaAQoUjWu0KbqSJQT3E3Twmz9eYyKRqUkJswFOt+hCXdkDNxjkl1aV1mBeHHF9A"
    "cdFF8upmJY0UhGQ26PytYknpQjSHYgxTnexmYcKI54jcT6AUpgozVILDuAW62Zitb56E42leBydpbwNRCJwzr8YFS5qFnB8lxnYl"
    "XBFsPQAozq2GjCZJLhgom+IcaeVmECGXchSLgYYigYO16qoV/OvKkSyXSRwSamdGsrSirXc96RXEkcIAZLJnHM0h+4F1k5Oe6M3M"
    "DVVFngKF0nc2V4CCvypaTdOY29o0qHTnANMhBLLRHMAD5OJ5ye3ASxakfA3nN3d9bDVCHjayp9SkEdOQvNIRZBouPbKxJJvf99Ju"
    "tmKCOnIViGsaP52mGZmQV0zqcnVzXeFpAZ7TNZC2M87KNZku9uuLVNAnKZEbUnCAdX/zlUk1gMq/IRIwG/oTdznVxGHHc6c21eM6"
    "uV5jrAuMYu/MlAgPDcsyIUyZWxZXm7Nj7qFug6eX49XL0LNmOLvIihuiuZwdTL+wxXSTeFqa58zBSVJYXB66hXBjLsqg0ky31eZq"
    "pJzNBLejclsfHG6DwpEQIIDPHbfWDoC5E3b03LilyhMdoey+gmbtRBodV1BgT4BcCionI5ZivJURrMOQGA6N1QzVi/ikpL4ZncSt"
    "mJA7Dt9RtjQAK3IbkEPMrPmwistZt1PrfuxmQsKM0U/JAK3aSxUzw8yVmBOcfcQj+z116Dn/SonoDWZv3YjPxl6MN1xxUs6eWyNE"
    "lm8VqcwVDhx5lI2m+nBbQTtwzassyVEWF+eRXrD6oJq5BIkFyQSzpcKcorjJtgQzCH1FMvJ2gM6Ea0E1erzeqoLA5VbNBBujqEE5"
    "ozsxIRCiwLDp1EV7Zs1olw6BVdLDdna374PQmU3miwGByHi4DjUwVPmoIJVvHQGmSUTyUrNCPthUyOtyIHTTwSL1OrR2OwikegZw"
    "/NWwDXfaiufSGKXBsgikGjwEFx64HTSfoCgIK5JKMNKt1RTuwAr+cRbaMLk+Vud9y8BpxoDmZaOYnTLGGkhTKEEfykEN2gimlB0F"
    "Gq1D6k3b05UpB1sX7c6HKmbHFqBNOtoapxBr3GgSEHrHk6rqVysGyTY9FSIQVUAyCWsgiNu23CYgWTMr10RxtxL9W+7CoGo1INvw"
    "sw06xGufK11jdw13lrBHLuxBcxN+BmT7mHLAwY5xHRZ2O7MMt8dG7ssZxfHbqLzekLE5JIp8IHPK3lxKwz2ZhqheTXOgBvyMOkck"
    "XTGVviNtoxJkxu+2F147qh0uk/FGCGxx8o4bbXOe7JDxRRJvHUe+tXpQ3G4juZbFzc2oGVoPoO5ARDhB4cAsYPanfDyKeF5DTLD3"
    "0mvGt8hZZbZtiZOVgkUsDVHh6Ow5QMxDfCebwkFa8WE4EVsDnk0Azfb9tBX4GXWvjpcgl7a94BRkHmxSkifFmXYZQSihYEDMQNKl"
    "sdKQtXjND76KEpEymBYVA+SunMl6deK1K1NcqcVknflljmz5kbWPR6WvMSIoNodCWlkMichI2WVlKGln9dL310OmwzWTnTf2pjOc"
    "Pm7FHEKKWyaIwgpWEMqytWwF7wPVBTZU06mH0N+gK0A/kLuqQtttTRJsE+zYkB3ICxlwfMdz8o6FVdw/ujCz5Vam1ALi9gQAFG7r"
    "gQ2jbogIA3c96ydnb0wQD5lITMI5EpwNbAJZl8APhxFcr3ilDA8rvsdtMDZAonPNJCaZtQGNcE7VjWax0RXzZlUj7OH8msfAzrt5"
    "J27aYIeBuaHJ1s6TnvdzKYDYMwinhUA6TDPRzToioa4KaE8KupBU9g6uyVvcNNRag4RxbqpmKFo5T9pts0M5xCE3l1UQYJ0bj5fZ"
    "tmv3jl8EMNJMJkx4hgbaR1vDBpoV9ZQmBfdypTwfPo8zf3R4h9mCXXYDcHF2MNGaZlpqBdtTZ3jakn5JnlZEnKeound43cJDPBjx"
    "viFkr3cmkqQpAh11ZxwOB9HW9uaMMwZ/bMQg2wkDGbscvrlkkEiwg9wPim2e4z1z9WKwMy7IRgMMKj6L4yDka0DAlW2xXu/8W0QI"
    "zQm84LQdbRm3omKvwmeIwhAjWXsj02wCf3OAXR+eNTWF9zoGrDmaxYL+OkDuPHnEyAYmsAVOgl2f9g0fpEHFlBTNsI5/ElVr3+1P"
    "07hBQBflUhppyJS+DMamZWUaJIjTvswUSxUhjuQVjHf5M5VVfSjsvT7eHMsAhrDTLYv1dUqQ52wt7wl5q4nEKDFqRzrKrszwHFlt"
    "z0LXyzHsRPvblriyPnSEG1WGqCxDmPWGtUhUBTikkZRbHbTIpguP1/2GPiC9ADMocVRoEBBpknVl1jxDckJSEbXC2zBk/ayMEy4Q"
    "IjDxAvAy29s7K0hmtedks01GiFWdrHNrZi2/HTFwQ04tmKLXvSDCIC4VpHaNREdQuD67JpWap6a/HotTZtm+AIGJP8sgzL4qw24W"
    "vEg+js5NgkL00mXbnZzoMSAGCbXTelnxUYovR38kPbOZpYFtIRRbB2TgCyFYFxY1s+TtgMyyv4smyE3E3RbNUwI79qa/qRjpugdO"
    "+hlGz44XjueiobY0B6gXFNu1jlWLjmkaVYl6Nq94hCiSRn8yoQjJthE5yFzDTCsroNQdEHIyI6KWe1SBwT5tB54wKNLBbXINAc7G"
    "VvqYoaZp2M3Y6OzlyfkU8xVQHVdwJdrW8l5PS1eZrgNTuQpuPUw6yBGDb2wUZZOXii0C58Cmnm1XdZ0nHXkc8K1YdAKBThtgv2vg"
    "Y8g2JDeDlSEftoOGusZB0rr8nEqqkRQGrar55aTjlngjDhulzLizaeAmM17ODRkeyEnDuIDG641N6ZgsCjUw8SsIkILTaJrZTr+e"
    "TAcqyw2UybeYQ3BYdLDKkmhd0uuLWSkwVMiEAIsaffPPFgRQ2gkW9dtpWkGkiXs85Jmz5YqvxYihjItU3xgzUDHDYq6F1Tu4G3jt"
    "iXSpiGFnacPg4azDC0jMSCo8Gt2aJbXYcNLRX1G2tmkmG9XyYCtXrN7N8H4FexlYJZ7REC0kZRy2qUIBImKPpAVAhGZ4vuIs0ljz"
    "AYW2QO+wNmsh4BFyW/+4UjrOxBElhFg8YyZldNMZl2aAhuElzABQAYy7hlcNkO5AY3IRblOR0ghByGGrMJdLB4woap43aK3gxF4R"
    "PTBR1HNUoluZ9ygs2MEBe6y7BiIHGtCJsTwKOz1iSYTn2QpkC4VX9esEFdXpokfrZie7Ob2fEAk2Z3kywO3GggqwyI7lmbAUHmd5"
    "Er8oBoTcJoudIJ+FEOXm4XRhpTf4HLYzLChBzYIwxz6ICbPtgj0EYOvYAk7HbCXbfdQyPYIKB/QUGPMzijEenWhi0BXghDda4Pf7"
    "ieui0wCMtVhjjDk1+C5yYdUxCcjag9I+OaGaEs6mYd1jG5Tz0nHtbzccl+1Zkr0Axd5kZ8BiAPxAgMa+DWg3A6TecaRTvkKHVIac"
    "MNqAtXnIFLRr20oZNTtyhiHQGVrUbtcDEZNjcMmTq+Mxaj4iZyGrB7cDaWdH1XbvJTePTi2wRkB7IzHh0alkpiwOjMd4Yi3iitAI"
    "U7OGzpJGt9RV9Uh5JdySAPIBJ0X0fnvTGk1Gd+igSbfVyjf9cY1NHq4Q4VHZl+cDoELEDrQ7sWRKecrzG3TZr1pNwWSSCRcxKIcD"
    "g0RISYXDiSRdrKCuIHhJkMqYJCQRdXHTQNNo0d2JmSUrfARCyKzjMi4aAFQyYU+J10A0Z3R8oneBZnReaFMQ4MfrjZdD0JCXWtox"
    "aTfjN3Cjynl5s8ccZzQeFWRBEANQQZHTzjyHB6SxgnBCuxOP8rtTc51CrG6AYa9d1muyaANV3ULGJTGCYvRonior0iTDhg7oUq6b"
    "RqElGHCmMyvmOUOdzD0wpm5aK2xtUXyD9+GaEcU+oZBZDwqjpU+DTDaU2JG+i42NQe2IM7nLRFQiOjTncc2HQSyLc+48L6z1iksw"
    "1fLkFO5VJLgqQp9DaA4JGydEG2Irj+7JCDVoo+GEbd9wHO4jzAgA4CRyaSJsFas4FjIbiHZb6UhIbnXG5QjEVU9lJrdCcNjSYi5f"
    "i6MHXEqn1uGG4VmRqVFSPew3Pes7LE3DVCKKSDpl0DUZ9UAnZOWAsbQyoGHkGWIxHN2bCg7OzZ87mlzGwIR5rbIyGyfqRpA3Ry0x"
    "hd2VnhxCHdB5NbgziuB4Dic0Mz974jyogRKtVePSFhJyNnnig1nur7z2yinWFrrkLsQb8ECKYgt1SqjO09IOnnrR8AsJ+kIUu30p"
    "sHswZiCB9XCGuKIVK0A4EY6spu2oHeDzCjAjnPjKapNhGthVM66A4JN73hBmawnIiPwYQUhnL/ZVPluJLEKLrCwYY2Jtha2eABIT"
    "XEK+8alExkX4Up+3yJ45D5VMsLvNVI1CB1SJNchMtCbbHWvoFmSoMoki4YjlQkWtZ8XJ510iWgWew7I+TmuKn0RlF+GlUpf9NSjT"
    "LSADtce09fFo05fTbF1xGJlRkK92YTSUzJZkSCphbzcBN0WlaVtVzDUnNnQF79eawyl61YI70alA2N0CYiaoiTaR8pomGQFkAdKe"
    "AJdAtEtzYHVbxQEt8GY4QFpZD968dV22SdKaEARTuMMRaiAYXkh0GiHQE70RbuCNpall2Xq7le7uGT3pxDXt6pQTHAlljwsRrVWr"
    "Y0rFiU+5J1YR5sfJYPYSIjSICBymmnof5HmAKvCG9uDtedajYHPoTYmBh/URpIq9WINWanJ2JRqEqBM9IKcZTpxnnqT2pBzckFOY"
    "sRQjX9nbemUmI6Mh29KvxGPOr/aX7bEau1KcjTpZGmJSrJ3zCCRRMCvEM+sHGH3S1GjD7W6dN8ZFz2/MvZD16CXbNCONz9Yniik9"
    "XLRrMqAYDtH3AUvyos0N7DoO5qk3rtcVdyNmNSRp7vHWGweA9rlzdPGiUvECaeTBxtUTp67dJaZkGOFePWTiwevM/ZmcOlYFefC2"
    "m0zQ7oEEH3MRzGY2xRldFJkDQuVkNpIz3mEDaUDyBM8zx0PBOgpjkLePOiP7I6Zr/XTxTUMLtS1deqSOa6tGlCb9CtvFaSyA8Opl"
    "doHOhiKO7GbabEEUmPWIel3Ll1LkWFWaaJ2VgXwtUi7FBxKPcB4jDFZ0zc/na4qkCNX6uBEf2PVG5s3BusRoWg4rtj4HoRF15ww9"
    "iNspMI7FarSPyc70AaDZSmNVNOeplSkCIX1cQdhpd0SPdCEw+GwbrK61Nq91nU916kYCq9nKkLdnhD9JMDmJhtWSkuwE03o/rXeI"
    "FJ2VEIsNY32YDSWfJt2CGWoT0W7nqle4hz6uVV4TNHYEiNMKxg9WB+4HOtSHMEC0iYbIjmTsbQa1B2mUyKMlUKttmCMoQF5q4dzl"
    "5CXc6T4QXY6MxVwInOs7JmSY1S0Tqw1Let4JF3P6dkNUwFu7+QG2pVwivKPLrXqIAwDPT9INUg1+QQoq0IEXSpnkKhQDUwcJljZ0"
    "JOg3EE9latwdK2qP2Cm0HcM6dYKrT97U8XKb+P1xw2UNtwpTJQyl8BQCqnmlSPJCR7erSwXZShuzXczdbuywdsM6tp3W9hRFcgJ0"
    "sxLWp4DlRWja1Qd/hQKcVWkbImlCmRLl7abmPLo/xavpbDlme9pq+2628RRX2Vom2/WMe7ASqC3xfjiEiJgyItJSAVDvrbi0EYiq"
    "SU8KzzPOPLmELKkyaOP6uaxkFIa4QbwSVSAp0o3yU0cEHVduxROAF6VyRUkN3dhGmI+ZjLZhra6YvJ6SUdzDcCLawCqXle4qgUdM"
    "EXBmig9XdMMJPMUdj7VOK2GtmwcCPp33Eo2h52C00B2G19w0L9PrLQcrF4zzGwM29l5F04at10BxKGROyXRQOJicdxsPOesr4tYk"
    "MzFX2nDM23yU+1Nf9puttS4bF8XzJlOu5yuKbUGu7EkP7tQYP+7K6KopJiLNFuNBwOl13vi709pBWcJnbHlghkt5wm5DFJBtEFw4"
    "aU2qcVsU617YtlwiEGB+HtXDrBERopYjuZJnbeY13Y7t81pA9706YFYxOqvwgDp078eMMR2lJEC3UYC0SICVJekicU9E3GYn6fA6"
    "YQogozE6rlDXd7WgDfwVcvUvNHGoDXnWcLsi6i6sS58ooC1uOtcBbY7Wba0Bnqx7GW3Fx50PQyzJ0QhFUgFHN3RX7Hvkdh7kTdmp"
    "YIUb515gOL0g8BMbwubU8sAxUYSV5kKBCEqH3amVwWO2j/tTmklVyGZFeKqHXaMyva267DYAJwULV4oO16VzoPm4DwTOX3MwnvsA"
    "kxp2tdOI1cnUTvKE+1k2xOn1XB1mybZqHa3kbq6PhSRDk6udQ5NCcjnQYwnIuEmHSHHCqEnadCJr59BaOZ3Pu01+24Vd2G7XrMZG"
    "JBxrWcD7IjPCIcuv01lCXi37TA6ObDkDTnjTWZqXwqnaG/24FgjgQkxpgcyIbNRbuOk2zDmhvcazFI/3mbFIWa42iukGZgcTsLKO"
    "w1svFYJ0tE8kftrzWbwi8ZbcVtXGDDRxKD1WFAo6IukrOatXe4+dN1ez3bpiwh76kyYAiMadY1wlcbZWN4DuKiymE8dkW59nALlB"
    "6gLfVle+LYjidBuIG9QRlAQlTgniClqtB7UL6hzRD3Sg+aEvuSJE7ZIzVRdYmi9xC4ysgK7e0Ob2crMRgMP9XD+SQdBbOw2xqHoG"
    "smgUrVZepGnDMG3JI87E5NULXH5Udxx02yY5Dh22p6DuXAK+HiCXwxNCQ2eY1HujlELTZFDxxm1xMzpQzrDDRY3tLDbUw4Qhg5AM"
    "ovCMSRZWYiZj5KyFFSSogFNf1+sddYomx6QAb7ZA1oFgCYphZVmpCJQ3GLP5emEDQtGom8vSiExGyPZMYjq6Kb242IWIGW2TmZFC"
    "v9yQ4Q09reR6fWvONxUhU9bfAVoGr/uswUNQI6GG5fvTvlCyk7/xSlUBK5CgZIZsLMQQaaWg/OjS+rd4gq8eLK43241gXVlJqtYw"
    "BJReet4ZO5zxJXE2+yekJ+PO17WaJItMKdLYhJrreDaCrm3WLF3AKwpIkUhnO3LgJVu+Sdw501qScg01kPe1q7lgWxNHpzZZ1/BW"
    "wqzSdc2DUGyY9YNtz2wH9RTamZntMm3InuUO0+FJZPekAZkdE4ckRU/sTtC3CgRqAzMvV6WjkAuR+8I1lvbOFeMxoQDWwu3WqTia"
    "FP3BsIsu6N14NyDHKYWLrbOauIC0GCFGomg72+42aWv7Dd6EcRIfsrhKuEBm2ZOlDgM+pQRWbJG1AF8sr+dPhkBugixej47sXbsq"
    "g+2cwdT9WGLSLLDzoVcmnK80l0fcK4Xp9FplUlHfi4HqKnYASaaxdvdbVRh5IdpT+xD2mHJTQeCgcYLTROLZyseTSkB9TuIU7Gyc"
    "rlD1tdRse1BkiZQwpA2vnSusvIxqXtwYJrB3OgnjHLiuaJoUW9KcqWxEjsVICas7uaEK9bzottZ44MPTBs104uJnlGDjoqLx0WR5"
    "QgMqXHzwPFWlmwJlrZpINy57WnNb/sZecBA8lOf4NMLWDrHZmBE5Do0GHBUQBtrNhAzj8JjwpX00Nxo2rnfbVUhPx4KrAZyl5RFW"
    "lbXiUxgR7WZVfka8G6nc8l3lx+h1hCQtrBkpH9fhQUjXLhgmanTw5R1WRUWLrTrDBC33IHg4JV7U3UjR1GjPCpFhhQGoBXcWZY1n"
    "mCuTOIbUqConfhauqCxKPApVbUZaJnzYqKuxhdv83PO+UMFtM8odujkzAwtRVa5hqu92ExzSaM9TBtzGjpWn8M4nrofCEyibIQcl"
    "xw1D8Aawr4SEFwcDOmzKg2f6N2bSoKnAj2jcq30QtremDeQeSqGqMeRta67l9anqTmQTtP1WYHXzBgvqZhj865oROigSVylFB9nF"
    "bZF+gwlCfu0iHFbryUrciIkbwZX02QiW7Hm+CGqcdpo+a+bjWtQr2quweG3GCqJy1EoJ8bgTwWN/ojf4GFwomlbV4VrS18rRISKJ"
    "NjjV5TLh9ZvyNjQVekkQjNeR3IvLI3W7aQQaB7Mp7+E4QmzQWwuqrgfzKrITch+7CVQwo37cWWG3MSmtCAD487mH2nG9ZTDZV24o"
    "ejqo3Bman4HsTkx28m4sldFaihVG01DqZdvQ5abgkT1EnxpEGSjkHgcsEQ0D8ZHFHAVL1wcwuKp8Uoxnq5XAvpnFwW5QyU3SBYRm"
    "3EpYGMx0yBoLxW9xQUgm50xJJ1sXEg6s8xZmqtNlO9IQCvpYfdDCvXA637JQpdI4QrfwcLsW19UOQDeajnCnaE+4qXa1D5e05U9E"
    "vkt2J3GYlekN3hOaAu+86iZILr0bOPm03fuz4pvyaVO5PbO3EL0zCiK5WCs6lrCeSCxihu3VzKekDKcGFrj5jSgBeJcIwcg6A6KC"
    "OY9t/PXqmgoQY7YQxC52os6ttn03yqNlXxBQP3vRsao0hFdW5ErDYlU4mQbJyKns3+B4BFZ9vdvTva549CqZ8cqAzl2o6E2FNgRO"
    "zwzvNjsoq6uL46kpEUQ2wnaDSMm+tYryHeYDjTdNs/EdHnBKVmQLbYnDie8Ja50p5HqW01Fzjo51lWcMAjh22vuACk02JA1UBpQS"
    "ro143bZohjGMzxWFTu84gw9rG/YZayyOhF+kZo7pBclfNkiqYnF4uozQkYV2qZ474KX3hXHW2FHL5apkkzvZ2IjtrVsL0QZiio1Y"
    "CBp5i4G+BDgxPyCYd/Y0vwVMd6hI22ATlRp9gUFj4dqOfTw4g+HjZ3e21cN8veKrlYuDqS/bPXmJbML23R4dypZYORafC9YMj40G"
    "Pwj+UYIwgAB7/9zjdHmaMR1pzpDLw0BLXatHBLHW3g5VYdFYlwDikPAK2zi1DERQD2IV7k2g2MwQObRJea0Y9qk6wL3dpAXa36Lu"
    "FhmEG1Gzep8VgolVXgrHfu3cTHA27qNchgF7Vc4mn2tyKWSnNH7qrwfjsoq3dcWFUr2ZtiOlqgzokLUyz9sso5xaLXsC2a93QEhw"
    "V6ktkoGa+zhTZ6w/ifsGrJ3wxtBV1RSdfyoSXaO20SzVZzUpnDqbqJTrDuPqHij19c4rL+GhbMQZsuPdbNlMLsvHHpLtz3y+Suuk"
    "MQ/Z9rKZbpEAhJvbelZOh1vBedKKxYHeOng0lI5JuKKPvKPZVbK2piN2AkEvEVT2MqQOaVxJcX3uvBjaioonr5DZRCb4JDozNAPL"
    "Sp0IPgA78Y5nJqdac8LYXCkUvlqiwvd+LzQ6EoNpvSG4jWmw7mnS6yl1OEXyGiXP8+MsKy+NdtELx4lgh7SGemsUsuyVM0L0rB27"
    "P+nO7cREZ4MFcyDf4JPXr4qAuEoB5xpUCHlWpYepKiqMfpqgY6Udm2qd8mXLaAVZBN5sBfPZam0cORPymNNllo4+Tq2zabPeTurh"
    "cLhvmdkfjqohobQtit+9v5bDK++FUP7/2pITty+25FyDI3eyRhy4nGmbEPUkDc/zQ1HiZkaeHKUf3TVUGjB3NFYcvOuardTuB6uq"
    "sFWD9B2K+fuDzh6lGZnst4JH7yH2kGT+/pydb/IN1mDfu/H7veim8nm2Kvz2hk152sM1DOcagM1/4HA2C2LXvIRmvwnHgAYCu0x3"
    "LJX0201G7kMtx67H7bYvlNI+pVwizShgS4b7SqnqLYUfua7nVnaxn5Lj2pjnXeQr5sQR0LZQu1GKsCA5UpkIgFJihtimuR3PusVj"
    "+9w2pEPmG9i+uG2uu6O29viytm0/lHIKvwQk3MBn79Rc8g1zASkLONkKcRTgubH1MFbBDpmY5Fga+7ph3ZiZGhdmAH5NG8ZevNWn"
    "NS3uRhKlSelYRZKe33CFqhgsp9HG27nHg7YtawAW/CK+9rJ9CV0yJ3JjrJk8yNeHAGb5Kz4bnWCXOxKxz6qNvi9WG0zlUyUQj/uu"
    "KpzE2voZVBhh6sQhkpiWpmP46sDt4Hg2F+idvrVrJTmtjnx+oswIuYHrInb6m4WnKRBMZIdx/mlPijwibhLjCtJSXwVwyhPbA1Am"
    "tyC4pvZRJaqtS3KV0WOEe6u0U74+lQpIQKKX1OjxGBHetmTB2yzadxRj2UNFKPtt0t6EczMjQXJ/288zQDJYjIAGsAflap+Bs/YI"
    "DnULpI1Qlg4tjtc6IGqm13wsC1YMFuwLMGhJEphahBBxQyDcSgoiDQCuGKkMSSSKJjb03aEa1hv/hp0vTRhlaiUfhq2d5tdhIvjp"
    "tmWx1WwJoZVVyuaQxHkhGBqOS5cdKEk3KzKLrc1i6zS/EP6x760zB5aMwhMXCnGcOqgLoYuAyPRqMiLAGsUO53RY6XGrV2RAENrK"
    "u4h4OzKYKRGDhVsGK7ME5ncpvBKv2FG77KXiqFM7fNi4J3SGATJyAVWbi9aUe5bwHQPpaiT7leKkBsmBGaas5xXFJJcrFigQYVOC"
    "xxNEDO2VniowoUr4RkKktXw5aiOhbtr+XO4sTdufqMSFxcyXks2FyzVzvYrasDDc+JQ5O29FRyDUFX2jDVJ1OgdIR65PXHEtut1g"
    "nIQBRziZEjKzBU9cO9jZFBb6WJ/KAsPOeqjQduO4qgkdlH7czKBH14ct0GNnBiAwjFUo507fVGYcXF1nR+4CZwaxGgWptaogDwJk"
    "9K/weHKFcW6IdZ0V6tAVC4C5oXma1Ju4K/MIepRgm862KtGW6whmrrULsOdaSEvHHqv0aER4BYg5AXaXrrUHFiHpCQRBBfWuXu1D"
    "+ZFb6AAV4TG8CkEiY/0NKAY8zRq6G9hGjac0aWu8QKFRkk5cU81LFy3lWydvCoMLjgdSnoB2s0q9wgSAWfEe+53hzjRcb3PCP/tS"
    "ZObedZBKhZSA9HIa6zMhoNUVPfU0dPHzA67QNwA7u5u43PCrQ0Hv57k8r2CgcTmbUHZ0t++iFbE5qQUACEWzJg8D1kPOrQBCmqUc"
    "ohVoPsStY08dwF0Y7c4Bi+eXbeaJ2XjR+jFJpsaz8nJLXrkDSka2rAuRp6xpUpDVmlgTIacA/VR7AWzNY4fWUcRUB2LAthOHn9ye"
    "JSV7hiUXE0barqfZW2aSWelZcVJPhcWF7hnvsL4WenyWvyom3oZj7mWaMcH4VsRVM46wzkvw/4+281ZuGNmC6AchgHchvPcAYTLC"
    "e0vYr1/oZa9q01WiKkkUBzP3dp8mOMNSiTlw7IliD2hacxb9cTJ/qyK36b6Vlvus63zF3FiJ3Txo6Kt/eRzF7tGjVMbUfbetU166"
    "nv10/vb93V9L2VqRfZUMTrmzMsPQqxB9WnDM9nKtnfGsE4ufOd9AgGd65vIyi+Dn2eNMUngppQudN2SnfqvtwxrDr7GVE4t9bndx"
    "5bNd4ofo5AffpsyRftrHmfPEGEZwXZ79uul02iJfNnznQgz9MfitEFTNUtWXeGaLZAPXf0GSBuyV6KDwmJceN1Xae+HjqK1SKAOx"
    "cwaObykAY67IxiOGskr1AiVygX2/XDCWYlVw8Z+Bq4TJCrPRfcEAPisHn/XZcGVUJO38UnpuCZBjkFEuoMthTXDd6JHPWwiJz6KK"
    "x0z0eJ37mxXBwCagyv6RNMuamGv1hhh5oz5ToJf3IlK7s1XTuXhtKVHxSyV01RDUVXWqLZALx0rWtQq8GSv3nU+4rZ74E+WeTPwp"
    "FTOyFjCK8GfBilOHGYEuyvUWJzHghz6JP9piHwYnfQqxkrfxpif8QvlKWYOk73FrBR7VGLoyp15X43yUvqbKxno76qNydRuHLO2w"
    "BKY3KMvRDEccIXSnnILXwtEqvalTSL+iw/gNI4/lzTqFlRBV2kA8R6a5nAIqA+BbWiqIPkN/lwQJ9xWb3TYfDaGsXFYm74Lv6YZ3"
    "9Wz6ids4MUzgKdTPuOrPDwgHyAYG8pZaniC1VGBvznVaYtKrHPbgqS9I9ER4j9cQ1beQV65mH6Y5qQhF2ib6CGrkBtNwfb6vLZGv"
    "AGyb4LfuUTGyGEgDAF4R2DPGUl0iavKY/F48a0grBbo0FIR2K8i4AzBpABh7xSThCR27QLnEz3Mhe7NX+vggARay81bYc43VUEBG"
    "brhBjXD44VWgATeiXn9GXSpdXdF9hMOyaK1oIwTD162LmzKSKhLVni4dMAbQPc1Vt9g4b9FsqvM5gmu/AzKQ7AB6dfXRRCdWHEYg"
    "zYbB2aSQgbkx3Faf+dK9UCzf6EL8/T7SbLPokl0Bf/GlnRJK013p5wy+7pYKrucQFvAZCBLkvPKb6xtB8sX+Rq3BlRXUPovEAesF"
    "eHiJenz8ZKLuQwCFh+Za2DRGJR8xsz7d94q4DADog2B/NjfuZv0aHpU5SqCrqvANPzhtkeJ4j2XIvVHHN5Gv5xFskNL6D34wy6BF"
    "an5YxKKxUCzPbdy+DAlsSiUMv+vSlJMx54KNiawMoR4HGTM4qmXLGorZH6sqVEM1UeOz2yRZ53ZGHsXJuL+MlaOmRHoMPXQJiJHO"
    "yAZ0QW/127zPvaaJhqE0WKIltH5E571syuDqUkF7zC7F17PbMU7qTFF38UgIJssA6jjGWeSbzwaZTMsvGtDqxIW3zJMGDO3qNfX2"
    "7fp1xBnNHX5S0zBjTxOLL3sRySSRSPQ4ftCVK2fFPLvzjCh7oFkAdkuCyoVVYIrdEs0Bwb/BVO3xRXse3h0vZkOeS0L2ew61dm0c"
    "hC7MriuaT4w+oUhQKn2GdJMkrnVg/cdMnKSPB/qBcGRX0s3Ez0xl8DhmRdFLvj1/FYdmIiL288uGz5BqYj2e5E6qjTHmnmS69GuT"
    "UNmYTdV5cQEmi9HM/nAVTI/oEOe7gFfBGLTPG3A59gcGKtghZAEQIBeJsCqZccpOvxYqowcswyf7WtOHqKlkE7sX7Xq2mXE+3kE8"
    "QXrVLZCOcAVK7Bi66Bs8Wm7Grq1YWDNOn2qjEpFUN5sfrPCvk1c6qP+wuJgRoFmc2FjOprrN1nHWJGJ74lPvNAWJRZVS6sFsvaEm"
    "IGCu6erhAs4jXu2V+eCViRbOJT5wJLEmJCWutR2JkAY3Euvh12/66FuBiKwdcIUqyq7UQTK4r1zS6lchkxLh6NXdaU593ND9IvRi"
    "pLw4ORWQg5BeYMjomVcDJ9l9MOw3G7BU9hbsy2CU0cgYtlzNTMdyYwbUZxbFyjzfBQ/HXEdUZmyNoKM0/htBMZC4SE/E0M5FzEgc"
    "So+AX0JSI4SBOJnrLHtzQW7Ia1qvPodwfqo0JaYn8fBSp4CB765t/mD0LipSZFjTaNv3NXawQsfammgdWku7x2LRZO/jLC+2KEHC"
    "g4j4SHL75zPh6Yl75swG9rpyJkFDDGsfROe7GI5pkuDwZH0hqkEMn/YCaHiwuMK4VubZKtgZEyc9rscGHoOkKsJKmebGyjB5cGUw"
    "xpziYWyd2gYnmO2+hQs397mRfgIp8JgFw3WxjScG6CYQZHNBP+0sq0rFdD5tnczGJCp7KteDuoXjmLxFG2as5rKnkMlY7mE5UZer"
    "UgnjFTu6oyxNcfBZwiKCVr+qcgeOUts7vDlWOxmKHWra9UZqiwUOt5CYLRwZn2s9waRGYpyX6mnyZBCuP2V+Nx+QFO/ErDau6C1l"
    "fxfsx1bfNhgvTQq6i1G128J8E+ScrKwe9JqUgueJQiVng24Lx91ZJG6MnUVZLDRfrpjPyr15hGUe/ZTsdt2efRZ1HFjN7SeyRyz1"
    "cVq0Z4rIPqxpqJ2udTExgshIxQUB3HY9kzUDW4MhYhezpmLKESoSfjicRYtmBgnxNIHGXX+jsS7M8Odl2yZGjl91AnKTWlIGI3O5"
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
