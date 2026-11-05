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
VERSION = "1.17.3"
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
                if self.mgr.marker_of(k, sig) or file_cat(k) == "他":
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
    "Sj/783/4N/8ldPOLP/7Pf/m3/8Uv/ujPUJeKy6OG8Ju//pvG3BslwUHj99a33/cH27Bpvxfe2n4/CPHX+kZ//fZt/DV4/37Q3qBf"
    "G7fa77dE2e32eg9/tfv9jfcD/LXd2u6JVgbbt1q3WtTeerS1vtk49L7OgxEgniQcj29Ex2Jr8gkaMjvSvWefeTk/YL8HWdKP8t2c"
    "7NpEzd0nQRgJzfQ4Shoy0Rq9e7377NWufksEeoP0zaLd50+ePH8TvJnNjqPuUstX9aCPJDtveEvK9/gsjs5NK/AAjSTxuGigyqhB"
    "YrZGV/71xRvlnJxcvNJf0lMDbZXN22fW22fsLQpyzcTgATpFLkGN/qNegffm5/177/h6AHlmrQfM+H7AptlveJdztVY7z82HZ70s"
    "Ye+S7Pg5gBe0sxIxbIA2inL9OMz6YcKd3LNwXDwdH+thUcF+9FF5ecOGpxjhSEXHGZ8AbzRWMEQU7917uYvaHLHJj3ffqI/fK/8y"
    "OTZo+lFfvcSn1zA05VkPeLh/oQdKddHGJewV+gtABa9SrKdKxP7DiCy//d6pDsgzGr1Whi5ygh8ncaF7UVYwqoPSxMaT9+NeHr/H"
    "lDJ3HVmFRCrozIg4UZXpWMZqH8ZpOAqwCu9nHg2BUJH3RpatrKi+NcKFzlLKiCkA4SkNKjo2+D+PjHvEi7XJOEJrwd2psAhCvXbk"
    "nJrBe6c0Gtc7nSNGfjxBGYMOGY1sQLCOhkaXp+Y44EfqKMAIT9fEyD1SHr0UkRGcxxPXg9akhBvwsnpBS3NqHS7Vwhw9PcS8vkJT"
    "yLuna/vdtRwOijC5psmvxX1KQOudRLSGANWh2vIy/LOGwFn8XYtSsj8G2qqgaiewLF35rh+NqUWC9gT5VW0f5UE6BHjsuFohCZ8q"
    "bENNoWichrbSmCFpho8EmZDPdv1TAbSYYqSkucLGOwuYNhkW5/nAgbZd5aRZaJlDbhIES2NVmaAX4RjgvSVVNV/RaWl18wlNBdMs"
    "ECeb6IEvL0cUI1HOy1U63BXSYjFrJPMJvdKcx1cRQ8lxd3fkYAyZwIwch+NzkvygeVh6zSRKY7b66ualYt0MlV8glY/HBLeWTgps"
    "oSvT+S2neslSa0ldWs647wqNklx3bKrg8lyyuUFR7qVauvvo9SnKkGnukE803vnEnVdaMlLemu+FrLfSiGQ2UIoZSS3gKOarYlli"
    "nEpMwUQeQEwJQQOuH/qSS+FX2QSlQCkYVBeSJpQfaZPydC0sXK1PImo2xxgUjrOiBUD3RiiyeNls+vS/hrtq3uH31jsXjRCiTeHI"
    "drdplkPKF2JN12Ukm9OHKFteztZSOiLpSi7S+2jz7kTnNcfwUb1kAteaZtSFf3wu7HpBlg5qsYKoe3nmR15Y+DiLuaD3QzL2kbhW"
    "VXUNaDKJ9I5FY4IoifSHkiyJ6r4p5DdEgbBPiAahLxhqJqcyoj4wjYFB0nUNfzEWUOX0IDoMUtUw+dNXK4/lKCTBZMahKKXasefH"
    "jtAvYwDDjjl5BENSfoEKwXHTLSQZxjGGilg7S+40XZXiUMM4rvB2rFunADOciljcNJQIwxNdHllEq11RsSjF+WMKQama5+b4p0Qg"
    "2X0w0IZAYYUghOpUfHAQoxDeTDW2lCxZoL5biTvyg+wQLqL+DXSyOOohIKyE2KMQrR5GyUFCcvrfHynp7aGXEDDQ36JbACaDnAOE"
    "1ieHCDs5GUULnGi5ncYyHCQvFQgghPiCljJ1FcYScWWe5Op72XdEU0pRdPx7YQv+C0zEOdmMLS3RMboPx45RHvIwpl39Mmj5gvq5"
    "oYv4qevjHLC87uB9P9FpsSXtU8DMdONFtfECVYXXbX7YsxGyWCrCyLhOmCeYFCJ32hLgAGmgDm9qazMODr04sJZUY0FEsKRDEmsZ"
    "u9rs5G6r9G6BTgE6MINOjsWghQ0E3Ec5C71EORFXtBr5IaXJ4wuUH3rkEYSEqDlM1kqxcGXHJfKHSyXhmBMxT0Zuq7a1W4cLn2zl"
    "JIGISIKIq1DvpTBPlcKQMvhIzIUjZNpJJf7UtAh8+v6iQN+SJrqTEBtykBwKzRACQVkQXL73Y6/wafjemRRy6oSsSqwlppmtUcSM"
    "8E5rbbM8JLh7MVR4794MO9naWdC72+zCX/z/99Y2V3rwj9/zw7tb3f+HtjftmRzLzgO/+1d05wiNTPB1kREkg2RJ7QJ3MhhcgxEM"
    "hiB0Mxjc952M6gK6qgyN5AXeJcg94x4vI6+SbNgea8by6L843Vo+6S8MGe+Sb1Z1w4aByURGMkjGXc895znLPRf6dL73ML/6/Wj+"
    "bB/L/uJjJrW07t3HdH9nGu3MM16m9N6Fhea/+EbMc/AauD6GE99mWnLKCLzvJ5ox2x0ye49K2PeX2b1fLrdm1eNXlu/z/3cOtl/y"
    "WgVLVMDykTyqYvcnT0oZtIivR+3tMWHCD+55y34QXecH9woe63lwgmVLfLKo+t/73nf5RQ+ZLx/B5l3ULcL5I2H8yhCQPNkP3j2M"
    "7tsP6/m5OK58+90lhdKyMKyPlBh32czxkWpizaqJ9YtUk2XsPnnaLPD9v/K8WWBw6sW19O5h0YWeqIIpl4VfBHezFFM+LeXXaWSc"
    "4BsQ9r5Z+XGvzct8zKOYfdbMAGbZ7v08ksu5mTNF39/fzVDAy2dh9cbr59F4xd1fhTXfnVDOMq9PU/FihHy+c98g9e6hWwIwv1gy"
    "M327/LkRRbbYypZa3ODtt8t/9/N/+Bgf/t9t3Lx2kic6a+//f3chveXi3effClp/dbBrcrc03GnuyeRwn/dvM5An6PHMJGYSq5dO"
    "Lwj7aX05TRMF+dslfcQX7ULj9yY8mRs+e/ty+f37w4eFeBZl7kl4/PzeX6YZ9z2ptYsF4d7QR1PCctqtmxaN95pkv6kML2FST8T4"
    "9O5LSPkDvmzyuddb5I/R/k8VPQ7E6uGxpmXhfrOeV55n9478Zpm9n0XbooneR+rhKRzg3eM6n9lQG/nTJ89UMI/Md2cZRZV3wrij"
    "w90CpB8u98/70LzKFBJ8rJg8iov8WVzkj8kMF3tY5i1Sqn7S45f5met/ef60ih5ebjxJSwRaMvK8lBJG/pJFY+5C2/yVbwRbr9bz"
    "q9/u5SINg3tS2KVLy1r6Ro+eXnzZdPgSuBbek23OQ/fhjtNw8/USDH7nXB+sTwDwkC187t3DzBJeSeV7RPV90J5DMoJHp/B9206z"
    "TOD94tmH//T10199vJhh8X3k2rtR5GmqHmMbZ773geXc+/P5d59B/mLnvnfq2UTwYaj+cvKRHe1XVqgH/+hHTzrKiz303rsPljTv"
    "g8njqeCH7z6rKO+WX9+Z8Qe+fp/h+r7iH28+NeY5KOtHP9K9b8zTw0cHn1/Kl3Qir/rxTFUvrv9vNWtmhC8GyWej3LeNUB9e+XDe"
    "2Adj1Hrzgdmrd2b/S/USfrbImB8U34ce0ua169W/T+ibZvjLSytem4ZetfyzN//Lm+cwnHcP4lNgwCdO7jzqPvdJvpu5FpHzamKp"
    "bwSP+EvAyC8/BgPPbGZxlj3n4F5oe1krC908eUAi7/rm3d3Smz6fGvudX/z29IOZ1dzffyr4m+9/iJb+pXomwu997xVZ3e/8Cuyh"
    "9xMnHrHK/d6SuflZXxLLu3voV99cFwn/5tEd8IPHL4Xvp1Huvfm111r90rrloKRiOVrg6UCIe6nf/1D1L6tPQvjz+wY772H8NH9o"
    "neDT9qFZ7BdLCr+7Z/bhB8XMcuYp/DYECIMHBIVeM7byI8Y2KwEvRoch9GpvGbrHILHo7dOtd/ekgnc+9knTZZlTT+/up563TpS+"
    "vM++fb71bkl+94EEXqG+l1fbu9ds8Rp/Z6ao9pMlmHfRUJbfvPmzf/5P/+Qf/e3/9oe/919//LtvFs7z9sUY9qJrfIMRvHtpxptf"
    "fQOwT0vwB6lz8dK5ll9bQpkeVZAf/qUfvj7GfkE0C+3/8jOsmcf8KR0a9Kg9PVucfvSjxcD4ox9Z31ysc+MeHs8nf6WCL/PzFPT0"
    "HLhulsu50st6eLQEPNHnnVzfzgQUfTLeSeiZXh5+HjG9UPMrapp/+EhP7+4Zmt4oCzN92s43i7rvPFLFXPbrB7MqUmdRs1jll2iJ"
    "oHZmxnl983HnPnjMPyit0SLrHv3SSy776GVfTXq3gdQfYhXv1q3nGYM/rLGlzNdNeXkJePPf/vP/9f7L3//ZP/vNP/nJf3jz8Pl9"
    "02H6okcij1aMYmYxxdznO3F+NtPpy5dl29N9X8ISSjCTwfKgjdo7pX1nobTiZdgXCPC44fKP//HiuPx0efeZut99oBXgQxeQz374"
    "l2aS/OGnd1fdvA4X3nh53DtaezNsqb1n6bOkLPnud/NPusUaE7nJ9NDM9L5k+Hm6udDH3bD9vHnDexSBn34XWsyCMzpy08W3M/f1"
    "8+KTsr7jBOYxAeaMiZ4Wuv8osx/07u09cekT2nqGmunrSfv8Q8jn+OB8exLmsbnndP1B0xZl6V0/e/OrP/vyf/uT3/sn8+i8zMmv"
    "PQ3t2+gXDeSnz28U93jYz968//Hf/tl/+v33X/72n/zkj99/+RtvgMcHwJuf/eQf/elPfv/9j//Oh9l6nKuneZ8ZVfE4zo+U9j85"
    "xE9XH0Z4OVfmiyUx2/MYu8vg/HfHuHiNpj57O8v54lHOF8/S717tY5F3vNGGd0E03yyaHxTlckpT4H7zV+8+vU+e8zJ5X7xiT/2i"
    "+N53HcyK/9tHj93bp3aR3TUqnnZY/OhHTzcH75JE7etHi73l6dCSpVUvCa+XIy0XP+RM8q8B+occzC+Jje9Oqw8D+sQF5/YsrXv4"
    "btq8+yZHTJt7eM5TqohFFAGfQOslvPwpP+8Hk567vHff2KE2bvS0Cevdw/XlNu/MC3FmMY/pyd40d87ofuIv1ODl7vS09SN9uH4S"
    "zK8unOmeApK81/t25f3lZUtp9O75+bL/fdnWGzmp4WSlWbx++5P1enl5bu1q/T/2i+fygWI5rWpRYpY9I9flx89f8rt/Lsrvy2x5"
    "626fvW/su38pyrf3AuZa0Xntep+9rd9iCPQAPczNefdQv0UIZL6c/8H3fCz1WwLHl6erzfJ0Ba+I+RqdHz/ZC6Tmtb1gQe/LPErN"
    "tyTYixV8/sUH6HBfYPOoPoLKhQK+oTh873s/T294tEm8/Fhq3j0sDXlIPnZlL9aOZ/401+192IVzX/zf9z57819/+299509+69/+"
    "6f/+4+/cLQgfdJFFPrz51Fi8HA/EBzBrPHqfXxv37v6z7v6rH7RF66QvoYBv5xrezogWePPuiVVdo1c2jqV9ny9j9fYbDVtq/ZZl"
    "6lY+LdBHq9RHAvZOoU2rvcjZD8vsvnJegPk3yhyfJux5sj6/vH0Kh3n/1b96//U/fP/1v3n/9R+9/+qPl8+v/8n98zfff/nP33/5"
    "B+9//OX7r/7v91//y/df/bPl5lf/6f3X/3x54cvf//Ov/tWf/97ff//lv37/5b96/9VvLp9f/tX3X/3G+y9//c9//A//9Kf/5/sv"
    "/8Wf//Tfz4X87H/9f2Zu/f7L//f9lz95/9Xfe/Ow+bAperFe3Bv/C0DG9773CzDGPYrpkbXOnOfJhrfkqTDvhq7/qfJeMMtHNqmP"
    "hNo1mgX/+69//T4qv/HY0Wdc8eb9l39vGZin3v+NP/vdvz7Lp/df/u59YP7G+y//7Z/9i9/72e//Q1W6D+7vvHmR+a23hNK8iJuP"
    "GOQXi6nrWbLcqfIbcsT7wOnvqH+e3Q9N+Bf/7md/6w/ef/kP7vXfG/I8DX/xR79xn55Zkv7xz379b/7p3//pX/zRb755QOa5eeVi"
    "eDn5/dH4+PkiambF4S5qPs2/+NgQeX9nFg/Bs4Pt56jKz9466NFiOf9bNF/uRRl+/PasBd+dGY/+x+TjmKgXY9Fi2Hw0d332yT01"
    "wRJ8Pguwn2+KeDHzel4+z9s3uvPukzb08rdu/mzhvI/3F49ccFssnO2DDfm17XJbvMT2FXcX5TfXIFd+w/rz7JP+WNTdzyh/Vozz"
    "J039rsM+Zut8MVb/8N6LxxH57D52v/Q5uxgS78biL773OIBP9x6BwRc/fE7ykr7IYXb3ZJP4UOsrM8QSBPDBnfEUnvZ6HtJPMq9p"
    "nMB7mY7nZf0/VvjdrsZ9v/7m5C6H1y8DCX1gaq+IUl545Cu/789zjXX3V16cxtDPeSd48m89k8QCqD6QRO2ld4J4HLFZ1by8bV96"
    "i3rPovGXitcWjv7R1j3f9F5JgCl4SWX3S8W7+enjLo2nkXqe+GeLYPtIxXcu/f7reeH+y/df/+v3X//4/Vd/989/a2Yof+u+ZP/g"
    "T3/yT//sd39Lo++sZFnD94u/eV/ev/O4jF+x2LnUD6jxqegfv//6t5aiv/qD91/PYuDr5WIu4+dX+a8fhcFf/NF/fuRhf/FH/+W/"
    "/vrfff/jv8GOZVrUXv0d8DvcEkFSf2cu5OlXP/6bcwl3GfPv7yX89p0FzaX9HwtH+vKvzizoKTL0y//w/ss/XJSC//Lv/vynf7zU"
    "u3To77z/ai7np++/+nKueuZpP/vDP1yasRT4Dx5Z6J1lYa/6+jSpD79g8P7qKyb4O4s14GG1GJDvU+k97RN4mTfh+SjBl1APL30M"
    "77/vr/r86QcPunffYvxquOsljeyydzxfLpYkv+1HJqD6k/ZXEBT63vfuTgjn0iznFtxzt57mZ+O7X8F/ziN7fjTNjz5UPBPW64rn"
    "25/Xn+YPiz2n/fRDdQ/jpy/FP0wv1/YXzy3/JrM6POWqcpdcqnX21vrsh++/mnHBby+E8tXffQy6fRbpv/P+y7/+F3/007/0ErX7"
    "/quvZiVvefbVX3t8Y57n1zG9C70uc/OP76Bioaw/+Tf/eCaQP/uP/+lnf/0f3Mv96Qwe7tQ8k+csO//an/7kP7zUN8/5+x9/9cN7"
    "fqP/brPefPo/0PTHtbTglWe5+Y0OLPW9e43LnnnG4lq4x48+cdanhJVv8+9ET9lNC/87S06kp7x488rLX7jIaxj0xQeHyP+UG+Ru"
    "iX11wskinL4h65w0vRsDvinjvIW3ec+tes1oPedjk+qTR/Up6mFxxb4Y++4eq/7+8Vegz+bPT6FX+/yX1vzqm3vOfK+e27/kg5p/"
    "/XQ1hN6MHn7txbYwN+hFeH/LmeQ9O5I+inH9QOxfPHxeLj6s3luSbbhOOTfPu/f73cMvLvXjtvXRi7L+7TfvsOvFnfVtVeSVzjDL"
    "+DueeYVMPmCiewDTIiCfnAPfxCbeLwQjd8r4WKlK7oG7r2JNv3iAPeTdw3OR5f0ov8cCvfv7r4J7X/LZ3TeZfvDlfVztw8eO388/"
    "EtnPS/dFBC0IczHFet9CCC/7fvju+5/fE6V9+mbxfn4aZfNrYJkHv7xkRdkgD9GRUo0BkvigIOc/yv4QsodgvhKXr/T8157/Zxgt"
    "E3bLHfKk7A1IJOsGcTc6SW6T1dZguYO3vbW57pFHxUJHDMcup94/75MdDTVH5ygl3MAaHtTKsZBW8U5g15okF8E+oXZUHJknvqIT"
    "Bx93XFBIASFuaJENc3rV23B10XoPBHOzuamYjHX4rbk1k3UTcbRFB8zFcRQGXRA9IzcVig9mPQGnMblykBXbuXmQVucdO5LpXmFM"
    "VlRVO2vaswSMSXg0gjggzl6yOstUmE0BzK4s21VpZkVFUcsHbkvxF1M5b/jxFBy2VCGyCs2pWXONd9a6CwSDzGSmLcOmVc9e0Lcd"
    "rCYEuY6GBBMpn84x1NzZio4ejoVD0p5a1YrRKxy/d0Xj1tDD4RZ3/SDYOhIpe+8YU+Jmtzoqq36LVeIWJbjAvYY32AKzim2psqfH"
    "lOIG5oTJo+1FlFoiU98cUiLquuOGUo4Gf60ih1nTwoY8ltxmazArc7pUQuSdWfAonerVdZ2mUal6DHwUWUMne39DQNiaD7aAsrry"
    "KVCfpbEbA7XGVY5m+fh4uxmdirK9oSZQXGD+EU3Kg9+pR4Aury2fDeaAZFgaJEJJ8M75YGQEtcrDLERCQmB2LsvC01k/m4inpa3Q"
    "Esja7JMjVK2jI7mLeQLJIn+1t1Oxt9Cp7vx4nEeKH4fN2NCevN14DU6D60bZr+iB3CLArU+RS1Ccfb6yoRI6u+Yo2NLBkaSaguqZ"
    "k/cQIEFxKbk6aroU7ZGggRqrEK+O1rXXJCbaQQpvr9kuKqx8D3QNv8eUcRNeAdpizkx0vFlSNdnEYewsYtT2YnTlos0Ic3XBpETD"
    "So4sAPRRlAouznJSidGBUA+ggXupqezEBus53qApxVWhUnel7ZXPk4ZFR5PsEVDc3hBi211ZJ8fyIO1oaThXZoqAliL7JQ7vi4Dx"
    "1CnqrZMi5amyF4D8pk7q2TW2VygBbkRzDrOkHTalklE+U50aj6EuJ8mFu52IY/1NvJW7lLOC3rx0+LU4zoNBmwiHawO1NTV1WxI0"
    "PgIMNERXQdCZMq+IssWZAe1UCh4kRIIJorV8AXX7+iIEW1bKt5NiFWVOlDLR85sMY6Srp1AC2VSwJIsa71rMVTLSnL0UUgO25USX"
    "dYgD/o6C2ercZGQfmwp4Vk7opJeEszkCYnwlD3uGNW7AulmD6wq6hKUKn4JtsAXR7bkjPFbt4p0snmzovD6XG8MBa+yWwAhtkSl8"
    "dk7EeDU011odjjyYrg2hZ/ex11K7mZzhnPTN4OiReRiWtxOcbBRJGEd+I21d9RBLHQzgotEJZO2SaTaNOY9P++EKc3iBRAR15K9X"
    "U78JxlTT3GEzM4t1xpBb7HzO285ABNyWjufhmLF1Ukotq5tNrNcCWiXgtFI1fT+MlzrGR23yqLlOdeuuU+CGb9gyDBLkQjEkKFhW"
    "10GcXNq6mBurbTZ3sPSVuKiFYl+RBnGxy/Z0RsW1ME07AoRxBt0ca4nb9JmPJVu/VPSA3imrwNOOUbSj8ZvR1yA4XPayecB3nLLB"
    "NPZ82HcsSZ2J82lFWBgWM2XDbOcmaULRQo7prWPXupmmK81tdnerFNyc3XEIXKMPevtYrYm6SZvNlqcDAcfW5Q26IlFnNqo68h58"
    "PhRG3Ousv9PV5gJBlA56qxRiUKHuVs45ddVUOEEkzWsxeh2QFkWzceS8WwKJultIZErDUrAukSDo0c2FcdMNH6YbTE2rPZaiqZBN"
    "kGQCbt3VJBmS/BGjzD23O/hygZxjXUySC33UoTKp9o5wahtWFLdQojprsSBQRJvFw4aisjwKT1oSkTjiX4Q+0wxlldLNKSwWtT7G"
    "USvd9nmcBBuUFHW8ObPGLO9yyznXYeKbhaC3o9FAnHQ0KwrbrbLTSu5XwyrBLvi4Sppajm0hUEeatV2trLQ2Hv2znGaxQOo7aN+e"
    "dd2wjHHP76epMbTDpZ9qYR8YtH3WgxDQiq2wDR1ezkToCCWazzsEcYxQcI+vBGuWyfIl84EROoQDVBWeeqmHgA/OAuOr1PF4Kcyt"
    "xcBtWpepGDM0FvoHdtT6HenZQrz1zDjr1dgRKjXQRwcGvbadysOh6wIF9i6V7ESikaMBvTcYW1cNWspC0kucamNhPWwD8m677yyA"
    "DxppHXGkVpiUp4P5NGw21+PQxG6/R9Bid9IUWtmjPb4proQsWiKauFYbuPKJIjOI9AwOTTqYAUZdMdArFMBBl1BwdKFuXKdlViro"
    "B9WNAj1wg11Qxw4YGfz+vDfFGirgma8B2jTKfQrsER9Zw5DNyecsmNphZv+QHhBqtPEhVXJN9opHMkNfrnhb0tgaviG1Q41cAexk"
    "dz0WiLApxGYUj142WmInkQKYBlIBTZzDrjx+nWfeIOHNbhS46poDpFHuZSeTUFSf17IOaJI+nSYSCevzmjrwW+dixReEZky0RSal"
    "MAIiFo+7W7NGA1u4HfzWqiU8hrpyoANucEhYjPBIG2bWZCLreLiuAsUzDQ2l+lmor0O9rAXN3B9D9Sxch71Ig6J4s0XM7XVThm9Q"
    "B4Oyg2C+Yo804Le0OEjDUMYDmJkNeIRAOywqyuSd4GB10KT56ZnjgtM1bM5nfBDXquoKwGELnHfdMa/xTejsoNrtNM5PSn3dD0hq"
    "x6tjgcVBrG425+sOhCMQKGFhvz6OAI/nNm3YVhz6pMtbrqbfBmzC+OtlHAGglna0Gkc+daWrS0Cheq/2hQpq0ZYr8euYjLuDR8Qe"
    "bEpEJ6/4I3dcHamRoQryply6nCfmelDOWa9Al9S2k5bFTlkjaMeH6x2wc26ucEjTc34GvIBfRxEJB2lx2KNdNpA2kV+B0ixF5Vpe"
    "dzpHqyhvVi1Ugl7Yt9dGctD9ViVx0N3dnJtSlp7gtvCpDC+yFnPO9hL6WkzAo74vRSAqxJCUj1lxvvYTS7oOrwIXcsNFWZt42eYG"
    "WUowaclOu0Fm6cF7xQMPl0ZODlrAkbKHOTmyllqfOADathDlMVNsJ3PZto/mBex2lyrJ97zFXEQyIG2EwsroZADnxD5g+ngZph3C"
    "kFndYiyEcMghY6mGYmiGdpg2aU+gc1w764yQgzxHXC31SUTlpzWgiPneznhW1AR6jIpNUB+UWEdUe2BFBBZFSkbinoSoSbBnBntx"
    "AR82i6s+UwmSAZ2kJ6dLZhNnPRKZ2zhx+Fk2tuuNuYOrqqxistqbgcbeyIqRe20ejAY2D2U+45u4cWvS2axoO13n8cVUsbZCBK8D"
    "TwVLi21t8R2pK0drEJ3G6jKLHpVZuhFFXzA6lxpCjvMz6G6w+BTSgxCS6FaLVXsvrKhYSoELUB2cku5cSKbaIy1TKospK2Inj7eE"
    "9ZG24g2qUzMv9D3Cyk4bLV0XgDPaF669XijgoNfURZAcKUMkMB4zeu/IJsWf+IaYRHBTdErK5OXozjPalEN7tHpuHVR72YCa22lD"
    "GFWirG/6wMiVGiYcB8EEyqZ7Ua9dQ17bI0ysvL3fzFRvzDBYQckZsPGowlgjTRsulSRU1Sh0UUfZxsvYnVEXTs0cjUuk2J6SCWu5"
    "H6+6LmXBxjrXq0N9PcazjtU2e46PMUHfob0vEPF52IqiGeOyhV8ojTzXxurmHQ9maiGRefDyk05BcjRsS4RCvHXAjlSrjGllc5wt"
    "q7bhiFi5OZrHcLd3bR4GiuMpjfRq0G7klKxWlsJEPqsOF8Nqc1y/WCTdh0lDXlhj3RfynmHENt/2xcmW6cnemYFy83tsvToJFk4L"
    "JOCEAhXJfLt3A8yQyToZSotSLIvkIHqo1iaE3mKyoGFAXAmraLSHFAVX7FjHGd0E/rBjTxEgHnSRPN5YMggFDqdXAsJfwLbnR0Lk"
    "+isndEMAedcwQ6fE7C9qyyZoPk5qgFadGoI8vcmH00QbrCjXpJ7Ta4oau+xs0AjYhieRhinRELiGONgZGoirggoPJ/l8IEXZF1zK"
    "HZHyUIeKd9PJRqMcCXN6YJLKgjBHHHQ2HIDto2S9Txo4ZrtQaHJX8+e2QEncXxrmNmuAeRiXzmrGOp4zQLYxC3mbHVgMt0NeTAOS"
    "ModAEkKlzwPSQJlAaBmkqOrdnsKaerLCEaLncdqkeZT7qEv2G7bQbHdn0+51oE0BR5kZkCgH9zqrZZNtTMrGU64zAgh94LzPdYun"
    "DspmbDliXo5hReeCbPMT3jT7lZ91WQAKFY5otSu4kSYG9RB3c5s8X2Mik6pJCbEBT7XqQ1zaATUr55RUl9ZhXhxyfAHFRRbJq5uV"
    "NFIQktmg87eKJaUL0RyKMUx1spuZCSOeI3I/gVKYKsxQCQ7jFuhmY7a+eRKOp3kdnKS9DUQhcM68GhcsaWZyfpQY25VwRbD1AKA4"
    "txoymiS5YKBsinOklZtBhFzKUSwGGooEDtaqq1bwrytHslwmcUionQnJ0oq23vWkVxBHCgOQyZ5xNIfsB9ZNTnqiNzM1VBV5ChRK"
    "39lcAQr+qmg1TWNua9Og0p0DTIcQyEZzAA+Qi+cltwMvWZDyNZzf3PWx1Qh52MieUpNGTEPySkeQabj0yMaSbH7fS7tZiwnqyFUg"
    "rmn8dJpmZEJeManL1c11hacFeE7XQNrOOCvXZLrYry9SQZ+kRG5IwQHW/c1XJtUAKv+GSMCs6E/c5VQThx3PndpUj+vkeo2xLjCK"
    "vTOPRHhoWJYJYcrcsrjanB1zD3UbPL0cr16GnjXD2UVW3BDN5exg+oUtppvE09I8Zw5OksJi8tAthBtzUQaVZrqtNlcj5WwmuB2V"
    "2/rgcBsUjoQAAXzuuLV2AMydsKPnxi1VnugIZfcVNEsn0ui4ggJ7AuRSUDkZsRTjrYxgHYbEcGisZqhexCcl9c3oJG7FhNxx+I6y"
    "pQFYkduAHGJmzYdVXM6ynVr3YzcPJMwY/ZQM0Kq9VDEzzFSJOcHZRzyy31OHnvOvlIjeYPbWjfis7MV4wxUn5ey5NUJk+VaRylzh"
    "wJFH2WiqD7cVtAPXvMqSHGVxcR7pBasPqplLkFiQTDBrKswpiptsSzCD0FckI28H6Ey4FlSjx+utKghcbtVMsDGKGpQzuhMTAiEK"
    "DJtOXbRn1ox26RBYJT1sZ3f7PgidWWW+GBCIjIfrUANDlY8KUvnWEWCaRCQvNSvkg02FvC4HQjcdLFKvQ2u3g0CqZwDHXw3bcKet"
    "eC6NURosi0CqwUNw4YHbQfMJioKwIqkEI91aTeEOrOAfZ6YNk+tjdd63DJxmDGheNorZKWOsgTSFEvShHNSgjWBK2VGg0Tqk3rQ9"
    "XZlysHXR7nyoYnZsAdqko61xCrHGjSYBoXc8qap+tWKQbNNTIQJRBSSTsAaCuG3LbQKSNbNyTRR3K9G/5S4MqlYDsg0/66BDvPa5"
    "0jV213BnCXvkwh40N+FnQLaPKQcc7BjXYWG3M8twe2zkvpxRHL+NyusNGZtDosgHMqfszaU03JNpiOrVNAdqwM+oc0TSFVPpO9I2"
    "KkFm/G574bWj2uEyGW+EwBYn77jRNufJDhlfJPHWceRbqwfF7TaSa1nc3IyaofUA6g5EhBMUDswMZn/Kx6OI5zXEBHsvvWZ8i5xV"
    "ZtuWOFkpWMTSEBWOzp4DxDzEd7IpHKQVH4YTsTXgWQXQbN9PW4GfUffqeAlyadsLTkHmwSYleVKcxy4jCCUUDIgZSLo0VhqyFq/5"
    "wVdRIlIG06JigNyV87BenXjtyhRXajFZZ36ZI1t+ZO3jUelrjAiKzaGQVhZDIjJSdlkZStpZvfT99ZDpcM1k54296Qynj1sxh5Di"
    "lgmisIIVhLJsLVvB+0B1gQ3VdOoh9DfoCtAP5K6q0HZbkwTbBDs2ZAfyQgYc3/GcvGNhFfePLsxsuZUptYC4PQEAhdt6YMOoGyLC"
    "wF3P+snZGxPEQyYSk3COBGcDm0DWJfDDYQTXK14pw8OK73EbjA2Q6FwziUlmbUAjnFN1o1lsdMW8WdQIezi/5jGw827eiZs22GFg"
    "bmiytfOk5/1cCiD2DMJpIZAO00x0s45IqKsC2pOCLiSVvYNr8hY3DbXWIGGci6oZilbOk3bb7FAOccjNZRUEWOfG42XW7dq94xcB"
    "jDSTCROeoYH20dawgWZFPaVJwb1cKc+Hz+NMHx3eYbZgl90AXJwdTLSmmZZawfbUGZ62pF+SpxUR5ymq7h1et/AQD0a8bwjZ652J"
    "JGmKQEfdGYfDQbS1vTnjjMEfGzHIdsJAxi6Hby4ZJBLsIPeDYpvneM9cvRjsjAuy0QCDis/iOAj5GhBwZVus1zv/FhFCcwIvOG1H"
    "W8atqNir8BmiMMRI1t7INJvA3xxg14dnSU3hvY4Ba45msaC/DpA7Tx4xsoEJbIGTYNenfcMHaVAxJUUzrOOfRNXad/vTNG4Q0EW5"
    "lEYaMqUvg7FpWZkGCeK0LzPFUkWII3kF413+TGVVHwp7r483xzKAIex0y2J9nRLkOVvLe0LeaiIxSozakY6yKzM8R1bbs9D1cgw7"
    "0f62Ja6sDx3hRpUhKssQZr1hLRJVAQ5pJOVWBy2y6cLjdb+hD0gvwAxKHBUaBESaZF2ZNc+QnJBURK3wNgxZPyvjhAuECEy8ALzM"
    "+vbOCpJZ7DnZrJMRYlUn69yaSctvRwzckFMLpuh1L4gwiEsFqV0j0REUrs+uSaXmqemvx+KUWbYvQGDizzwIs6/KsJsZL5KPo3OT"
    "oBC9dNl2Jyd6DIhBQu20XlZ8lOLL0R9Jz2xmbmBbCMXWARn4QgjWhUXNJHk7IDPv76IJchNxt0XzlMCOvelvKka67oGTfobRs+OF"
    "47loqC3NAeoFxXatY9WiY5pGVaKezSseIYqk0Z9MKEKybUQOMtcw08oKKHUHhJzMiKjlHlVgsE/bgScMinRwm1xDgLOxlT5mqGka"
    "djM2Ont5cj7FfAVUxxVciba1nOtp6SrTdWAqV8Gth0kHOWLwjY2ibPJSsUXgHNjUs+6qrvOkI48DvhWLTiDQaQPsdw18DNmG5Gaw"
    "MuTDdtBQ1zhIWpefU0k1ksKgVTW/nHTcEm/EYaOUGXc2Ddxkxsu5IcMDOWkYF9B4vbEpHZNFoQYmfgUBUnAaTTPb6deT6UBluYEy"
    "+RZzCA6LDlZZEq1Len0xKwWGCpkQYFGjb/7ZggBKO8GifjtNK4g0cY+HPHPWXPG1GDGUcZHqG2MGKmZYzLWwegd3A689kS4VMezM"
    "bRg8nGV4AYkZSYVHo1uzpBYbTjr6K8rWNs1ko1oebOWK1bsZ3q9gLwOrxDMaooWkjMM2VShAROyRtACI0AzPV5xFGms+oNAW6B3W"
    "Zi0EPEJu6x9XSseZOKKEEItnzKSMbjrj0gzQMLyEGQAqgHHX8KoB0h1oTC7CbSpSGiEIOWwV5nLpgBFFzfMGrRWc2CuiByaKeo5K"
    "dCvzHoUFOzhgj3XXQORAAzoxlkdhp0csifA8W4FsofCqfp2gojpd9Gjd7GQ3p/cTIsHmzE8GuN1YUAEW2bE8E5bC4yxP4hfFgJDb"
    "ZLET5LMQotw8nC6s9Aafw3aGBSWoWRDm2AcxYbZdsIcAbB1bwOmYrWS7j1qmR1DhgJ4CY+6jGOPRiSYGXQFOeKMFfr+fuC46DcBY"
    "izXGmFOD7yIXVh2TgKw9KO2TE6op4awa1j22QTkvHdf+dsNx2Z4l2QtQ7E12BiwGwA8EaOzbgHYzQOodRzrlK3RIZcgJow1Ym4dM"
    "Qbu2rZRRsyNnGAKdoUXtdj0QMTkGlzy5Oh6j5iNyFrJ6cDuQdnZUbfdecvPo1AJrBLQ3EhMenUpmyuLAeIwn1iKuCI0wNWvoLGl0"
    "S11Vj5RXwi0JIB9wUkTvtzet0WR0hw6adFutfNMf19jk4QoRHpV9eT4AKkTsQLsTS6aUpzy/QZf9qtUUTCaZcGGDcjgwSISUVDic"
    "SNLFCuoKgpcEqYxJQhJRFzcNNI0W3Z2YmbPCRyCEzDou46IBQCUT9pR4DURzRscnehdoRueFNgUBfrzeeDkEDXmppR2TdjN+Azeq"
    "nJc3e8xxRuNRQRYEMQAVFDntzHN4QBorCCe0O/Eovzs11ynE6gYY9tplvSaLNlDVLWRcEiMoRo/mqbIiTTJs6IAu5bppFFqCAWc6"
    "s2KeM9TJ3ANj6qa1wtYWxTd4H64ZUewTCpnloDBa+jTIZEOJHem72NgY1I44k7tMRCWiQ3Me13wYxLI4587zwlqvuARTLU9O4V5F"
    "gqsi9DmE5pCwcUK0Ibby6J6MUIM2Gk7Y9g3H4T7CjAAATiKXJsJWsYpjIbOBaLeVjoTkVmdcjkBc9VRmcisEhy0t5vK1OHrApXRq"
    "HW4YnhWZGiXVw37Ts77D0jRMJaKIpFMGXZNRD3RCVg4YSysDGkaeIRbD0b2p4ODc/LmiyWUMTJjXKiuzcaJuBHlz1BJT2F3pySHU"
    "AZ1XgzujCI7ncEIz87Mnzo0aKNFaNS5tISFnkyc+mPn+ymuvnGJtoUvuQrwBD6QotlCnhOo8Le3gqRcNv5CgL0Sx25cCuwdjBhJY"
    "D2eIK1qxAoQT4chq2o7aAT6vADPCia+sNhmmgV014woIPrnnDWHWloCMyI8RhHT2ol/ls5bIIrTIyoIxJtZW2OoJIDHBJeQbn0pk"
    "XIQv9XmL7JnzUMkEu9tM1Sh0QJVYg8xEa7LdsYZuQYYqkygSjlguVNR6Fpx83iWiVeA5LOvjtKb4SVR2EV4qddlfgzLdAjJQe0xb"
    "H482fTnN2hWHkRkF+WoXRkPJbEmGpBL2dhNwU1SatlXFXHNiQ1fwfq05nKJXLbgTnQqE3S0gZoKaaBMpr2mSEUAWIO0JcAlEuzQH"
    "VrdVHNACb4YDpJX14M1b12WbJK0JQTCFOxyhBoLhhUSnEQI90RvhBt5YmlqWrbdb6e6e0ZNOXNOuTjnBkVD2uBDRWrU6plSc+JR7"
    "YhVh7k4Gs5cQoUFE4DDV1PsgzwNUgTe0B2/PsxwFm0NvSgw8rI8gVezFGrRSk7Mr0SBEnegBOc1w4jzTJLUn5eCGnMKMpRj5yt7W"
    "KzMZGQ3Zln4lHnN+tb9sj9XYleKs1MnSEJNi7ZxHIImCWSCeWT/A6JOmRhtud+u8MS56fmPuhaxHL9mmGWl81j5RTOnhol2TAcVw"
    "iL4PWJIXbW5g13EwT71xva64GzGLIUlzj7feOAC0z52jixeVihdIIw82rp44de0uPiXDCPfqIRMPXmfuz+TUsSrIg7fdZIJ2DyT4"
    "mItgNpMpzuiiyBwQKiezkZzxDhtIA5IneJ45HgrWURiDvH3UGdkfMV3rp4tvGlqobenSI3VcWzWiNOlX2C5OYwGEVy+zC3RWFHFk"
    "N4/NFkSBWY6o17V8KUWOVaWJ1lkZyNci5VJ8IPEI5zHCYEXX/Hy+pkiKUK2PG/GBXW9k3hysS4ym5bBi63MQGlF3ztCDuJ0C41is"
    "RvuY7EwfAJqtNFZFc55amSIQ0scVhJ12R/RIFwKDz7rB6lpr81rX+VSnbiSwmrUMeXtG+JMEk5NoWC0pyU4wrffTeodI0VkJsdgw"
    "1odZUfJp0i2YoTYR7XaueoV7rONa5TVBY0eAOK1g/GB14H6gQ30IA0SbaIjsSMbeZlB7kEaJPFoCtdqGOYIC5KUWzl1OXsKd7gPR"
    "5chYzIXAub5jQoZZ3TKx2rCk551wMadvN0QFvLWbH2BbyiXCO7rcqoc4APD8JN0g1eAXpKACHXihlEmuQjEwdZBgaUNHgn4D8VSm"
    "xt2xovaInULbMaxTJ7j65E0dL7eJ3x83XNZwqzBVwlAKTyGgmleKJC90dLu6VJCttDHbxdztxg5rN6xj22ltT1EkJ0A3K2F9Clhe"
    "hKZdffBXKMBZlbYhkiaUKVHebmrOo/tTvJrOlmO2p62272YdT3GVrWWyXc+4ByuB2hLvh0OIiCkjIi0VAPXeiksbgaia9KTwPOPM"
    "k0vIkiqDNq6fy0pGYYgbxCtRBZIi3Sg/dUTQceVWPAF4USpXlNTQjW2E+ZjJaBvW6orJ6ykZxT0MJ6INrHJZ6a4SeMQUAWem+HBF"
    "N5zAU9zxWOu0Eta6eSDg03kv0Rh6DkYL3WF4zU3zMr3ecrBywTi/MWBj71U0bdh6DRSHQuaUTAeFg8l5t/GQs74ibk0yE3OlDce8"
    "zUe5P/Vlv9la67JxUTxvMuV6vqLYFuTKnvTgTo3x466MrppiItKsMR4EnF7njb87rR2UJXzGlgdmuJQn7DZEAdkGwYWT1qQat0Wx"
    "7oVtyyUCAebnUT3MEhEhajmSK3mWZl7T7dg+rwV036sDZhWjswoPqEP3fswY01FKAnQbBUiLBFhZki4S90TEbXaSDq8TpgAyGqPj"
    "CnV9VwvawF8hV/9CE4fakGcJtyui7sK69IkC2uKmcx3Q5mjd1hrgybqX0VZ83PkwxJIcjVAkFXB0Q3fFvkdu50HelJ0KVrhx7gWG"
    "0wsCP7EhbE4tDxwTRVhpLhSIoHTYnVoZPGb7uD+lmVSFbFaEp3rYNSrT26rLbgNwUrBwpehwXToHmo/7QOD8NQfjuQ8wqWFXO41Y"
    "nUztJE+4n2VDnF7P1WHmbKvW0Uru5vpYSDI0udo5NCkklwM9loCMm3SIFCeMmqRNJ7J2Dq2V0/m82+S3XdiF7XbNamxEwrGWBbwv"
    "MiMcsvw6nTnk1bLP5ODIljPghDedpXkpnKq90Y9rgQAuxJQWyIzIRr2Fm27DnBPaazxL8XifGYuU5WqjmG5gdjABK+s4vPVSIUhH"
    "+0Tipz2fxSsSb8ltVW3MQBOH0mNFoaAjkr6Ss3i199h5czXbrSsm7KE/aQKAaNw5xlUSZ2t1A+iuwmI6cUy29XkGkBukLvBtdeXb"
    "gihOt4G4QR1BSVDilCCuoNV6ULugzhH9QAeaH/qSK0LULjlTdYGl+eK3wMgK6OoNbW4vNxsBONzP9SMZBL210xCLqmcgi0bRauVF"
    "mjYM05Y84kxMXr3A5Ud1x0G3bZLj0GF7CurOJeDrAXI5PCE0dIZJvTdKKTRNBhVv3BY3owPlDDtc1NjOYkM9TBgyCMkgCs+YZGEl"
    "ZjJGzlpYQYIKOPV1vd5Rp2hyTArwZg1kHQiWoBhWlpWKQHmDMauvFzYgFI26uSyNyGSEbM8kpqOb0ouLXYiY0TaZCSn0yw0Z3tDT"
    "Sq7Xt+Z8UxEyZf0doGXwus8aPAQ1EmpYvj/tCyU7+RuvVBWwAglKZsjGQgyRVgrKjy6tf4sn+OrB4nqz3QjWlZWkag1DQOml552x"
    "wxlfEme1f0J6Mu58XatJssiUIo1NqLmOZyPo2mbN0gW8ooAUiXS2IwdesuWbxJ0zrSUp11ADeV+7mgu2NXF0apN1DW8lzCJd1zwI"
    "xYZZPtj2THZQT6Gdmdku04bsWe4wHZ5Edk8akNkxcUhS9MTuBH2rQKA2MPNyVToKuRC5L1xjae9cMR4TCmAt3G6diqNJ0R8Mu+iC"
    "3o13A3KcUrjYOquJC0iLEWIkiraz7m6Ttrbf4E0YJ/Ehi6uEC2SWPVnqMOBTSmDFFlkL8MXyev5kCOQmyOL16Mjetasy2M4ZTN2P"
    "JSbNDDsfemXC+UpzecS9UphOr1UmFfW9GKiuYgeQZBprd79VhZEXoj21D2GPKTcVBA4aJzhNJJ6tfDypBNTnJE7BzsbpClVfS822"
    "B0WWSAlD2vDaucLKy6jmxY1hAnunkzDOgeuKpkmxJc15lI3IsRgpYXUnN1Shnhfd1hoPfHjaoJlOXPyMEmxcVDQ+mixPaECFiw+e"
    "p6p0U6CsVRPpxmVPa27L39gLDoKH8hyfRtjaITYbMyLHodGAowLCQLt5IMM4PCZ8aR/NjYaN6912FdLTseBqAGdpeYRVZa34FEZE"
    "u1mUnxHvRiq3fFf5MXodIUkLa0bKx3V4ENK1C4aJGh18eYdVUdFiq84wQcs9CB5OiRd1N1I0NdqzQGRYYQBqwZ1ZWeMZ5sokjiE1"
    "qsqJn5krKosSj0JVm5GWCR826mps4TY/97wvVHDbjHKHbs7MwEJUlWuY6rvdBIc02vOUAbexY+UpvPOJ66HwBMpmyEHJccMQvAHs"
    "KyHhxcGADpvy4Jn+jZk0aCrwIxr3ah+E7a1pA7mHUqhqDHnbmmt5faq6E9kEbb8VWN28wYK6GQb/umaEDorEVUrRQXZxW6TfYIKQ"
    "X7sIh9V6shI3YuJGcCV9VoIle54vghqnnabPkvm4FvWK9iosXpuxgqgctVJCPO5E8Nif6A0+BheKplV1uJb0tXJ0iEiiDU51uUx4"
    "/aa8DU2FXhIE43Uk9+LySN1uGoHGwazKeziOEBv01oKq68G8iuyE3MduAhXMqB93VthtTEorAgD+fO6hdlxvGUz2lRuKng4qd4bm"
    "PpDdiclO3o2lMlpLscJoGkq9bBu63BQ8sofoU4MoA4Xc/YAlomEgPrKYo2Dp+gAGV5VPivFstRLYNzM72A0quUm6gNCMWwkLg5kO"
    "WWOh+C0uCMnknCnpZOtCwoF13sJMdbpsRxpCQR+rD1q4F07nWxaqVBpH6BYebtfiutoB6EbTEe4U7Qk31a724ZK2/InId8nuJA6z"
    "ML3Be0JT4J1X3QTJpXcDJ5+2e38WfFM+bSq3Z/YWondGQSQXa0XHEtYTiUXMsL2a6ZSU4dTAAje/ESUA7xIhGFlnQFQw57GNv15d"
    "UwFizBaC2EVP1LnVtu9GebTsCwLqZy86VpWG8MqKXGlYrAon0yAZOZX9GxyPwKqvd3u61xWPXiUzXhnQuQoVvanQhsDpmeDdZgdl"
    "dXVxPDUlgshG2G4QKdm3VlG+w3yg8aZpVr7DA07JimyhLXE48T1hrTOFXM98OmrO0bGu8oxBAMdOex9QocmGpIHKgFLCtRGv2xbN"
    "MIbxuaLQ6R1n8GFtwz5jjcWR8IvUzDG9IPnLBklVLA5PlxE6stAu1XMHvPS+MM4SO2q5XJVscicbG7G9dWsh2kBMsRELQSNvMdCX"
    "ACfmBwTzzp7mt4DpDhVpG2yiUqMvMGgsXNuxjwdnMHz87M66epivV3y1cnEw9WW7Jy+RTdi+26ND2RIrx+JzwZrhsdHgB8E/ShAG"
    "EGDvn3ucLk8zpiPNGXJ5GGipa/WIINba26EqLBrrEkAcEl5hG6eWgQjqQazCvQkUmxkihzYprxXDPlUHuLebtED7W9TdIoNwI2oW"
    "77NAMLHKS+HYr52bCc7KfZTLMGCvylnlc00uheyUxk/99WBcVvG2rrhQqjfTdqRUlQEdslbmeZt5lFOrZU8g+/UOCAnuKrVFMlBz"
    "HWfqjPUncd+AtRPeGLqqmqLzT0Wia9Q2mrn6LCaFU2cTlXLdYVzdA6W+3nnlJTyUjThDdrybNZvJZfnYQ7L9mc9XaZ005iHbXjbT"
    "LRKAcHNbz8LpcCs4T1qxONBbB4+G0jEJV/SRdzS7StbWdMROIOglgspehtQhjSsprs+dF0NbUfHkFTKryASfRGeGZmBZqRPBB2An"
    "3vHM5FRrThibK4XCV0tU+N7vhUZHYjCtNwS3MQ3WPU16PaUOp0heo+R5fpx55aXRLnrhOBHskNZQb41Clr1yRoietWP3J925nZjo"
    "bLBgDuQbfPL6VREQVyngXIMKIc+q9DBVRYXRTxN0rLRjU61TvmwZrSCLwJu1YD5brY0jZ0Iec7rM3NHHqXU2bdbbST0cDvctM/vD"
    "UTUklLZF8fv3Yzm88p4I5f+vLTlx+2pLzjU4cidrxIHLmbYJUU/S8Dx3ihI3M/LkKP3orqHSgLmjseLgXddspXY/WFWFrRqk71DM"
    "3x909ijNyGS/FTx6D7GHJPP35+x8k2+wBvvejd/vRTeVz7NW4bc3bMrTHq5hONcAbP4Dh7NaELvmJTT7TTgGNBDYZbpjqaTfbjJy"
    "H2o5dj1ut32hlPYp5RJpRgFbMtxXSlVvKfzIdT23sov9lBzXxjzvIl8xJ46AtoXajVKEBcmRykQAlBIzxDbN7XjWLR7b57YhHTLf"
    "wPbFbXPdHbW1x5e1bfuhlFP4JSDhBj57p+aSb5gLSFnAyVaIowDPha2HsQp2yMQkx9LY1w3rxszUuDAD8GvaMPbirT6taXE3kihN"
    "SscqkvT8hitUxWA5jTbezj0etG1ZA7DgF/G1l+1L6JI5kRtjzeRBvj4EMMtf8VnpBLvckYh9Vm30fbHaYCqfKoF43HdV4STW1s+g"
    "wghTJw6RxLQ0HcNXB24Hx7O6QO/0rV0ryWl15PMTZUbIDVwXsdPfLDxNgWAiO4zzT3tS5BFxkxhXkJb6KoBTntgegDK5BcE1tY8q"
    "UW1dkquMHiPcW6Wd8vWpVEACEr2kRo/HiPC2JQveZta+oxjLHipC2W+T9iacmxkJkvvbfp4BksFiBDSAPShX+wycpUdwqFsgbYSy"
    "dGhxvNYBUTO95mNZsGKwYF+AQUuSwNQihIgbAuFWUhBpAHDFSGVIIlE0saHvDtWw3vg37HxpwihTK/kwbO00vw4TwU+3LYutZk0I"
    "raxSNockzgvB0HBcuuxASbpZkVlsbRZbp/mF8I99b505sGQUnrhQiOPUQV0IXQREpleTEQHWKHY4p8NKj1u9IgOC0FbeRcTbkcFM"
    "iRgs3DJYmSUwv0vhlXjFjtplLxVHndrhw8Y9oTMMkJELqNpctKbcs4TvGEhXI9mvFCc1SA7MMGU9rygmuVyxQIEImxI8niBiaK/0"
    "VIEJVcI3EiKt5ctRGwl10/bncmdp2v5EJS4sZr6UbC5crpnrVdSGheHGp8zZeSs6AqGu6BttkKrTOUA6cn3iimvR7QbjJAw4wsmU"
    "kJkteOLawc6msNDH+lQWGHbWQ4W2G8dVTeig9ONmBj26PmyBHjszAIFhrEI59/FNZcbB1XV25C5wZhCrUZBaqwryIEBG/wqPJ1cY"
    "54JY11mhDl2xAJgbmqdJvYm7Mo+gRwm26WyrEm25jmDmWrsAe66FtHTssUqPRoRXgJgTYHfpWntgEZKeQBBUUO/q1T6UH7llHKAi"
    "PIZXIUhkrL8BxYCnWUN3A9uo8ZQmbY0XKDRK0olrqnnpoqV86+RNYXDB8UDKE9BuVqlXmAAwC95jvzPceQzX25zwz74Umbl3HaRS"
    "ISUgvZzG+kwIaHVFTz0NXfz8gCv0DcDO7iYuN/zqUND7eS7PKxhoXM4mlB3d7btoRWxOagEAQtGsycOA9ZBzK4CQZimHaAWaD3Hr"
    "2FMHcBdGu3PA4vllm3liNl60fkySqfGsvNySV+6AkpEt60LkKWuaFGS1JtZEyClAP9VeAFtz26F1FDHVgRiw7cThJ7dnScmeYcnF"
    "hJG262n2lplkVnpWnNRTYXGhe8Y7rK+FHp/5r4qJt+GYe5lmTDC+FfH/j7bzVm4Y2YLoByGAdyG89wBhMsJ7S9ivX+hlr2rTVaIq"
    "SRQHM/d2nyY4Q8tvG3IvOqpUYg4ce6LYA5rWnEV/nMzfqshtum+l5T7rOl8xN1ZiNw8a+upfHkexe/QolTF1323rlJeuZz+dv31/"
    "99dStlZkXyWDU+6szDD0KkSfFhyzvVxrZzzrxOJnzjcQ4JmeubzMIvh59jiTFF5K6ULnDdmp32r7sMbwa2zlxGKf211c+WyX+CE6"
    "+cG3KXOkn/Zx5jwxhhFcl2e/bjqdtsiXDd+5EEN/DH4rBFWzVPUlntki2cD1X5CkAXslOig85qXHTZX2Xvg4aqsUykDsnIHjWwrA"
    "mCuy8YihrFK9QIlcYN8vF4ylWBVc/GfgKmGywmx0XzCAz8rBZ302XBkVSTu/lJ5bAuQYZJQL6HJYE1w3euTzFkLis6jiMRM9Xuf+"
    "ZkUwsAmosn8kzbIm5lq9IUbeqM8U6OW9iNTubNV0Ll5bSlT8UgldNQR1VZ1qC+TCsZJ1rQJvxsp95xNuqyf+RLknE39KxYysBYwi"
    "/Fmw4tRhRqCLcr3FSQz4oU/ij7bYh8FJn0Ks5G286Qm/UL5S1iDpe9xagUc1hq7MqdfVOB+lr6mysd6O+qhc3cYhSzssgekNynI0"
    "wxFHCN0pp+C1cLRKb+oU0q/oMH7DyGN5s05hJUSVNhDPkWkup4DKAPiWlgqiz9DfJUHCfcVmt81HQygrl5XJu+B7uuFdPZt+4jZO"
    "DBN4CvUzrvrzA8IBsoGBvKWWJ0gtFdibc52WmPQqhz146gsSPRHe4zVE9S3klavZh2lOKkKRtok+ghq5wTRcn+9rS+QrANsm+K17"
    "VIwsBtIAgFcE9oyxVJeImjwmvxfPGtJKgS4NBaHdCjLuAEwaAMZeMUl4QscuUC7x81zI3uyVPj5IgIXsvBX2XGM1FJCRG25QIxx+"
    "eBVowI2o159Rl0pXV3Qf4bAsWivaCMHwdevipoykikS1p0sHjAF0T3PVLTbOWzSb6nyO4NrvgAwkO4BeXX000YkVhxFIs2FwNilk"
    "YG4Mt9VnvnQvFMs3uhB/v4802yy6ZFfAX3xpp4TSdFf6OYOvu6WC6zmEBXwGggQ5r/zm+kaQfLG/UWtwZQW1zyJxwHoBHl6iHh8/"
    "maj7EEDhobkWNo1RyUfMrE/3vSIuAwD6INifzY27Wb+GR2WOEuiqKnzDD05bpDjeYxlyb9TxTeTreQQbpLT+gx/MMmiRmh8WsWgs"
    "FMtzG7cvQwKbUgnD77o05WTMuWBjIitDqMdBxgyOatmyhmL2x6oK1VBN1PjsNknWuZ2RR3Ey7i9j5agpkR5DD10CYqQzsgFd0Fv9"
    "Nu9zr2miYSgNlmgJrR/ReS+bMri6VNAes0vx9ex2jJM6U9RdPBKCyTKAOo5xFvnms0Em0/KLBrQ6ceEt86QBQ7t6Tb19u34dcUZz"
    "h5/UNMzY08Tiy15EMkkkEj2OH3Tlylkxz+48I8oeaBaA3ZKgcmEVmGK3RHNA8G8wVXt80Z6Hd8eL2ZDnkpD9nkOtXRsHoQuz64rm"
    "E6NPKBKUSp8h3SSJax1Y/zETJ+njgX4gHNmVdDPxM1MZPI5ZUfSSb89fxaGZiIj9/LLhM6SaWI8nuZNqY4y5J5ku/dokVDZmU3Ve"
    "XIDJYjSzP1wF0yM6xPku4FUwBu3zBlyO/YGBCnYIWQAEyEUirEpmnLLTr4XK6AHL8Mm+1vQhairZxO5Fu55tZpyPdxBPkF51C6Qj"
    "XIESO4Yu+gaPlpuxaysW1ozTp9qoRCTVzeYHK/zr5JUO6j8sLmYEaBYnNpazqW6zdZw1idie+NQ7TUFiUaWUejBbb6gJCJhrunq4"
    "gPOIV3tlPnhlooVziQ8cSawJSYlrbUcipMGNxHr49Zs++lYgImsHXKGKsit1kAzuK5e0+lXIpEQ4enV3mlMfN3S/CL0YKS9OTgXk"
    "IKQXGDJ65tXASXYfDPvNBiyVvQX7MhhlNDKGLVcz07HcmAH1mUWxMs93wcMx1xGVGVsj6CiN/0ZQDCQu0hMxtHMRMxKH0iPgl5DU"
    "CGEgTuY6y95ckBvymtarzyGcnypNielJPLzUKWDgu2ubPxi9i4oUGdY02vZ9jR2s0LG2JlqH1tLusVg02fs4y4stSpDwICI+ktz+"
    "+Ux4euKeObOBva6cSdAQw9oH0fkuhmOaJDg8WV+IahDDp70AGh4srjCulXm2CnbGxEmP67GBxyCpirBSprmxMkweXBmMMad4GFun"
    "tsEJZrtv4cLNfW6kn0AKPGbBcF1s44kBugkE2VzQTzvLqlIxnU9bJ7MxicqeyvWgbuE4Jm/RhhmruewpZDKWe1hO1OWqVMJ4xY7u"
    "KEtTHHyWsIig1a+q3IGj1PYOb47VToZih5p2vZHaYoHDLSRmC0fG51pPMKmRGOelepo8GYTrT5nfzQckxTsxq40rekvZ3wX7sdW3"
    "DcZLk4LuYlTttjDfBDknK6sHvSal4HmiUMnZoNvCcXcWiRtjZ1EWC82XK+azcm8eYZlHPyW7Xbdnn0UdB1Zz+4nsEUt9nBbtmSKy"
    "D2saaqdrXUyMIDJScUEAt13PZM3A1mCI2MWsqZhyhIqEHw5n0aKZQUI8TaBx199orAsz/HnZtomR41edgNyklpTByFzuDXECMPs7"
    "HAHlsPCMryKHTc5j/aMSz6TJMZxyjPwhdyH5KsqBsF/brmpdHJEO5y9xtTutgTDgQRKIi+tkKL/YqXIMY6HPY18w3lHsmrlPrbQl"
    "ibjoPpFNrF9jTUsJs3lk1uHuB8jQGJMrKF2kehY39Cg59OjLiPutJu+2gqkvsVf+bU2Q5edBXvhbtf0J2IK1X10A0uq5AEnIV0EJ"
    "GZbtZiWk0Z0B5euDaC+Omn97Zd3jJwA2gSKCNrWFZDsnySUdd2kfjItc8crRzq7KsI5ZRR40xfYl3mMYvsW+XFPmwm/Iyf132vHz"
    "uT3smIVjScWZBBzW9NcqSWAFWu2E6nUt4etvN0y2/erKehbvBc5XHYPsRYAb10W9xwJuy7GycgQs2EpI4evnRwIgl8xs//4GUf6z"
    "fTTIyJSln81mXhxIZuvC3AnO+XU088hgtkpCjgJ+8xJPlkCLlKYSe9WgxwnJtCHOp5pBb8N96ojMUZqCFhYZsdJ4kyGJEJW8ntSn"
    "MQyQzUBc2E+Eg7ZCv+1x7WF5ysT7R3lcYd1UAaGNyrEGjcjQoRb6KOLO2DlU9yz0gDA64za+Bhelr91piPECwxCWvPzd8hUYfQKp"
    "3zr3Gs8vW1Gxh8JPClPoPlUegHwLAEvO8q9dOej3SjkiZWUkrFSOfWLGUsMHHysDPm3rw/sCVPoTKvNx6l3YTy1e2CkqvadSCRtZ"
    "gwV5pGbBM68uMtVCBk/gEGMR9CPJKQymrZXrKaLlm87QAX+zigBodcosFxZUBnSZUDBAX8cCzTYqyjgaNdMO1rgCdLIh+RwFS0YL"
    "ZrTed96cqIE5P6sXylP30gGjwTYKmbdPACwkm2AD6AunTutrv88QLRw3dgvRl/OnoNmPif79b+mAxgQHeaViTfZYsEw8BVJGShqC"
    "YTlQSadtDfIBVvHQBCRtAZ4cGLtbRWthpZr4PTL0NcvaMOe4i6cC4ysBM35WDovV9mvwI3ino/RencjbCrQ6bBsr5nClaUGt5ieo"
    "CSNRWN2xJ5sPM8XUBBtH9EqUysFjsDhiFhgf8gffLfCoRbkWZn72Z4/0haSW3yoRN1tpOIAhlSbSMqFjbvXtZLRUCCYasLd/V/iq"
    "c4zkml77FqGXEGg4K5DClGlqmEmQ2iU/omZV71rg2w6XUVkPt5TpsDkxGhX2BUJbcj4zib8wi1l68qAMnldK7OCG71LsFNOhaLsM"
    "U0w8YYlIEPs6yjT1GE8la/IaYT5JwKRH/HZsBngFKEb04p9t0adrUDlM6Nha2EMoxbshGlBdEpVoCtl2TkmMvCDfjXtCRmysN6+d"
    "ZpTHH8x60CyHkki9p/bpToh8028cM/Av8Rn1cvnfavSYYC0jS2x5hiESg/rIzOo19/SfHIFuAJ8pGGUIQjkq4iUpPjlPjVGwpH75"
    "hrmuX/1jWLJNqnR5vgFU2iR421Y5i3nuONEFhi4DGlT6MzKuYD+2JEF2j3bZzGXu7PGtrMapRFkgb4kA41bMS2Jr1aeVfzz+z/Z+"
    "Jtxhb5UhO/7lbNbtfu4DvZ0uOgyJxaLlILVAANhpbdnnsGaaLCr0Heieg5QB4OiqnL/KqvwzMxVFkpDNnqjiFCHO0XccByzkwKrx"
    "jbbRNUZjZgo9cLTZZ+1lpwsxeyAl6lQr9bU3WmgizHewqdkNRidmMR1+9fnzicR6bMpQ7arSWvU75tFH7JVAVWlXZpVAhCwTYU89"
    "bi6yClEP1xg7ASWMldCG+0i5MYqCRZ9KDICnmD8gfba7X+nlp+6vN5R8ebQlHuG1PtXhYSf+VLlHcwwPvbGcb3Da3Gt302p433eP"
    "6lvCjEGUQZreWacF8sB4RRkYbMtfOxMkAPPcdTo9sukIedq71pdH6Vwazm8mKtGH5//4qFVlRHa87F0OdaSiuIktN2m/zCRyrRav"
    "ovlVADYWncOc5kAjFKPx1RMBty/L9QQjHCkanyBHcKR6BpUFyOI4B0IgZV049rgIvhRytyFCAt9RYmiT/TqseMq6TF0JM5mtdXIO"
    "jSYjWrjyD6Ev8e4GhrmEy14fTnh51smxvTzs4FYl6iPh+tQE6XdvrLgIsRCx7h5QH0bHtAwf65yhVihQCII/tBcSdWch/UzBVH9j"
    "da8YI+YXsFgZzc/PsxXBwG1sLR+7fnDrFUfXMH1r+KpGMTxjcvtAMmmwb5w45U+e2HI429R+xOgO3WM1WYr3l3fSrtg1lx8wNrnI"
    "XI+yvKK0Sd1HNuaeUwzYVcc3ceKx54JgLmbsG4jqbjUhQjXjrZQZuqKr5JIxKFHckpC6Tyud0bw9tdtBSbmNnI6Fzkmo/YRjf1zF"
    "Aw/F2cmX2VS4cniM71qqJUospAclEvOOcV+WZYQO9Nv0Y8k7epbdr5pGh2HPs9ocR7tAld1dApuFHVVtSFf1grpRpw00Rgrqm3+U"
    "l4Dskq03WuweDrYY0hMxIY3qte2CqbqZyZ+X0h3MyC9KWK7qEzEY/MW5+q0awj5y2TaqLi2jD/v3bvdcpL9fMj6LS0iHneLCqhMx"
    "nPj1OmPTUmW69PlCMXp+zhAL/IfRYniHrKYCrOonvcCqGla/x36NcCFsH42BB/3XFJfSn/cvOjEFfw6Vx2D2n+5mWQ3QOaNY5rH8"
    "RqQlZKDxRNeURwUHOkENac70CGNcNxwDp5afdVZsGLM+i+OsdPOYAeP6sU6EYCLCuBajlQZZ5t6bFtCA5eX85GQKtuds/0bCPInB"
    "rk55cPjfobdKR4o6HI8YPocYEwsrxr5ilPk7q6DlUyxV94s4f+uExNYgcHlF/5o7SJbQIeiiVMkXPNts2vyl13BdvHa+o2Pu7zqa"
    "3xi2oK4MgqsKmuEhBNzEHG8j0eOSLXzX7yVQ0qd9jR1r9C3+2sfSj807Y/3fvU7kFsH+twF79jNzFe3Fvho+ick3J7GdtcqAblkC"
    "UgNHezeNlUkVY6wjE0nAohvaH0ZlyqdiHOHsXwc4DhTOZTMwpnfFt+MmLJT/UqGtdf159hadEkWx+nPdYBB3uNNR9d9vigWYphBZ"
    "bGnG1nOWYLB0g3AnFGUiq3CPp96/gwWXi1PiSt84sZL50weYIKUUe1WmGt0+smnX1KdiSuEpeKqzBCSnxEFvgfXJiueGKeRtMQyB"
    "hKolMT4PqgTBydSQWs2wnDJt8BsAwCaH67uVwyZDldNzaMPY2nNhjofFy9CNgNEehZRn9d5coF5w0zEC8vBt9aKHTQsk2Dcv+heH"
    "3BpHW+3lDNE7hiJIvAG2HF17cXukd/3X1zC1xvZpKoeY8NVVjrCE7s9kV4o4RcXEWmUbV2XJJ6tY8lnZ3icbNM7VJmXzZL8DpxDK"
    "LhUf+6GDGAVvbNfsjKo0CIx+y+wszVCiUkDyHA//ukw4C0YC+eziSHnjTe7t+7IFfTDKWJ7fXkkS7FrSPoLvkfBF1z8lFydTihoC"
    "4JCnZ+p5p7Ryc9Zsw1qGrdsMbJYJZwSvVbSJ5Wl6k1eTvlnmjd8R08Fjj74OxLKWFgpxnVqoTHnH8TI5i9ZUsQavHpnmajJDc3y7"
    "8Cl+mB6jHwFB5Zn7+ISFPC/ln4L3K8eJxqYblkg0Zr0qNMZ33Pz2xxhPdYKPPWVuk1f4nnFetlk2lkuREFqyIzQdy3JsfN9tj4GI"
    "EqfiLVdsh+92QwkqH8uX5W7ZawgKthpz/KNf7uG7N7CfcQompb2IAYNKmEonYwAE8VeYBWF6WWUDqCdwyOgF+ndMjOMYKvGcw5vz"
    "g1MH48SF5SaM2adnd5i23gQAdFo6bVlbmQ7PX7telJVqbw89+mESzSeAlU1JA9oDryyLC8LZnEOytgXBRZXEr1DMBqyu7TUL8G3o"
    "0+tkRDQI3WzBtL2u9j3g+wehzhr+ZZxnwCVxY6GfafjMzhgJVY/QZl4mIF4po3+4EdiD/odTaUX0Pkb+ruD4rrzU7uz21tqY9Yxk"
    "vZDwjq84TcgIpXRmIhbJWsRZNaYYxcGwA7UhvpQaI9zG8mlKRpRJ72ExlcCboK0gTlFAIbtUiXksz003OintlKoAps0CFLyNQKAz"
    "3Jn826m7EcZiPagEAPjoR6nljVLqVHA8SpIwmY2/6Irli6nwu7qxU1UymDKugd+dEUMbO4t5L437BX2xo2N/t2CU9pExdSZrGhny"
    "Ze+nneCnjL1DZsBKY74XjbYGF/PVubPEzfAV1pwZ6B1kBChoPmyszzC3sv60VEWxajp1Ocby8zcxN2LLGYeeALWAwQ+BIslEbSy5"
    "9UJsX9pEDVzaHzb1PgadtZbrNu1FiRNoBcM9T9cPO2qjcpTP1QdC2r/K7m4nBwBnVrCFsdGOe3JSNvFmz/i3Z5pvduTcbLoWtAp+"
    "ZzTCyXiCwrm9OPvykPS00y3ZnDNfEI3uv1CqmY9LSQsj3Zv9XF8bZ+Hqb23rzm5ITQX0TNaTrGW7ULc6TrHtmmReKU8/Xm3wq80l"
    "bxLFn+TLxgnL8RpmnWzJS1JXaMBYJCwTcVKMsuHGsMQPmLn2Ll6/FfGdzSajTv0vVICqByWkQRk9JxJvCrmKLgszMm5hZ3vrATdr"
    "3XKu5HkJ50LY/XMi+QO3GDk7ZC4POHXshjpqn2P6WqLIshTniEPDc66NyR1rWGdmKant10R3+OSpOGt74cQJXz3C7Fz0qUJJ+Z3t"
    "eps8HmysePSYsjMKa4JjBjEbPa7sBZR/ezdIwbhFRfClvMUAY82uoO6FDd0t4aRjVucjyb0PTgHliH5AMZ1BnudWulUKh2kq6sn9"
    "ICptbmIerha4XbPpPHLTXASLyjqNpCuCYVunwBTEcLaRHb3W6+r8zK8NQa6CGgoLQ63a3XEsDaJOjGJbvhIr13NdtsmUdgOBD7qW"
    "LiKH6PNw7FI4X9kO488MAlFWM9JxWtGmjFjsMlImsAHZnCFXeUGnsy1puIM7Gk5RQ1ozyH43fsMD0b4rwl6903dcMaRimjk6PihX"
    "v0UKPnIMxpbqg5Y0M37vtmzFi1tg10cNW19Mz4tpX8DkGp1S3TmUwKm4HG6fMXw9nuROrPmCJsocGRIJDurNBPPJzob4243XFBmm"
    "Are/mGPFyzUEbwvzGOkia3HwIS1NNLnmssmIkDn+xZ+kwp4iMUYbngHAe2RKHsclWQr6NkKHW6U3X48GxGGGmCjcOI+nMXQJ0F1M"
    "/AqkHZvBR2rdCl7JAWrPi2OlS3QPRdEE1dg5SDkmj8SJjrbK+od467YuDEwUw4d5WpILM7B67eCUYJZqXI5h4cjGdmQXk2sGmBvj"
    "nZDJKbdVoNyTzAZALH7BazEQ9H6Xs32CIhmejaKC/FWNhdF7s9vHzXxVNkiPebBxCxMZmenqHMgGvINyZpDZAtC2PFPMukaRq3li"
    "bRcSiyYm006yH2Mb5YrEe5i3inHmTryemzLpuv3VQ7oVwrdpVrTXLH/GVEm/11fjJeCEXFjuvQJxtPSGQtkiVnXYeh7Z0eh6gCGG"
    "u4izHL40pcXoI6UJLUbelTsKFzlpYEqQkb1kKMJqWqU9z3qZHaiMfiCYeQZjLZqA+liQAWRdXNk9Fw7BAUrPVuAIHJP91YeZLtE4"
    "hRhm9MgaB7GQhEPq5zvInaNQfE/RP8h9KH6RpCoh6Q4mWFkjNNMPiSYGz+k7KrXdrF1SBFLxCV5zNCo9nlLPKtm4rejZww2CXwwF"
    "TiNbfBCCugaw7FassbiwHdE5Xc/PwcblKF528oTJ/+4bMDEFXEOwi/DynMppJg5j6Sa/ZbzNehxHfeB9kuRft8qsPKbs5wMVRyRX"
    "1r2OIIlZLyFetCyndprwIRN7YmGxQZDg9oCqlpCOpj9y6a4ocUM4CR1VkePGDqskuQu5sGMc265NR0SREtsWGNsCe1ryRZhPQD7k"
    "X01T02EtG4Ccsb5iJILKJhZwX+Zrjh/llZonMWrBkB99a4YCUTyn3UzsdBguM0pN4EzGx0T9TA2a1DgCAuZcurGnX7SwEI8bGGpy"
    "L5tDZMlC/jhxKT7133lODHZaBu/7ktBN86P5dFGUUzYMAMjLBdeyvP96fQxJzBrU2XFKLpU7z8GjIhtErVVThkK9bYww1x2X1eBO"
    "NFQOjQY6bbG8VkHD5pQSYRZrJkfWwRGVjYXaUftYoFKQ5HIqh+PwusJws/K21cNaWZgkuvO6jueByAD5gN3M24aVeZXCed2CNsGL"
    "nqaEVXN4PbZlXyADOzwcPx/lGUEL4s7NjTa8Uj4+J2qQeY6w6vuw8fStdnxCcIc+GFiLAqjX5YBphozpVmljYxAIPLYzXsU+TNx6"
    "1omOXPwGDkZgpIuTGfxrUaWXUR0K9A7LQSp/kKAs0vaHWh9BbnHSKisKH2xY5TGN9dM5xtaxH1bzWo9zXPnq16RuzOkWtjF2IEed"
    "WBPLnpWbIEk0Io2UeX0A24anFO8pIMf1w6ijYSgDotRhFLLs/WsK8iUtH27rnmkH6W21Blu84foo3gCY12zJTY7SMQXsfR0wXwkW"
    "lB9qY6w3e97cduFISvbfCv+G44+2LlA5sO1tcVUWR754GPaFdq0ue3/5FXbyGb9yo748Y/DBOXW1kXHDGVWkI1CO5P54/45yllVT"
    "nUlj2KNuFv7qKQjwmNVNx/1ksvzpIQA/U62sYkbVtQvM4CV+C44/jWrtXEGXRZbR/nbI4WbLeeOkKI9kcIi69UL9mczS74mEmo7E"
    "O4BPyLUAkr2BH+C5U+h0viEBU+Pt9dN6MeNuTvRCcrVVFVcmPpQYwNsD38pMY9R+dC3bh1YA9gnW2CPYxDFkmDc1Lm6wa/fXM3U/"
    "nX7gG7WDQM4ux+EETptMvsrQqHNQN9VR8n3gp6ugbwoxpH8JP/JHgRDNbGBiWzyfzFhlel8M7C1mZqde/RKJ1BcDnICjTbYZ8Wps"
    "vGkqm7FczArV7wS02Rjzq9ZBeMR9taZzcKXtlGBWNY33kQKxuXap+qCcfOJKo8eDOdvvBEKpc/moldronKvokzY51+gR7ZSIamKB"
    "OkaZQ0X2or9+cyuo0oACgxY9B3Xn26r3gptXYIza/XG1bcY1QzvJpJlw8oxtoFO4TJoa3jk8Rbrbqo7PlIqwiQDmJ2RzmDFBNUr1"
    "4UJmSOqk/Ha72139rs9bzCdB7CbxNC8GPx2iGFJU4anlo3s3Lb/P70q9vPisZvupt3CqqnjS/46sQNitoWStPadLuI6wZpDb0a7b"
    "zurFZWZC4K1XGy0Yw3p3cgt+nEYN1T1J42DTU2jmKPJyAX7YV1uOTwaUt7wXkegD2k8xv19JU7WB41S04hI25FWd8QqaSvXhlH9v"
    "EARM5ou2DQ5ARBXerWhZM1F6TfkEez+hY+cm0n7i4YO2oVQofABTbOwwVZ1ntgaYQKEQx+drAJZ68Dr8PklR6cHA7cpP7WqHcZVQ"
    "kBsXDz/XkrE3ib25Ytg+ziOzXdTIMhbYu4HjuZv0X1ufnEGQ5AwBK4VpbqaCDq4JL/fGLccvmJ0ENV+pcA6UrwYFPqLzFPlgVF4k"
    "bT8QT+D9ayvNNXDstcn9LgZWv+f9gDYZ8uNQifcWjcN2tvLqYuzLvhQFaR7rT/PKZS3jROZgHOeWtapnkmRIyGNASGkwN36+9YLl"
    "YNskihDxORUMOg3vK4KgCazpWTYGkzhvcqNRlJFRzpcVIZV7FCRVtwExjrGtJLRj4yLWDC7R6ZG3vEG2pChmxNlKuC8IONjvrZE6"
    "Kb+kGu4UqBHuvveWGwElaDyO4wbC/eabkH+K3RgkicNZvuaD92ey5pCBzzZsN3gG4tKd4NoXkgBGEuvm8oUkEH7EPlHjQB8OB5s4"
    "QsGURc29OOzeRBUpTSs0utLy5/NQkWDVhu4ZUHIcuMym4bcMW2qaPvHP/4ynnh3XcuiwlZ9Sxn45SBfC4NmWcLmLRbkNToNVk6cD"
    "qGY8M+NL9Mx/j/gZfvmBZ6ff025UILzrnXsfQE3aYdmg74vqxlLOMN9XmaBxe1wwqociHfu5cPxqCXsoNhwduLNtUOhPlUBMvdyZ"
    "BIsvbtzf8DM5VR8cevxMp8zCg0RPOA35OJC0n5AZGSlVlrZb9csffZOB6f1X6wghRiAo1WmS/6KDA5U+/n1Uk7HR6NmXRc+l/O9E"
    "kmZzde5mEE3Rqap3VBZ4kYAh1s8yqRU73MAUvZEyH/xSRpgG4svB/qqp/+t+aIs/iPTxt9cqeMckjbZ1I6lBMn0jr7ZyE8ZZtumX"
    "qREURuXhHPcmLbJzCqdJ4AQWUHiSReDtdes5LxHerWnF8x3Eg8fQ8seXuEIMn7hYSKj3q9ecIGlBFZxL3QMtpsQCzGjB/sUn5PAN"
    "aXGQKWB4k6KDgwyq6VlBS5vkrq5+1AIcWY7BVFqbnzVYtr+XgZ3E9tP8u1berEasAfH8SKKUnYxe7X+lC87p++cvJxOLnVR55egT"
    "b12/PUhkfUOZYsj1Nhno/jWUxNDJsJlSakdwGc/d/Oc5yLu5kz0LPhpjerTZJk2VSVMp2+MxUqVZOt6aByqXT3P6WUlqMpOACsU3"
    "G8VnCZWWB9h8gsLUl9/NEfBJ2PyqK4iVvhxJX+dv/pASgZc+AM/VfxO5JiC5RxORi0H8QT+zZGpf5YC5o1mCe0k/r5ccTbdxG89C"
    "QP4IMQ+K2HHez5vZC0UMFg5h4deGvkUQubyIba7x+vX1mZ7IQuQRRFkvjr4vjK48Y8eqt4JNCoUeZZN01uGN+pYuqPvYQU42eA0C"
    "tB6CC27CzHXDFWkUdKzg71kHHBGdA+U05v7dFLUGXZ/rmEoNncTELs89Ye/E0SSVFUo/6K0CwzeWzxHV6wMN/m4a0x82nJySR4fb"
    "b9dnobH9V6orDrHrjvFppk/cgq7yWrNz5JUk200NpnUDGRDG3t73AUFhII1lfXyS9GKQp7nwA5AAnsxlulST1IBREQhduzpRs09W"
    "3rNpU5l7aGg8cqGtD/mDiJi+fgh1VcXfsb67PPYNNHjOLE1dxeMos/iONa4I9jNEaTql4CUItwc3GjCcaRErTbtgy2UZ3la/wipP"
    "DR/rEF+fIJC6mtqUQSQaSSWorbrB88BAyTtsyo/e3BRg9gkOMsn4YzLd6PYvW2+muVj/Pqv2v9p5o+zz/+28Ec2/nTeU5JmUIFSN"
    "UKszx1/sm+qE6Qlz/F2n94KVxtaXKrdGz8Iapao+AqQVJdctH2FxUWdiHI4LPs4xDx2E5iQK7qT2dfb5yNXC/6VIuh9FaZAvEz9t"
    "/8wANBjjLK1iQ16fbP8hvzZF7DYZzBE5u6X6WvyhDf38/fyyUdU+w9/eHuMdwFNcK/z9hUuoqV99MGusOJSOXyIO1tbe5zB4/DCL"
    "jA/J4A5arzuKyEQfuQhDviKRj2/cRq/5XR2xATN6vdaPAa17Sh1oeP6ZOygv623tJB5iPgsIfhdWX5OZXr/3zy5kwdxG1Tu2YM41"
    "dyyZzpyk4jI+rQZpeGHkgdm2znfouDX5PgI1wbVBFk9Dqmcm7GwmPuYH6ff6eFQ7dVzcABClNFslZRmMs1M+j+AT/JESSnWz5hFQ"
    "LthpbB01rPGU0mj+i3SfPdYcOA2v3xKagDm06aXYBfH7hFZb4fU9e1CGyy5UbIb9UWKVYcPVrIOLDAECVeQCfKvR/tW/EgPKWObO"
    "xTqv6a4XETj0MTqgSaCk3wfs5rtBWCoXW5hGVvdqSW6JVGdl2HhHcw5JIvtYY6q4wKWwRkutOpOb/E+bqjNRwMx4kMmcLm9fY+pe"
    "T3f2psdG/Laws1B/l1ocoUzLgN5g6PFDo0KId8Ob+E/7HSYCJriIBeM6uYsxvgT7/JFBAr0N6TBI+sMA3yPQKOWf60HDrBSHC86E"
    "UYUXSGfqlaiC5ufiAhUb0fm6eS7MjJxuwBEeCyagwHXqFmOrvhC2PUqP3932QaNNU/B52Lju/3YiGtIRYr/lh6wOsYPWaDtQO6FO"
    "kWR3LOgFkYdtfMA0ntnoQge43m8XwIuh2rMTQ8p3+WvJ6PiBdAigCiHqqwEbbCZbPz+kzLKAL0yNGHgJROfbsZuNyBGkgsAe2dcs"
    "umqetPOk15/1xcrocDywkI5nVF5fv3q2YkKSTPJXOY+4JN15sEGr8Pa6UqMRxa/AalEUaWXKeWslZvqFTGx+pOLC+0JAZgA7r7bK"
    "OGN7rtPugvlJ9zr39W2UYDJeRNA/eLQTXx60SWRMwdjh/Wd8nRjROAiRXHG6w8dGT2N72Y7deOnJwR8AjmjpGJ6AG/UQjcXysUjx"
    "QNoSB2mB+lLGxTaMM4mnUTziWkC/VSOeDsQe0SkAZai1FqHh79RvmFHhvTIxZrIj49rANGXlW05+oXrQqt3iR53AkYMGZ4xKB8du"
    "9C7gFFbdrQLdVhbLLfZkOOfpYxjQwWo1aAeX9+Ox3d2Js76nUs2UICLfH6dWWuXbzaNWr3uqoRH8JfOLnk5VuAWNq1KGmiC7BJ++"
    "BadpWIaOZ0eoJfkEujPIESVHOjl/vumtS74D184w3iid8UaGdUZfSkTMPNvhGyiLSq0iRjai9TM/2O6Jd5FEhxqk5Rhl0+s5P+cY"
    "S/4U4wNjQtlG4AclwQ8DBdSI4/fGPy+CGUTgN2P31qSsjarbqhT5ncJm6H7W6t5lf7WhTopSwAw8tFsdLRprUBlcFQvvvLUboCe7"
    "hxpkWFL7gHu5wAh3soXtAIcb2m8O1cSfbl719qWp4ReOefz7fpPICpuKi20JBfqJAx8M1W6jERLte8dIn7TlTQIogudbREGewtjz"
    "iYD0WisoSE5SO5SYEwGoY0d63pTD5jIWYA/uTNPH01tN8wVcoA6gsnTpDVlR58OUvETJ8nJqbKrx0LHoAtXmr8HAigssDGg3SAp9"
    "yd+AePePJlKYc2bL7zDaxPmF2+5vr/N4qyW89FGI+u667dRXzAgb0i8Ky4cdepPd5vucigaHShZwmKO1QtmyY80TJhvQ21fhPFC2"
    "FTIRQGhi90VrJPesK4jKbW6F9Tsx6VFPs1G65ynQgvVaAK2SKBECLeDBqmI6WAS5BlWZZeLEHrg+dOwAepsuBuyc5iuQiiFYuru9"
    "HunK7dVg05lS4+bOUO3UfXygZCxmfxmh766HAMEHibbSZzu35EpooLwu0apV6pdWICM0DdDj8K1AttybYHafbwrBDXyvXwBghgp7"
    "hDiev1YDEBVQ567OlPzzBt3XaPEuCTuzDIVA896/Ykq/3uAyQNRGaAmZv5ZNxr7tvhh8EfX4wc1kAXgdHZU7Ou9xL3rXUTGNFGA3"
    "mrcuCXORv8Pu3Zlf7ZXksytHMM7rn+SLbq83jeQngsyWuzbVkgwXcs+f7lOK9G6yEgvh+ay8jUS0pHVt0/enWPyq3dn+UE6aDLct"
    "reQPJiis+0SvJ7ABS4RtO4p09qjY1YQLCUuuOxmdpmS3Xr9hibTrGTnSXO/1MZYOBXe0HPv2NRgtUGGJkMZwy/U5u/2L1AJbRI59"
    "6csapAfhGS13mR/Ivx9dQrZFHZ70CW/sS9lh8sPsMJUhNVJypkhDNP0t2jVBX+eXBp9erN3PwSfsCfLfjKDwQm1llu+d0pGB+JoF"
    "ohapO3EcrloBiSWK5iu6r5c1vzDNZKTRxhzkld5egHRNFEtuS3IFJrSyZ660Mj3eBOAgZ3R+vhJ/K0u+nuW8jM7XRoJw+TjJ1JI1"
    "l6LM5gAyRUfA720pKAGaB9z7LpHeUCpdPtImS4cKM71oQuX9wtahleMYO1Ue0zOUc4WnfFMgRgK8X989CpX81HD/9ACvNJi+Bl4f"
    "rQw4CRAAR+HqLkP0TCZT5sfKbzL73VBMv7Jg5I4+gYh7ps8oOV+ne0PSAXYGeBuUsZYmme8/gSQxklfXm6LlYE8m0FECBzNWuLJ3"
    "sWfXKh9At5q7qT/B3b2qPZiLHVSuP07jyjmtlIPL3spmzm/WKjX9NtplxJz1yNGT/jQdbOVFXmX2iqu2kFspTNgEsxRTNTXGJtQ9"
    "zgQAxOjDnrwKlNwuEdku8eM9WiEr0c8HJtXt9epizaA03GhwnQmrlR8gZUwmRjTTZfDpyr86O8ogfTVwlsvQ0Bqbz/34l1kTUNZ8"
    "364XO0PiRzM2m4Vk5/nsUJYbyN3Kwhgvxa6vod3YTwmK5Qzy1cz8OujU2viXiQtemn+naj0ws0XpYKU/gmDIX8OyHCLGXTEp4KSK"
    "lGAO4OD61ijt+EvGMfL3iR/2C7Q+TkV0cZQuiMwBeYTfzxBFCzVcWypZgYJo0RVQHm4PfvMtxQV1jO4c+QseVzIDaihLTym9W/bR"
    "wJUHA4+z4lxqo1vex+jHaXDNMYAtajaD3cWFF8Ro/7yFcM+dAg6gaye2vS+z8ZmlXch9t2oShZiozO76pMoZuEBAw+45chkxNCbe"
    "euijKA7zjCobUg2DKbPD4hvhszwEb1FWJrCM2QTw0u7eKiOvCs2d68xCQEmSyyShjtP2s5G9DK4+1PsQnr6tbOr9l9KUw+CoYX2o"
    "zbLcZr6jfKwOo1jpHGxJOueilvIF11xJHBIIcWS+eXIgH4upfq9Jp0QOfEeCjb01rvRbB9EetOyOpqOrlMFKhJSvGVIO3ruoxV0/"
    "964gmb72+Zb7ayl6Q7gLYz5euPi9z/Mw1P6576xFZugY2T6UychV39kTmDKAYkY6qUMZFn3J+5EiZQqolw+LW+9C6iGZ7D12S27h"
    "c0DWONL1nUlYs5g6tVyMyvweIXNFLUpavSyyBTFO/lJUVsPSQAQZ3zEZI2EwlFKU8D5MbC3ciSXRHBOZB6TPO3Mx9wSesQN8zTNp"
    "N0kMWrCEr1jZj123VMTy7Q2NhJ8s4e7ZkHmdVqN6GzrITiAwsnPtlJgHr6a8ehh/rflOJYIh4Hx33NsJCbk2FdsGL+W3piFtfk+l"
    "8IfP8Tj3RoLNBFLzRb4hcD4PluJwSecqQrEvoWVeIoBe7XJpG7VkKtCVnAzRHMqR9ryxsqXrk0hz1ntjQfZEzt+7yprIrvkRrLBJ"
    "DH1u1oYXDptT+Qi6LXMJcAjdl9n8qmOTfbg+TJG1YtoJ2sRJCGkz5nS5vLISuxfMF+ZUAz+2Magj9MTdbxaIyi6NmMl0lFG980WB"
    "l3MqWQbc7S8v3nTi8PsEuT6nM1KbT2n+bYrSu6pA6pZLJOhsU6Mdf6FStCLjS4IciHgDYFvyDCX18OCYlAayB9H6NAFD2Wh0yTlm"
    "fTqXUO2ry7Ee/SEva/lA+W2b3CeYSDGAyfL3s4ekTw5GCJ80lpzULD2+rVIL3jKpfLTPmCACmwgmAaYkmdYR3gVjMLrwQn7bAWLf"
    "1C6mLoygX0Ififpyg3RbAHFLrccMIGaTJSeYwQI8fEkCaWn3OVtukWazD5TIMxoAxpymsSG9qePL7Pc3N8J9fHBtv7npAqyrugTl"
    "xyEYWi7R16NeqX0T+7yUlOSCRz3oNPQOmLM+BiTzjkPKRK9kWxv9TsSUnuwLTPoJtqgA7mhG+5YpgVT53dW8sAHsc2VHtDi/CIVG"
    "uZYfu558wWEAOVqSN+9iHyKhbVbkZz7XVsFqnHQvR+vj4wjJE6fFV0P72ztoOgmEigWF/T6fKsbxJV8uu/2kaN0ods0cn8Mb2nAu"
    "nm/5Q21YIZ61xBg1ocabsv82SdvokICWgFHDmAhDuDH0vGdL4nKpv0oFhAQfyX0HzhqtLn4DRnC0H2LnEeV/1vYMErZZ7JaiwKjT"
    "w97MZsemXpwi1tzV9tLcDb/ZojXKuinTQYVCeF6BAgbW/g5sDZgT/qVaGAX0NNFjfsGRfp731iGo1FRpAj5D28or3CJa6Ice/+RN"
    "/y1lANeKISbWD4hacZTtTma+/t93KQf/CoGh+HxnDKay7WhBXDiiIaNuyNGgLLzcZS95PQfgqu9dKVrOE5+4O7NUrjo8R70RWH6E"
    "AxsQwHt4bSxTELIfZBVhkyJI217rjeYiHjj7D2YJFQpRfmUBaf5jQvSLseR1qBCQzwOAkpTyWjY91Mm7ojnv3YxU5dktZC7tDHQM"
    "RKb3/p7aJ5I/ObPh3ljOKzL1Tf3DkvN7Qpe5gFjP5pndZheII4uRWIHMjcXMNK6lKn2hTuk1GIjEGqumT0cmktuLclRqD2PrGyop"
    "5wkVi0mHwUhsqxiBu0X67IwyOd27LVOlswpUeLLM3zFdhuvuQhsTwsgvRFduWonUGkt+3NcuP4ssnWKJQrQHBJ3KCVrNKJC167/6"
    "ZVhaFylqFGf3C+2zJPSoSf0om+7kJFKZRGYF/jF/aKD1AeFyNlPXbMIPKJnNxkRQU1leRIWiZMlBNiOptVPp8Rlu5sPo1Y88RRMp"
    "+K/Oc/Dh3SMlQ+gVbMlRRz19OFzpMj61SDwIdcdhV1yvr6zu0a8oCofO6nTFMVC9ZeGP2G+1xXO4PE3xazAKyAs0GPkzREjOmIV4"
    "RYK7+o1WUehSmelwxfUdE+3RL+/yDrEPvaDU5s/6WZYeFZo+XDd2CDG6GUWjPX1w4Bj5lHDHjh6xgYc8AuNEudbECYoKwFAxM+wE"
    "Z5+J8bisatGTpAmzXiGYlaLcE4Xpa2uBlNcgh0jCViXMGIYEi3GhVlcmYM5M4S0avUO4L/ZYpljS9k23r31wTsoij69QgKryy7W9"
    "Vns3clRB7bA6h0T++itIv8jmswwX/rDYnGsSeLXebYOGImYEzLTuZARqcsQNQtZkURh20QGIa0v8DE/yEn9+/6sOGrSCA/tlNClc"
    "RXCnDv8I9fjQI7v2tfpK+QIXO7THx9G9qVsPBdDDbKXiqBCNkeL93t45Of5D3Jt/t21dC6P/Co3X55KPEOdRLq3FSSTFmRRFSqpf"
    "CoIgCRIESAAcJa1lyU2awfmStrnJTdPbJB0Sp7l1em9729wkbdZ6f0oV2c5P/RfePgcDAYqS7dt+62tqEcMZ99nz3udgd+juAsxy"
    "HanXTOZ3ct2kJ5kcVKjCeORqBQqNnQNPd9QM+bKVxGI/J8/b/mxq4vVNA/ba4CA5TG9nAsH0vB/fGYHNwlSbQcnjArUxyCSacnok"
    "twruvhyNT8vlmE9m2L5/3N6dCfHWVJqEmN3SzqTub1Hpcs+HProobi8K02l0z19hYylfOr63N2n4W6Mc00/26tvRwM52YdBpuCfj"
    "vRQTbNt3J+1xN5A8kLdr2UnUlZ7uJGLOQKbRsHcKvXpw6gmV/Gxg1xujGvI46N+vu+VZtNQ5KJZjc6oQCHkawva0CGYD4IV0UJCi"
    "9JSDbpvlfm7PExxUQp5cq+KfVMvRLlvYie3OYy0+lGzOxV5nXvXlglPXJA00M7XzdL+QE2fZ4v5scTBYJEuy3KEa/XaLbiTLcWax"
    "79oDPSw6jGeiB9x2q1TOdYZhlzNTTthzvBQV8t7RhG8ApifTXNRVYvqp4theEuaTg91+cpgKo32CgcmgkG6CZtp1+VxcPpH2VFPT"
    "WFlIuRPCdBDt9fdLnRy3KJYTtFAoFnivM8Du++jS/nYYfeSNy5SnxYLYj2ZZ+zzRiU3zVXnsGmWnnrSQ8JWrfDwX6AT25PosRBUa"
    "Qg3Np5tkouPypNLr1OrZ5FCousOglnVcAdCe59IoTqV68+ggUeR3eFjX/SJfD9DFbrLTGNrZVJftHkTzmY6nkJsFqbE/xwolegTC"
    "mWsUQZRPqmKg0x1khslush1MuAJhe6PBT+TtOszPme6BbebfDiRbvmk9yh2A/IruIJUtWkjsUtHtxK47Exr0fUwj5i1vjyvuecze"
    "3i2Gd6PeA3fIM+lGa/5EdBRuC+zc3axVCp5GcCcuNaLBar5fyfgSiShnryX2W9SgtjejAuFyQObSA94/jaZjTCmbcdYL/hCYFe5g"
    "GEwhIZNsdDz97ixZYRLe8R5T8UZnQXricua4UagerEdTmV5SqHR8US8fKkZ79UKq5KvDjDyd+X6p0szGh/1AqzfMJXugeY9S6V53"
    "WG3HnG0w3IZ7AXusHsz5+916rtsaxqudQEicM4y30upPh6WZnffveLr7nU4nPvZl/PPsJF4BmMXzqUSKLk6EvVK8Fh6X6OiC88T6"
    "0m6Wo+WdIJeYgmnlzoZbwtzdCsVDswLXmtcnXJeiO4nOdiqRjyZjcXEatvMN0Ruo8X621nSJ7sGC71ayO3S/05tJTo4beSiBq6LT"
    "i6XdcjPny+6DZtPxyJkkOs3Cy9iD/Hyfr/Qbs2JRWHTGWT/dLleC+xKdiYcKwU5oErcfOMus3x3ox3crYTYRC1bYWVXMTrtyRhzw"
    "g14KeLV7OzGX7Ac1Twt05OCksjfmgs2xnY0mOtQ01ou5YnwpWqZ6XBKMudEeO8z19ge97YHgZbmFOxdqUtPuIF8Q8/1eZlHMbbPe"
    "AJfK9ZKDaDKbqfrZPuXqluNle3i/Ow4O5Fprv+0/8KWHhW54b7Zw94rlaDGaGcbiVW5K+9MjKdBNMJP6tJDYE/Jyon+wk5eavUzd"
    "x4VboYwd7OAwz1Q9Msfuzrxhp0uc5sppuWr3YdnaG449+VasDRImurcfhRJe4I72fRcXHbN72Xol3+diBT4TTOWjxQHoor1xyCll"
    "nJ5gwVViqzyTLIw8/pRX7OddtLOc6QSCgXi/B9pkP5yqgc23I/kOspXCToqJRms7xSbj9oLGcZCfZxrddi28sxs/aMacEhv2emeu"
    "bq2WrKSKSV7oFur+6Yiri91OTNgXp9FOrLG/ne/V5DS/qLBdV8dLh7K9bHybDR/UmVFjJ9cvIL4lFhlXmet7uUSPrXmpNCUPO8K8"
    "1EtnuVQ2UaK3ncGMlGDSyJ/CU+kKv7vd2xlFi81uaC+zS6cynSiV2s1HfbGoJ8aGF6XhAIirGJULlVpdDNszvr3tSj5ZnFXGcY8r"
    "lg0P3GLfWeNjVIirsplFNpOsNcL2QTO2CFPR6EIOJXO1YWqnEm8lG0Eg7dygFixOs+mwh5vu22MltyeUKLoawYy96ypXo+IsmegU"
    "XZ1UvZRkc4xQBrBS6Woi0UiEPd09Otmw5yh+Z78TqE2FrqvYSVDueWPHE/dXcpndepNLOJmdVq2dSjUrsT5YwfMdLiPXEgmeZf2S"
    "BwinO9ufp8WF3F8ceKMxe6YkRO12p1SJxlyFuCgeJJlYsp+ZeWJDb3Pf3WsPOzuJaiA5C7WrAbkhzkv2g3BzO1WruqL2UlNupLqU"
    "WGwK7mmovktXq23+INdIcYtwoB4Yl7dH1Z4IQ0qMnD3BF+Jro1SyR6V3+XnA7mFlOdrv9r3R7LAu1kbzGOeXe7EQmOsLngpT8s5Y"
    "HnHDmLvjc5WTDarNjcJUzzOO7ff3Y+58aLc3je0d9KhtoZcYueMzdLJP8aAyC3bjw04jOQ3R00yFzZZpIdreb1Ts7e1eJeCO9zLj"
    "USm7yEaHaW8g6eRj7fG2nU5N6WE0MWuOgiAy5kkqHuoLpfS8lN4dU3VxX7A7+/6Si9th27vh8GIy3JtEW9VkPVrh2ZFLmleaRXpv"
    "0plkJrFYjjoIpdlAqt0vT3PReXG7k90N0TuxxV6jxC/i+43tWUtoFdupXjVBhUv9ujtVDFVCMWrEUcNOJzENgTkdTbKp8n4uPaHc"
    "s4PELJyS4oEMO/D57PPprNTh5WhiMk+Uqi5QG5uNYKfN7W536pRzPG0B9wqO9g6cvUwnFJvuOLtso5Ca9yvVNqz9XqHrLG87AzOX"
    "NCm3k676dqgfa03aofFevRTf9zgnidIgsR/djyaK3NzfLAu+YmIYd4dyIptNsUBfU4nlQzT2Fc7SbS+Ytvx4wu8mvXszYMhc+6DI"
    "xVzlsr/v7Pr6HV/KxTHznfSom8x3CxVPrkoDI93zFjie9Y2ETn27LzFtd6baD6Zqoe2DQEwUXUl7JTUNVaKlGiW7d3KzXnnQF5K+"
    "6LY/HK6DTRZkJq7iIHUQnXP5YX/cCA6TJad9HgvTCW8qvJNzJcICRwHzztX3e+7Bbjnby8ipWqJcoMpgYQYDTHvBttKVOVPtbGf4"
    "g/SuLxRPB4JNJjyKjsMV3iPl5wd7uzEazMBWM16jZnIzvU07E1w2UZSy83E13+r44u3tUjYe7XQyPtrulnfFWXMnVclRncnBopqo"
    "cOVQTg4t7NVBKdetpMT9eTRP5VqiZ+7L5l38NjVYFPjcqD4YlocHO3xjf5TqxIXs3k60E68n2WaXdlZFMTiL53zDSjkW6vucCXc5"
    "mYjSu9NJyTeoZKLtgDMb5RbRnW7Fn9znEwt+N5BN9XY924m4q+7d5UKBWCI8GdClcMfVaPtjlXJqh65E477CYqcSjcblTqOD8uKA"
    "+4P2UivVE9NA/CAxbcejQna443Q2XaGKe7qbiuVT+UYNqDAv9hMBLrY/dWZqxe4OI46yfpCHB+Fsj58lY74CNR03xWmyXu7vx8ue"
    "5EwWfZl4Y1QKAy0khomZBLjJ5al9oV8XD+bpeoMVq81G071bbi0q+UVvb+TKlodpfwY0GGqPmxacwVErbHeGk3Ijaj+IVcupWCgX"
    "9009QcFN7RRzAr1fkZJyz19N1uwpZzsn77npTKUFUyykw0WPp+mMB4oZbyAxm2XafKAlxN35Fr8/GFbz5cnE2a1MR/Z2meFjqWI+"
    "Js94d1TkJ4nqtORsSGBXl2qsp5sLzf20pz2c5vzhvWwxlZ+6WgWhQlNyPSYPOszMHh+Dgs/WquGRG5Z8SmWzs1rxgPIVBrNFMmlP"
    "5j2JZhz0TZ7nOT9TSAfZSrS7HbK3mVKjnPG7mgzXsy98zUKhmhmnElQrUx3FXVx8lwrn9+qIPuYzdyjeDck77kyrkXA6Z3xaSHns"
    "ZXruagQy0iDpcs6HfNCVpFMDe7xSATsxHGjuORO17JBKBJtSJj32SulErlWeNDJOei/fkXLRnXx6Go/2vIF+put02dnEyNcK5eh+"
    "et+XS1d8zQrr3htWR3uVOBi4gcIeR9UH23KoHfPMy1wpmxBGA7B/WweVeDDsTtc8nVwyfABsd7K/3cuPyq5czRUMBeX6hAelo5Dq"
    "50epciBK+dtFFxVsOUONDJfMhxkn1XdPqXAPDKhiszNp2rvpfb9It0Agj7aLk0AjLYm79oPtXDfRqy361FBwJavhYqlUapf7A6HG"
    "5aeTkSzMWzt7hdKilax0ZoP+TrMgs/ujKr/D7WTpcq41A43CF9jNbldc1WxYrE7H+/V888A+4OvhZohpj0o5D9XPuROtei8bExmx"
    "mhlxjLcVD+Sd4a6nF58lue32JGj37sWoiScle2KBNvDI/LgO9Ag2Ddj26ZQTVLwK6xqN9/Ot6Z5H7lV4Lz+fyyKVEtiYlCkm+yUm"
    "Xcp7Z/1sN1me1zgY34jKTgKzve0ZzSe6e2PglRnglYF6dsx0XDzNZ8d1ZgFW3kzwzOdj72LO5vaEaXrGTEfN6WzhivZ3OjU5FurR"
    "dFSMCp6Ycx7f592uRMbbWrRm7b1orbZdHtQTfMjbd+bZTDw9jNNix7Vf8xXS0zIb7Upu5yIk5tvRxjzvSmajg74rlN+ZFj1Blsmz"
    "e5zL1SyN8sEW8h9WEr7UTjm78FVHbkqU+82+tykmOxlQUXPjCt8tVkLZPWa3EWgVw/EwXWAmwZJTGGXHfVAD2mNvchBzByrt7T5f"
    "BCQL1evbw4MmV96T7L1ZLZOcxqYep1hM8PvhvD81nItupjTr2/frqUG8s+N1euj9wnYsyfQZ2dVsByRfPJaMxhdxZKPEF/l5fnzQ"
    "P3CWEn0PvVOc2YG/MhOgsd5Of9qh0LGMO/52cpzZDRTHcsO93WfiVSnRqVVhPTP+HT7W8yXlXCUZ7R1MAonkcG/E++3hTjpazQd5"
    "PkU3ix4pOa1VRwG7UPS2C+m9dDnZpLMVPnBQo9qzVv5gAZZOYt+zJ3r7DYBNWE6PaotgNgScaLqo9/Z3YtFMP5WIdTPttlTqFIN+"
    "XyseczYrTuci4EtJwdQi2i+NZ7XtdMlFR+POzGRbBoY3H1WjPBcOJ/fiTV+9n4xmhPyiEWNAiZumx+7gXnucZfdn+XbatWg3J1LO"
    "X+IWPXo7UGb53HanHd4ZBry0tw/WibDNVwMl56wRD3eKRS6fjI4OhGnKWW6zrsZ2qRGTa2JUTu4djLKJcVYozfzTRDyQru9uLzKD"
    "GivuwfxafHUalGM1KRSapL3x/jCzF96LS518QqZzvmR82JVhJpmJV5oE5ODCU6bjRWdw0inma3Qxs7+Y7A3pBFWrjXKzsaszSmd8"
    "xdAkUe7nEwGBbxXqYjmYqtAN76yxzXbGbDTnSw+65XnJlfMEw6mch29PhdmIqgQHg87IOc65fb6d2aLU8+4uuhM2y4R3+VmYx9+p"
    "SfmZALvn84Ts/JSpzyRvjN1t724nm/ZYiCofVOfdQbrbd+YKYB4Js7CfSY+yE68zvb+zF0sm9+PORMkjFNEXIkuBQlnITzv51m5i"
    "lotn+ovMTibL+urbsdbefCSmXQdynKtTWV5sib7e/qhQDbNx/zRV5jvtTohbTKiOmBGS9VglEfMxaa7a2KW9seRuTPYtqttSrZfY"
    "ycIUx93tWO2gSm17g50Rnw/l9gbxer/D70bZwG586qWjhQO32MsBbrbmDUGiZY/3QOIDO+UGFxVCJdE9LufGXGq/MOB2xjvdhi8h"
    "5VKe4X6olJh2fQcw0Kk83K/lJt5+KlsqlcdDiqvODmqhzGxRpBI7cpmq+OeNYqKR8pfCfDaY6G83FpwzH2wMdv1jT3V/XGDTe7HQ"
    "rpAK7jSc6KQJtpwA3TcTpiuLEtizoZ1FuFFpdMtuvi4NvEG/v9qYFvJpetJOT4NBnz3DFkelfbYWTQybg322O96lfP44G3cxNCBu"
    "UA56y8UYF7JndjxjPxOuehpN+qA38znr6Mju7Wk6kBFTgYORVE9n5D43Fva2e13ntp1vDT0He/NAqxHdnzXnzqbMTFih1i2Mgf63"
    "p+2d3VSdG4r5xbzulkvxcKvYdWXz1VAU9N/WWPb77PG45M/Zx/tFyj/spxP2HjNp9Hp70f5erFOOCd4Q59zjKjVAQ3taDBzMBbrQ"
    "GHkbIiMF7PbcQSdeK8fKtbiQBr2/79/J7vVLwqjY81cShb3EDt3Yc+31Jgd7Kb/PT8/3GWEUi0YT8dZ40rAHWoGw3Zdf5HuZ7oDq"
    "S6GYXWwW5j5Xw1nie4tA08f6t6NC1BvyhUutwi7XoNlMIN9BZcc5fm+nKjeLAWfuwBdsdw+6OaEc6xT5tigtaq5CqRIOzbvlIhOf"
    "eHqtkTudaA4OCumKvLO7HetH0+2Ji6b9lWHB7kx6xVI77i7H24k5lZ1P+9uSu8g7+9XYIhntlg+iyUUjzXtSM3o32e46F/5ov58P"
    "hcScuDfq78u5RbNV5HfZedKT6bIdV3QmhksTj6sr2+322cLO5Sel0H5dFqthf6GUCxWL6dy0vd/drg0y0XzCHQgvpHaSz3o7i36G"
    "Z+3JUNAVzvmnPkaM9mapzLBQTvgYKV4cDT2B7cqiOotNk4tpW3KmDgqTekjMNgtijWmHnTtlKpqZZqJDnuswiU6/dJAdVjJUflbb"
    "c44n/d0DOdBwV0d556jh5+eD3WiqM6zZnVwwsBPPhOhkpRGO72QP2P5By70Q+w3JKXvm+bTTO23sDwfl/VZqxyt6g5MDD9Nvc/75"
    "DrCnkZANc+O4093wjUotwZ0Aw07MUZ5sAZApEB1JCyEdjeUXft/EHazO+5SnyPqkdrq7X98d9FFccrCbcRXSk0RNdNtLE3sqWKpu"
    "F4tMI2RvZdPObLuSncZdreKkPgtPmDIgRYlN2QsuXy4k7SYrqV4htTMB+TxZ0NnwdDTeBhN/7yDPePvzar5bK8rb4/JOlF2U2Xpy"
    "kVlIfSrVtbcDMQ9o8dXtspB0H3Tm2414MO0JTgP+YqVWoqrZSqvRCtT7/pQv1PbOxrk9phHPRIG3wXIBjYDGX2OG7IE7PKtuC7xn"
    "npFq9kw1VQE1pzrf6TkHo/35tO3MzlpBhh+A5Z/0FemJVGOCfEgQZv12QK7u7Y7B9panKb+0n8iAiloouYLA3dhA3d07sEvsaF7p"
    "0nOW8g2rAWqYrQX5eatcmDcS4UxjEezSY9E5j7UqzZRbonln9WCQl7k2F+r1FpRX8o2LfaZFu0YtsRloCzUBFNFdQWiV9hepzn6p"
    "HM92XDQKGR7InrqbEtjCiIXlp7pVsSaIg/0pLYnFuXuXLfhL/lq1ftD17e9H6X59BjIhXRnJC5rdqWynEj551K3K+8O8SDX7wfxC"
    "CrijO5K8d9BFOkq4MdpN1zPCvlOSJjlnoj+QpgcdZ3a0fzkb/oSc0JHU+DAq3jk+To0dU0qmu7faY55GH6ewTDtW2xEt8JJsYSIt"
    "gR4PGF520CJDyUySY9CdleBYvk/YbjEOkeEiBAvFCZJxyPMhA3dadj161BWZdmRCk3pDXYZqOajhkOFb8S7LtayM7UTprdCJHEkM"
    "JdLdze9+j2ZFmmMs9CxCuN2EhZ4rv2KECBLO298bUnLX0ooQA4/L4nFteB1+9A/efJcE64eDBrQS+YAlRAUsAYsL/nNb3B6Li3ZZ"
    "ghavJYz+pb2Sd8Nj8W6Ejc3m3S6H1+JxU25H2GfBf1z4P68DrnA3dJeh+x5jR+4Q9BK0uIPchn/Dbx6lx+J2bQQdfgv8y7m9FndA"
    "aUToGFuAyQS7qyOB/oNp3JwRJkEVJkEME+/Ka/Xt8iXqipOgL5GhZcuUbcldqBwiLF2G7XRl5XqGylrm+K8INx7TQABcEyhlGptf"
    "e/ZdkmMl2TgXAEbX7TUVDwH01zwLrT7zQlWHy73yDOqueRhSH36XlLoCow2gzXKAlkC5IqBcXOAEkbBIsij0AT15gWcIXGJDHHPw"
    "gJkwvNBqEcqUAo5QyOJzhFzRsMNjQf8w2sDCAerg5274Y8F/FJQKO1xeeB3yR/2OgAX9Q0/hn88RDiovVqssezkAtHF4YSIuhytI"
    "uRwB6A//UZpweADfLj3eUJ5D3aAjGEateV3PXReP7n9a1fc/HDFeqQHLjyUjrvgxYvjwS2AMJqLyAH13V0giAFTodQQoj8NtQf8U"
    "oHot3hzMKMxt+BCIN3xKb9KUGppaDFi8nM/ig1I+U7OI+tK+Fez0uKG5DVzc9AZRZVelYkoUham4fkJLHgBUj9hQYAP+4WptgWsx"
    "4gr9e1wUzFjlNp4Nz15oeb8B913gImH9kRvgGghvOMK5MKCd1xGOLitDOYBI2mesb/FM3F5jBxaPAiQQtSYYAWF3A5PACk8ElAaA"
    "WMzUCmzP7Z0EDGOCq7TfeG+ahhtNq6vxv+FcY0rAcEKY+8BfjUH5DAzKt44pwTIEaACCG0PHEcZ9+WgXeoTucF9uF41LwAAcYTRn"
    "jYFPDHMeAB2F0Oqg//QCOWMJgIo7tIEXUC1CcYxoBNzA43YEEVfaCG24jZAHuRGyuLgNgJXPsEYInIBFhhVB9TdWAAxsaOJbfQTo"
    "p3E+lm8LKyLTo4oHD5YAbtel2oHJxqUmQ4YWm8LMhJkehNEbAQ7Jyu6GD343vGnzWvgdPj+wPzcsMBSeBMx4Zp4mLMsEtQZw8W8A"
    "MzQiLpB3MGDxpYPAMgwgdGNWB80vFOphOWYFZT3pwCqyXxqEZ4W8gger0tYz8a1UUhkTdxXTMgHRP1EZ2eySbhCwmOXnAD9CwFIU"
    "lzGoQyzfMSsvHsDnFdox0RKaZcg8CdToJbpfhYRnlYjDXc9Ku2EzTXc3PKv8IND1XWIRrjXPfGuehVS4toSpkeMDUMIao8Tvx0MT"
    "DQIF+RUiVdnokF0VGO7gxL+iuoCwCgZMbBPQFGEUh/AqZGKcsLB+QL09QB63xW3RZTZCHsODDfdkw9go5jnujWWjG4ZWoZ5fGcRe"
    "UG8ECSkMabVJ14YvbWD3mD8YylpUzO+I7NBM7mGF2gMKsa+qiv7r3obNjOKKule81iqHrq+8fP1dUug/B6dCPNmDAaSI3++SstB6"
    "KqtTNb2NFiV1QTRTSKEFNU5Rg6UVdPEgk4AKA84p6xFweDwbIYc/oIrFIcW3jPgXRAuJ/1tR8YPQBDxDbzR9m6OGEmOuDBJ+Wcj4"
    "wmdoFIme/opegKhiaVkA++MoE6MATPFLCJ188A9YoSWEoYbv97zSBlaI4J8fGHcI/vmU+8WKNPUAWw4q3Ijin2elQJu0oH+g9Hrw"
    "H4W2WSTaL2kWvlUG5lvlNCuqEzwPIuCsGlaoOeB1ytJ2W5ck1v9BCWVix5ftGTSlgC5vhxw1N7N9HweiCCkRlpBC9TwjGzQl0DyR"
    "qoR+VF0psFSVAoqmhDvUKnies3wYl/c8rbhRGoJK4TXzNiPHxAxsckmzcYNqqBgFzEAwIQqo+CCJzRx4RYoAPbnTwRVN078iLYOc"
    "HwlltxnFFqsCwtsNrD4KapJfmJr1dDdG2hWlKgRGSQCMkiUvcXscwaDDpTRCcwLdf04tDTRwsFQwKZ0sHTQJ6xG/yUCDlCQVqAGz"
    "yZ/YjkRGHou8RXL0pJmVkCYdgjxaliBYwm7ltwgLYec3CcJGTlhmGgMVj8CoDn34CJKgRJba6LKtFsMTm4QsjhmCbFF8hxGFscTN"
    "q4yc4XlGTO/mc5tHL7zQlQfcZqFzyNw5PiaIkxPNj1PtRKwOh4OxRW4zDlDTZEa0xgSBYyje5ugJLG+FcdiW85nT1iNWZgYSTGpC"
    "cWOYECnw8S7qeVMmOarJcJuiYb7cieagYiMlx1hiKkzbyo85zkYeCiR1R3lYlSmZUR7fUqGDn+eouTCWk+02YLrVCoNU26IjrEP1"
    "GGw5RmNGhAlzUEYQrURzLMsCf4gBJOGnTCuCAHQHJkLfvElZj2abtENotyVGzjFtmZzqt3VEQAAc8pAnGQfH8B25e8dGPmUsPDO1"
    "VBiJXTDFpsSIE4Ch4X3rfzrWljrWlnmsrZWx6hDTu7l5E+ajjMSqP7SRaEy0o8VKMC4eTQLNE2aH8VCyEi12AogoMu1N1rCA1Q6g"
    "KAMoKty8SXQpaYPlWwQJyycClgDmUU3kTdIwEiMAgTAA+Quh381DqKdhOghoM6pDw0p7kjyH1o4wA9sUHFNSFileagviYPMH+JID"
    "BGlYv3MkOGYnw5ntBydrSeDEBss2oIZWOnJb7VQBMXSLHJ6b+q0+eoJkW7D+bIuUWRme0Q78qzavLQqxyUciEdoxQdjOscAdEDRl"
    "KzyxLedKO/D8T0j02HYHFkcnnBRvPRqCeDXxggjRpERCpxA5kgeGAuOfWV2kcgkE6Ha5SOb42GWzOeHy1grzWAUpr85sKAodkZEk"
    "1IE6F0yv0CKx6TI9oWbEJurE8IwXpsQmHgGwE75llf8fKGCYqNo7C12rK0dsbAyJTRlxFuOsOWAXMLlNJkIgnx+hAplfNiWray+u"
    "MEYdIQ3owgyG8txC8ewAsGGjTbUYwB4NeYw4p47vUgMwFmJ1FgkSsWg0bpLXUbWJ6mnlgGeT8h2dZ8Y7kSOWp4UBsv8OiYs33vnm"
    "6w+/+fx3AOeB0CLuqM6iF4AtwOtHb//+yUdvnN/7l/OzT87vfXp+7y5aD5qGclSrBQWefP2Xi1c/QA9bqDI0gWq990eoqLcIo0Dj"
    "h87efP3ildcvfv0KFIC38BzetoDnwqtXXv323V/DQ7hdDkKvaRwBasXchFpaaclU1NwqsB6O5VF7j/7Xbx7/6WeP3v7d8h2vvrr4"
    "6ycXn/9enxEtDFkGTer87A/n9946v/fVxcP733zxkrHA/AVGFI1Fnnx0+viXXzz57eta8ydkdhg5UkCGzHu1NqnBT4PcEOajgI3U"
    "oGiAH3IwqpMmzcDUwIgdnmqnpAbUO0g7fmFN50ZQ6QNBZdc1tgaul9fJNML1i6ZADMoqzszlYDTgIWiV+MgRGHAGkD76/OXz06+h"
    "nNCHJrB1ZlyTv754fvohGis7UHtQ8FsvoaC4OEb4MqVYWcd9ZTlXGpBEujmW0CgL0erF6R/PTz/+5i9fP37rgdLMlBJRO2qRiz8/"
    "PD9959F7X5+fvqy3oxYB+GDsfv389OHjV17++1cvw5pC6fPTH8Lt+eln56d/PT/94O9fvbKsw7RASTGj3ItQ9GMFgOenZ+dnrxpK"
    "q6j34PzeJwh6JLDlloLsOqJD5fPT13FX752f/VQrc0ImgRuAIj7ZRGAlO4K8ScAfUMYEoAUC/YVrURjCNfwlNDOLUH4JEo1hUxmJ"
    "4hzE8AMVW6aUyxMyqneB4P3lv8JCqj1989XPLj7448Ubb1/89R38VOn18btfPPnwweP/OsNUpvT+6Ku3vv3wPhSFqX/z+Wvnpz9Z"
    "jkVp5jHiB8pwHv3hwaMfvqENCLX16y8AxuenP9ZGpozk/OzP52f/fX7vpfN78PIhPLn4/LNH9168+OA/YJ3O7/0IwHl+Bqv66aN/"
    "gTWDJfgtLBtaKkDQjkbOz8gBr2J/KDx5GVX/dvcjrbJBH09Zj7AM1lm7KpBkg1gWL6voq1J22wqqA+hEhLxB2BlStC2bMQiNpRzs"
    "idajPhIyqqTnI3FFFz9kVGHwNLlO9EFPsvShO/7QfcfQzaHLpGf0QEFXtHAG5CLMbyB1QCxrHYuREn/Io455lVBvrQjdyz3TQws9"
    "hI5F1LEyT8ZObFrQE9cdu1UGW+Vvd9+CexnbK0sxjHQmRBZbBklL0N0+qDxYnyJULmMugNw+BGnUEtEDVAXsA5JZCuL6MMKA3YIa"
    "QiS3RShxXmITP0IUA8+ge+Ve70tpT3mI6XOLQB4a7Qmi0i2gbr2IQqhb2gVojcA6iSVOlYdW0ILw6j5tESWZ1VSgIa0aY2v1kfrQ"
    "ytgMMFg7AzDkzNrW+oGsXVQR8NeCcHdVaXq+7kl9GiYs7AMWUoaB3AAF9gbj4LfQEm6qo5Ic2yLVQYkGBl3rkHGgNfkeFNaUsRTo"
    "7ipX1IsRTz7+1aNfvIlkCQziBrQNTNxcAfHnNRVev3jjM63OhG0xmnly1XhwOcQVr2394tdvf3vvwcVr//L4rS8VK2TShiJbl6oo"
    "i69yXGCZdSBrYSpZSnEknl56/fFb72uiBrFKGOyTe395dBee3P/2039FT/7yy4uv3oCaSmfwXBFnWDS9axoTLqCUL6QQAaFRoamY"
    "hqWIHnVceuuK8gWtX3z9IuhiMJq1/QGXf/LJRxcvvfvofz24+M0DLIRXRwDVlTI6DS9BekMFlHp1Gc5IAl1uUpXgJ8jGwitJ4Tau"
    "gvb5vd+e3/vD+RmoCqBPwQTe//b9P1z86vdYvfrw/OzXSMM6vf/kIxCLvz4/fe387BUF/Od3T/E8YU0+U4Tqk7svoqV6CKv36JW7"
    "52c/eXT/R1gZ+QgVv7QGWj9q/xrioZQc6fqJGsaszpVUSANIEROHcndbxXwr46AF1rSwSB9ZthcvZhD8L6+8qQie9jtQUAXrWBbM"
    "w1yt8+RHCDG+BTgpY0S1eIFGJvK1BIMmhmZ4Dy4e//DDi1f/W1lNlbXvjSNHWBVxkaC8uDVNxaNoJF6DROdl61EHhB2Ysdi5ppnS"
    "AJA2B3Lujg07BKwcyYLFfsiByCI5JMlYeCMJoqy9su6ND9GLO1tbPtsGumO1u+Nj7tBzZ4OFP7ZbbNt6Q1Z9QzaVzyKsvqVJWFgb"
    "7f1tfkt2SAAMBix6fsNt25RX5O16piMqYz7k0Ch1V8ZlLt7mLG0ORDOrYfrj9x5evP77v3/1M8KetHIGWYzuTkgO1lVUx/Y9bZA6"
    "A7yyg4Eg6qa7Nh+tGQW8XOQ29ACwtWluQyAdky5A2KEFtc6GVvnOidlLwlN4MVflhsgMOZPoUFAKPdaG9QNFIb34K1D3p985Uuqc"
    "XLz3C03lVwh/SaVamRdkaYtARsXP74LCDCKxyFj1Nza7di2NB6gYwHX5AGk7dgLxPCQLf2CcLBg0YM1YUFYdKm2aJAPKIM7AAg1t"
    "3G6zZrwdsEj0ihENViQHl6pntsvatKdsRNwyOGg45KBxirZN11P1OdBdkXOIIIFrcMBMxC1FC9rktgiYyIIRBcJmhqrlO0fcifM7"
    "R6Jpkip18yR2bLFA/BxJOKFdkr+kEOwNtTnDVBEF3bjRd1S3YPSCLAEZDhgrCyTIOjown6Gk0C1+LERuC45B/wXQ8I6P8RUarc22"
    "hvSuB953ZhrwngVE0B29BNHNmwqMbGb5rRteyNi5e1+/Pb+LjVVMiwr7NgtGZDijooAfKshMwEp0QI9jeZpZWgyHJG9ylbvMfvLL"
    "Xmk5MsWahUNCkQCY/4Ti8HveKkZui3a3jXQzXq0V7BrmGErUi8pG5/B6LhUfWhMwFmD3U6vNCa3ZYUmzyfoGY9JK9zjrkQi43jGh"
    "ORSFdeoyVhuSZGwLoCw7hCFGCMQ/4ZKC+hPGdINSWB2STImyVGflrpV39Jm5HSBo2zKUwkqGOrMbvEO1D0HFEJ9B/7xhrHGlJ1Kc"
    "6cpFIVo9P/0c1vvRe/D39Sd//er89GtQTAEnLl588M1ffgqvzs/+C2kZZ2BEf4bLP/zm87tPPvpY0zU+u3j5JZPeARrH2SmwUMXB"
    "onhuDI08+Pbu+xdffATqh2Kbr6DXlfJCbFKiBTvc17lysQ/0OpNhBYV1v6cOsdtuJW6l3duJb778E+KOqEhzLjMSfj+yarc29I6h"
    "rAgFSN4Gb/+/P+MCy2fAYp2S1gZe+61rF1BpQkXcRIdUSUmrjCXOJmZPSHlEqpOBbLiI6JAFmeIU5trmBEEEUYeIX+Gwylvgs8CB"
    "rRjnWowkqwxL5TTAslCd5XMYADeGe6sAU7IpEhPzNWyp6xLz3peE7dbTfODizILcSAryJaEfIAnbWq68su4Eidg09xxLzJIEwmzN"
    "qaJwq/9bAa/as0MacqxsRRToGApDK456IGZms5ol+/4Qe16WpimzdfUwwEweMMaRDGXABglpwMyNCKLhLeJvd39K2PFzBpbz/O7P"
    "0Ypiyl922lANYiXhmVdFD7NWdPDa6rVpXciKoGlLMrJ9OWArxPGxVbvnmZkM9/pr4IMigVnZmJdZ7nsRrwvJnps3xeumOd0YL02v"
    "b99+7eLj15Cf896X3979zycf3gfawuzgIfKf/fy3qssNGM1Xb4EZgi2xyybHIaEXhWWSNaBoeKWNWHF8XEtIV3sxUFQTOzaX+rzq"
    "bERKwB1saRrg9gzdSFf1gxswzk4HjaJbDTR8QGj56OFryAyx1zmstg1UOjcPCS/d/3BIoBigQeEmSMNag34gCQJvVngf/fuHaFBI"
    "ATh9QJAwKEN4T62M6UUZH6eaPrkO2C7A9yK3i80eSHUHDE5kgXmAhUchjgJ8WsNV66GM7IMb8I7iKRCVaIKl0i5h02wbmRShAHLd"
    "bcjwx7a0RgxR/dFQsaEuJSesBU+ug8enmijQgW6irHcfdtmhhQYjxeAcRbVUWSHiNSJlm0lpOIARsS2Tx1QEXYFEdFpVTLDjY6Q9"
    "rLXADu/cagPfVlm6RWhbZEXTxAyAA9Y8BPvHY4MCMsuPmVuHDocDRfGrDDIHTUrokqcLSNnQmXcSjB5SeWRbzZyw3VGgn5XhlSAm"
    "KbqLqoiO4VjqglUHUsBOHBN2gbSqA9PsRfcWmFGqWLATFqeFwEZG0irYwLQ60Sbr2EsWakmk0ShKMphfyPiC1VdfASvSelOfkOqv"
    "igDaHSgDzKzYtsJwbKAUInPm5cdv/PXi5w8UVwDSLO4sjcYlN8OBcVhptEq6n+UUKTuabwuFC9TQAeJoP3v8/m8ILWlEHZOeOgIT"
    "4Dswc5DQHUZ24FKXpRohDBF2QK9KM4TJo3D67vnpf2MTTx0C4kaiZp6ubwG7A/Q2kPkPRjI2Yy9Lkymt4yTCxVsaYiYkjJgJ0crr"
    "4pt/JnhpgZV3z89ee/TOb5AV+s5vzk/fAn6BuL4h+Ke53V7Dr17H+p4yA3kJRFDsS0OQy/8kIMJYEAR5DEFxSeIr9Y1xd9AKbORU"
    "gr/Ypv7my1fxtLCBDJAVbQAowFp+qRHJtqWWvdKwbGpYtpFrcfNkzUo1jdviMN/gQZJXL9l9DK12CItCcExbNoUdgJMxFvXpUzML"
    "ht1VnXqd8qZsmSPWO921t5qGBko5PxyrOEOMQJjjDBYZC58hR9FMV9mVQqgKwb0vz8++xC61P5/f+xh7D3/y6Nc/f/zHXxIk8uTF"
    "hcGQY2RoQ2i3NfxhHCNDBhcowvAATDEjDiG1a8CifCFVt9MTJdbNUQYmKF2aIpRUcoPWaBjaNJX54SBOU5jhxBxC4Ll5jVB28DFA"
    "Og78wDTi7yDUUYrp41bLo7EifUjzZj9EAfA7BhX4fzymwuqYCmvHVLh6TLo6ZxqTLkHVvJo2x8w23SdGrd3ASQgkZpYrie4uDUMp"
    "Ij8vV0DpCEbOoHL1Szj27QcvGTB2tRWRoUF5MLajB++vrzjmRcbsMV4u49lPvvn8VdCJFY+xAXSX6Y0WBY5TVk0R6oYW9UhDsaPY"
    "viaDpXgFD0G6B28S2jYzW0lxgDWaN/ZXTz56ex0ff9WQSWBQGf/+1ZdPHvzu4uHP/v7VXxR/wMXvPkKQf/N1Uytg9+OYuRZ5eANL"
    "23/BEYszzfYlmiI26skrFfmBwAt67l0blKEqu2A23W6HH6XEo09wTSjRurHRYgc24sSIDH99bdPyffifO+xxuAMhh8vhdn3/+yiH"
    "n/n+9/UxKwukm1hJUFNHNrCgcyhJN05JAFUH6LYDK/LZ3bhhlZFFhUlZuyiAcgzqHBjbMxZKCUjK2gzKHYWUO96g3LE3b7K6jsua"
    "1BvbjUiEQga4rvYBM7TQESu1TuHrRm6XeSsqT3axlnfzphVfIBUbTL+5aKWUN6Rgs9lugVyz0hHaUD2plF+dsEH02ZBFi+d7qXLX"
    "oVCAXqSwpgi0fgON5ubNNm3touZoVe3vkmObWgKPd8u9OV7ebLhVZqHGyRGJblnHoHdK8gvIxHDZNmDwhtvjY4lXpkPidmyGBlRS"
    "RY6UsTpq6E5pwnAL1vN1PVzuQkOc1tUrZATB6mqZF4hsR1rrwKuZ+sPIckKY9d28SSl2wu2I5xa2GrA6fbVfpmvmV4dXl3Q/k6+u"
    "JchgHsGclLw6GNgNsJiQ5N7UnsEtisOjJCrCdh2hixxhDAVRqoWB4vfXRX/k5pqR6gm1hoKdroAyvPHRArotoGqS374NSusbhClx"
    "dn8Ma3PDbVub+0AoO3mIE8OUnrdTHLJ9//zs7rp+XVf0q20DIlRhYFQULq+i5zJsGJFUohwtLbJDWBQxv5R0e0OtDDxq33ZdB3+a"
    "l1c9O4oItBBk2yz6LlfWnYSUA+1TuOTxbbZYo+KDsAKVsymTJwGhCTtmlzbyBq2JuiMjGVyVoauLlCHVwplZ7pBBeKwg9Pr0uk1x"
    "i3jyyX9eIO85jkhvEk8RozBiRhvwLY3DnyBpPQQ5rpvhQPumKbzAkkfiJkV2NrtklwVl+ob7hKQ0A13hJcYGFZY0wDn/eWpIzpB0"
    "mkeOTsip/qygXRkEVRcJqpamUYwjCUbjTrZbU0eXkoA5ThjoAfggDtpo96TalsYNe5Gpo7N8bbvVU2tLjJSF1o6Pe2p15QGO4vTU"
    "KmoZBQBdG1lYrVsw112pZyPnh9rNHeDnhrvIUYuag4yBvyQ82sQvkD5lhgCNhfRSLtmOZtpgVmFshtFgBUaD62E0+OfB6B+cMnIt"
    "DdAcJKvBLbREBHXoVqUcGkLXprv8tBrWDjkB9jVkof/OoevOHdzp/HCiXSvSU3sJ49BfwjVSDDS06dq2UE/ajWIO4I7aHAUm3iZ6"
    "O770mIxHlkSBxGFXm0EnckO8eXPKW+M2chLpaTI2E7mdWZWxUXiN3VX4pRoispG7kc7Nm8s3KG+DkroAYQmvmt5vRtUKni6Mt63E"
    "RBHH0DKBMqwJchddoYa7BNhf6NOyG/jFZpyUqWYG6YmbLnXzhCZtlB0RijhCe0BudMjldocJTWzmRFXnsJ2Y5IwoWePkDQwUUFp5"
    "mEsC7ZyG2R1ZMxryJ1GsFTRJ/YEFRRDg/VBEx5zICaZNjTkEfGNztpNnUR4mLL0+sZDQdq6bxOuaBniTxoDEAhm9ZifPsIWSnjUx"
    "bEwZ13vRpWMPHk10ybeutSbV6hitz8l1Q0VnP1wxWbRfndAE2oSwo+Xo2FYYTTWS6Vg1gjg+HpNzg4VxCJR3BxjXWMP3aASoDDgB"
    "Jn6CwJRPgPTZjUQx3WUiBdxUB5qaIFzdPT6OYhJVG6gtKalDcoxGPjUbOWYiGd2VHLkdW6WfiQzvMZngtzoB5ZgIx9y8OdHfXUlC"
    "MYWEyBwfacvWXWBucqSqDvfZ6EpS6Ar1pxJWjllSFrSHQiEoK3ouOyTZTGm156A0jlklqBqmgJqJoGKIoGKrBBUzE1RsLUHpzT0b"
    "QT0Lkl0TWJWM5HSI8eHmzY5spWyOFnc7ch0ttFAAxUSMCjpBfwi3QIYag7A4KBMj88uQTGltiCt/Lf1JjLFHlN79hQURctIaQ6SU"
    "V8JWE/mfxBAyJwj5n4sjAPUiNL7WeuEua+j7Q5Q5luP1MTSGyNW2OZdJbSR3FG4hEXaEaxyzZBcTXYusXalF1lQt0mXQImuqFnly"
    "MvsH9dCTp0fnOFPUfYxDdXrWjRrjumVlzAa1OigxcntAK3kXouK60N5wkduyA7R5K4eUiTKH1RX5DrS97CzTMXeG4yIi8tjIyIsz"
    "pnEwErGZZebhDU4P4Kkqs7ZZ2BjDOxQQC2a0pqkID0+wJ446Pl42RiG6uBGJcEsPj7ZFF7gdhVUhtAOYVQB/BDPcFEh5kz7RAcuq"
    "+pZAUjYU8QMmtkGhvzayRVtZw2xfYPW0JmXBjJss+jBfnJtkIE2SVR4pLhhGdS64leRD1YFvdPG9jDfqvKoFgtQ0ZSWYggIh7/0R"
    "b+O5/JY75LQ8S/cdUohwy+Aip7vGNtxa2gkMDckxKtJVlx6PEkzkyI0boqOazKFQIvxgJxtOPmZb2iOMRDjqiNwsrZUd3rcu5aah"
    "JaOPj2+09F3JCtzVdZpFUKnWcru04r/N8LKwxzJT61ETb8wneIYSGUkGTnJrpgfi5hFQ6XfZASOMZeuM9KENq1PzM7ff5TKmvB3h"
    "nDftPZqz8X4KBEse0ne0DtrG9SOIzZJk5W3kUE1i4x30cKsOwgWz4FnkNnpwOANg3VGzsns0qW7NmSn+F7xBRy91QqIfJZSl5skP"
    "Iu3llhTTZgi8lczgG7+8uevEttleSfTQKq+mbhh3i2nV+MvVzBsw9AgGsZJhcnk7eYs0p1aKyDWBdpMD2RBkW9MY2oB5isaDJMEy"
    "AoDeoyCNuKLVMBp35FWPn6KF6Oq9SGxifFbuOsSmgqWaWgFLlIaFIk04/3TvnUmQtzWJVVbESPtaJYA3AvDwBoBAuE5+DUVT5gt1"
    "jXScYGF7yTbBU6NQ2I5ss1YBAKNI8jtYlLNYiBth/szSV6t0nVpOdQRTDdXXu0XTVv3GhjcRXRfBQbsNDc3cwGlajISDyKoCfH0u"
    "z4C0tvXtYMfHbW23mHqppPUi8l16kq/BesOWRnWjhDpy1CnOcCXVyaH9ejdvtm9otKQ12wOlp79pKLT0DHLkMlH2jrZX4+p5DbWu"
    "Ka3r1aGs4tZyY54CRXWDsSo81gQh9RooYxMdcLG0GfvAzSiYB8VT+rPREPdM8pveVUA87+RXonFzkLaIcAWJMW/fnLItlCnAtozb"
    "Nq/IieYiLJJBurkg0dQQLQzw7xONe+ln34Kyk0RGQw7UQoYHi4yAaljVR4dfYDmlFRWZgTBhri4NUoS5cw2KCy2Kswho47qymRLN"
    "Cef94GmBio9LIE92XoCJYcsHFLIjLV0GJsNpMnMXP1HmZN6MqsAgjc4uaAuKfEFHV+ELvA37hpvsCU3lAUrAFMFKwydwKGVFprV5"
    "dGLYefPC0BAhTTtQs7eM+ZVHwKRRo6s2wMWLOF/+3pvK7p/zs1+ii3vvoH1VQFSfgBKjJlQrruGzn2jh+3fQfiwDxl68+B+Pfv4K"
    "FMBu4AcoZfr0IyWAiiOjODXyRE/UQTmBtCC2SBkFG3mczommpWrBipaEn+L9WcanmtaA5yRrW2G2fqBkPKGRf4qyuJXxnD7Ugrgv"
    "f+eIR7wFQLaF/9pxli/ieur5CXivNI6qK/H0r87vgeL3KYbIyxgS91FW4+mvjHtXzu+eYQC8i3I8oPzpfZDe52dv4GLvoyxytG/t"
    "p/j/KIj896++vHjxHsoifflLvGnvLygz5NWvLoePf/B/cJ1O6sAmluoaJlwFrY6PF6CnUkPWKQydPCODnSt3Gd7KGEpYlYsIQ/bV"
    "bBXgIShjEqwX3BQ61seHtjxQ0pynLToa7yA0lsW52lKEQmcbWFY7JJW3oDM3QfaklV8r/o0sX6Fi+A3+QTsVZGUv8pjnkc/t5s19"
    "DghTGRXYM2qXR4woCsD9HANGkqgOc3KizeFkZbA91qokMacdiGZRC+g3csOlT/uWMheg7bVTceI0FCXb3zAOVPzyMLTW3XrrJwbj"
    "kkP0b9SY0w7MNxAU8IVhD4pWBM8HrwcapsY91g4UIEjYbikgZtBfZbxHKKhzPZhtR9pwSTRIlXZPlF7Qel+xTC1VUC+H22PJENgM"
    "J3izzHLqBTBtoQ/Ml1FGMShfaWQrD3AyMqmAE1/qA0HdKliLZo/WUWPJMoXNHr09Uz0Dv22MrUeSKSWWcQh9FEZzqdvc1VuwKQEI"
    "KIWHeOp2AtQQaNDP4gLj2fUOMH2XP97ar9zibeIzQt3WanKOqUO4StM2bATHRtJTtmevO69HrYnyrM7v3sVqDeC01FF3paGT7lle"
    "viaFjTel6BF/e+kneCcfqqXUF6kpyvWHnxvIIIa2deX5cmOiRcmzMYwPKmoR5iVSjcZWXYNBCUcKOmAFEhDMsHXJOmdJXRuSKUUH"
    "Ag6AspygqHDZURlTM5yWncU6VlMaqybBUXo5znRqKc5SnG8OAlOXnWIEEw3JIRkqIkfAZfIjD1lSMO1XU6gDXlAkvbKRzeg2cF3h"
    "M2ARqaLhab/68AyBNLIXOcIZSC/IXRaH4/SbG4gqtEO8xw7lAh++gMtoZfET6B6VQT/4fggrOYWZwzPtUnnOMCLqBf/iJ7wgcQwz"
    "hGfqldItsJMX9EZu3EBhwuUDWLw2i5+iCxK5NUSWlvET7YakOiLDII/gLZXL9EjB2sN23RWq7jjSg+veJVXX2oPlEoaZwYBpsQD/"
    "kigMqQ6FUAIlMVOIKz2PKjzG2RTPoQ3jCnhroe5VYQHFDOt2w6UtlL48/OryGJdFXwrDCkAbZqi7VTi7DRB2L+FKDiNjHXaARg6H"
    "o02iQOgqxMmBmqf2HKojOYu0L+HiHG1QZ1UHLEpCn0aw1CALkXUicrxeRMIkx0OULLoEn7ErDZBtFeNVcKpFFFC2MaYvwdnWsVwF"
    "a1vBcB22bQ27zSBur0Hr9gpSt3WUPtEE+xgzk6H1SF8LG2kS3qqSMrYdNa1jTTMhg0gcn5BdA7CAT1DfW25IBcZg2J5q90MFs3tv"
    "6YMk9cs1CgveGovYlN+9dB6eoCe3nro8Y2gMa1qmyT7z9J4qvFtcxwL9wM8zJZ5BuY3u1SXNGceXNYKuxyhkwZB5XbFSzu99hn0i"
    "qvmDbQZF8f8DmApg2qyzIJDF8zUuBKU/LcUtuk1hSAoeroyfkWjzGRLPY6l8is/2+C1KHULbKF5DSbS//Rqni2k21bKAvg/3AU5L"
    "+my9QXP6qX46imrNrJg4H97Hh16p7RPmlLIrc9qUfGVewgJ+mcAGkn79voEZAhnx7dswoH+FuWlbW/HJIIJ+Ks4qNOGlSSfBha/L"
    "eOMl86bMaxW6tUdYmXeaaJbzQ+VUL8O6N9elKRuGSguD4VjG8hkd87U2U+85h5MpYax55fzev5+f/Tfx9KxpvaqBj+tHX9wlbHhs"
    "b6ljw1vakRPgnwczjIHPDDPc+4myhQZtBsAZgfjoimdOFu8T1zq3zY7SQxjrl4jI1OGaz+H7FJ/ahzfG3/sxgBsRL9oS/7uVXU+I"
    "bvEJOyZHATl/ik0AC3Cm4NT56cdrDvXRiFrbJS49wyofEijdHfomCfQjKyL0jqbFG9y1/xvW9mnQJpQjEA0eFd1XpORGrmazdr2m"
    "ERJ/+/EHFvMSLf06xNNzcKWBxrIq6LRDVqKaHNPaVLwHOv8CW1rvUnm1RSgeI/W4PsTRgQm/9M3ndy+++Eg9/lMZ+HRrqjCorWdh"
    "ZlONmcEV3oav7cbTbnGWxJjsLRXmOAhnUFaHkqMNKoA1Grkd1axpG1mNxG/ejDt4hmnhg9BA8QNdeuxAkyc7kRtxdKPUxik4uHZf"
    "SSWX0AneSLeDSodKFZQ9hHUvXrMyMDIZdFreaGooL5+qDWxbAf4tgoxv4bOWNjv4OJeOILSIZwtsSa3uunRvI6aMdcv6WbnjGLOa"
    "6yrggxSXh4psEQYxbMjvRfNZ+heXj4liVsURbQnw4kbJXf3gpMYYlJvN6Ak8grXU5OEu2MRoNTbVdWR5Vt6ckNJ4OBREdHooOspK"
    "v8NJIWAALMl8BQORc0APwQ0oscPyu8Jw03ViYoomGrtvJtuVE4rQ9IAxGrcE/e2ln5zfvW/gFNpW2wemhu+i/aHrNgIZmMx9gly3"
    "wMQ6JQqxZ619dZhnr12c/lFV1gi0WtjnrCQkWP724w9BnfsYRq73B7qWOku019XggH5X2ScMxYtZnASOFSWdnV4B5iv4yMpBbMBT"
    "sGRZ1erQyT1vopNj3fjYFRjlJ1hUvYYVw59i+bByyh1KulDEuQY2Mwsl8JzXaIjLUABWkwGKP0eK770/qMAz4ti1mtq1mKUu7KNP"
    "3n9y7y9IsmnHCurQ/eYvX6+ooisKk8K/t8HWNW6CnWEmAgafwqCegY1g97JkoQVuZczK9wt8wxlx8j/fHCpSLRbYC69yrLzQYrTt"
    "j4R7uSVzttwFiew3dAyI0cGwNlnvWsZnFM8rO/G0lUaITagq1jMYQNgwQWbFJcqCl8gW+TfMDn6B/37svnjvF8vtzuQ/EWquJdRu"
    "XA829z8ENj049o5ChDqoTGbgEiwG9fHsJ8oeIhWZ7549fvjh4zdfwmeg6AdVfnbxoy8MfFMD1bV7eDoi2/KsIS23x4iis2dzQa8C"
    "hDAihun89+uTRCRRmK6Rw+YVVTaBazSLfDumreuKEFZWWHf+qFkxDNWao1iB5kFFm/NIachwXBzhAfKL6Vgwxkig+02NW4ifaXeW"
    "NsQSi0JOmiL4LA6uIa5xhNQ1TLC3FEXi5k3jeBTVYr0Lxa94iAzL8cbZ4xc/1u3Fa5IdgOkpa4e2sKJdvJ8/euU1XS9X9rX+U1ew"
    "qnBXbb0U75yOlTP8pY9Njwc4/rXrpPmyLy3T7Lo0o1XDDUU7TMabekSZhbjW1FRmUuNNHhpsM9mtJotdYwno7ET8Vp2wuhMYSizh"
    "bFOZhP4EG46fqAP7GMyFizfvI68HMinfWQrr69dX7eDxWw8QQz779PzsIyWQ/s9e15qE6FJbVuxnXV1Vt/9pq6rGI66ivUuTU0xq"
    "1Sl375U1x0lcHmgJJrkcqO7Eff7BGoIlTxvwNcbsFQusStjrVlYRFDrFApZd1/Hqij4dTsgTfg2nVTzlprM58Fb5fDRT2CjFSUss"
    "Gs/WShtYp9ZcFK+ZfU8g3578+kf4vPzPcCYIYOYvLu5/cfHyj7SDJK9fAjUutQr/S4C4FtnXmDMrtszFi79RzlLGSpEpnQV5QfW8"
    "mMfvfvnt/f9UkkKuNDp+hCaOjgR+WVGQ0Hqvy4hR7I279wF8pTgAEMABzOohQbb1ENGSe6CS+LSIv/xcV+Vx6oyucWnmAla6Tu8/"
    "eROU5w/x3uEH2hHcn6Ch3D3F+PQxRq8fokrLNvSNq1ivRryWePzJF4/+/Ycq/poNAczAzFVUZjW7JiB9pVJ9WVv5h042AVGEIjtL"
    "lXAZ7FnBsmWs03y6CcYz4tv3vnz0xZsGnzsGBgb0t2//VPWnL21DzK9+i5f6HZyH9J72oYiXja+wg/AzA3ErskkzbZYHZ6oigPxH"
    "YcHIpakRFqYI16rwNQbD1kNFYWUa2T9cET7Y5nwXw+lT41lPWvTBxNW1M1AeXrz04sXD/0aRiF+/gqCAjOuXl/oxMj5+d372e8Ua"
    "UT2sq/1+ZjAODdrzPwq+ihrrM0JQD2mvQE8PEa6HnIGdqGznDG99ANRBXge8SeLu/UvMH5/Dq6gvihn86bfvvqmAaIXnnt5H8Dt7"
    "Q4P6isvgDeziMLKQK4yWn5otFnQJHOAB+jaAyi5N6Xb/JEjX2TZrhDKOuq5AGAdk10O3zm5ssxYzu1LcNIATr2KkfBcHtJZ+N2yh"
    "/heG00uAQEib+vPPctGCbqIZPnAAja/lBN988YW6Omdn2Ev/MoaO0slLJko28sdn8bxtEqHhDH1A0nRqzSoNoSPOfqk4Z7DwwGFC"
    "RGxqKO30fXTa2Ad/hHldvPljxY+iRQpV/RjN4UwPHL55OSaKqyjsbnmymvKxh5d/owdADGP6dP2ZPkYzlpEpFh2xZVZl6C76SN8Q"
    "Jcm71qRzjQcAmvkVxrn+YSS07ApLQT3O9HjVmFubs8Wx5jiC6nZaOsIQq/kIW75f4W8sfHq1EmDAoYfo5GNF77scZH7pRZNdgj9K"
    "pPkS7t6/JB00jHwddX7v9PzsY9UXg8D8vonFnv7bpXrYkbom9AudVfMx9Pbel1gRQciEj1qDB0OW71iwy/M/Lt74TAHqk4/euHjl"
    "R4aDmzQCA96MvAJIvqFm7t6v1i2FaNVSLCUr0d1iBY0cEG4NYj18/ODhtx/+AnmEAYnuva1/T+HvX72BBOm9T7QkYaxC3cVOEkVK"
    "rOX0q8tJrPVnolOoUYM/VeJ2Vfy9S5h0XRD7KBMMJZcto+4wX/yBCBSI+68/4wvsDjl7GZP4Uqm/YghXWWqaVmeWdgqtYS7z6N2H"
    "39792Rppd/fM68KnLH5s0BtM/B2vyjIOpbmpH1x8+afz0z/gPl/BPMAorAFZf68gEG7kr7jxl/DKLeXv47e+/Pbffol12zPt7EfF"
    "668ZrlcCwrATcOl6RCDAmeFL35qGxpeE/KdPfgvC/2vlkHJkfWCKxyzv4aMHn2DB+BN8IN2Pr12R63S1q8jr7pmiEKpGwrtnOnFd"
    "3c9lYX7ZyDBIXP1LOkjT/sOPHn3wlVrMbIA8u6VhxDAF+JoCf9/Ayl/CS/cGFmu/Mk5YOeVdI5Y3saXwKf6KjDYYIw2aA8jjtSrA"
    "/3b4qBzpeUd+JfNYB+m7p+YRq4hrOtrnc9z9dUtyTa+rUXSsAV8hjVAO0gqVKAbfKptcyTB5Fv0jcFn/wMf7re7DOP0YX7+nsx6N"
    "pt9fD4J7XxrW4X3zgp89+tPLuhsMsx4jWB8Y9q59ZiipqXOgCKMTQ79WVdrPnnz9FjSDTZVP1+4V0YKMyOJVuIn6kcZX//ToxdcU"
    "KGKl4iEmjD8gHvTgXw04hMYIUtSN12hFDfotLvRwmVJ29p+4gLInRrFYfmgc/+P/uv/t6f9SJPm6+MBD5RxuZAMowQSECb/C6/4K"
    "ur6CKRsM9EtK+hIFuCZn4SWcwvhUB+Gq8h7VamnaO25mVX1X0iPX6+9mS/BjM9nriWlGFY+4c32iV1PmpWc8+m0osrrBh06z17M/"
    "jJHN42Pu+PiGYWo4DlAwnLyMEskpnJqO0iaUvNYt4uLh+8ph7zg9ZLZFXBlQfnndmt/XYkJqBNdELiho/jQmM1h+EPjK5Bflq+tL"
    "BzhK+bwKCPrUu1dOHeeMogCEzidWY9rEJnV7mdm6RaxXVkz1cd7UprFR9DE2NS1t2KKWwednChGgb3C+9wsduTYtBFkF853vWPXm"
    "bPi7RxTNWIldgkQnsSzjceJ1Wy8ktO2HNH0Ky7C7wsx6DXsPcMIPcXxseERTPM3AIgA0UQT9mVI0cG/oZBVRSSYxfEBMSRcyZpSM"
    "UUYIOmL80gai6wSFcWpCf4tQt+6p2ifWmoDnII3v7rf3HphVjOUJeVj1RIUB9f/2c2DHD7/94MXH7z007cJbz68vExrCQIDUBGax"
    "ZU7cM3jgNZXdIAteU9I+cPbY6UOU73Epf0uRcSupt/AKVz5dY+jqn2Yx7Y3Z7ViVZB1GydPhDXk6+sEbhyLJmTaX8Gt2oqB8LipC"
    "64lfLZztL6Jsfxpl++M8LeZOpEVy1pbt5Bk2UOF0MDW6iq5x4HOTIa/+noQxU/E+QTKKo/qS0m40zdbFJIwO4rEWhBDVfH5jDOL8"
    "3kdY8v8JJQghx/gVAQSACqUGnOgr4zdPG8nQsxzKciuBeTjmCNX1w9GdqvRzxZ+xXFouClqQJVeWj4/ZNeFowXrDlNZPX7GDEi+4"
    "ho8YXOLKLorl1E9st5pWqzZ2PRORWNHVzdo1Imz0gd1lNcMngvAXIaBFzPKWDZ7fvas18vFaTqE0qNZa057UZ4dDJAj0S2PbqK72"
    "2FDZTliwza3wjI+vVE6X3y9Abj1Nv15NdrvCRrn3C+z/AAz+/Pzer5SoyzVcTtk7H0YJAEpqAI1SA2g9NSCA3giYEyw3uKIdmSdr"
    "83ENBuSpKStV3b9Z6eD9m+gYGHyidFuKEIbPAy/wsUj4rEt4w6PjnNFhw8Lw+PiI4VWEdJPodB20hQmfWIkucKbq5uEd9GXLFwbN"
    "oYQEFaN/ccq450h7FjlUD5hZBtlJlCOBP7KldeU6uWMj2xL+4qreGE5bFSO3VTEu4tQK5XAxJSxvw58Y1cofuu7gEpE2/igTPH6h"
    "hXdGKUWouWkHlH4AOKOem47lKTBrdLCbg0U5rv8XYedst6zKkFAhUBfl5VHZ+uPlOPBpRDIMBI9yKSm29XPbD5mVj+bhk3VI/MUa"
    "42OELPhLm6sPBbyuBuIfUqyo7T3nVzaXo6MPLm3GE6zLbW5rvscnKBvSr/oGX1v9Bt/aL1ZR6tandgQ6R9ufQLxQE4Yw8q/hZf6F"
    "p0DqiMc41Cu82Qtu0Q9JC+hQjePjicC2LC4kGtswQd46BGUHQ6ZpHWoVt4hv7/7q0ZtfIL3563+7+N2/GnkYUKL+9tHvfoklvvZK"
    "I84hIs6heesTi3oBajRu77IS7ak6O966dl5OKIDC2mh8xNU+6IeqX9Z0iP7qqNpoVG19VCHDqFoRRjnARATL1/wFxA39zffc/mf6"
    "0uv6bNL1GYMPlJOaUBQPRdj/7fzsdSXkd/WWqbW+CZSHGTLnYRLGjEXkKljX/8NvPv/w0dvIxDTaXqg4mNyv/Eh5BVrgo3//UA2N"
    "nH6OU31/iBzz+tg1r68SnDc7Ck8VDVJtTdM9cVOfrsTg8DeHcRQQ2fz3lawR9SA1JE+17pDHBF2rH1FUAyzvI3mFlK4P9LiO4vuy"
    "KN6uJx9/ZEw/V3Rnz8Ubv8d2ozYu7ZsYWmT35ScP7j758bNFca5IRkRmJELmKiNfc0y8QUytRYPVctf7Lp7TZ4GGV+QNeaM3lmxE"
    "V97a6FOjSLVmdNHTfkpsV/HIv0TcuTa/aV1yzzX5qFcl86BJoHSe5ddTMOszKap6to5F/wq4xfDFCw+xdrqYk7YvK6vEtfuNVo1D"
    "Y+qsYiUAM8KGwlOz2zQ0fBo+XA+cuCFLWDbBBaXztZgXQJLhwwsVZqCS190zPRFBi60hCtOj9op6Fnj09o8ufvfON1/+BvmuNML6"
    "WLM0z3BKjxG2otUM0GfLZ1L5Huj9MPw5+po1AyjcoYabIRJd10W4JKbwlzh5Tm8XJlEkbw1WxQ3OdGYtZbUZvwRvlpIE3udc3XII"
    "ErLDQTkgLvuatI62p1d0Qy+/+30p7Pnw8fu/wRfvIeffG8COfqyHd1Rj/u6pvk/g6ojtUlr+6Q+GJMunONxgUd3YR6QFesh1ccWn"
    "ieaV3Z3ruAF2Nq9hBPoimczTFt7PsOLP0rnXlq7NKN/vxR/7nr3QFoUBtnPwB3n+41U1BUxzySkofWkFLhXEkQSUDAsmmP4tcbhW"
    "j/M0VEdel+VmPpThosrd51RqLhlGYOthHvur1WEBd2lP9XNcwNxDH668ojOlJ4Xer3DX5J+ihK9Vlg3aHDpDQmac+PCYK/Tta1Rj"
    "OUJ0ZXm46XS6PUFg1MCqNxGskb/IrvShdkCQYuTwUPkkKEmY9ZaXNQApSR4/WdEicOicPESnNIIgJ9xQSHWsoqdSFyWWEgalR20F"
    "Oz6UwPwrS/+zmln4Bq6LjuZbUxeoDD8xRuX1RCOloroRYE3VlcCxoRLyXY4llCupTVchKYSTBh3KABt1vzZQ+E61WMBwuPMP6Lpg"
    "cjLUwJIAlQD6Qd+oo3gliQBR0aOfvv7NX35OPGf0bY2Ge0gYm0bpYil0NAlLW9K7uyUQq8rmulRyV80V0baz1So5vMtHS9/SNnCh"
    "XLRX/hOURPyRko8MKaBP20CEFwZNTt09h1ikcX8WgN441s+MeToog+K1q3y7qehuEk1OzTNQ1/mHepKrJpE/xc2YU1CvPJ7QoJcq"
    "VFMTTd/3E9UPwSILermfVojIds5ObKEDaBDtwe8KjpSeZzMN+zzCPUBSHNvhMzIzkEB3ZfCx8OSA5ZUsdtcaWU9jZecZv40mTBix"
    "zQlThHytFoM+PwQMpKg/ZTiOHUosAGnaZWWmOgTVCW2iW1U0hGc5DAJvrjaqFX3JKhhOEgNTV8FQc1qzbs+SaqF1Gcsm9yBhs11x"
    "vgQtDOcKqmpt6DwfnW65elZnumM1f0Z4nbUjDNWza566gewzrBKeaiT5qkI6336AYhGWv/34g/O7P//bj39pMdIo2KCKloWjD89r"
    "iFGc/PRhrTGQVWpGcWRLKZpIFONZi0KRRvahZ7Zp8ZTlHPCegKVdqeZPmTb1m2Zh3iOobOuF9nECB4IRSr1CG1wfrsvFQBzwyb+/"
    "hwzmP4Cx/S7mep9fQqJ3caY9Nq5fUkLy67LCPvvm89fxOSiKHf3KMmqu+kgPxtpHrY+WzkDdvYf2AdmOj53/72F044DaWNzZdDpk"
    "RpKtjG0LvdsknMTyA+ZaYNF5+P3vO+/Yv+MkkQNbtvMn5A6reIwsTOT2io8I+1WlLew2vIl9l4Q9yUAPNpvylSCJ3IkcaV7YFitK"
    "yrmn0ri5eXRCYj2NMJzG9x3WekQj9/9wkyeHlCibDoBHLspb6l3B7PfUPs2n+T3HtluFJShExc15fKxeRQqqi5MUlWEiR/KJdp6t"
    "1jA6swB/WMNqLZBdaN5a0NuH20hEbZZkI+hrE1tqvUPujjJJIcJusQ7NVXzpkDbVcUq2Vo9uaysHtlsLkdsFu/uKw9uE42MZnWKH"
    "h09oJ74jT3khcsOlreu6dcIrxG4pU0GxBsPCCTaVCXahm8LNm7RV+ZZEV1tNZcUUv7pwsjwMdKX84R1csqu7+pYVMOs8gkG60UHw"
    "wp01p62h+YnI+X18/GzztJoOrNrB6wCVhJs31ZuIQO44EPop50DuOAAB0efFdpCpgBafvKG8tyFPqFpUPdkSnfGt+i+7tiOlxnJi"
    "MOn28jBMNHLAsVVfvYbC3YjStPY9mnHk9py3jm1QH9eJoK83KtGh7qZaVPu2gM+mhMyhjlUNSIzVuMYY9G/gkzb1LM4SWFasxDgo"
    "jrOaBoOqK5TcNZxpp66t4aMKQBzIlhjfvHkDQ+pwfEeFi3KzhMzB2CoA5Wnw6dmWZdC5p5u95amnyIOMlhWGA8tqGheOk+DvR+J5"
    "YcpCH2NBYQl8FTEWh9FtKQUx/qIVsLbRl2Tx4bTWFQTDeEQK+sl4w0gBvUXnxSk4hvtAgZYCagl/6VT5kr1vy6peRtRfu5tkHS80"
    "x4MhOhr2/6fuXbvbOK600e/zK8AeDV902IJI2clkwEBYsiQ7ihVaCaU4GYYjgUATaBFAw40mSIbEWSRlO7IlR45jy+PLRLFjm4oV"
    "U84kcRTLl7XenxKZpPQpf+HsS1V1VXfjQlmTOWctWwQa1XWvXfv6bLj+yeU1nlJ8Ynf7zzvvvi7VNWiZIw+9ZNZaCq948xc7f3iP"
    "tbYZa0y2ZGW06EtiJMjAZudHZCepH9D5WB8PTjgVF/NRZ0QR7OeDNK55uXD7GPsrZtlpFKIFcZaFQYGJpNpXjZmpWedCYTGxvcSW"
    "1nNl0HYTqw+kXBDlGu5rp6a2YU3fhrX4NqypbThtR2VoG05H21AC08gCkxdGR48GQWkl57Xpb/aYjbA06u64gLvQ6NHYBZqGLsIN"
    "pox5UhZeTDtYVEENB9VQeWAuaIA5F9JecqZFf49Bf2Hrwsk8BrOSUnZiNj6caej/dDScmk14ldzDY9wbSj6OA1oqlDDhi8hJ4hdL"
    "nIMiTa+ACWciugwnegndhIhmizuVbtsEJTRSk0wVlnJ4X2g5ZIEewkLC5S3zz8hP3zh8RJaWP2Vb6FqAG5yTI8c2OEmaN5NnlHRQ"
    "U4qwPsKE8YRtWOCzst0jjxQtxlHCu5LBw6XVfVs4Bq5foVZeZVdIYg8vR7gzbJSJH2c0yaG+ZQluQEqQW6p0LPtrWLciJnP7/vr1"
    "nU8/GMYwMtgWwnXRdL54/42X928daC425qQrn9/6/hymC29g4Cva4PMT7iMOOoXlJ5R/izTNr62NR+pqpNrRT4XvA8uC32D9YCl1"
    "JTamPabdTMaB7z92aG/rFVjx8Uwhs3PpE/TIJzfYFNyP1iDbgTbDu38glSyGDl/a2X5h57kbwiOXo6uSGEHoFp1AawPRi41dIi8R"
    "x64YmeD//tnVZB4jFmJYrNndurx76WWy8xgBual96KFGIeHmJkkc6zuXfs7hDPe++IyUcpG7NoUDYcTD5roWyLOJGWu+fIcVYyk5"
    "lzDgWk3cW3c33mRpioRO1tCZZ0XXxLH/MFoNr+huyUPM71aPofZv0NDPRSiXMC8v8qQYMFkcNr0pMSJfkLWSiu3ax1T22b0XcLV3"
    "/gK74/Xdt0y8oLRhmCWv776+RTXcMoeHt/c5vSjpDs189kD7ti/rbuG9lGixmk1VKDm1vyERnG4lMgTzroAF3dn4EzreY3FyQtrc"
    "1JvvCZ6VWLi9v9y4/9bzwp5sbIZbvHOooSu7b/2J5pi9yjFYhqJtXkxdKlMd93hVA2X8Pn2ZZV8TIsTkjGPZStAMlHvOfhSyw2pU"
    "J8ZjTgN8GMVBYjWDCDC4QgqPF3unpbiddvzwVlLxYklVBB7gS/+1+/b1nfX3YjHkw+s4jAaF2X/v2XfILoZBXKp9nUiJiK9Urwgz"
    "dPCmgkWI6YA2rkh1jD6yN4zLWcxNFOMs4WXje1lXYekAXhVkOgzdrIZ3yIqH3ujAhIXBHpOeBRLbUKZ0Lr8APIdwLeCrUchHpjmd"
    "7QYY44KYGMrjhG4hdXsihymlqwvGdSmvyqF6g4oCwy8VpIWMDtZRYwxUvYOLcKTGiymRSz/9qb6LoPbjefNRJnMok0GwGw7qPX0M"
    "PpFqLPZmfJikzug7yj7QSv3glC4MglO6IOCUsqoTNB0kMykJeS57YTg8pQcPYI9WTNhgI7eSWtKphGdNPI4mTryheCnE/3jxr7pV"
    "Y3D4hq5iX5XnBsUV4LwXnQkhdmjDfwF4zPfIOk1qhf0YqBLAkIHh0/mdR6MQggHQWnPHj1YqPTrPSS6FQ2iqI2h8UIbWv1VfbJta"
    "f7z0pH0ZTvHZ6cci0G6ca3QqnUIxCJsCiQu/D4cQNnf8uDsfG8aU9DCNz/yg82mEuAw7j1NueGy+anYBs7z0mBzMyEGQHuK8m6rz"
    "N5StDXN7cnYkYJdELNsLeGYio/nglK5Syyv0bcMLSuaLRyYeFMguIbIO9ixqu3UXoT9WWZb6oY8JCqXYhL2Ky0uk32qRU7bUfJt0"
    "MdJ/O0IFOTNrqErNbWLo3Fn3Ibrmt1CBD13j7mia8ujtKam2413YJZWN3d8VJSbT013/y91rf+2PKqZD+zwcWEy/dbyRCu8oFIwm"
    "xCNMOG1kWuMMgr+xoEcfYxIePWPGzfq6MJRGLyd0Z8L0bo7Hu7n7+vtwuo4f/QnGj8KfwwT3+kJ8CAwC21/poUnY1HjxgY6J1oYA"
    "5h1GAxExbzAjsKu1XUAK/GJP9LKY1E+lu7ZQxisqESK1j9te4WGKQiXk3O5Jr9EwSOs5Mljx4W/3oBKxsswv8xvKShmbM/GSyAap"
    "ns35FQPFpKGfcKXdnErVTV5IeZ6i4nWkznUR1ZlZnlCh/6fC9iQaHDRV5SJpLunCXZTq+2ohrqwtHpPv52eUgHYBaqqaOtwq13Qh"
    "2jy0AIo1r6UsXeq6KSIccVnz8swtRiesUziyDNJBx/SwTDYSI5yW7tMHZ+w+Ru5/IkABpmlZOr2IbkfPZ98But2xY+s87IA6ckAX"
    "jAGtPOwBVY0BtfuNaAaH5CRV9SOarr5jk+8sAgy9fUPLUWC4nLN3Hc6Ng0r0ZI3xcUROohoE0DEmDIOmd99MckOyx7V+7DExyDV5"
    "eeaHpWYWw5WwZk8EgHfthwDCMDRjXVpJZa2J8cjlcg0nYq1lzFZ3diiGGume5KPpHkWHywnaAdsCmkboWl/hLcghFiowl8rcVFEI"
    "ClBOYm5dUYg0SpnB6pgUh6/2A8NpfT2kQbrsjntBdPHT3J4DUssJsmLsofgtYgrjMl9MZ51qS0FmwQAnigB0iFmTyAhWDPlsCEhZ"
    "5T0JDQ9z7cf4Y5iMiD0mu7NlpUxBnCc2d1tDGqfQHYMZWDYYTfXmfVlNE+d7u458vy9wa/zMwjZWWh2JdbS985cPGKAiA9OfId/J"
    "awr3jUFNhQpZqKU5G2wsq8r+WLHePMVw4sqPyFSoFoTOd3w5WBrpuyBLQzGSQ9xCwk3PdObGtChsZey/xvpVOwXdmyLMAuo+XCqi"
    "Cs0BiX6xIxVErD45Hfp1J19yhrjTKJ0LXklDXl9L6vrKpw8w0SFl1e11iZibaygKaGRbYBKTYdyDrRSLbj8v/Es6Apyk7Kz4jdH9"
    "v+rKZ1PQIRdmhcjQV7gR3dvchIa0Xl2XeDiiacMyTG4WZh8upXqQJG8aeuuPhiWFppyZ4rmgoGWpdGVQ7LlzZ46e/eHJc+eUlx+m"
    "Vy37AfzF28Ofz/BX2Kcdf8EtFCzpiGcVjV/IDaAbz/F8tqqlKp8LsmRBcclFw3RECtCxcMYFglD3Ku45hFPkjKZNd0kWyjbhqEUJ"
    "ApvOI+PjwL1KvWmTW/Lrbm6pFDTjVTlNuK9i3XtyUPeMDp2bL3moKLVlPuR4dU+nVReLlMC6+fvIiGqjihi2XrOpVa69k2jnB1XM"
    "HS2TEauGmgMawimJGsJMtpjUOK29eDZwY0y4RcwuxwNExlVyW7eA+LwhzH87HwXdj1OMPbl7zgEfx3EXjcV66KGCbwl+A36HivCm"
    "UgNvlyIPZy1qBRfnkGxHz1Huujn5uBB9dFyXNLUF/hOlfI4PJDbtz7joSuuETsCpwCmMrO6XS3U58XNZS2bM2NYNZWS3eh3h+zZf"
    "MSMJJAT2Fr3xpQ5RbVGQujMyMRntRzxPk9IJNRGLjfMA60qOlK5TDXzykQ2AVw6Jr6n5S3mg6JOqt9l6bqlWIoumiGEpWmkRK7Gw"
    "q0vWWJ2mjpxdrHxUC4XfFK2+wTZGZYiNUc+hZmrMSlZs7fMFewxG1GhXi+f/6fwYfSJECn72r+4j+UdoRscFxairzYSEwJnDl7W4"
    "cwfdA58eHc3itnM61az0pKZTHe0naRdBu42Fs4aQoDdJT/6hBGXckvtC2KiT2aUia64xeTIFC8dsb37IATDJ+429haSTqdiqaHXQ"
    "+gmnDTa53EBPVAtwRlLGgVeA3+J/c63AbRfVpxwfz7yOs/Gjanb1cUqPrqW1bha0ijGNNZ810b+RpmxrbW3EzdFOpU8IzjESaim3"
    "00MY5rzUxKtpoiUUzVR9U5zE2WFduGgbJ4r3rq0CO9Nivvru65ciFFPNOh4ZJ5DzNgMyY1JqacXaf56ftB4Z1TRKdVNIDIXsYSW7"
    "l5K7p8ecDjOhRNf7T2hs4k77S25w2gc2UEtL22O+qPZ9z1e/UD5NWIlPWjNH1xNlFuQLqmgdBjZbBFJTHradL66IAFSQ+QUo6R0M"
    "q88nisaUtSmBnD9Rh+qhn6cBoE2+j9pKEdEo1k5kOYv8TYwrIuYPIrcUUWex2YRXJM5O5sRyqw58Y5CJHZyhthT3q5d1UPzMTkMp"
    "gZciCavY/0IoEhzyj6uFGSvXaoVoHIe/bfE3bIjv4m8ovlqzzrnFwup33VIlZam0xcn0IbHNyFxQMwHKtA43Yx1mrsg55tbr1LKD"
    "uGyq+Whv9LimtI1hMIxQvJmDX2GvLxhOpkJr2ZW0PSg0c2XsPPwL1MSrzBajjzPjs8jY1QuBiGpeW6NPbsULgVcU32CdLMcrQIMt"
    "EKLxLj7009zMf+QorMheW5uxLPLiz4X+KaQJx0rA/iMw0I81lb2HgHJ1CiynvZY93ZwJZvHlSCf1BezXd7iuMcvMQXJFAgCiMEjT"
    "/csorjwOP0czICTT/sGFMwOVunDCjLNG7G8kgtfNUxe7RhS1GitFaATIoufaod8CSalVqhIYOExX8gzBfEu6rMvVEQH0B6X4zfRL"
    "S/t4Vh+iuFC1oXJ0dtpQ+0dnP/hYuQ+GF0OPG1NQ4C4FDjUDMm1HTM4zVYo6U4iHIAYYMVlIsuAlAiKJjhzaNQueFpuLvzcR18nr"
    "TkJx3wkxcghOi4bxxQYvoVGElz04VqOjAiDMSwKEpSMlsj7tKZAI0gFtYq7h/bnPGM5Rbw3NQ4W78X0d7KaZ9EryEJ9EiZVeKsqN"
    "AiZKZ8wv3uECSmtKYJopOwT4dPhJUuXP2XGwNzfxyxSw/VnDjjJ8UsS0uOkeCbiiQOHBkESm6tU/jlyN0Lw2WTCOTTRJ5F4MX2d/"
    "xj3WVsVY5FjMkWZPENrWOilavZ4mQDwhWj+86L6E29PTcq7Pdh0sGzN5pjiUpMpwEV7WP9yzxD8+p1w8xYURnQsQ60iCp8eG+wYu"
    "mtKw8HnowwD3YsC/tseJ0Xu+AxK958epvaef+vS+/+URH9W2dBB72AOTPHNyYcQP6UsjWVaNWPVgXSXjPIRVLGWeNq7oUkiU5uof"
    "v5e/j6KUmjYhT2nTRqLWSJ+Ji6kK2UGph/SlT6AeDEERE1eitwRokDjgmPgE4/x/h2npEMvpMkbzbG5IUxnnU5IpbMywm4ewrcwZ"
    "Sm4sJYwOmCFjc/XaVjhKdHp/RaRO2biMcNbCoPBJekbfQXFQMS3oYGiWeORTkk3nNdV2tIB9EJmhZLjQdiweRJMwBdYt23ooQmT7"
    "q8/f3n3/IwJK3MAYJcTp2iLbqR5hc3Pn8z/cv/4lKm9/TkkKzJR3uljBoD0x+UMRHdmfyxjitHEzAgrrE+6T5gSMTq0iq0A8mVIa"
    "BIew+SqEcLk6N1Tutmi+KQxRRxOTeBIxZfi/o62DrA6BvRqzF5C+9Nvj40odKe0HqRrrSHPvQF2Tw+nsBYPu9GpZNHmqsLrgriAP"
    "EgalFcZcuODP8YeWX6/nxwlIgqoCfrqFxgl3uVzPo90JOGenJrAKAlfgUiDO6PegCotCFF3EqFAmDiqA4g75fbvNyrRb54fz9ZL8"
    "HT8+ttheQfDh5VrADxfbc/lV6SneKsHxYOMHyPYIpgMdaLtRpyqB13Hxabfr/KRZUIgIpxDuJwWYyy3QLyA6V9zlp+az1pol14at"
    "BfyzDHd1bWE80B+7YxMYhzBVpuZGRrKncqhkOpWD+RwdpT8RHn+w2ATJ72fcNWlfiaSpc7qhbCE3feKU0yyQ6ZHaFTAZY9DNMfEI"
    "Nc5NuBOoR6OjWfpbaDqncriwvBdO5XDlCnKSTmHSQ/kLLiP6LVM/hdsyVLMQwH6ZLoMUldjg+JPq40+aMWOeUnNTRyLoXwY5ToIs"
    "zPwse54B0JYPYY8ZZ+PA6gkpttrdURqofEZf7O55mMXoTRyFH+zj5VnqNfURJk8aCCfFrIVyYoIcbTOUPIVpJLRXeYrhLZpuemEV"
    "GUnajWhhzc+s1jt5aw59V9HUEqoQ+lkn9MMSHC6gGz9D14zY3OKMrxLmsjy8p3J4GpXdcOCEo5AeFpShMywo1Bk1WbDQw08UeqHO"
    "Sbtu2pRJ1Vfv/c4zjdsr5AQf5mlYxYlweJwaJrWcgOmy86hGMTHQ0KhDZLhAHRsdA0GGRkcDXCnxrYA/O2FuAaqnTBx+A04evQZn"
    "AXgCWko8FvIBdAip2ExzthAhKsdPUhmjk6BahrDH2gwI/NHRuax6pIXMs19v5lAGSAEapxxeIjxYcpjB6Gja/ghKZGrT4qq0BcZf"
    "aLkm5WxH4wfiSdOMGyzaydg9A+Y63t6BVpYbO5UjQh27qGAz0WMFUu3aquRqxSO4Gzg/rTrMYFsA2/gI16ogJWiQPJLvsdlNKnia"
    "GjJTEx+6ZNyUiv1D/5H9aa7SPofn3l0La4uNuTY8mFuDW3Ah9Fs/BZru2QcOeYzbFKK3K+2aIGw/7YW1rJU7ZyUf/j8HMMW7BqpU"
    "jUzb8vrQHC+ycA/pEHP424+/f+q7Ydj6ofvMIiqbT+XgLiv4jp/DOz1rnX5q+ozlqMO4CKJLqTLseWS4IXoWEg308aiIplDjDhNn"
    "/fjg9NMHz/gLaPOebmEZbiTnN1uBX4X9DeuI3HAph4/dChbxm/iZb0ykIaXCapft6wUEVczB1Qvj9fF0tGCw7hl3OVT+Hn6OQRvh"
    "aB0eHy/WsyU772VxMk7ggkNDtPBraxZCG2asMfkCojhg2/QzNa6/ZhGi9pV0ZDh8rTTnB2HyNeA1EdvdQJ3jqWpWsk07ybO5Pu7c"
    "iFFAe7Xw2pRaslSnN0snS1N4W9KbBG27c/UaOppdvGMiAmzfX3+VAuSRPbdijGCz8D30YGGnFYV/ZFYZC/K/Eg8qj1UZ0o3hoGki"
    "cCuLQIKyZaeCyP5jFT5Vbe9nLnqmINtSWPWA8UOzHjfuIHWFJ3xrBU55kc70Us1nFsjhlEbAsXV1tgJPNd1E9cK4uCA8YDIm52F1"
    "mBuAPsz68xnUXQJ36bZx6uiaWGzluE57LnBLC9SrnFcoj004/ONiUKhAS6KRyAMETirwfzQkhwvMw1amd3AQhfrYPL3S1QD1U1v0"
    "ONiB6hhjVFwFu29362MFfd60+ruSCNAzmCKnVNBq5/ll1lUGzs1lzx9Yld+6X935RAEj01JfSUuu9Ca+kX6ZdKPKEHklw/7Z6LPf"
    "PU/ZR/IlvJLSzodDDiCSs/GL0Y2UT7uH3I7uaIXe5y5zSrOGfl5et2xYkcpKL7fkzi144RNueLR9AtZ/pZh8lGVrHuK7cPXEYc0i"
    "PO6scT7QLkcgWFDziGdLJj9UCEGooxWhp1hH3iPHH49uEwTWCuK+efWs5/i0Obyc134c3pFDLYn7z7gC+Dh51EH6gohkWnslas8f"
    "ky123XrbzYjaj3uBW0bWNWrCw4xPcGH+kMk5H6TyZMVfLac1X3HmEdobdmupckIcJnxmR6ctU8nAWSvb/HYdfpa9QQwju7tUo65L"
    "gtPtRm96+GZTvekhsqG0qwTdKogmWY0ZSHM1O5UqtZ7KoTSIQiv8QT/6uI+Zg6yH41epDmU/Tog/k4pN0zNfHFRPvzPxbffR0dHI"
    "Iw34KtHftqs5hbGFjCUqUXVXDKKcAHpGoPT24ly7HHhzrukICGwsS7fpPPoT6n6fROmhyS3pUG5h4UgoTqG89Yk3FdWmCvc/iJv4"
    "bKDn2M0ZqxKUqogOi4bVwG9Zs+pYwLwKZrtUqZzoAB0+BRIPIhBTdqAjTfRrwsfH3fkSMMQoCvJePBHGbIDNTk9wbewelF+FLnjz"
    "K6hEWHDd1jlaCvzWKp9j3Z5F4v85wTSWFkP/HJyMDpaB4x9torW1VYyuANFMzXqdrYtYLuhOQmsYeVvvlSmNYIOXh7L9seKrLxTU"
    "Q1EDm9a9YPlHNFmRXtPN8fRF2kwYfJiVkxqk2vcICuV2xHzgJfIb4WK9vsF+6HtCUfaBSNW5+crec1s7L1+KkoEnY06crzm4J2H9"
    "9aFF+yE+PG2npA8xuiqFDlShveAQDVXl5mWRCvaFS5TiRaXSklA7b8RGS7rLD5HX0nSUcdAgWR/V8JrQXX4OZV7avfqWhp6dgMt6"
    "yDZO3qicZJhir6z+qCS8EqfLWqoRPocmPAqhonDdE1Z8deTJDRJ5RfajD+fad/7w/u5Hf9LS8RrpblltC/x4PvKxSBpkGEpFVc0X"
    "jAidAkrieh238vfP/qvnnlnfmCuVFxZbWCZtmePb/yEv4d5b2zsvfbz36p2di1d7RS0PBzXeF1a89254HMgvhb/JLSHpccqeQGAZ"
    "Le3M+E9/2q6VAvenP+VRRCjl0K38hNGj2C5SRD/YVy5FERfJo5AF+sHPBEnNBSLQVDw2J0wGAn3G7BIhLUh5IUBJLOgNP8NmIZUg"
    "ZHZACixt6a9+QVGSW0YmjM3LPJmUc/oibwzE4hs/x2dm9/al3IVWNXN3/e3MxLfPsWFz78+bX336PD/XogoVBFTM1LV75eexrFnC"
    "1nPxl5Tf8CabSERHNl8R6VrQvvPiznvXhJEFpc8tHb1f7uJbHFVPz79IBfKO/P83roi3ZLbjXqhpKoSnZ34A/U5OnMZv9XPK2d9N"
    "dhSYFP0mU0xLLF6Ud3rE0vS8zGh6zeRj61fUanNGVoNOwAqmgJbd1nIbXTJ/ErnFzFSVuNdEQrPNzai5DUJNE9Fbms8Omn/foBW/"
    "GRW+eEdYD69e2/nidZXijPej6rYenyX3pBmIl2pSCzvCpHYiNBlqN3mqI5sZMoUnQsVhngjlJSf8wyKGE36Sn8VvEaT7f4CwceBQ"
    "FeWeLupI0oQZwRCTyNJFDvnHgk+vib9uDRNwxkZ1MswmwmVQ1yPx9W8x8rAWBCNNm1oojNL2RKQuPinwdN6rQknolabKo49tcp4D"
    "JjKLMWtYDgTiWp2MicT1t7HvkZRG0TJPgwxVzf4YhqVKoYVKfs75rXNoimSE6YVcw6+U6gWrjGBGKqJIqYvnsm6MpKoJatRhguT7"
    "NI/R6zTSdgdz5eCZsuT5oY2r/MpAAKoizI+lb85EEbIgSBcauWONAig5YQvXGGn07gaiou6+9rGGrvehiIGl8iTUq2aBy8bib38o"
    "jzhHqehvoNUI8/388cbus0jl79959t4L/018wAYjSsmS1BPiTN/E43nri50v31bIm0QKnhUZmMiDb+fqx2T9f0XzWoJaKI8Rej5s"
    "SGTCLRz7e5/KuwAJhTU76wQ0xV6z7DcoVtBiwNL71y7vbDHiqmbf50nbeFnL83VZtsgeF+eaLkL6KYDPJPmiwiXEObB0RafEJoAf"
    "YT/EfmQ4y5gfi2wY6Dmc+dgbyCXTYeL1Qupv/s5gEVrHzWpEZ81qREmtNlksqs2fn697tN1APhP5iK99xD81o192vvjdzu2PMY2R"
    "Og3fWwSBL49B3+TTbvqhK5dFwbxFl0+IaQDHwhjwiPAuTrs9thnYXAfCI2RznW2fcA47jziPOt90vjVLWr2wpwtiaHi/UNXAxYez"
    "XSckAKvI0rIYhTBivBSfe/R2Qsqxtjby47oWrpFd8TBO81jdb7v5Rt1Z8iquEaTNpeodhxQ2UTP1SFfhuPHsEc0CUDU2KLgyhYST"
    "SOK+2iJHfgrTzD/STUnp3sx51SaGAJNy9vw/nQeqmshhAaXKvnduwV3BrNxCB6S/UHHmk2mBW04jkT1+ZtlZMUvOldoYYbRUMJI7"
    "AEMrfaPZwvH+zotvMfawyIC+cQvj7wSe3ufIX7z4me4soyXUjQXZPfpN00grp6DgCWgjHJTEBZiS3ZDa4sd8v+6WmrACxpwUSvt8"
    "Gfi8hTZGT9CHKHPDFCZ+WMpP5Zbk5R/AO/Ad/3Sjqqj6JVumAeB6iGuLPYJrBZrzVdLhwtMY9mFmr6bKVFyL8FOfSvqpO/Ldc5VG"
    "hJybbZqZq6O0F4sSCm5RghzUClPa7yOLadj2bFWaUlal+WwKPhis+IRyhhxs8qrptRlQAeK9Z/mao4Z0SxVFq9ZkTg41ICs1qh9u"
    "Tqhy98VfUySrRJpf37CUi38XzQE8W0Aopnj6o4rRV0P8THkx5BdKZSNgRboNwsOfx1NGViVYFOaj0KHLQU03f0VmVEHw9+anmtA5"
    "DJGdEgtbnJLLWchODVjZ0dH0FUzkMBH+3CKTCb8DuzkftTUzKzeu7IjtTFGEldqPKr85bkndFv7PaB+PCmCql0mZiyWVxXSm7Elk"
    "2pwaAQ0gbzw6Gn2OrF7as7gvRB7tU8m03bau8y4zwoFgIqdw901FFroGIQhODsr3ValXM5GwkNTdpr1wsNanZEKZfNhEgCG2vndi"
    "bCAcZa32p4sWApZsXiY9rhkLIMMKmenjDH4CaemG4Ra5vnFv67e7v34ZdQiXXyO5Wk/fJR0Z81W3KDVxBGOObZoNStZV1qNqBklP"
    "agfSapbpU4itTB3K7ntvk1flNirhkPm6jpHcmx/DT/fX30RWcuPGUKMYHJ4bgylu1HtESy6TB62Epr8slbe6pWeq0AceNQGkGMRQ"
    "sJsmfmpTRwaddqr9QLEDExS7+rVAsafTQLFZEADWVuJiM14LPdBxsTswGaKCggls54QPExd7muNUYu2SI0y/Zr+3CCwovEzMK3LN"
    "/B4n/OkYZR8yTPR0MiCL25a8QicOGRbuHyZahSB/dedFlSIVVX3XP9399JqQMeF0vf3h3ruf0lHZBlFl58o1ZOpeukFJBlCAk2dM"
    "E0hNhDnkGqYxNmhVUWYKDripJwiNuAKlinGRB2WJhm2sWEnXzBPJOVylNmqr31BEM9IU28H3O4rom0h//B6CihBY7MVL1gPjbtPN"
    "FjSy5++uXzkgt/vaGu+/LoNPMIkDUfzeH94RQRNCN0qkaQOm+TqneUhzxKfUIZ+/Rm7or+vqsPPMqjBpEMCGVQQ2DLN2T+Dvqm3n"
    "e+lFh01Ma1EvfpPMVkGKylphMIRYahLLCuP5D22SaJ6OUwadKoAsEx2v6cKROuW6D5wW7LNYIJ5B3dB0wffQydMSEx9IG3yUVI6g"
    "8/89H39y6Ed+fRH22yH1ziFVIG1/EWbjaUK572eYmE7Hxe/ak9PCJKGPzDBITOORnB4OD7+v5YqX5vB+1uaUfo0EuXrqWtQHrIVx"
    "09y5Q6qvF6wYBQ9ySEf1aoHCGgGjPXEbaAmSmJly4iNxOFXdS/LStMCuIemYDCkgMqfIv4r+yQPLDkAUuDDtMLsO0ySlT7qFaGgG"
    "+H09qVsIh4DvjIA7Baey2P+MTjk1LHVhIA8zTGInLRNeIZOWLI8SvyL23gdp6qYrQPt2t/9MkVU3Zfjd5bSIn/SURNT2IzQNGqdi"
    "Rp5dlelrryYTRPWIwBofnzjH3RXHG0TTq4zcndoIpWO/c//Kf6dlsOrT80cH9LxH9xB7T/Zq/4MTgOnCOD4UWB+uB4gkf/vlO5ne"
    "0Hyf6NlyMo9yGsYPlcxvpUFyo8YB1h9dbVGfLvkJDktOBH3xpB3OCzz12GQ9yAQgQuj6Otc7kY/jyw+3GlF18f6q1E6Y94dcbtiI"
    "sPPxJkZS4lR8QP4Hn4gQM2H9fFGl8DEKbGyJ3A2CAL0oo9U27n34Hiemp2w+m5rbz4YMyttmw9/O9nUVGygi748VHiBnHsttDydP"
    "nuQAUUi8f+1X99989eulysNQEk6UN0GJ8r41bubJa1Kwybm2WzburdXoeWFsOlW2sDJ7W69YfSOMid3m+MbdNzZhOF9vLKijIBhA"
    "lfbvkfHEcLhQ2oCiX/Y7pME4u30ASfU41Z2ty3Sq0d8GZmQP9cxbwrLNue8Yw41sR5E8gr7/f0YuefNT8qJHGw/QD6iBdImkANl6"
    "BagGyDUEV/MC7fSr9K/K73VFBYaKpGccx5lIKYcwqKRl2Pvzy7u/fpuQYl9idmS2H8iHhTnI4kjUDxXtI1hq6yHOwKr4QXiOfHYx"
    "+qXV0gVNXvS0MoXpXlKnDsKIfuFIMhhX8DrsXhYc0e7MgK1//gvQd1qEm3Kt4iAeCVqh4QzwJP/v4KaUmiV9JuFrfeVnbnzyxOPe"
    "8wXj33v1DkYzowvGe+Qs8xnBYfyRkVOOPXUS/uWbkEJYXqTQ5wgyY+/Zd0DORzWWUGwlZ3CAz5DSiHGwdYbwuUBMIXwu4ftDeUc/"
    "uvcpQUGY9w+dAgmja8Sn3IpJoXBLPOmuNP3QxSP0+tbO5+/ufHY1i+3Z6BFJUi/Ju1tKD+cMjWKc8I+zcO6QFfmSxvDG7rWf73z0"
    "OvRy4t47VwiRHiO8t/jxzsdX+QPIZDfubb2y89KL8C/26sqnlAdJKDXQZWX9yjEQ5UEICNvo0n6yGbqB2w7Zqebeez9HOvL5uzjG"
    "V/8KTWmr+xqtq4C21/oWJWfUM4SAiFQK3JIQAMs+iCHtlluvH8NNhJHNTLJLxq4rZ03SPPQ+GD4nG0o+5Wy2Vi+ihS1hbNSkxiih"
    "YZS1qufJVj5qsUygcTc1mM+Jfz2nu2GYTmrWPuH/U9QWM+nmbOU5R8t1nWApnr+7+RGBo6CXgKmO2ZbJC8QVwxsMQbWjW4xZY3Ri"
    "wksq8jreouODd1APRlG4RzI+ww3m4nZf+IPCcMV8kvpOTtvrqHH/3ad7b3xO4AxXzlEKyTu7l3+/89kWjnL95bvrv4yc/y7eYQr0"
    "1R0cGZr3Jer37hWg8+/wucdMuVc24HNGz9wqj5FIPLvz3KX7v0Fj8d5rH+5c/Quvsv4CWfh4glCbxfP1rJ4jUkdaubnz+a9oLm+R"
    "d+DlCAnitb+gzVBM/LaCKyGF47MpKSNScwo1FoSugj7ET0wia0/SZhzTxPdIOZSWtiRNa2L0bCnSbS8hS3eK7AD5R8djtMLQlsT8"
    "V6Tv0WVFIllZT5cTp3VLKOuX0jXmsSwsEs2PXHYPP5q4jjV3E2NUQTQqNKvHG8dnae1rtXd44mc6ztFZe4hMPUcpFc3XSCOznPHK"
    "+IsBLIjkf/MVoVU1VUdik8TVsYkZiuxIIt9MVe/mYLXKPqxYRr9Y67SE6iNycGBHr2HVSDRuPQtMX0zDfh3pYxjHGyg6afGepV8/"
    "2Jmniw8gpDKHus/LxfCbt+JA5ZhNOg1WCwWYyJ82Ms1uSfSg6xRV0gvyR/DSm5v3rxO3gSbR1xOpohUan/TWQz89mc3ZzBa9j2wl"
    "qZPGTCnbjAZ7W+spfuUpBvo5qxHQfZvYIk4d2E/YOjPTszHP6g7tOPVrT8NaFU7gtN2bi5EjFvblf3TEV7tZ0Ue76OXa/mIzIdXJ"
    "570lEx4H7aBX7v/xTyQSG272e5d/D2IJcgFQZn3zqWkKSJcvwdUrXnpNc0/9uiFf7XAhProQ6MVK2vDoh0HjQyIltYyUMl319pKJ"
    "S8iurF9gMRHi9RCG47efomwCxoj8NiXCSBmS+CU5Jv3XtbUsfS0jIS1YpVbLsiPxfP2KQoY+lHkcoYoiiOirUmkootxi0Jps4N25"
    "fZvIFoaz7f7ixs77N3rNhCCErVKlAuT6lDsf5g8/MjCMyABpK9fjy02jQkfOOR8NegYk22p83Im1jhZUJAAVW3nn+eeQ4zaZfSXv"
    "Mn1kqyvaqm+v71z6+b2tD0xf7X/oDBTUDEQ4v+mbJzEx/No+ZoaHn/n7Z5czqXsH7xkGsN0nft3f1u+k1ngrcU1u722/s/fy87pq"
    "gHslXXdu0l79rRABNv989+JvMOiI+FuEn7sUqTewsAltycoMjBgEpkVo+1BpfoaAYHKVOVj6pym8uU0hUM9mcsenz00jWAz88v1S"
    "mQOjxO4QSdc4lOkNLfjI8FnEUMQIIu82XhcK/m77Cghuwt6BKsg31H0fO39RPFRasopUpDucc+nftb33519Dh6S2BoHqmBYKhgDV"
    "GbeYS0APzos3UIYU+c62jNxmyZwMHBy0LdNvaFwEuT9yt5odXTMc1wY8+45y9oqJK0qFg6bUL0lhBjfQxjdg79zIFDNkCPzSCJnt"
    "qVRBT8M0nYpnkF+/l05lSO57aJ7XZ60KuzvvV7FCBih5IrYfKNLVrUm7r/R5HIpVXimbbM18FYRo4ONEDknVJ33TSAFvOZrpFQnE"
    "t0qIZ22Xb8nwMfooKsO8ZKkeilYXTfwW5+eh9/hyFe/1wNymd0qVjnjlKH6S3f7dH/f+9LHV7evvAAOFSYXu1bxKBWZkmS4n6nA0"
    "SyM/rGZVQtPvVqNdTwjRZSGSarWiSaZcCippbKF5TmZ6Li3W0dT1vGzlZYeVlKzns/tRtrLWDO0VhreP8kuKbNAJE61y6TbCAwhc"
    "lD2YTCVyhCmKdHpTBB5GkZvN1PzxvZwV1Dq6Ycmrt+OHIXDTTIyLDRj0ihklf+n91FmMhF50bxJy0+JDa1b3kKDJeo8zN2FrF2LX"
    "7z9uYx0WWkgFNCsSU0Y76oAHNeSbCAMaIvJmmLfIwdz63+oye3kY5KNvbykUIxGMPRw18AWPb2h1nqlSG/3R6lOrI2IVH3NKl7Ec"
    "GuQfXHhPeuBghYvOBaq0a2d7T4QbCJNzmT6pOiv9hjvv+6maq/3bjGcqnmNlOhgkCoLAj9ygDdvKeXptreoWzyNY+dHjx5869mRm"
    "+thTZ89kOgdWzy53M3cvvkHKl7+iwySqvazM//1L5v/+LjN94kcnps589+kTp04ZfP5AAIVv90tZQh5lxwjPK92P3ELLwsXfksno"
    "jsBi7sNORG5q06WOnuykpWpf0ipn/iA9MVK9pENyudLZGFOUUWBhAVUnRYpAxAhM4UeypWNAW7N5rTQG20H5ucX2CkbHkouGSFmK"
    "5RCQCCSkqIRyL1ZFMwjTJMrN5jHCESuiDQq/WvgI39t4e/ejd+kB5m8SHSieP7BKQcmLzXBtbdymhDflUt0VcSs2wqXhWh9YdXPt"
    "cql5rtEe4T5n1YNDE+4j+Obj3rJbyU7YY1ab0NDwHUTGPIflirRlrLHTQVZ7ahNqGqLrCjhgTLroNPKhFqDsdTQkXIxZRLDe3DSM"
    "gmLxfujOZxnDLIgejNvOTN3xkjF8vlNKPCwXmkZwQKNwpJHzKmMNmUuZo2fWLOwt+ivS+yfm54Emc7SCR/UECJuH0MkFOHAz5Vnb"
    "oYKnSiv+YqgX58E0CqF8YXKksbZWX1trwJQGfr1OOB7QCRBM4Vf6NjYxOpqNWjBKOh5GVSG9TPQs2RT6W0JrIr3qD10E2Htqru0G"
    "HTc4Yi1aZuz/MoFtmqW45vroqOrO6KjR1yMF9UuRpiY/UsciX29wku9ezvnckWzDdrAryzk40NDdJo7ahqmvz6bMBI7bNwfXKCzD"
    "D8tKZ4Rhru0wa9FeaPktJxcAVWjlStWqZa+tlYyQp4pfXsTLIgnsBWwLtA1CMRxE0UVVOHAbfsftVx7670P/o3SqvS4S2rCWE7jz"
    "cFxkzFilYHJ9Ryac+UJDbgQ8XstwvFa6BSBkDQxdPZGV2xwTVK1bY8szE7Nj2RXKYYnQ5fYYfmqQU/QYFCYQ0SI/Y6BZLAM/NM9h"
    "uFkbfiJ2VHrEaXdkBt8RxcYsoCxIJhIJhBJ32uNZi9YBCPfoKIIKt0poFmvoJBd+QJIrY66XnCFYn4ofZnC847N9c1CkCq06NxBN"
    "IdQzgn3M8DT2r7eh11spGsMp9rg68rJUEdrsTbXF5GIfQHSMloZoMMMfQBfVc1gFuuccJHs2p6BqCfhHfTPZrULv4YglGm7eicdM"
    "MlG7b38oAvhQzpYIjiNAGUcq0LhOpOf5d0Xg5G8izHOpcGQpigpe0ufWlqiry/1fyi6Zt/Ta2pK8Zm1Vx4qqQ+K+LjlTcOCXxrJT"
    "0QIh8GufuZMbPIOExmmovczGRcnRAMt7EgH08+OGYqSEZC1KZGZkfU1zFN/+6vb6vQ+2rOFPSLZRpA7ll4vMheSRx7D3eWjasVMz"
    "k7L+GSsmtOIJahBfemC10QWhLvVYCK50H8dtJXFkHDoykQTDVlsiyswCDop0pW4vDRXjqlNurXzLGSF8mKbUh6QlxIGfdWlt5/mX"
    "eEpUmvtZTqNXV5WkNt/yWymRkoL7Sb8sBsX64i5u9SLLD0qOe0T99qa/fQRdbcBIGfvJW+ZmiVPQnvdbgqb2lAL12cf+4+2K3Rd3"
    "au/F0/UhorCQUgT1FuBOSMOfCAsHJzQA0VoqIw2yy3SOMEgJPB5x4GXE7Iz8eHBiFirPj08+EX5nHGGIpoE+QvWh7QA371dRnyif"
    "qFwF6pe1NXytOJ5vSkpbLxypQ4VHngglJY3vrj5qYZLkTvmIk1MKvNJBdxkWu+JWrLxqUdJD4VN7EdbrYz04UEhRqIb/TxlOYnhY"
    "qJoKI1GlODwYr0BH6uHoQUHI/TbinOFiyn3DF4Ij430O/lypUnXliNmMlg/onif3OYH0I3ByNDeBI//2b0Xr3/5tDEp3ncAUZv0U"
    "ySomU4WmTBUHaYHbVC5cX1nHw5ytmgDimYy4L3LI5GjAyBgjHQxLXhN2gmT47KJnChlhJH7UScrwDAnDS0gY6oWCUdKps4Qx6SvM"
    "iVKa2OOrsZaUCOIxf18yRZCIstQIXhqDc4HYNx2DWtYq8EOgsbT2MJcHbEY/zSO7UY2RsFKwYDntoJzvlJ1SPSREeXI2e+RRp+Z6"
    "1VoIn/pemXXjFq94fbJ6W5omiAR958nlKFLu6dHRGmyvYl9RRr87H8ZFKDV7WY+NaUS0RrKiL7bKNJsSwtt2U5ze/73FmimpnhUn"
    "fKnMj+sVSqAeEX00/Uh7ifAjSjXzuLmO5y4Z2S7DKm4szeTDyAbU+ilPD0sXAVp3EhFVd1RKVeb3OIAp1ZAvzTpD6EGHJHH1OZPE"
    "fchuwIKTIsPSnE+KaxrSY/xZ0uznbiiQm90bH5JfwQd3N/6KAMrk7Iyh63/cQH8Mwcnus/tlv97eR/flHL9N5lQRqtLf9FWbC5sG"
    "3MkI7LoRZd5Nj7RoL3lhuaamQfqbKXffOKyo8s5RXhgcm8ZQUxPf3Nt6hQJLbpkGaYU/sD/3oqXHgVzqqTPd3ONPnTr11NPGxm1j"
    "imDTBacvUxYGpfJC0m84pSB6HFhde/iLVTfYG+eyWSNykFiSQRzHGVc7eOiPjrHKIG5dYnA/6d12BZ0KKbyWNbQRY7Fc7cEywFao"
    "74tleJ7Pk/K7HBKShSO1kXIrT9w3+GDtvv4u+XpIPEbV5wu9+kyre3g/vTbbstTNwO+XOobtN2YLQFRL0WehIDDYNQT57NVP4BP3"
    "sWkkfNAsXxgqncFAH2f2cKbe/mDRUxvl6aIR+MW4l+RC98HdTTJgoM39AzK7ExAOe/VjMIEK7bt177dXUZhHuVfLEU94Qg9QOddG"
    "pONZGYKm6uxRoXA76lethPTUAnbUGp1tpbtutzBizRIii8GalnTW9Fwraw8hH8j07xasXK3UBsYK/gWmihZlylVr4ubor7GDpto9"
    "d1DT3R8//xKjody9eItsZrcYycKKDbAcDbBJvHdumjVua2sjxJ8k0yiGhK82EHLLb1EqSeFH2Zor6VbGGZ0rDzQFWLMik72D4B5y"
    "9gynXgiKIPsHnCVmGEWt3wqJpw36KGeJNGMIvMLTIp8oCfHCUakctorkdPuK3FfXUxMUm7lbb6ciYA/yoHjBGsuyUvtENjD14fVc"
    "OySVeD3XoBLwV6nFA6EWDzS1eBCpxfF/be7rxQHKD2prXNmkxQasVfruv4Uks2L1gEM4ASIQsa9razBcMdA0azbyYJ//yiKbUj26"
    "Igdo1YKhVNhiQh1ZWloG0QA0SKNtyXSwaGGHwUTwfsLcMd6vs34LeXTFYA2ByPD3z96U9HEby2sQDAo7gNEWklAJ0YbWMvJGIEvD"
    "qMQWzAs06oi+IWSUEB/346WVaeQsde9XzvshkGJxziKejdGy9SwvZoqAKLUoyPDx/Lk0m6vwb77etScRwcWcq7vrV2BP4zl6ScOX"
    "4gRbl6wxj/fimJXpP1V0lXwzyuBY9RS0tYfAMZ4C5/lWDJyHNwipNYNegU6BpixBDYlIrTGSsrtGR4/DNRHfan12WuzSi4mKyP6E"
    "WVt2T1sBcQ5Wu45XALrjL+CZQArkVkAorJBJwcdfgNLIn4DC0vMSPkc1vfyhHZTlV6dcMM7o2povVPultbU6NNtagdOGH0O/4uNf"
    "nHCp9Y8OLEwfYecUhjvx59WaMuJ95sCq1z10YBW2Gma8g551D6yWmA4YWUEI3gFIQ4ndCXwucnfzBvorXvwMUxySA8FQNxNImP1u"
    "pQGkfHgNdrmvaKnr5pj+9iveSHMQSivYSglXrngm7Q+klpm0xQFri50wVwKOpIM5xgzWQD7nNSp+H17Nzdd9P8iqXxDS/RsT4+OH"
    "zLJ2fnzgglhkwk1nuNotr2mEctIDwyuN3F6cE1FXAreuwbjmWn4LIX+51ieazmqrHMLxtp3Asf7FwpvjmUUXr8Fx+8iEMItuA/1/"
    "Ee8h/deDEzZfOnjjGAzcYi8GzuDcOFEwJvDG3ATyhMfsjn7hiB/ZHX3DWAkUgIiEXlT/Hdt82o5baiUTiclyKVqxJzKK5py4xVCo"
    "kQuxEXa9bfJZnFPiN9KB+bXo7tQCka2BXlm9pTjpGx05JD9IqKTJ1/fnzh2riRlMPUXtYSMsNts1bz7sPX8ekW9YlvMmJuwVIFfi"
    "fPP118NyeYk8VT+kCRVwKkqxk3oVno+wmdetgVOSmOTYhOz84vrOW7+hUI8vUTwH2Z+nooJTAZuWciYAE9hzUpJzUldTcmD1RNaX"
    "trl8BqeELVbmIKA5XzSH2bwjy3/VteP7euB+7oOw2wtWTIbV/8M3tNpz//jppfTDPlCQyZibuDWFgZ4e8FfIJXnNDOcvLOqPcy03"
    "aHhtdB2l5OCck8QqDiY2vdVmcvr/sHP11tef/p+1nGTU7ytcuzbx+b6janpuxSpm9VGlQFH1G9PFa2jfE+4YsTFhpNOxWuA33Myh"
    "zIlK1c0QkSUwpouX5D7cykwc/tfcOCYAo9/Xr4jaKSJRTlc8wgkjEjHU9AabF6X94ZZAdjZQVcQWhL0wbueFsADy4YBR37/23/c+"
    "2JIIa0IHDdcynrFL7+/dvLX79k0ORRC6xYt35JAEao5EUlMZeBjDTYaaJSK2zI4OXBVWWeEC/I6UVZ8QJkmvpbrJOV6i4HJt18UX"
    "iWNCnx3YxYGnYQBq9/8uSUJd0zl0VqwMdxHqjARO9foVacWhLDoXfy8YCTSivMumFNjDKqkOvndb5zI4dNBI1ialR8oaGalHMz2C"
    "/aUr+xNHz5xg7sGU9K+r6MFEWCWNIH77ignXQAewcb2VjNlj4zwm2rjBWEcwRbsvwGLf/PeTpzHG8Q+v0Vq8EUHfYNjnfzJeGOOC"
    "GenLNm5qRkCdQ9tWi7vzGbzy0t4nb9zd+EUMvcABEUNu2D6cT3K9me8ppfE9pX8A3yM5FO54dH0OeXuWxO1Z0m/P0oDbs66uSLxG"
    "8yCNEnOEEqhKhy1KZMMCZTsLv48YDb5TQh+B4owRc+rg37ESjGE2Ty6/yQy6c6VmE70HDEFWPgx6KKyDolWqu0FoRbgkw+muQ9J8"
    "sK43knMqD+B+Tw9SPeUlKvBCbp7siU+6KwIBWDiEaD8UNN13tTCdwyjo5afmyRPf6RQaiOclU7RXbUd+qY5N2Lb4DOLbzPisc7TQ"
    "KWJ+c+WGDfJdgHoyygp+tF7PWv9MBulMru22Zwh0HvNMzVr2LOvGzxSOnKH8bG0Xc57XUUveEWrxo6OjXil7lLx/417bUdwWrSe2"
    "wXFLOpGGBxm2hys/7nrhRNbNzT3DmtAlNzgGLWdlMhsQCkdGsnBLUxzHyln5YQoPBOqonFLhODqsOOXCYpn2n1MpLHsizfk8Znfn"
    "dlr4UYmjImm1wGRCl3kg/hU1yRVjCeyRQoEg6w1Xnk6hGmanbZhyWB0977YQYE/CHYSZtzFeyxod/UEzi3U49AzE1ZUAGqcv0Gd7"
    "cr4wj44gwJ/B/IoWzpBvDhwsLfX6SUSbOyr36dnCcVdWY7OScfIMmoSyZ+21tTOI1pk960CnnDO5Kn62+aY+aWO6nREo4P3MtVdh"
    "flsC68dttELKqx3kp53Ay1dVOELX7ATusjPYLizCbK7tB2H2ydCOOsYNnuR1qLuFs5N1oLbwoe6qDDVu4cgJ+Jd7by6/1yzXFytu"
    "O1u3bTRQ0uqnVQCvLzYxWb0qNhUvNl+2Uc0J7Y/AQ+HhPToqhwytUzIBygN/kgbeyZ90OoS+0Ml16kcK48WTKrlFp6wengrEmtr5"
    "7wUz1X/5XiC9eZ324pwshtmYzEiF4rQ0SFjOPOYgO+tU23nMHNVV56JRaHjZedtZLjTkOGqe5o3dkB+XCiusswoQzCW7THqqFTs/"
    "7kxFr04Xjkwrn275Zi32u5hH+fNioaX9PJK1aG+goDRtI9o3nCdc22MoWsFu8tXVNFK2V918tF2mcc+KObCjx1V8bBwdFIRxM4yO"
    "wrVGO7vKewNoFWwtaGl8cg76uJBxu3E35X3Sn2Ec0OZiFsXeOr7IdcKP5aMm85Lk25Ke4SzDw+/LjnXIclb6enbDldgK0BsUJmgZ"
    "yPJKkXNNors63IE/cwM/RX0rlYJLUPUSKgXjMcIpo8m0y8KsOnesZeKzm4rJNHZ0apj6F6UPwdmmUT8nGLn34Us9Kq8NyD0wX+8X"
    "PhoP0/RIv3gwitY83N0Palpmfk6MAr1mU/1NiBM2PdaUDGLIKz+oZy84FKSXqipm11+RSEgirTj76CGlNtxPF0W2IvS2YmM0PHzz"
    "N0JuxF3wR8LeIAlz42bCsZjHM97bW6VeL7XabnpqpJ7L23ZLQbnWU5/OvyZTBdEMPCMTfDOCogGGKO3td5Izsfve23t/etdyMOHy"
    "Mb/RwuxneQ57lW6Nc8+YSE34pBBDx1be1LqHlrSTzbGdzDkWt7TJHwWkiGaBiSP4/u35lzNf3XmRbbQxC+799f++984V4U3Iflts"
    "mlUdkS6fc6bP54OCWs09hde17kJH97cxSwcwuScXm07xpIsoAScr/vpIW9SpqXinplI7NdW7Uyp1mejUoC07V3er/W6RxBDizpIZ"
    "ykgc5fRm02JqENDguqoiJC2WwfgBaxN21ITJ6gGra+JtZkzzA1YkMiZHA9176099wvb9VqnsAdub+1YaMleydtlNPcVzCuJ9vPZ/"
    "dZDyHHfLfkBqWPQvhtsnrAEHVK1ZZq6dKDe09UBTwMycZZwkpOXXPt77r3UDrSzVwOvpBllL3QBpgHg3BEqazKsnEO8laJrhklrr"
    "QDN+vZ1fdIgP+yFFhjVLHfwQ9AkjotLkz+wo/i4RWBZT8LeiD6gKgeOtsbDFvoAjBMfIOdnwI0LQCglBIk5YBw92yhby/fCbp7H+"
    "KVsoMZpOzUpi0idKNXvdc3OL8FScu55L2GkakVc4Ahk7ZiDDJ+MuzOSCPeOzaCqjctjAMD4SejnCVzCxINKzSF9Jyx6GSj3XGuO1"
    "kZ5k87jDQIRjyQUmKe85x4/+ZDrvO2eO58sOiBJPgtAKnFD+QheIPMoX8t0n6nALlv2Ik1B+fL/7b0KXRph241wQbxDBem8+a+Cp"
    "bb6CuSTQFz2pQNfbFK2kBbEmBq61juBJAlztc5EorkcuIZG0IhUfTsbRKT3YfCcLM+hqM9jkGQxxBgN9ButdW/lMLTh+wc0FTgn1"
    "IqSQAQEc1lfKkNXCkWpcxKyklYmLqfMpahCSHfld2YMO6kJ8ITFOzpMWpJPjztpra/OkDJEPnNUSdH9m1ul4FAuIrl0dchiD3/NU"
    "Ck7IPOkwVCU5eId1BlW7m+hLFWRbKq91Q70Jzcg3I31ULpebNzUo2arTiZSHRwtcYdV2zoiPHeUe3PKyR6nDZygP8dpauwkPoD3n"
    "DInLGGKJInqsn61oumTlKLyHkUJ8JFhbo6kYKRQC28bwNA/1SqpPYkZsVAc2NB1K1QnzR2EjNYyxVHNhrn2wg//aCmqjUkZMhhVa"
    "2GnoBBNoWH3ZJ86tTOqpIxPOktQ1TOma0trww+vQAsjk0uoB9/OocwZhhXH6UBt3hkkCCtlyGlCjNFXg/VEzbV0pscGVtgsyM5UW"
    "VQBBxOi30Ec2X5eITmQ7nGRaZLLavfJzaTh8HVW/iTp6GQGZ81ceDWNV1JrRMonFtNWe8qWqqzq5xGPRFI4jzdHRJZgJ2zkJ4y1F"
    "J/OUWzhyyo2f37OFM9g9LEc5srGUh+aAdg1JBJ1B1d4pV8xs3Y02kbPoFpblLu+EBb3Pk5QSfNB0Q3nLgW5YqKy2nLP4CTsA1HvR"
    "hS/t8KA1hrmvQ1vc6FQwf1THGTABCOLRtiNnxEVwIpsVazIC/5dyFVID0qMxSjpN/tKd0B47n0AP3jqweqYohfe8JvN20eZjyM5B"
    "GzblCK2DDT/AVB73l5p5nN3VLE8j2u1PYNIRa20tepKhFNvwvRVQnPNx9lfA/PRalSkRvWlxhzW3Y6VHMwiwgL5B6Dr30Ql1lzVC"
    "8z7lOqeaEZr36dRYtlPNvr6ndM6iM5D52/qnGWSJTkDteBCgAexjbH+eUhhSdp+6W4jdEYFNaKIN1HhymABm6XytibEisVvU55Nq"
    "Ct3AWUXGK0+9RWd0t5+Dd5gStvkTkOFD0iKLOn/cQhkkv+g6es2U0BEqpyOBm6budVyLvrfKIWNeydGh7lBvlRSiqEzkwkxu2kRu"
    "gIjKq6LL1FUaWY4WjuinONsCDi0AdqyK+RYUdTjKxMHudsUdC7fjkiRMi6SpblbwihDUQtyv0QhQJd23VBPVPpidropmh3mjgNtO"
    "caqcLixpLtBLCB0QrGSXmkkgn2FECDqkMenBzXXK3WFU0Z3aUBrrry8xSDoHPUP7h62LEPIZ1FF+WCcAfYj1WR5pDhGCVp438myc"
    "Z48DhWmc1OEdWJ0uRgpPRYO1J4oYn49rMZeckWk7lQ5CnUIta+gzZUxde3GuDzRJ3TKnFkr3xYFsD5P4UChNklSFWWX1/Eet+PNK"
    "/4CScqv6tZ2YKzKbbFG3kFfF9b/IfPugmK+mv1TP0HkfgFUlQjT6bngjsP5YdhEXoIrIZQYVTJ2QZmCaLcin2nKermepAjuK3slf"
    "SB3vheHHO3Cou79/Zz/jvNAf0cgcWguJZJuApd8mZ5bNuxs3aKBkdGyUltEpARjD0KvbNudZ1QbfMEB5ey0oadSSfv3mIN/+vUj3"
    "GjveG7eEBo6QEHDhZofXbqDcJrtYG1rX4UlD8wh/OltES9/Or94xNLSi2FlVbKqoE8NbcdE+pmdICOYtEMwDEMyriBm7KkMlFxL+"
    "KA763cPuSlxpIGdYjlc43c420X8izFWC0pILYsXISJibPnEKvYrgD2nR4MZ04W6Wj8hKi/hg7LFQQKd7NGyXW0UV2tMqHMEHMy14"
    "b1Ys+AWFDdES9nMEvlSluk6LdDfUb/rXKRc8uq1xSwwDPP4Ecj0JhaVSIEfR8PAuqjIo5Snj4VJDlcBv7aehwACUStfU9m5sn6My"
    "z4WpcI4aK1Fj/Rrv2+IIoRW5bbx9JW88Ouqh44pQpCt+MG2utdAJsW8T/Sql90w8XYA9UuIEmurZMy0u2cwf5lujAtt12pkvnMjW"
    "OSI12yrPeLO4pe2xrBhB8TxDuIqvXT1pAP/yDBQlpxcCY6U30bxyLhTvCoP8gdWn3Ogno3CrLkpq8VvUJP7U3Xnr16osgb/Kinff"
    "Xod1Y9giWb0ooFXP8rV8Q5rCsXb+JSo5X8fjN69c9c7/E2cDzGfOj9FzcSJPZFsz47N25Om3wdG6Y9mKliwEnZ+EPzTh15z/J1Qc"
    "ok/xzZgUy8zTeR3PMuH75huIqV4pQjyVoJ+JV0LNG44pD0kFTXYH0WrLhjG/OceoP8lDoY0giDkWwglmvYDnyJlF/scSRhOElbMI"
    "GieMKTPMjtlS12BJ1UKAPL1XEd+qVp7pZU9NAzOw84rnhAX7LiybQ5VwG5oCoIXyfysu/rdM6b+VFP5/4Ga1ClPE/x+wpOj1ZSIa"
    "BsdKGHT65A2SBjQrjdjL/eBSqjEZQfCtdSe6AY270SO4alegXZ1shv6PPHcpuzoHu3oBoQ1KAaGasMdH9ED5WzULymcS2LMTdRc/"
    "PrZyspIVxibbCHpTSAWuhqaLch5csq6DeANQy2PokQXE9BjBc/2QILPgcu7ZUNmlJUWvxwV1N9eLHrrBEoDXQYp+bbsM9XVw4nA+"
    "yAUIcAUf6ULv0eikz8WOeMWmmCJMRTRWIB6u7Hr1rChx0LPz6Mk1H34noD9jE4dhU+lvHdTeUmUO8ku2tiQ1tCOgrc+NbH1NaesL"
    "FQcTFNLh02g8BpTa2loc17hU6IeE9iji90mfO3ZRi2DXQr9arbtZAhEv2c5IyawZuJCeK1gZYgXntRWssH9eA+hvmWfZ0Za0oi+p"
    "nZclWlI5PumlOPHyVlMqFgVlmUF3wV6bYFlsgjIv2qNwaJd5qecP4pcWIjxnG8r7F9qg6xVxNtP60CEgXKMXjZQZ7nggu7aIfEZ1"
    "V/3Qp8rtROXoonwaSBjULGP71TLj/vtO4XDaK1Ok3kl/ZSwGqGfsmoOHu5NJTL+gJ8Z4T4g/DjQbV3uT78K1taxfCFzobzs82vQa"
    "ZPoHNqzhisuyAJcCQukhXS7Mw5P5XDkM6kD00WqVgOwmAQaoDO2p0lw7O5+ruPWw9BP7SPzRj+E+6HNA4Fwbk1SQNTnziTsEOldJ"
    "dq5UD8WnhhuWxEfh83w0CPwlrBe4R/PhD3EXWmmDI/cdR+ZnchjxwflnearW1hZyDb9CUVvJLjr17Ly8CqPGiwcn8hN2hGbupcCY"
    "8xwAHXBWW7B7vY6bHxnvYphIsuxSzSXMPK3oBOqwKHYwpXxA0IoUxNAHSB26zbDoFYZZXPXSAdRVT7FzqSVk/1SXUkul9Sq1oNax"
    "ruaz76nT4GsUu1Twi/GDyZRqEn7gvj+2kl1FmpP3vpEtFUu9iFVuicEsD+cfGR+3nTm3Vup4CFDQbviYva4brWhvzyu4a4S7CH2K"
    "wxAP1DM2OzraFdEkhd2HOb2VyvH23z+79LfnX6ZkHZ8lXCHrGJ2RbklBI8spq687BhJZ6fUiPmvaC3m94VWHHL++MA0PzjeZyHFl"
    "UrzIywU/ssR7hiV+Hm2xprVvGOBavhIk+ws0HpUgSb23R3pvqWv2hF4Z8VE2bu9t3dm5/FoMpZaHNK/ttVZhfnSUTei9rkcR0ULX"
    "knanAX3whJMA3HlInHhnnvHFztQUWy1xORPfM69/mfhW+q5MdyAjq5QcZ18P7zIs7+hoCToJf1gBoFuMS+QnXp41VLbDcN0VMtbw"
    "wPX9Nuzup+tVqfR//05i97/Sc/f32/xJLVcDw7Ao/OpcVcHUunEVVwK/dyZ0AgOxl0OzetzhrcEsHN3tLf1ub6i7fZnv9lMsnWYb"
    "Y2OwUyLOB9koC7i/ahVNLnh3rvALjYK2txpIFRoov0VvMg3WX+46S4UpDlGaSl550CWn//vOCPUS4YMsipa8ufOXDzSw1K3Iu1sm"
    "ZdM9hCznUfcRFQLkdqATeJTOBKVme94N7FxYc5tZ17dzjFNUKxyBhjidJnpBYTCnjCjFmjGeM5+xxmoGlFFEzFsplyMOhhfFWbad"
    "XiXqLqU8WulVAtV2S+J2baVfdvGGehbS2+pRiJvrdin6KrELaU3W1iTCVLB8KAxKK21LzCcI+gEI8vTMllNLLyKFmaG3Z6PbeJi8"
    "XtIzGi9BVzjCo5LMchqwlbxWHXkeOurB8uPKy1FFSrBrbuQr3dJS7iAVbklejhRvGM0zS/fRcuFIdhWf5Zfh/q3nl3NIAoHZnWwZ"
    "/vEFy3JcP9uglLQpXW4aXeZuHu/ZzSV3bsELWXnpB5jc5WH0nGv9oVsvIRLP6RKidAwzHkzxgcSED2Iq18IDEgFLEYxeb3NgsBy3"
    "SRhGOa+Jbu/7TC9gSdd29OsdQBbIHV0jJGQa+oKCtW/FcIQJdMQkMxGu3K/ov61Ih7z5CvTi7sYvSa9+ReFHpIe7GOlBSj2BLVv1"
    "xTZ7QqfBKopkjcI6GaLFI4mxl7IANbIkGQnozvit/MTh7mDTJKIdEBDC7Z3n3tfQDjjRgpgLnFOEb/g9KrA3blLS8d8q3D5ET93Y"
    "NjPbLhpBESG72rScRuRoY9W91H3QG2RIDFAAqR/+ljPvN8NpkB5gpLlvdk1zuQtUC61HQBfJYmT4D4hnulmKldLsuUO6WwpFh7eb"
    "8CmmvLecZ6AKUt47I62cuwzz3+7DAZUac25gGCrW11N9ixENCmP0L8c8jDHThK0gWyel9P+TZhatZ15yNGRkA157qoxbsfCECywf"
    "44tWkJvLlmNxwsCcAjWS+ltPTtl8oVw87mbLjnySCkr6wISDAmKGSd6yXBsKuzFYDk2DmGl3S33D9E33k65kPC7DVFtRp7Gv4YxV"
    "2afbWQ2Qm+1OlZjne1rHdGz++eLMPPl8znNotYM+xO1ZKSI95vvABzRtzdJix3Y0Iib0iArBmMP8RHc4POv/ATonAtBMMOq0TDfL"
    "zMuUUBrxJMqwfDpMFK1XHXhLWfIiMPOyX7wTR8C9+IKAGbr4et+sM+1FA9n+7PRjCcwZAkTV6pORjZtPPYmwK0iNGa7jVxHey83o"
    "biJKLCJfZI5K6WCPrvhwuzGBTwDxviGyFveesRimfr8NQrg3CgK1pHbKVKfHnDPGLs0ITu8LMiH2NRFBQOZs4tzX0+/clMZwW7oq"
    "ESKqGMsLPTcpcXC05vpSS75gX202h26TwjyjVs1M1NxqWlpfQV0p6Domwi7TyVEvdPCrwxyeeHRBT22/QF/i4N9uRYMcwXtl8lRu"
    "sVXM4r/A9WNe2AJw5adyy7VgdJT+5Epz6LVu23l3dFSTH8oii+wqXjh5l29huj7QxwX/duOChOrGMorcwKFis1FAB36jey6Bi+lF"
    "gJheTyTMlPskNpF9Ur9M7NvbbMgMbRp4022N0XyRXdS8nEf6FQ/5j79/9qZFWhvYZPrWGIJOuxUdqfr2R7sfvWuEwcmYfN8xNDZB"
    "hsyVfYlD/bA+nGfEWiDm0yHikOSCYP8vQY8c619IJePllmr+SKFAW1Qg0EoAQRTIcaBQIukGG0FRy416Ci65OZJoXMRjaaO6BZX7"
    "wWLTSkFzRxSdxBbSMFUjMFXK17sAbBGq8Mt+o+GFVlFkq0/j3Azair7Z+T50zVhrywkKx6Hbuaa/lLUxr+9B6MY44sAfmSg+I7p3"
    "SGlrJhAvecw6RPl+//+x00NCzHTFjna1He3+D+7o5tff0W5sR7vmjm7KHV2XeOr1aIsqklbtgPCeB8Ec6RoMvmTCFaU5MmEpzR0A"
    "XXIbcqkxb7IbBEX9bcTG0hHmKPj1q9svMfBiXvdtgvWccHBU8AeqgZ3e8Squn2/m6K/TQXwt/AZ1rq3Br/PwAb/PqweyBH3ARyUs"
    "AjvWay60Ec0Q/zpl30PvOt8rTsBvCFmAflXwx2n6Zb43mznxkWGzm3Dg/PYClkddRQwTq6NjYp0ihZTTZAkooXC1hM7UHZjPdxnr"
    "GSLENKwNkzFn2VgFpXkkiiATZAkNjMtKHhkJJvrp5nBO0YKCf2MOq4v1hIiAWGj6tqG3eora6tVWrq4zZfgVqSZBl0kxlo8+o5p1"
    "UbvYaFelGJrXaGodYbHwYLSQLaA0GOg1goLn2toIjBOBzBEzDj4S0mezCnKpHL4QYEBmGTkFcnS5TsZ5VGWiC2+5UFI5XnlArbEG"
    "yd3OOEqyJe39elEK4ueoE3n5VYvefII86VAMHoJwxnZGb8IZ1ga6RZvM+nVDr6K4gG2lYtFVKe1BG23G3Erp2gpJuWYfihComGBP"
    "UWVKasD+c8HKqpm1AHhCVk1LnrCp84RN5gkdDIMlWzdvBOl0Al8Dt83+dVztQqByEbTQmNBSCvxvxnIRGLeYEO+UGgtEpd99GqVf"
    "MpnuEMenL6F8PudXVvTncvKF5K30uYnd7CwXem5RZ6mQxR9jiOqMATchJXl4lOe6tELOVGGJ2aP4lg4DY+1kQmErZbOGlWgjiHyF"
    "490EveuFaCJRTEYasY3BWu4azEothmBSFNNTcRHDRsxQXjxEm5WYs4UIqkbbmdTdXv6AM0tD5SUxNAYnskvRHNvIpcySmXTK2BKV"
    "lP2QFqzotTLlg9YYiE1RE/BF1/ckRrCoD0EpF/uMOUxRZVRBspvPg3TlLJtu0ugPrCymnJdHAKG+/BK7DxgSsBHqjzoCLrP3wiVU"
    "fEQqiK++/K+dj/5TVzXsfb4NXPDu1bcIakAkAhJNPf/czvZfUa+8+ULPjEC68k5zara6iYUwd+ujyd3a25ocNIyYLY0kMH/+3jXK"
    "FfM/QuRgV7fxwoW/s4rUmccgSeVqSOVqPalcnMgJQAqujb86qYyFZrV/UN5iAGtBXINgGhy/2Oe2TUmw2o4l2gmWvw/Te8bXLB3L"
    "5D2Wf/QwkCuRa8cwr5HpUrOFpaQUiaWmsYwgh607sBUY2TdmNWJ2zsnOo9dGCuam1KajLyN7nIktYItYfzGJTfaidhrsEC3vkfTO"
    "cVHDjhELrolZMZwWV5smYfXd38iihmSp7zkHSUucMs6nno6BZwMkhBD6KduMMhdZziOYiegHkntzwh73fzwXkbVz6f2o2+TQw1hj"
    "WiDK8Juxh9IzQ2rlaDaB6y1JXszwHNIYmaCkqctYu9BvZohbOAcsdj6F10YKslhx82hBZnoy2+2ZKTtKIVkpGiRWZXoV7JBpgrVI"
    "4u2j/gAms9SXAS1HAXmOGEEcQk2R45gm/Hosg664tDZfoe798u7Gm8jFrW9I8CeR2S61n9LG2SMd2CAWR0x6Kp/ToiWm3wutGL+j"
    "MzJoWLzCyg+YBvr6UmqOYB6J6DFzqIOCY5t+6Jqon72veYyDdTDFWwaTFBhbQV7c6trHCMHYtR9FV0YKuZVOYdVfwDy60f0uIhAd"
    "5EFKZZgyY9vJX9vUfZ1TsBwUHPPWV59/uffqDVKUob7CUpmo4KUF4KGVCmhSqQoumKoCOHWmNiCmEaTMXw5mesQWx0i9Av9i7RQ+"
    "4S+McUgVdh9/gL4Okh/JXBUgHkhYtJpVOE7+wnC5xmuVHmq4MMIYj05xWDx/YDXoUkr6WyJt4/rGgdVQPIpWIs39Kc2sz8xcxP4h"
    "JEj+vCQGejq5N2XLm6/0oQzaicPXzutWFdNJYEaXpbJ1xxvoK5ACxJFpH+ScjtEkrnRm8MEs5lZrh/2MrvNmXBHwZe2Q0jEiG9PH"
    "vq8z71SWPRwJB3q+XqpqtG4f4/CNVIQcU2cN331u2h421RlSpShmeJ1OPjWJfjDmGqpcvdjAOTwnDzZASnH34EO0/rb+qjX08MyT"
    "8CHy+lGG75jkcznKUtFrUuC0Ge4yuq9Gwri2oBOk7Kkc+usY3GKTLIhIh5QY7xrav35+PwNdfH6l8UDbwtTyh/d3P/pTT38dV+HP"
    "f1ug5DSB6TKS2Eb5EuuFbKDyJQaKUuL3OJmM7Q4KPQ3b0temmWuVKTCcv9bpdsIMgrLKImIZ6dcH5jOUPxJ4EfLvgUjFGER68vYw"
    "Xjkz5Jbz9odMRuF6zAZaUsdAJn6cFfpPp2me7XRXEKxTbBm+9fktvvb5AkV2ln17YirvJfMew/faUucdFhZyj6dca6xbrniBPVjD"
    "SRUy1Okw3jX1uX0eVgYGNtzS8rpeyYANRLdtedjopG1xC3uv3tm5eDXmMwHbYHz8nDqZuQutakYlOdp57iK/xOlsJJKZgAjVfP1I"
    "YyFpnGAmN1+I+EPlL+lylpL/D0xpfM+KnuluYUGBHAcFcgLLE/ggwk2gT8Uw54Vuo22EWTQWRkdH5nMV+rcVpT4gvRjv+rrCQMwG"
    "goaJoLt5zacdqqKIvUmhArXp8kV8PfJCrhPwSEvkgICmbM2rjXf6Y3yGCwzN6fgFTps7T1y2LIAuCZK11tLmtgoJ6RPf6CtjUY6F"
    "ecqpS17bSG3UwcW8NeKp3eU0YHG+Bngk4l7l/XCFIH22SMGsc1OXuC5W/HJQI6GuPfLN8fF+Yq0+6AmnDDSg65S0SZEj56mdt3Ft"
    "cO+2FJ4ilJj3gkbWHNa8GtB711Tun7vrm//Um6fDc5M5sMpQiSeMeP4upmPaeeHF+2+8p+cC14AZbu1+cknP7sRpkc7b9uBlbSSX"
    "dbE51MK2USsKK3s+Ymmi0QpO+MBqQ3jQV9IGllikBi5SY+AiYSilBJcEic9twG0Vuuax8xf4lqUvDI1rEyJpWvERKj85JC36WmRo"
    "iP5q+w4Puuz+EBFaICJhSoAW5gRGpMMAGPf5HIIS2Gm6V1ShtIol1ULeh48cxMSKg1bxfP8tKzZ8VpwQUQ/TMG2l5XnQ9ungLQzH"
    "X54n7pSsZJAS4rxuhzVtr+XaAmMIyq4CqyBrtx1U99QVZqu2Pcq8ELZaon76q/m5DD7qMd8lTPsikM32NbfDzer5nkoqOXAaMp6F"
    "oWw6PfgNHkAlOmE0hXrndB4Qs+MJEn6DpeF7H750D80cnAsQ/eKZvUAFitJ5Aaf6d8xdH2doZF2mhYWztAmkZoWJLEHMP9e1MArD"
    "SpB6yRz6JWAOkTaeyi2253KVwOu47UI2QSH5B1gAUURQL9c2X5yZdeaAPpk2hliTT7fxtYgeN5P0eC7wl9puEZNeF6yxEy68QJ6E"
    "0BA9a9IfRz5Bj0l6RoGU/JS4EnhIf8WztqvswaL/TaS+TbO/SskW6/eUcCpMxJ8Nq89OdMLoKkydNkIQQHhWcIEcfY7FXgGOZmJ0"
    "lMvAjOolZsZnOV+4I6LLCxb8aEXaQzWk6XiGOGZT6SV05cDXUtVd1BxID+TiyVr+ZDEBhCHqYwZMZQ0xSHt2xePYF7/t5gNnyatQ"
    "8NZgRPlKvZoJluHflAuqdtgQYIdyENa0Sq1YS267bOpEpbMhOaGlycyY5Dw9pEIGhpDjRppf9rauUNNd/RRjxb7YpFLF2JuettC+"
    "qTwqgY6IO9M0t1hRfUeaV4+ugLQw3woJ3iXkEPkvulEGYftpL6wBPaf9yHe0vZ+MRGaoAGx0UVVfZ/A60eYBOZuM8JIcquodcr8j"
    "d46XyNpQz80HrktaqnrOveCWw8FYnlFA/fYLO8/doOXDhZP24HQjsBRaEpSQWrUQmyGs5XnsxIJ6qB8Evl9UjglwdEsXEjLHAw6r"
    "72pkm4rYNCMq1NRJlGRTPaR3nsmmagRKHesEkBx1jYVgRzRs93Z7AD5RXb0tEJQQrN96tLWcGTeyidBZfoey0X6YONTp4U9K5UMn"
    "/VdInjdfgIt2960/7V77GC5aM/Csr1vTUPs1WuAB88Q9sB6w8mj31JO7pwVlKx7lLLUn6+J4qjtDLIdY4TqucL2ne0A8zoD1IWy/"
    "niXkLK69J60pLwYmreHrepgTFSMB8lXbyBb1y8xXt2G5b6coPiKC3BRDtvsiahrqUH6lKA5IzJlyaAcv+XqMkrJ31f+MIxWdY+Li"
    "Jc1URkaPAFlizlRcHt2mRHlRg3ArkZW4SWeqAb5UdVQkFvuRevgd3X33SeyjIBi0shA7jtpP9aWX09UIdaiPIUY5X9V156v6fpyv"
    "eMyWlcdbxPDCGvTmUzjVDdsgmAQE2wfL1ZC78f6KhYZtMQketgo6SNsGVe0dNt03eaHvh0OpDgbpeHkn4jyipTL6JgyH0LfdF3/9"
    "1e2Pzstrh/m5fsF3GJq3cXdzi4EgrZ65tFQofpRU8dvdPqA7cgsH2oRqcNwxSqm9qNIYoh1IS1RPsdGxsMH1jWTsXzRwGZcXw5wJ"
    "SJJI9R7xGi0/UN4joa4AEzysg51uM93GpFDGFSYypCe6NOBSM2P9RqJlTcPKqRO4AZWZnXwYQ6mbY5D7+zcch07BmRoPrvwndNOc"
    "8lhwC6sBOpdZlG4HmCi47TBWdjImQ5YI1VFKUQu5acZgXFsbMVN9adKlmRRpS4kdfbIgRSKnBHUkY09QwKsCc/uAaIceJs2qVXTz"
    "YZEnKb/AkMkLCjJ5bU30CiVKr0I61BUXY4ZTNATwtA1DbBfJZEBSe2DblIqAnvdmM2RnoWqYxELgrFBAj2GACIopspS0Lh40nJst"
    "K5J74TZrpQm+xxKp0WeaThiP/nBmAqduPOSepSdIr8tfnRBf7jozQvJ1eGCzeHcq0Zp6liI0e5Si3ccgA34N4+/7yNEY3aCYQa6i"
    "UmiKbOO0uyq0mfTDifm0ItPDB7297yRKVdILT7CVtG+4nw4zZXneIMpcwF9hA1Ha8GKwtqae4EqRvaQC3Clyx9DNrz5/e/fSy7ow"
    "g7F8FQLtgROPYM7TIJ0YDfPhFv6TXdaX82abx6HPxxz7emseSvvTOBgcmoVomN86PN5adibGx//FtroDNRL9gtojwtlfDyGCCeMQ"
    "8glHMPZtU+b7WKMw67ptqVecNxtZ+sa+VWFBDqeBiBiZKL1Y/vChgBB6ZYcAWqjz/NLXl31dxRZRnG+F8AYqvdx5ZceQTa/08p+t"
    "IPSwJlRUZB5CB3+xTeki0enYUmHX+x+Z+MDYibk0jW5h3CH9UBlDrfceqWiz/0DNUfZxEKZR5x+YvfNHR32QM1qUS95K5EPYHpBC"
    "MD3T4PbeW38iGPub+va2+i2NSSNT8i7r+ZbFOuAIOZny4355sY16S569ppmR+asvLucz4xOHz+3++hPg0WXimJQszPoKhokVjNCz"
    "4efVigmePTpajmVkjtOPWJrl//PTn2YOZfKZb2SKGSvzncyRzBo6cmrGA3L1W9/8Pw/O5z901rqks54I0vdbyooDu+bmMBynWLgn"
    "/Ig/LuvSD11BMT5PcQ4nEpxDHLmvJ4p8tSpSTCjod/VZITa2CuNGMhOViAk7LZD89IhkBMrJqOeaD2THc5dwXzDWd1wvg7VVam6p"
    "MpR0Flq99EDSydgaLuKPgBeP02Wr9KR6YvYT7bIBt/j9Vt8ovH2kWRcws9gBTqvHGGxR7VWZnizb0GEutPnC91itMzDOd769VGol"
    "yh1lhA3g3YDBLrqKzSb8fTfKSpK3Dlp20v3vqL7zFpwmMYoIMPA4W21YHXIiwPQn4aCQ5TjYmva6Ci2GDqFgIququkXc35I1wjyv"
    "pqYW7/l/U5bSdPaGJXXTkGLAN16+v/7m3vX3e6VmRkOrOuCs2ESwnf/qYVTeTk/ljFeIwOfhnM7SLCvRbOJNpH/tkWZaKo1NWDGD"
    "ZZMaFt1pVHhZa2FvQm8tpubinZ0//Hp3fYu8LzHNOU/HaX/JDU7DfRzyECmRO/mdbmxz8Li0HGGCd9ZySwC/fW+T9HD0yGUsIaM5"
    "dZRkQoEa5hUiBzLgbOqjo/Xo2sdk3ilb5hIBXMSnC8eRZys7X/LJX4MZmcL64MQsge8bnmrVwpGRKvmoVXONBUYUllHiItPrGOb0"
    "RGdNjBMvJ35XYBrwNdeQ5SopDVVFxj6Ri8aSjUYx5avdSV+5wFURlnymmkM31q/uXLNmC1njK7mSTnSjzLvNnN/G+pe8plW0Tiy3"
    "6n4AF0JePm+UyvD8ca+J+tK8HlnDIRCNQq0sFskJJWrbcgHWB10x4hBvNCBmO1ThlUKlaJX91goOL79cPN3OLnPiBVKXW5h4xhJw"
    "ls4SvOej66DfIud4c6rcJumDbFSjTEHJhtvwsXWnljqzJdtIz9tuZqu5FixIy7adRfWGSMebXV3I/2CZSsDaw4bMV7u2WcET+PMC"
    "VLAgfF+oFQ+zMaY1r63isRgCizNdeLr4RDUb2kmMlT6CTiqDNVy6xHKw2JgbIq8eWqZl7nQn0MSwwNCpkMs2zwpshQ6sdzXM1u1c"
    "B741+rhEl9tuT4g0gZHcxzLbEUjPJsL2qUBu0EbPsDQ9KeSJbJVvUOh+/iF0NWHbr9qidp3Zrk2Yhbz+6vFSOTTs0OI4kdy3H3DA"
    "FT1Ym7EBl02OKL4DZhRQupXRKafVR3R9JlsyU2Wm1WtxXig2amYs5yk3W2YcUgRbKS+gTo8+UC6qfhWJzFVUhf5Oem1NuR/1WHWD"
    "y9CyW1mOes2xdt76NV491G2zNUxnFQUcsuPyoLySggTqTf/t9asZPXXkob13P93ZfnPni+fubrwj8kg6cKTUCnJWoLqjVvFp9UvV"
    "WX08H/bbVPE9pd79iXq3yamxUBbRM2aNPB2NTDHxxLI/Bb9bmgufdh9HrN2B1VY3yqdlqPCrydsl/cihYI0wMcjTiZrSAfSoW8dg"
    "sk0bx0IbGiKbGeNO4zNSfv7y7uZfiacUy2C4SzCINpaLfgY266VkqBviOvQgFtgXhgaJt0UjeGoOPTngcgsDz0XHSuPS6cxMzB6s"
    "wj+C6M7A41m7j8dNZKOs6kIMQWR1gCxV7b4mbpwizBtlhHqFunF8JFSAtKlUKUX1FwtXSLUK3dq7+sXO2zfkHrrZ01eDnb+B56Wg"
    "U04zJ7n06ztXb927+DnwwkIj6RA/ES0fx5nH2WvhM2pEWuHbjLblTA2DkgwCedpNXHskxY7PGwPZF7Ex0GNFiRbtRqleH6QPFrpb"
    "GMrzqOiAfXXxEsxOLlwOFScPHdcuauBIgPfrHe6F3TmIRWJLdQfWAPYOvw5EcR156gw3dEkISZuv7L29sffa+0wQ9Ys1tZmhWJbG"
    "QNijE8iu2b2vJehyEYg2/GF42llKeitY7Z5pWhtzmVjaR7xvvnwH5hu3n+FydwVuhrubV1kClQLj65FrLdwNVY6g4Ty7fWY/3uoM"
    "SVTpUbVv4nJQtQMzXkpdX+DG29PaquZQcbm21l961eOqLmnOBJpo1eW8wmGw2Cz3zgidnOH7r/2Fzh5Kp/fXX6WtDcPe0qZUHc43"
    "pAJOclhLD+94GoSiz4HkHQHrL0KiGUZg84V7P/9w5/JruFLx60RZT24aUdMxn8z+7kduJ5bSd0mKIUL70ylUGaOyeLo5Iz7O9oHU"
    "NuouZyru4HDPKosH0MuODhGI1xTKk/4CiJPwj3qA0IFF+lc9wrUv0r95S6DAqH7IMgiwqYmNOmpKZ2Zc7fpUdMNItmSsYobLNGm+"
    "mb71YQFWA5NRTWMy4rfP/zrPsa/bvxrd/nC2vYqMJnVqD/HgRcqqDGur+p2+y6/tvXqH3HY+JP3+Lfh87KmT8C8fwPvrG0ieoYCm"
    "Kdx79p2dF/9qya6Lk8ONgLSz6oUg8uP9YAs5ghLQtB90jPEhovhz78tfoo6OWBZrPwdddSYWNq0ffVgnUkKwPkYWfGTcHgJLAk4/"
    "XimLmBh2OBiJMAUTPXshcFYXgEQgsK1IMN+q91EHYLnMwsFBIhnXQ/LY3lvbkcQ1JDwssQAUBZ7JwvOy/GZbzBAsQUn3XBtG1HIr"
    "fZz/ltoGU7Dx9u5H7zITlljRGD2J9L1d/dJtLzYapWCFd2S2o3ba2hp0sXlOrOa4fQQWMdp9MVCLDvN4R50zkZ/HycKTrZmjwPnO"
    "wmbAeHf8b9Y5W8BnpPbz0fID3+qVc+hWJbiT85g1OnpqdzN/e/6VDD+UqaT5k3hB/ZCCFTwsUoPfyvggrZwEyi8EyZMzh2cdqxR4"
    "pYOM3cNPVF0n4QYwQtlO0pXQF9dBxxqTswCf0US7tiYfsKXjnHjeP3n5CRg6+6CiZDUcZCvMJlHlDAbqH82FvnBLPSop7HD1nCVS"
    "fAbLJzbK/pEy4CAPjwUayQNmywcfGYdhIZzCbGQeNW+Lr82a6cqoqL/x20HTXxG6wwUCdeBuA/fF8XKwpy9IPAdhIVyMOXAnKV4Z"
    "7aVJRyDl6a3tNoSZScPBZMPqarKOdG/vmnntkcCrUZnY73s3tu+/8+v474IGIYN/tO5VoRylxjWiJu5u/pkQSz/tXTmr7XZff3/3"
    "jc0+XXjxk93nyJd1KYkBGCsbcSS6HuvcYu67MElCIWWc6oTr/GIK+2u4AUojj3M0/gvnrzlD/HLxdJWYZeaUnZPwEON5jh3Ev9+Z"
    "+Pb4+ADo08ezZC6yyPOtSiAHVmMh8Jfwm2nfKdInK39mdPRk0arVUU0DRTDHfMoRSHOeNy2rmKAx/+2xzjdMNyroT9H627XbGWKd"
    "gcDYol/9sUQy6lwRX30C56WxAJcIc9hCzacfRHQY5GC5S+/tXvuI+VI+YxTyfjSqwuqyTkYLdL4hJbtbu699rNs29chdS1ZHiO5V"
    "Afwgk1hMo+0h1xp2ZEJgICRqaY7ee+NTkDNjOD2H726899Wd90kXZWCVou4KVU1XSB4FGfBj6O/OF1d4GgT46XPvy9A98hhmN3ud"
    "eZDlVUkrnpbDjEygBbVQo7FQ7BudkBpoPwSabFUPaKjuJ6BBdO0ZWJp2n5dC8x1TM5M+6DN99OnAtLZDIPwW8g5nkHdImlKV/Kif"
    "rTPoCocnuwibYux0kMXPIvVDD7qlB93U4MqbbpXKBIa3FJRaOiFlszFL5WdR41aGjYn/zpyFm3BWrNyFsrNKfE3+LAvTcKbzUSns"
    "X6Nd1Z9MwF2Kn5jvtWP08pgLVAvppUMiDF+8LXnv9gnuSL3Retv6Y9F3h3WPrH7BJSlKDTPT2iOHuzGPlmYlu9qhnAYRjN58g5OQ"
    "N1N8o8PCDCJGNcMSCK+BI5MNYEKAiufDTrh//Y87v/0YFlw8chBxLyXBlXBfRFBJm8D5OpESwz9YQV5UPCPNBT5EXlo+XGyi/gPR"
    "+A7CLFkIZqPXsPP8S3uvXpfiPEb6K331zntb8arvfbBx73cf7Dz/Rqz6nc/f3fns6le3X9r9z18gjiZV+tSTQG+/mzv8rUf3PsI8"
    "hAl2PMWcCjNqil1UMRHaEGgswp8JqCxdE6Qq0OJY6mQ7WqqtDOevO8hbJtDje6DWGAzk6U4Btk7gKvzJePgOUWyiDbgKcJw4LwDq"
    "VFMT4DlibWed0lwbbxy6Ee6tPycirlGHgu42lO0Rn20hPlvfxSRvNVUt7GviYF8i2NFLdy/eoivwljSXYQNUHDcTeuqiEkZ/Y/cX"
    "7+998iYqHL98DvZFVFaDpVyuy0NDXl8yu4zbmHMrlj1wO5iJxGZONqEOAZ22cx3ma4P1lZRpBeUj+ENhVyI1CeYAkKKgzEUHbBx1"
    "aFZLNnK6M4OJdPAOJ+l0571r9y/eUJqcaGSTX6fHPbZsEy8KzbVNzhFPuFV0cyU6aEQjLLQbUbdEsNsfmYqgMtF8zgopK594XY4q"
    "elE+Ea8oadAVzryYZohRZ9CJ+tU+oqU5liaJwCkTLyN9KgW3cITgfeHYI1A3/MlRWg5/wcJWzf0yOjpCReQvI9ovuH74Hc+gZUcb"
    "8Hgn6zoI5Kdg/FwmxOSkU4dvzXP0XWgP1Pe89DQhAl8Xe3VGKPowyTqyn5ZQ2zr48qyKipkqHAlUxvfCkRqPr8bjgwFNKTccv+Bl"
    "iRKjTxd8JDqL/lvwGUkrumipqqDaqdjINa+sfsVGR7NTghcRhAfmVz4BAoNYKaKiVmEGbqfzKaTk/2XvXdvctq6D0e/9FRzImYfI"
    "gBTJGY0kjClWluVUiT1xIqdpOp5aGBIk4SEBGgRv5vA8sp34tROnztU5Ttwmae43O23S1k2c5r9EHsn+1L9w1lr7gr1xITmy0zcf"
    "ThRLBLDve+21130RKgY2NVjcwoSEt+RlAO8ceNfEaspFAK+b8LoNr2MYe+n/AKkKX9qLW3lX3Z0Xfm9gcm3YozaX0zsnJ82TEyDq"
    "aH0EsTyN5xy10KxLXYKNqFXcN4F6qoudfLBerTRCJpvat7oynvu0h6C5v7Ckt3/eXTFdXtmaZUlmXaAAesPEPYeBTtGQwUZ3umkc"
    "O/uJoNMBMmQfjen3hTE9FswI485ldSp5Klpq3Dr95qvvf/8VovRp8whsYd3FEBd33/gl6g7lTY1xA5luCwM7YSC3/8IA2fFNnqz7"
    "8i30Blm+Ijx5a/Lw9K1b7EKEAfUWD8wHZFBpbA22DGYraQDcLN2JidW7EkonlLXxcSwr6pVCKZRhS5GpN2YzYOf60THiK0n+iZiA"
    "MnipsIgsUnImFH365NEemuibiJEAQ4oE6FPAqJBHAoxEZCv/kJtT8Nq3HpjD9RFiGLZvY3Tjez/52q04hNNtw1Tu2ahbRGWBpE5T"
    "DoIbVaQd4TKweMLypZyXq3JeLnJellfHC2FAprhhKqNXhmWP7xhreKjpoZ97a0pLvTjzWYayLaRUYoci71Qo1Ot/gUOOycuy58Nm"
    "EaGeNssKy/ydajZCal7i2n/B1VNxK7HqSpgmfSkO3Cti/bJazLIL4J87KOhKY1aGHUqRY+1XMpAGt8zGULgrA4Xqq3vwZ17ezPRw"
    "CaXlCtU2MLzaFpBxAwmNFOIxqB8AiRESiXHIoI3zd/yH9JHmztd18Z7fVJP6lUn6sp6kLutJ1mW9FzAccsCZScOa8QuT35AxmoVD"
    "8RR1zAkd+WzrAwVsPGPi6dSVPRPiaUDOopLQ6e1UuDHYxNpP3ASTBbwyDwXV5+B9jOnyiAJr1nEg9KwMjKXVk9kVkAQKIiDtKMAn"
    "nzPSA+K2Q67kVaJ7v0pZ72PCPbkMzVUXi5MKAz2zJkuN29Ik/ywm+WflUdg7XEATaIt66b6uqmbpUqzIsFpygBc+jAFKc4KEBoYY"
    "Ho0T15miIs6NBaJiSkvkGWacYoEJG4GxNWEEgJ2/PRlEtDhZSNA2A0/d8na839c+eQPZsmOqzVjr9v2uxgEsxyFbDx6wekbGRzJg"
    "Ne4ezoJ1yuxD5KDzw73rWbCZMcDpSz+7950v3vvO26evfpmsBeBs/YDMId6iDCDAgb9NLoLv3PvVy+gnxAIm5seJErGif/Lev70j"
    "IjlzLH/6vd+efgUTWdz94RsU2UrDfty2J/bLCClVJa23CKALhxGuk6cirw9IaNiQ2EY1aZArEh+ygaQT//nbt9ZdoEfHRRQQHqIj"
    "RnY3BCy3WHyJzL5wOciiggLXrrsxsOco+Ufw/C4BJoXGphQcFLTyFeKsvxm7KuF4/ksw2i8L119mEvOWvDnfv/1vqimVsXpq2eeg"
    "jxhS5Aw94HcMZQ01ZWsZNiUWuwINDOumjNY4y7LwubzwLYos8g6JF14kGOXeznhNoKXnzxkEkzLly2KD1OVSneNoZRQjQgaFbm/o"
    "FmBu/dSFKSIJ67DIIjEjq3tQOUT3G+T0+ir/NyPiG66evaXrNJGmWeziTAJzPw3Ma+KVfiy6b5xZBJmFklFwp3cxIYfCtzQTI9Tv"
    "/FyaLqaXn0VqSW4CY3XIjlJrTQNkGZvVXNB+LQfAJUA9rWMOF7zJWu4QVxaful6rhab94pfkZZE4/ad/ZvxZgXFFvIgZkyR7fykE"
    "6Ap7hen9Jd0MCN5na0VjU82ZlJ5nijwuQ5M7TlsHEC0904R6s4MaNjI72D5kBhXYqik1O5IjBbBIuZ4zH2DK5sxMx/hp7dWvfMov"
    "9pjTBffhM4W9mFkOoXQ4hF/oZBfWNzZ8dAbRg3KkJLOaL3ov6KDvedoZvbdmovBBt9Drrg7byi3/4SJ//tdn8TJ/NOhwP3MtlpRb"
    "hvGhOwtGVs+Ixri2l/kKJ3N9FSJx7iIRAFBG/Ow2k7u0liGfAcWFHZ/RciKn5AGm7ZVZrJN4vj3hu4G4ArigT7nJ7qxjdUlEqKT0"
    "mqxtHrjCUI/i20WKDpmZE/aEOWHvA5gT3v3OHw3egG4+mDkoL5GniQwFWKKmsxgLirhtz/8LXes/V0wGf/Hev/8nEYjf5baDWZaF"
    "nGfGTt3QXWJ/OtGOi7dkWONWEGU4UPKd9yh/XNsr8i6XA7Ue1VAaM1rouY1i2HwHgFaUSoSFFcigrVeGu4PZsBKLEViOwmJkgDxO"
    "MeDpR42JHmydTGCAxyAJAOpU7AIWZt4OQRk7MlTJDPIfDnCPYf7Yw15i7LhyTwmfWQrNSEZv+TKtpOv8QV5XXjMwstOwej4G9FRt"
    "NJI5mTD0s/CNeisZFgeRV7az3nO/gEqnr7ymZKr6qYyIQHyNCIRwKG4hHoTPr6O/KaZrCpwWBu2rLvZ6blQYtuqPh0HfG7qocQ96"
    "Y7yerkb1itV06pVkGLyRw0KpXxUBCPbEtdZ09vIjwweD88PI6aA2iiqfnDSdjXpdpC7a6/ko0fFJ74hDRD9HHKWaCIRFBpsvlLga"
    "fkqfRRE5fKtXn2N6BGxwgT2StMgPAPraQVjkGLwQtAvcuY/SKPRMs3fgHXLZEpbe3PRglCE608MHWkCjRc5y0dDWXcYX5l7U6B2E"
    "rFSUUcBm4VgLWMhiE+7JycGKb23BisNfsCHDFvNPWCfUtFxaHtPNFelP0GolgmFdjVjEeQ96xJlQz/igXBlKqGhhbvXcm8xYEPk/"
    "nuc528sB7RG29ADTMJtSiYfBR4ih2S3anu/0erM5flxIwHzCrfNdrF+hsR3wTTxsEDgUi1GjcewVP4a5BCzfNBvl/vFTuAsNthdk"
    "m9dyhArCOvaoQWjObRTddBCEqH4l4kEQfPPkpOWQBsIFrMD6Ne1x4LUKFSts1c8/WS4OBtH0ZDAY4l9RH3/hXxH+OIFmTgattvnA"
    "eY8O02CI8SBws+DXx29+ch8DHgO1Rl67N6MA+B0Xu7sRuf2i0UEACUIM7QADMeYL/AcAnAE6tRUDe9jNAXacC8DeYIjAFwkoo0ca"
    "idb3MKNviwbKwkp67VlxMDTlYUsHYGw7bBxWaMr4nnBcvSGjkIL6lYCyLFheHTCt33Knn4TzB+f+wcrJiQy8UbHYTw9JXWkGGpom"
    "nDePglegMShQvJ5VxRuLPy2rj7WtCiyQxZcKznM87CMtBg8P35mXETQYAGn+MZFumMwZM3IlAOQ0e64TFk3a+xCjsfcwDrsHv/ag"
    "csuZccDjRGQRyiDhhSuGHwVVDzXoxclJjxh4oDMfHhZx3kKphzXRBh1o1PrDQA9QPi0C58nQ5NViMbxIX6CnpJ7Wr0xZSmpgMCIk"
    "OOkRw8mHKHCn9k9OZmExYl8wgyWq4oVyL8adU8SdQSyWeNgVdVDyMMMAdZ8AqHRI6jCBATqk8psAvejO7AkLHknFSJifsPuFBSdh"
    "SiKYHLLOZLYDKwWV4W8rsttRkdqBxQIQBKYI7k52oicmg0riyqcACvroo/Kw5YVsheQ8aApbxvmnDNpvsU4zk2UiY0u0ublBa0Tr"
    "g0Ztnj9y+dpP2FLAMuzXJ2IZoKl9qM3WhxKROEIcQ09UMG6JrdU+W6t9tlZUhCY+iSc+SUx8MYVrEzinGGrYSqCFBb6v8++wU6gF"
    "bGSUw/dSyMSKAQwskovnsJh2AKM0gylbadYc0+FjP6KD5CLNxEAUvU8IV547hDkxSJ7FY2ON17ly/WBi7Vtda3QYe9M8LbfN2JpY"
    "1zDYC0PlT1s360W09sTLDVH5wT+UD7cAWZvC7ebQBH6+HAWPoorwmoN8tTWu08I/bZGXgF210GoK9qEfebAR0LUfuk7LRvoILvn5"
    "AVo4G1DDaBifuP45w6ZnuBTg+fGHH4Hr6fHHnzAO7SrwZQN7dHLCb5fmQH2Cix7jD3LlrC02iB2fRhV6GxzNYIGSX/b5ZSVjo7YY"
    "9FyzxjATDC6ib72y4hv6kkPJds+JgOISN3OT4jbHW32YRABNc1p2RtM67DdQFjfGrLnrsGMIs+ncKQJBtepNBSdtOHg84VBRYyaK"
    "Q8IZQ1aAy9tQlsVbmMKpql8ZeNA8ngBCALCRRaqGS2SWABWI3/Ch1YBvUaNiV+kL+0UVYLT4DD/Kw9IM/4YaVGno89FD+2TmZe61"
    "pS0DjGnOQZ0Niev3fAAyRJf7dMBNCeVwB0tYJBA93Jthz0nQ/uS4OLPYb9yG5gjY1z5thKKQIDO4gdFQ0b5nj5qUKNmC4j15/jwo"
    "O2i0msW2hvojxrFNKZgSQDjD8RH8G8WhlNgqKyuDeR814455COQt3l52jxCSh38/FrTQLFSEjLbbVtSz+wr58kmyPROYNhJ3CqZw"
    "YlTDAZENVoCgiMYZfOQBUmsI7AEP6kQvEFvBC6unCMQ16oNdyR4JTxSwDRBsfYZ1WYYFXnwu9LEeyzcJsBLSQt9ACqbYrF9pcprR"
    "M7eqe6EgSBygOAK8qDH7Amtr4dXpx4KfyJAfpxvj+vl/KDbsgydbTz1ZKj85PPyoCY/v/eb/3H3t9ZPTL/zr+7e/ffLuO1+9++LP"
    "Tt793ZdOv/T66b/ePjn93U/e/+Z/wouXTp9//YTFy3v396+d3P3Hn5y++cMTFmrn5P3nvnT62n+c3P3+S6cvfuHk9KtfvPfdH500"
    "g34/8E+AtWueMI3xEWCu4xNgF9rtk6DdhgmcHDnN49HAPO9ZD8H4nhx+FIb0ZGtetWoLuwE/agt4d1D6f+7cfuPOC+/86aWv/en2"
    "1/90+xuHW/BaL3fCH+++/nzcxulLLzbMxsomMuqY8PW89WlXMzNCs5ts3BJbHkUkEGVJgYsPjVEXa8rn8wd3bn/lyYMi0he3X7lz"
    "+x/v3P7Gg//zzhuHOMQ7t7/65KHJFDd3br965/Y3r/zPO/98eL6TaOPJ4bxmLVKv/+HgySHs7OHWifjxAJZBot5XzJOeGKuR5K8j"
    "VxMhZBxcLf29U3r2ENbk4MlJCaADmynfuf3c4VaxjNdW2Z26zaIv5xo15n5gRyiSJiIhQnG0je9EfG5/wYGv62vr6CKAZtFd0iwd"
    "R1mGW6nhK/Mu0wX6wHmclO2rNlef1ibloowIZsW5a36BuOXmAPkbMf6NjaJPoVTH7SOnhWZhDv9Xqvh8NDQxYWCRkosWXuGaUoJz"
    "7kwd9F2gkK+EPDoBMxwVko+utKwFxhHjUKHNLPzsBBH/hXyk+OlBiQiaf8yHGcUTvNbECUogw5IhRq7Bvw2bpt8wyCoGzYxTrTcM"
    "eOZfWBdw4VEXZMjLB4ZRF/CbYfe61CA8uN7YbQFVMaQXR7MAKArhQsNn6NEMXSWZeA8T5J2cQCU/NmZ9Figb0aAIwX337ZcMC4ZG"
    "2TdO//tb9MwGYRvMnv4eSj+hX9u4+wramBuSSjEwWTY1Y1g0dRt9IlhQB2gFVoaapSiPXzMW1iPZA7jz3B/5GFiHciTskMpHPf86"
    "SswYN5AcbSJZJ3vPEjCI0DBfopo0qcevsWlRJLFfvvu73/FEbj/hchDNIe7nJPL4CaoVn8cEcNSMXA4u1WMprFMBi9JrRBFCWQTM"
    "n9154XWW6uT0VYybffc3P737+VfRChVNHbRA/2zStLh33/nG+99/hQW7Eascg+xVF4MmohkkA9uii2cD4RAAkwX6IGDjTwhayAu6"
    "9RjsTMtljtj8ORbujzsJsatnWBi5+KFgahuVQqVQ3YH/G9xNnCkoAXKjcJSVGbvphU2m+oPaF6HAjP6Bxdo1kA7viQCUwygMjlFO"
    "Dmx3qdQpiZGZ4tNnWUz/avmCGomfOOc5AN1jO+WdwsVytbBbrhUulS8XLpd3CxfK2/ffC3/zqOe7TQf2BPhuv6W+RSNV8ZrplWlN"
    "Ga74i1tQluh83dW8WNgZb5d3125mN2e54sazBn65fJmGjv+wsSe6UZaVRIL/+6t6MTkyHIeZB4LbHASrHAQvAgjWsvflXBsDy39o"
    "UNcDMI4TE3w4q7NycXZyt00MaxAGnRB4h7+88yBGdoYjsV2uXd0uXyrgfzTQwsVCtVK+9PfJZYjbVgEYCYq/uGVAjVxpe91F6G8X"
    "qgDbpUtna+hQ8YT+XwLNVbvPjeXzT+DDzrDrhCHmQqjBlVIzlORSN1zK/+O6FCu5UfaAuP1sVDQPKofsAcjtOD1BM5FgCq1DMM6y"
    "A9/HLmmx4HaOgBzvqTlBXSH7IioZPgIQuUKuuxGxMM34icVrlmT0DRclMqbUKkXlKIicXoPk6u1eEGDYXsRiH61WKuf5V9MWsRaA"
    "sqAgYFakRIp49+1fFYwtb8v4CFBFQJN5iwW5OopllJ2RbB3mJsXr6PvVcJ2ih+JWN7Ob4tUmkcAPP4q0IBBKShAiTIokggAaPLXO"
    "L+I35hYOggRo5FX+jHw0SXsUeYN0peV1topB7FkZmLABQ4O9h2K0PezzvX9/5f3n/hFKXRsUdYXgFuzxJ65/tiTKU7O0YIwxMOMV"
    "YMAZCSZAIVkTtCn5JhAjgKNOfXyJ515FUvKrzI8hUQbox9g3sDlolA8QTqSvZ9gIRRQ5HBeaHMtR0b5QH1/h5nVoV/HCnRfYqNh3"
    "Y2FTC27Li5CejFuJ68tcyj8RCnJB6y/Q/2YgR0VD6bUMLpzHnw0VLk9fJobh5Ze4fv2F39997ddEmH+eXvIMzGJMwtWkkQfbcvDA"
    "gIo+4Xam8mRgGtmP+wchRggANvwYzSe9SL6FUVcOoZr+SYmBJ3j1iVc/YNbcfJUsmtqhdbWpMfHEUA+QyWwOzOROCd4S7cMmXnzs"
    "gWu3HvMlv+gO0T1P1YJDaw4iDODTGV8N7KSP6iEMYG9aj3Ep1uPXTj7r+SePOU2zwaARXpLZIzOm+WX8+YHznnVziF0mWXZo+jEp"
    "NUYPWVVQ8+Twzu3bh0yCYiqc+N+Mi/OOFnsAcar0fUTxoIcOJITghKjBj5UT4njEKTEyoy61Ai0aM5NTRnL5MWUC80oGMNioNggS"
    "bH5mcAToUBs2aOeZOZNX7zV6yTCMPS2eIv4tXymRGRm08H/0LGiGlzDOayIG5qZNPFY8OhJ+G/AZ9o/J22KQM/UwXqvLL6xIxIyK"
    "ZbtBV726Dg4pt4njO7HgldLxYf5Csf8+U8v14nAKGM+mGJqWOEsDu7Kwe0LqrXxFBerArsIxit8xz5aBvb2IhWN0WZJoqcF7Q18o"
    "HpvwuTeZc66h9WfaVAUHhDfmGH9Q4p9E9UIc+sE6FlbSMKbyBQpMiGIsrRZzSEo4ESW6hnpc7KVVzTImTtZzMXOMUkd38ELz53Qd"
    "8uvOmJqRWE4o2gw8rSB5fqRKob+EPgrNql8vL6NqJ0WDSTFfYi1EwM3nfyoSYOjzcgl/6NMi48IC+nFSlMJjEWJ+YNeoxnDm671o"
    "9lbMXlsZ/Q6F0iBdJAC1icqUcrkcWh4G2RBaFPYlLA9KvTJMLCx78MNTjsxnGBKz+s7U9us1qw18QBfNdSR6oUOFOES6OPloJyAe"
    "fXOtvBQ9oRbJQ3SPFI0OXkQNrg2JYMkNp+S7E2mfCmgqKB+r8VuPmVAIVhGDDahWnznhncQm5Nt0MgNcxc8WW13wDSXOAMa2QNtA"
    "AB4vw7U83STOS87AYJGzGV70YmVRpDvaK2PeMmQ/WnSTh9GSzh2ijB1h3t6oLBTLN7e+xNYHqhnmnguY6WGfkrG61sM+nRy4QqTN"
    "TRxlx0/ozJjukd90IapwhSA6RnvK0kRclwoln3DhjIVIXIekZgtNKSyRvohMTu6qunwSTmu6fKvTw2IOQidcpvDZGU3jy/mhSB+y"
    "K7PISlsgX9HVyI8MqKOtKjfSwsnR9EMkYjq9ImkB8B6Nl+dxXSQv26IGkGoRqlqgNCJpXEarQCpZInjIykxaB5pITaUacstRj1SO"
    "ZGtlihokS4HR8W1Kje8TXOUZqx9DUj8yRW+8d5ub6d3ZELuzuYlWjupHvmsyshJf8r0NDkqbmxy46nWfmfvAVdgBCDcsdHzHwMW3"
    "XzG2Po04ZAud+tDL/9+fpzDZv9AiHW8VgYm5c/v5u7/8PhLLvFbEa7HwUcQ/YY7XeN6fTc07Uuadsw3qPCM2T5gjDJutedawgbRn"
    "w0bmD0XgIk/AfwvDxJdOv/DT069/HwrcfePnwq7xF3df+r1e7GUjMYMO7Shq4Ofpg+rTafcbS+zq8JwjF6sVCd1+MHaT2CDf0K7Z"
    "1VVqAixZkC1hWpMVayuGBJ/BcLt+pc3V12w+ZM4mrdkiyfOp5ePDM8g4PIOMw0PueKLRcC+2DhSNyoPUzj9IbX7g23SgzliVhiDi"
    "0xR63AigVN3z44AUbWtA4ShEZ0WvPjAVH3bvSr0CFCPDSJ7ESG2BkZQBcuMb7DQQnQZ7wpRg5eB9TJqSGLyMJeHsCSscX2B8HALr"
    "2EITGm5U2LR9gVBx6JubLY72obhoGdFaxDK0a9836DXe/GxkvFw8VD5ShnI2N9EgiEpImyAGIQQwatFG66AV53CzW8gSS8j+VEYm"
    "TrTP3Esl3kTjYWkCM4HVDCZ01DBrJgyhOHKs7TgPOVYhi0z5fYDJvA9jXOk3mqgZZQxZKkc4SwKakR6cRfWzDoBKQszkN8gCyS0/"
    "I5v2oOnHm6R0jVjrAdqx+o2PjYu+5Zn2HPPKc2MvfyqstixHSUHKLGJM66BptdYZV8xdDaw+cFcHBwFmJbW4BTfya4cWvPOnlgEo"
    "3Dg8ZIYvg6Q93rQ+IDLr5KRizeqOTG2KYEDn3NybCT+k6RW4UFrMgIi+WZNuYHd9WGpmNwWEnGv3LfLts+K2hqIta4pOLNKvXU5/"
    "/hiarANdFVl4qG3PGjheaAcxR9cWjdVzy1rpzUOrbMAAaCFVtaZomSvMs2LrelyVvqkY2U/SRvaIviO3MQQGxa0bW4ol8gBO7uBB"
    "OHiAKBE8n2HGR/vQoWJ6dBPvwEm52W8xm1Pss3gTiz8I+Id2ZlCnZ+smlpII4uREPg9Cd2xQ0f2Tk1iaWPJaD16sVOJt3Ue/Ca+l"
    "ZLVb/O24SM1YchU53Qdr2WWrOGKr+PSiLstY1+oJ4/A5NGc/jd8bsOn0g2082ZzAeOGjP2Xf/Gn8id9e9qgBN/iIgtCNXRir3W1c"
    "Lx6XbzZQHExvSB5MUUf3rgEZNEU7ufo1K7UV6PYQjYbcfJ3Z2V8DDoz5MtC+4nYvYmP2/slJjEOe8PpuMIqKM2sXli5OLj8rsgQP"
    "c7TAWxD6SEOVQEl9BjzH5X7QcuD89EWUqiZ6MA4jnn/aQq2HE7qOxXOBC+HuHjl5i0TQw6YzANw5DxtFjnOsfhn3HHbiYbftjHro"
    "KdIvo3fbjX7fbXmwv48DBekAPQGLW4Qb6bj8DCwY/I3W6NK75KzN8MVY0PAANbhOhAll4b8IJ9mMwt4n3Bn+7LuRw386vYh+hbpr"
    "0BSVGdcf3dw8lnlziTRFUqIRCZZGWNrN6ldmfEGO48S6pg13uLpWvoE98od9w8yYYAswvRWpzvSJhNtTui032BAOpocxPb6BmXhp"
    "JTfSO8r8Vy0H7g9AdXXgdUeH/HfkHB3C3mYMptstxv0QQXsVSVtO7iofLEZLyVHHw74ahsEE04erU6eXnxng3cwHHJrzdP8S52W0"
    "1qji4iLGmtSnWzNCWXt8TJND5CL5T7E+e+Zkqz5Ti3zKTcxlwiYZn6pW0ByhVADtJK/j0B6FYq4PRA2aTrdwHNbAAoKbzp4szWjm"
    "pRUWq49nn/svwrwrSdhM7m+jLD2UgaWakjG73Poy0u2oaNPeIQRwAICj1As6h1gkjWloaPFCkFrves/FpzrhuWn5qDcK0asZprXG"
    "ypG0cP11U4szvLbEa5Nmakmn681NY9gNJugcnQ6+97mxpdzIgf8YLIhdBKIE7npgHYrzqT2wZkAUdOgmQMpAao2fUusqXuJ9x0uK"
    "c9iruPMm0FfCD9SbsWYcTAiPW0NO1K2iiMcMBaN14k58PDEcoPHKcPf1iyY3mnB5R0tnOVXCOj+w/uJMuctmvmtqJ8c3lXmdwg65"
    "eWlP/QbP6nf3Wz/KSbnN1WFJZ1RhWYdxd3g0k2/GkXVUn9WcNG/QNdOtZnX6ChdTixzh0pmVEbHvf+9FKPDu29DXb2LfVozM8Xs2"
    "mP955w9QoAAdFFCo/6sfw2D1HmSrpFN8k0+GEpoLN8bYuA5bT0R6B0p/TpAgj0KeP3BHjx3Aig27lDuefJZl3VCAa4SxlCW8Ck5D"
    "jx7xsfEyMWAAXFwgxYAW6qWI7QxUoR+3rTclr07KqUjK5EK8YFFDhbxvdNDbAp5tWTtSPCUoBWJvQuRsPMXo/2/VkcOEObkeLuo+"
    "86cD9BoqpJAriV5zPuoCBO/Tb6uNt2dohXidx5SJq5DEggsLtbVpwdq04rUBlkyhNFo0sYhNrEUTaykL5NSDK5WGdxAg/xo8WGkg"
    "7+sdxgE42PLktsKWR5EQbDj63dOEDurUw6EoddUXLTkKLYCxZOMvTSEcsz7laqXl0sRyF6TnkUJHQQr99qc8gi86+lIoxK/CyePn"
    "kqdMUMJpCT4SNecoA3yTzGMTxV42VB588YwcVY+PlNmQotLVaLB/mKUTy+aD79gPQmAw3wXSIr1WHRjloE58TCUWMI80qZi88OAG"
    "51fpQ7MbLbTcZqbldDrxCuRXIlAPAzI0QyVO0G7D9Uw2PZZaFH05ZDnlILa6DJxhCRXmq9d6cKci6YqeynVZChBLGQSJrbk5D0k6"
    "N6SgVoiSUXAXi990Qf/mptK3H1xBySUwZWqvKCulLUqmZ3yejI2fe+v92//23vdf4QlKk26WP0kHJMCYQ6IKqYa5GJgnDGHZYlPt"
    "8KhK2OnPMRobagKh8Ivvvn379Hc/vvvFd8TAYvTLBLEClGj722jihDElXdUJOeUMvQwp8riceiytoB41HoqKkcXFQXtBo9jxuQ8P"
    "LiGD+OS0uAw6EDJoXWJOJ8G0aQMyF4WyS2Zfg/qtq50pcaJVlySBlzOxO8fkIcPkoY7Js/E4Ck4ZQ+SponsHxRahKSoyvOSk9BMx"
    "ytK0E6lFBpgPoItcVYWmp7j7xm0K6SqoFRFxIBfm8hUZAQVV1hUZYg+htSRcvg5kA/b+0j9xpActS2QYN/46D9BsWheU3UJo8/7v"
    "gtlbYh20xKzSuAqBDeOGZFRMnfwEehe77akX1Kdc5aVyTD83RrGeS7SvJJlVJfcxKbhvUqyAYAAX9PVi0VPEQKqLUjI+unLHz/xi"
    "y5ROTEW3geQKS+GCxkNwlz+F6aSaTORXaDG20OWJGLj7ovTvNuePD6A9S8KisrE9loDdjEWF7ZSoENpDM1hnZrcWpMJKaN5aWXtK"
    "Ib+vF9ts8rDtBYS57/zgvR+/Rnky0+lqudaKh9noeCJCSrGNt3tbC8ixiDlxwVs4Q6+VSIvWYa/WCB/VmWSlT/P6aLQ7DJv2uGk5"
    "PcyaZU3IYrZWsXgumVolLybO41cffviT1z5R+NjVJ64vz3hH0QWZJv/v0PFKGYkrqfMsuygiYzWrLTKvit8yoyyyw0KSPThckRqv"
    "M3SdsNnNZcjY13jGJA3kcdiegTnMBhjOCukD3RBLZhT/fRrF3f3hG/d++y/Ax6OdXJdIp7XKI8K9FvQHGB7EJnM1i7Q4cD08g6HH"
    "uo7fcW08G/Ci3hJyESpjhTLgWuB/wp2h4IiKthLCS4wlwWSPooYlW2LCDQphFaKoSkBBRjy4qQzOxUZPCXI/z6gJOCnQGcG/FjAt"
    "0e8iOzLTVCY8ctF2haJwpDJKpfcZy6VYu5lMFGUwrpoMu77ITJLF6lIf8fo2LR184MRQkkabjwUNU1poVDS2WxSPDrsuAdLgCzIZ"
    "AmpqGO/+/ovQpQFl2ABWpMIkBNkoR8HxyQlgNmok76REASEwHR55fzzQuRkLcDJPRVeP3ayDJPADwnJasbVge8DSfInT4jvp4zZk"
    "UfrYr9hciJKeiLb4GkoELXWaLXbrDgC6VWoRA6Tux2xiv+51i/DvtE7kOCXT2Jii3jSmyfczVOL7aZW4NalPRZiiGWbwUNXWDfaP"
    "Ld8y3yVevK1piRuxi0zs/plE6fIksb3jOhzD9hv8lNL8G8xJQigjdakfLKpeenPTwCZh+sC6+dImDJffZuyuegjhsuNrzKD1OjxS"
    "GIWtW3+Fjo2KMSPwEUvJt9fpqL+qWHa8fgv7CnzEl0RJwCbM99OydkwW0ux58O7vLPHrc4w3zwgYedXFIIaTZRFLfTWSHlBlLXPp"
    "9aRlS+1bQLxYg9iQbFlWZLWfA8CbjQHCLAZh2KJ/RVpf40+3v25s8Y+Y0enO7TdIZ2ZN87MPYl5LNSEcLbWxWJHlpZgCW3OZzR2V"
    "UA+/5BsNq50w2mgjTy5mVLj7JkbzNrbo7ZZx+tKLBscGGwCE7YTNRP4I/KmeNA3oa0Q2jOQ1LEVv2y6P/MjrAUhjZ6meOHuTI9Q0"
    "7r7+/PuvfV2uosypy+FsOYJsB0GURWhlxkY94oFRr7U7+pV3A6E9L8F8h6IIMiGpcbg8/iqefOiFohLBQYe/kYfEPvfdSFzFDguz"
    "qY1gf5g7Ah9q4ghOv/Cvd9+gQMkWJ56X3vydo4LXxJfU/adGXpSO0ykRBUWJ+jEGjcdo3C/T76+J1B0/Rq4OZQ6SdH7rvR9gcHhK"
    "1PZVhYwWM/rMIJtmGGB0IEE3aKJZIj/naigxaV+AJlsh+XC5PsY1Rit0jfQUKeP0NBy2UoqdDGl9j5lG4DPH/g2DR4KExRAlKH+i"
    "dEdn3APziIpjlopLg7TuutIdkPQt4EF8xjoR63nb2Iq2imJMjVt/9cAcpWoBnBxMK02hk2BL3ZtkIABU17u//48H5nAzNh3/qf5Q"
    "nm667ovyPfo/YeVHvKnbKlahK/KeWmBVgIXoKSwnqj0eFpW3ZBpwyxbD9Sk1NzZNTqUN9o572qM7ll/2n0ID/SF8eu/nv6I43xQR"
    "XJG/FLAOL7ZFaanJF4tz8K36HI2/iX1X3OufQSsmsl7K0T9G5P2n2C2gCBYYWQrtiJGEg1YZG1bCQC408wWMKSl1t2GW/VOkCh7S"
    "5k+hZv7k1nmHLPYducJw2MyJg0eLHk5VkSPuXEl+ebB6IZcI0dELpVM6iuDDBsWBhaVuottfEp2xs15EdVXKjwz1Nz9VhdLsNwsh"
    "gSzCc/905/kvU57iWOhh4EF4++7LX+IKIMzqe++7P0KBJJy45145/dcvUlldm0V+fABFBE/0i0Mca8su4NuB64YZXHAW4+knOEt/"
    "hcH8+7d/cPcrv6NrM4tZBtQyfaodBn3VaTazKd4SxbmnhMZ/fOPer74hnP0Us/ZJVAeeIwHjfz9m4V6XgblPYP5ZOPwMstFHaoKp"
    "/SIFrAWUAJBaHI7T+mzMXBs0j0sD1PP6TKXNC2cqtBPlmU6buia0kwHUrmL0pUeq/VSnuIFVzT1fhtympvzYiuYIt/H07bdRlfnG"
    "7dOXv/z+P/0LhoqOpexCyqalxPgaKVpe5ZpI9RNAH7ooxoF7mTwx2YVkfhUB4IVKxTQXZz58OCVG0vML/nFcO3EKXXnVcrFi8m7N"
    "nzwj119ih4i5j2FfIkWnyMn5TTxEMMu/0tYBc78o2b2VFVO6euvdt28D0XXv25+nKMivoQ769nNUEtM73Pv519Preef28yhOKnCr"
    "b1Iyq6Onl3Hu8Fs5tAwC2IKBVsOQ9VFME+8RTU4jDp5SpZ+LWH+Lvt0hRf5XmVAPmFBPMqE2JeREx8aVqRw6R06o0pL+evk1EiK1"
    "qBTpTI5PaAqjaS0RxEEtjWcZoI8E8itYM82u+JxdEQk21hqL27helPJcMy0n3DjGzNL+kqDqHP71LGgxNQnw8uKXGTUm87kx6ZAm"
    "LFzqahT3IBhfrI2kicmkjjF1Ip9IcZDNjvLoMHmiUm5OkUlAMi84hYpKjlphjd64DXQ0ox4LhgV0llbTVJJrWegfJc76W6ev/lBN"
    "p2yIkP1crIaqVwXFelzlKYzUMRS1ovZsLGV+BOoqMIohKW3gonWOttR8Q7kKTpHZk+EsiuP0ou4V8no2B7umsjT7xlabeZvhIh7x"
    "gq5cs7hE/jAcGMQ9oVzLY7oLT4VMc/UtEEMouweEHxwjnj0FPD2FeL71V8l0Of/43dPvfA+X8Od/pJyoUq30QyIpXrnz3A8SSRMz"
    "VRe3VnORyYPgMQSQvbi5RyF3TXv+sZbTITExvjsWxqOIlZmh5cRpdfv1K49hXiMA9j5z+8bCwr2bzGS1l9yZP47H1tTa2qDGzDjN"
    "nyfYrPnCateLrfLRaDhDpgtlQcOwKR5JnAnLBL9XpuQWxADw+ijudmBcItdhqYkivhF6YQ7gF0vDrIEJQEOWthEuewrdQImPzz8w"
    "l8kT3/3d725tFZs8gaIWZoKSD8J3nrAIIY3HfvvCT9/9w9dJNsjBhlH3UAFmjeJrNn+2mPiEXXosOgk8LqDHNsCxGhyEpY6gNMtE"
    "m4mcoUgS5+YDJdIizgGqBRuRUMw4zEEDzwn3SMYsbIw9XYczAEBJgvYwAdsHDkkQA0WCyENpiByfvjXHYCuiRMOhiC3i0a5oGoco"
    "dJrUaXu58+xwdFRLJmlJrqhhtXE4A7WlxF3uJjQBYpUAyA7jA4Z5RbQLI1QMOa43i4HJXY6RexLpPqXPU2XlzWyssxfYOC6uFvEj"
    "E914XA1SXDbsazjsONDb/Qyb0PUgK1NPEjmqcRdzR2wZE2PLY+OO4shCycta+UQWc6mwQF4cFsiTYYEIM5JqpFm/4iWDFDVlkCJz"
    "JY7ic4cRxMQUNZgnaRwS/6fdl4xez+9Cy1Z24FCmYZZiNI3fSAhl8TGkA88eJpPUyWYDy/gIyT2LtKTPjFyUs1XMK9UzHTwmGIch"
    "JJopVQ9jOGTr8cw4zplX/Hv1wScrVI09cVoUHlIJcSITZmPSbdUBDfnqnuKqhdV8CzlyyiPDjIekq9cxZXaR8CQ/7PViBy6thcrC"
    "olk95jVDAKfhMQEknSI0upTpgZ36FYe1DlcX/QBC0sSTAP9aAOVlf4Hp18h3Ih6PX5cOkikRBlmh6r600qMvYbof0jLUdispeZso"
    "5ZGP4BK7emM4cbTTrHJ/Hl84Qebl5nWaDArBKFoV+gwXgxLP4hrlZokCggDaw9RbYrVoT4AAIGWfAhuWq4PPx3O4Wz/26EFUENsO"
    "M8PVpmKllrTag+IbzVgP26tHjVBJIaKYKOuGbZndxKZtgMW4XSUa9Ta4vzyzxlqdsa2DY7UCqf9cwzoGlnKd9FE9LcVo7LQZW563"
    "ELajBlmJ2kZJzUvXWJJsLFgrtZtaClYTeu36sMrMizNfF6pW4xUCxsgE+WOKokJbd97Q7jHaJ7p7V5uzCREY9hhqGUUz+9VYfu7f"
    "oBk5J9TSd26/olv6EZOI5lpfKvzPO6oZ9Nv/884fWN5ge93uP5hJqDBcWQZ3BX96dHbYQ+/gBNR5DWLSbbgbh7ax5aRB0FsKgoWW"
    "16+dGQ7j445h9hlIemcFSS8GSWcZSCbVxJmsjWF92i06qrRqxS7/6fY3UjuVo+g88jqGULOi1rrlDUkbY0tj5c3NDY6u0HoygMvr"
    "MwObkhFwdP2EalqlMdXcWJ2TUEEjx9A0loao4mtMvl3Y5xEC+XnR7GC5zoXbMP4YuKX4ZOTaymoNK4sfoBuIOMp8vnnjfe5tAyfD"
    "9e52XqmUUAYwpifaZMfXIBsIri3S68et59sAC0Kb69u77liRNxwftXSBnbE8ASlG3tOA6MWv/unFrxfQRem5/7jzwu/JZbWQgZhY"
    "vHAFfxUoxCN8+BGGx0qQfA+sY48bByQgD2RPpfsAB/gsM1RramfG9sFw7Mx5m6RUkiaM5X2it2k9EWon5QDMiu95CtmoDWBKnU2v"
    "1ON+4HXDQMVYCf1J6EdPBlYMElMxDKsvkpsseICFR50ZEFdpLddUoWORaJzq1OKMcuVMkToPZzfJyTsIr/Z66B8aBpNh4UqBfhjm"
    "oTWpB9K/HrNEKZO1uhnJtkZogi+X7en6qIwmWECdljuotreuwRvmyvJEMMDBdSnawtPWNdPa2IezNSn3KfRHMu7DzTp+QcO4p2m7"
    "bnK92XyU4TcjYoKNNLeZUdJthhfbE10tbsK+XwMec1SmrKblKHT8oYfgWOdxTbUvMO1+/Rb97AHr8bniA/ObpWuLwdS8leo63WBW"
    "Y/QyMcp2zxuga0+QBVp9uysjVBw4VjMdi8NqaWTuVKU/pzzIhSRzyZyOYv2uALBWQ4JYQwek4i0CngMyvevUjQfm127eLLtkcovW"
    "aMbhLR7TZFafNuaY2kcChNWVT39DJtgLRvk2MQfUZHNztrk5KSMAzsr0s0s/MVDmBBOdNSb2zFTidegUO6ZvmsYU+wAtJ9toQTkP"
    "7YE1sNtCuDiwXFvNRnStWZxmSEcWq7Vd2H1BTdjMMt0ZVui27d5axut6UnNDepoyTl+M2TIA6RuWT2mxlmiXKLN7Qm+6Lol37/Pf"
    "15PTJyomk7/e+85v7/7jj06/8COSs3OBJQ9spWtQobXTr3yZRcAlJ9pfVOna+/ad535I7rT/pRlJKHcP+smsM1a1v+e+Qf4kv0i3"
    "zChkdK+jrFZLbb9Clyek1O26u+Jo+RY7fTJJKU7s+a+dfuGFrKheL6njh7VgC4HjwSimfL9Q+fwzWvNfs3jDRA98V21e6N5/LCad"
    "bDJfeWTA13vfRHs1FskYTbQAxpQBv75cTtVzO7rZ5kGuNk9jqGTCDrLAE4lWALj75TDLBjW7FZlmBhqRqV6oERTewj9ulhBzbVEl"
    "teQeSndrn0UaJOdHJY1hbJcfzCzAK2hWx4UO1oavRytc4ThfwJzYiDOg/vX79aRfdsjJ1RyZzDUZulyX+eylaBj3hyH0s4qjpNTS"
    "aA/EnYAV13pSLr+5sqMPzZl/OVOLEhgkoDAYpyDygOpT5TDOEuQMN7DHEmNQRnVJFdg6ieGUZ4zE4F5KTrm7yJSvMTAVyW55tjzW"
    "+6AroLMDlClgMlvejI0KXH6CRp4CZ2t59gxjAdkbwPhQcJxQDY7D8J14SRecyB8qqXarFTode05CdoYo91laYyq2sIBoC+0Jex0F"
    "9UljZs+ApWaZg4Tsk1UxZdQrPxmOp1u/0uUEKi/LY1tRq3uTB/c3N/dLJQuzAgskzQpa+yb/hUGY4H88PywqIhhhr7Em7oyxJnx6"
    "mr2MFdavF6PyM6aeqZMH5gCWRWUkYEsfYwJUL+kSfJ25XaoyfGbhUKqJKLCooUj0IiMSh+bJyaddFC/kFpApCjGshweAECxM0/wA"
    "RM19kDPcY+r2K0CVyOglFrocMvqmp9M3+Rry5N2TZwl/fdgswLmWRg3sQPdWyeb4sY5lkOxIyYWzHHG0hsXHs30TUH9dwezHTql6"
    "WJ6iQsBc4sQFQNJNzkeVzmhkR8TcyTp+0Ut5jhAUAEKi8Ki3ybTJI7Mnim+TFgscKgFvVDQREJrwlgjBJdYIGNZwONaIGNaIsrBG"
    "pGGNQMUaPukBec7LJSIt5bpcuf2UoeyHdJukhZWc897nDBYsTxTYFcXCdNAt4nLAYvi0GBFMMqRJ9sSgPYbqAqmeSvJklAC+LlzU"
    "GRPnY+rYaxiREbiS6/Rvv9718d9pLAYYoP7oYGZNtPbQ5TdLUzQVNxAAGtTc3BwwtXRwjNHEJCspFNXzSXGjIjinTlKdNMFuLAzb"
    "J9BD3AK0a6W0Sx3M76yUWFgH8Le07t5PCG4y4lgCqo4ZTIZtbvhR8LeeOynOj3pBE1ONQI/uEF03oP2ebL2rtC5iRWZ0IeYqy6BY"
    "oQNXCO9WGYHA7+O6fLU3zpA7hIDR4dia1ljj/sdJll6UW8jO6h2YAhuJnMcI46rHzuOd+pUO20OydyEMRO9kWPAT6PlpPUgnppsd"
    "NUbiGoES9gFmrT24Zt3UZQWssJmrfZTLlduqNZYfUcDUORQjvwpo4mlJEWEE16smiyD7dDx/WCWS+8xvFsdiBa4mAfGmHKdVrVXy"
    "tZtXTYyGOEqpN5Hv3rdSFFuhE6JeEQOHuXCptRSXKmPgDCP+CkUk8IaUbH4cgY+lwbKOy7Srn3BnQ5qjK3wtfZ7hyBDQwdwSKfkm"
    "4AD21DG4RIdTf0ap5Bk28wCDvQ1hvuTQzLA+7Ls/K3asGImYCX9DKDHvpP0NP6UiHrgWih3pftiR7oc+v0QQlXVQyg9IHNC//zA8"
    "3yQajrWOA3+CqFQ3LLsEK1d7PaA2WnUDD4RB0acT5WBHH4bnIrmSnx/0KFAa75HHvgwazB6DuXBjr59EArHDdeAifPFeJy924Lje"
    "SSgd4L+HML8csIjXaJafRsA2rat1Oe0Hx0ArDbbGZUZXn6/tNYtXG0aEOVONowBjOwVlpFQRuvi4HnWdMQuH1STMjm+BZM1ZfF6m"
    "UUaAiSd33W8pTTBwaD1r2E6cfz1WPywzHQ7RemidJGPswqfyym2fpe8KVaKK0l/J4oxZbi+rHjbHBWOrzSUYj4wP2odxa8/iI7Hm"
    "frCUK1JG0Cdt2Zrer33SxS0rHjmdtKf8Z8bWHG94lubi2vIF6jiDpaabGPdVXX+JR/J9Xwder1cgHJOtcLdbqdyRy6znk2prVSdm"
    "HK5yqc20QAOsOWiio/CxhT7XaPWVXiS254Ny5CmeigNM3w4VB81IeK7ohoH0KW0EiNSd7OFv2AZxUhX/QjYP+EaWQF1mpJgl4y5F"
    "ASZhZ4H8Kf47cq0dWM2eFqgqLEcP7lyobG4S9nWOKOULQ5LwbWo+eCnj0+fg0ww+mXM+ECuasZiuPCALvIZRw2tbiX6FiimBf2fy"
    "9+cWiKexcsxzdrNjia0veneZ6P3PEWssmslYY12kWKwNl7IMRIBth9JtD8O4oeTlhddI6qvZagsfGi7xUSMm/unFrwF/KKIqvZnt"
    "rkSJIZj3Tqzn1WJ1XdTDviFkYLQ3ZZyto55Mm9Ksn3+yXBwMomnjZDAY0t9RH3/2TUwRNpzlFzhBFcqg1caCMTSGXGbgRIBaWBRF"
    "VZmZUGQe9CxPI8+A0/TLUwvVPjMM9lI/9liosXIHLYVilQ6+WK68mdVDTTs407WDk/pMA4B9+cxUMla3TvGrH+kFDhD6boRxWkaR"
    "27qJhEtxlhGBdmaWnw2CPtweVXysWiPhH+r5vhtSP+e7QLqqb1lv57t7Hk5eusJfsiRNBAsCtUalSekSULSznDIzbLm0j2Vg4WaJ"
    "EyPj5zbKbThTQ7yVD3CloWJ+MO1ZvUtBXCSDghpEIGSGxS4PIIOx9bGtCTkc4uW/v26dNYLp9tG6gsUVni3xUURLC8OaLCkBRxlo"
    "biqzpDsh7NmXwXvny6P3Zo4vs2RyiJmFskaZWVAb6EL1J8bMFMNGMl+Opr8fqgEwUxu/gaHgmpubtKsHAXD1gOboXYbrZqu+gd+C"
    "OGthBkIEnp9KXUXja2D8j4HpLwJ7D5AyX8TipEztE0Ya8Fr2PgXyFJY4+2X4KVkEhLZuggpOoPKuh0RtMuozAitG4bcuVzRBEnTW"
    "tGbWPgoTsk1H4BOTp03rM3lWJmRtEOZoi8nsgM3Q9oOoaIvZmIgpDg4PyepACJayA1Kbe8VZVuDxWUbgcSiZIstnFF1eCypvTQ6K"
    "+1tZzTaq9kQmCzHNj4iHQ4lAsMFUoKk1u40w5hTCX9OUqIbsQZsYnqe5VlCfNUS4GAWcKaFDlgPDYG8479lz25HdAyQI44N/Z2og"
    "rSkT+bLyq233NHnvp12YFw9dkpiLEtNoc7NfNNYItxMnTEqYeZHFFoIyJbWClZt7TTuTGMap9G+6w+ssrfsEu54Jgy09VdPrSzM0"
    "CWfo/AJsRJ9NjSiWvT6qjujTbjBwyTGgnxc4UVjDsZY7PnNcyG5bijhF4p/G/zpwDFdBx0HXR+cZP7CMgmHxByiGCMXZkOKXOFYq"
    "AUrazoytR5yhK1CjP+Lus5wKVhIoKNKP2IJ9KC365ZIg2ZliT7ikP27PvRz2HuYPqaMc8ERjfYwsmg1LqR6NVXD1aXfIAt1sDCjz"
    "hkbRUAovQDKzxiypWIPzuc9RGhPHYxIGkYJkc3OCVu5LucgJXoEwlSoZdHyR7JFfknpWeV5jxdyMz2kCODY1qRGXWkwenKka9VJV"
    "6eNLZ+hjK6MPIl5EiPuk12vazcEdsKN6cwhQmxUORLIqqYgL7Di/w+1Xsz5J/ojN4Bk3ue8WD0ZtzeH2tDdaJycbbSsxoUHPmcUI"
    "psvAW4J0ZkiD/O4oMPbS7qgE7RLiL1XxvkbrLMS2bD/VNvuuCmbyd0SYCLzwVVxbZBK5xxzr/3hYjN3f1YTOT54/3HrgvMWzpPPv"
    "ccLXJ58ElgH/3kqpaZksHgvY8LzFFVg84Aj2SXxwcjiavwAjsrFc/FlzF5bhhTFibOrQB4OZDruSC+0BF/qIlo/aLVNIRyGq78FV"
    "3Cu3RG5YYEOREvWLvfLA8soD6C3CXN7BoFGGdYhYeiilck+y+1ZYzyB6ZWyVhMY1wq/JwGNRWqMXHQWtmW59gnqQnuIT2FNywVMe"
    "c+CWMUdOD+4NTDLu6UnGvRS9FIUJaVePR1kTNkYo80J1c5aDTdRKe+8Jz0BYRLUKf8HGlS9h1DLDssy+qh6aNEKY2cjASJv/7+nb"
    "b9194Qun3/tXiiX05umXf8388YfR5ib+vaHNY81eWRJipVe2HsBEQKfv/fEPp1/8niHf9gN8e/c7v7372q+RJiLLPmZTJoZSv59B"
    "sMzVihv8q99694/fZzJRxV49uQH+qJ9YMPSgfAY31cyvFSUqNT7pQo0+y/WVV6mpWUFwgGPWN44E0KYAUIcSr7fqTUy83gQ45bnX"
    "2/VWo5XMvd5K515vffDc620ZLk/LpY79J3KpbxWB921Cjw2j8Kfb34C6+ECRxyxHZFnPWxfNK3hDgfc8euHhZjlCERKeDwEfD/nY"
    "5lBG3SOFP9xjPBODBWgNiNaejZgqdk4J4oB8y2/W7GB67NKUM8sfA913q8awtC95Y3KptoWTp9z1+aYPZM7L6XIMMEWh9HYG00Kl"
    "cGkwNRaqBuFnv0vZxf2E2XTG14MnhJSZMkopcmSeDpinIEP2gUHSYwRsefUiPlNi8ebAlO+Deo+AdzScAfQ+jiZKj8PFGRUo6MLP"
    "xM58XtoFMvPgey+/FIdNFKZ7gGjoNvw8fn3uF2hQ+Pwr6P3//KsyYpJhezLahaeEuABMpdV+K06/84tEXAe2YHduP58YGUsZQS+/"
    "fO87v82QPtt6J8lrX7FtXs27Oz03BLzIODP+sFZgnri1dChPI5kBXQkgwaLOfVmxVv42KmxxAOgE+WYBnyZdYNswLjz89i3j9Dv/"
    "DJcP0rSH+YajzO/NKmZvjBK6NS/SqGYD9UwiL7VCFusRtg+yyGJD2b7X1UEvjfspzzUHx3hI0YqI3vGZe8gvYoh110LE4hM2iQCR"
    "hAyRoFmXxCSecJCLG3cs5CftprQ3alntlL3RIFYvZBjCpIwnBtLsRRGg9vUUpC1pOcSVB+0ie5TJ6lioOtiVkGy+YFfIysvqoU6s"
    "XZzyIIM+JWnL6V7+rGdnqGvT9KaN6k6lYlNqzMSlJ3ePr3BM0wGQBgBC5D0+xJjlZtY6i+3sc7U6oStbTj6toM/XpB+VNKdi2cY6"
    "OtwVsSOaDUNDSYRKWARWFuiK9YbExNqdNbsUeaXJEsWTfypdRhJugxkzhkv61M9xt5llC204M2tZADuAiH8N81K0IeeGpfz3GpKk"
    "Xm5eA8ktcu8YzC33T5RXRITQUHhf4s7XsloX/PoHNXFfYtRKt/tKX5c3T3/4GnNcUfwSmHkqahEtKziMxTwYU6B8EB5azSzmDLkj"
    "Z3OThF6UcwH1GI7OLjloq+ggyeow7urkxFEpxZUb3GsLor5tpH2g8gKgSBZKYaDwaakxiEb5P4MhL/JLY3AJtPPiaIkoaKUveM8C"
    "GZHBi6RPz0CdRgyhK3Rh83+ZNl0ygnUpUyuV8M+ZKfnRjy0UKDyCkaQbH6M8q4ALuLdfWMe8lpubQEVGqKWmVLkMu3CYoZy9IYX6"
    "vXn9UcwDJ+yCDcC0G5/yeYOythAeZKWHablRhvn0WsbDy7xr0qHV2ZFkKRqf+4+EL0nOzgKWeAPjiyHG+Ond3/z07udfvQclgdRS"
    "goEKW2z7bLMsjmbW/BGgJELY8I4donEsWzdujMjWLt7B5ky1LDk4VLx5I/Tm5RIixYym7DDqn1zhg2NzToY0RG2iF9BgNOwWD4z3"
    "fvKDu//8lWScOwu9IwYmZzV5rUPFB1dwEVQuHcJIGZ1H6b7KY1iWgKUpLx8DmYDYy+0fAQm5uVn0hFDCGw5R2gA0phBeHA0NsyFG"
    "CwWdMb0etbwAuIL3v/ub0x+Q/OJL37z3jd8bGGEc941MTJ5/i7KnvGJYjGdWt7mAUWyGXApoGSIyOcZkYmp+HALlmTg0ba/c7kcY"
    "YxL+KY8FN68s4umLX773je+KRfy5GsmS58YCzoiNcJ2xFFlPk+6MewPIZ2TlDzNWl9bjPldXmQdbzg9/BfeA2PeC4bHcSCNpWcQS"
    "+8Xwx/rjIR8xqOov7zz/DsUNfpGi/slwGhQB4vmfk5z2LbhhRXoC0waS1g8oQzETfwqPvswx3Pv890+/+F8Jy6Wcact248kfwklN"
    "nkdd+hrF1zccGTI45M7KsB/KC7zRTW2QCdmyHlUc02MrQiG48HlbhyiqioNky8CruwpOGTE5M+AgH3CQFCIchFZP406YwUE4m/PW"
    "KOfCzSgA4tRFm90bgHlYfudyPwhdgyIlVQxuKMyvjQpmafLqY3QbQNtxbE9raJhuyBo3jCqc7oohrY4XVlCnIEGWU3+YzO9I0IEm"
    "I0AuPYHXGSUNR+YyQicOQpwY7hLadPuBJgqHwWyMqStkvyKgPPGz1a8PlBJjIeUbIBeT+rQhPs3qbM/R8s6a1BUAYGYsWB7GBk0h"
    "iQ2XqlIC5d/76FQCQ+5mEX3WqN4lI5QInQduDvHfa0m1APUApN/NjA8wT6Qcx0ysN2OU0Rh1BVyJMLauMiUCvLSukhKhU59tbs7K"
    "vjtxUTCtDqs/6kXehpJyVRSzb/KDBvOsNm7CxMoDwFoJgnMJZ5N1/7e6rbX4C80K+SBALXUzdgm4b1te1kh29ha9lXQL3IRXE353"
    "azxhW6eFVZVKQcIYOjXDo5luqTHH8rZjRXY7Aqp/RZKYIGMVVYp0EHo8fBDpHpOCWxJicBmMEjk+plRHnFLtNkaNpxvG49fuvvLc"
    "e//9jp5vE6mmu2/8kmIHkATvlXf/wGRYlEQDvf4pleHt51IMGY/4Sp74Sd0tZo5Fkd0SIv3Lcf6GzAAHa9SVCS8p87eCnNHzmbjN"
    "iJmTieToWO5tvegrGCQIhZ4oGFW9pZFVjaPavpJOm34/FrfQDkWS54LkFRK2pzc3H0PsulQ7nqcCVyRyClRxiMJE54+k5PBp2Fmm"
    "64bVT8mg9chP2drtvDE9AshLDInhscSgMGgJ31A9IEe87lla8xwoWTLUWFnOQxdsjFApJS0Tc90qgShUY5U1DAWgWDw61BWxPd0v"
    "R3J5n/sFnboXdUf+V9Jpmin607+QlPyrFOrCzujiQwBMmPOIaCNSQ0SqGoJu317LWL4MhZTqUdNFaGc4pU1gYfxinUI6Zy07HEty"
    "JsyygiQmEpJyhLiEVeWnT0OQPxF79i3JduahRpxM+uDSCuO0V6Nd2MmldjF/YBm6KZLZ8iFmjeNNdaDaHKTNhIzfgLmEph4QR8tW"
    "ne352dUsKS3LUuVLRraEAkHJ11OyxFfynJdzZROnL3/x/dd/iHHXFB08qqQwgvh3FUZSPZyvy4zVug6Mp7PWo3OQaeS38haarXYr"
    "GRvlz7vcLSb75ETnGdZ+DBRl/mIiQU4SsKsmn1c7Pa+lPlQZNkpNLeQmoUMKd75kCpqhZj8zemrfQXJxrshJx6RKtsYyH9u6MmfV"
    "xsIeM2ENT5SybhMij1nKcimWbA1CV1vqMrqGnpygxFtRW0sRPZN140bQYd4oDuROIHpn3txR2fEd88PZGRbun0b+5ulb/336xzeM"
    "pcRw3wmPtXgY/bWOwEokT7fat8mujSBkLAMvr7Kd0SwwAB4A1M2FRf8wHew0bwnp4oR/hZiNPTQDT/zEVM2m+cHmpepDFhjwHQfQ"
    "WBJ1fZl1Eumv737njwWDNyTM4Kzp2VZNsOeEmoSFTcIAK7GWFq1Jgy3WigmoAyYJHg1YLrUcNW8SlryxdNzxel775A0jURt3ad3q"
    "TDb2PoZ4+6IRZ8s5XB4WNInN+BWinZReUnzdW4v5zoxQHWkglCbt1RsiYY/UD5CdZ1R3J26607he7KQlzjYTVVypNm49MIcfi9Pb"
    "X0pEbOPhqUgDQLk2JKuGEXY13ivOZWfl2lGStEXYUQqYnYuQCIqop7Fvq0bcT8A3EtGheo7/PFRjh8P1+UTjiaRt2RNp27InVtiW"
    "WRE1VDmMZxqrAPUDLaaMBtQrlYOrd1qdfSzChMPKpJUqtLWMlZ7MzAzuKvotWVfLkaW0vizvgX7FHbDcnxYfwnrGI4Vhv9AczAQY"
    "3tJTvWTYK1O60zFL06VZvpAJM/+QsDJe1eYHMDrOZDZVy2O4occ8X8pGGtJXBsFb48zHu39fu07eahZwrtakcdatnsitVrCjJQSU"
    "atKM9MQKdGDWmN4yZJawNxklMWuyj5sZaCRpJv0ECoI3Nq7qCv+rqVPbw9Vkt+QAD95gScjHbC3+OGkIPc5S9VmKjBgOJZS5XzNp"
    "4/S/X+EpRTln+F2Og4Umf3wflqZjzcrzif8rlqY5Y1hbnz+WRqaHacLrfg6laju45FyynshQUJBpT0VDSr/FMv0VHph/0i3KL+aC"
    "57A6jN0aqF5zjPU+0IgpVGjuCXs8LMp+FJ+KNbKUM0VTiClM0ZePJzF9jN4yczJ3CnDccuF2DTWU7qFp7TqBVI27v3vt9PnX733j"
    "p4Df3/vZb+799teCNJH2RdfigJwv/F4RcjL9PGaPttwy+aYO1ZLcYh8/G7ohZzJcHE5xib2q7/RmQ09DeNc+MOs80nJCpGcFo7qm"
    "U/tR15p7kT1mML88OYXe/IGRMBHDBVuiBZN58RLr1iPDDJeSXmrr/WEtA5yc9/74VTIJE94W+UHzxmraUjEeocu9ZGqLl7VG69nl"
    "RWul1WAEuSwIB39cjobm0nDDyYuZ9qXZZDWTS/90iKKjMVkwkCDkQ2IwxzEau/edN40UcsjaM3XYQKSP+n0nxJgeMHICKkYgiZ2o"
    "1thWFK9aT8SU/o36JwYHV4GoOoTSeELx/4cryWtvve0ICkHJ2LoBPAC/T24c1JTATTeAWBB3JeGCGyQ5W2aKp+Uww3ETv+GiitE4"
    "OREvmK7iKf4euLGrPCutUfjTi18roAkIEOmBacsvdIc9YcbU5qq0M1jrfkASnQR5j+sR99I4PN//MEHE8w7+fH6Ca5DsCbDlriU8"
    "0HBtZxGHW2q26hvVOLxNSzUDDBVD31Qgjc9izIwWZiy+SX+VyVQDXnaJ6dpAA40WvihiFxXrBsVEWJLRPeJh4Yoic4cIu3Bycsza"
    "Mik00TH01EFdoTmXP2EOMmW6iA70GIZmWycKC/TGYpzw9O/LY5MopVny98/yNcB5r2OX/Sk1R94DI+XhGfbglp8ZeVG+Kgu/BuN8"
    "q8jlQrqMtFZqFqxk9nWRkFRzhEHVwvPP33nuxXffvn36ux9zPSFXEFFAcpHoGrC5O3WZ5v29f/9PSs/7rXRrxmHaCxiprCigqI0a"
    "PcbfuWX68diwI3LLK9eg+LQQxW66z5hKkLSskN/OAKPujQFjuuWx506gKocujCcJNDs8Ybet0AEqhcJF4g8DAcA4LqFotuPSz3Ca"
    "kYk1ULe9qT6MlAcYWp8iKdL02U8Vmzl6RjM2UsS56EAvgtEddbBBjh5arPVioigaF7EJSH7pujqooUjeqAPqZ0VhDqs4Y/bi5jjx"
    "4tr4/4fmPy80LySmEj94JB2ZrAfuoL5bvxoy6zQ3dKIgNBpAEYVID/XwOjD2VraC1BY0sjfpAHZdgkibLG4pCxviAjp3uaFnHEvM"
    "8wejyMJSTug6Btm4JSPqLDDq0946CNtVrg8AcJ7zJhErfY99wSV4pFojwG9GYe8T7gwR97DrtSP6fYDSJeNp+K8J/x0bh7HsxDe1"
    "WgfGCJ3S0iXQfZu36/SyWh3pdTCQUXr+sMupiEJ8UfYHcewkWFe+UQ/NbmAw4gBjm5pwawErGhb56Z/hITT3jnHrHjw/bIbeILry"
    "V4XCg0QTFEK3Vzfo57DrupFRaIbBcBiEXsfzr9jYJItCSCAgIOhwXip1Skcd+1zlUuVy5eoePgLl5fbgzSPVSrVKb0LHG7r2uepu"
    "9WKVlelSgoCwc+QUaxcuWOK/cmXHpO8sHFRWgUusAIFP1vca+35EyVyWNMAKlIZRGPidjHJV3hBCqH3ukYuPXHrkknxRqtnnLl29"
    "9Mhl5dW2fW63tru7+zCfQBP2wz534fru1YdryqsSsDmsu8s7VrWya9WqFeht11TL9DzfTRe6cIEV4jpfbQgi54p9buf61YuPXGMF"
    "w6CDsR1h/LVrl3fYS7LMU8dFOmD73PWHLly8cDF+owyitn3BunQR/1/eEWMIBjb5JBdq6J5MxSoW/inv0AoDUIydsMjgg72oyTcE"
    "Iviy6YSt7LewwtXt6k51F54ZtIhi9ITFME67eBkvLvXFdl8OgB7jD7XEFw4FWKAdDxt3lb2CsVy7fO3awwjNfYyMqJUpEaTgtqbf"
    "cjDQRxl/wO7OtdtteBHijqbLdVthYn0WFIURI6mgiNHuhF5rD/+CXvsDTClSaga9Ud8f2rVd3Jq+52MIRWA826FZgCunPyhu71QG"
    "U6u2O55YO7vw00y0gMkR7J1Lydp7nG+oVirj7t6R0zxG1xO/pe009B6EiUVsw31g71Qqher2YHq+ClBUYAWGjj9kn0tjFKDBvz4g"
    "tdBr2pFzNOo5IT4P9wYBS7JmA5pyEDXsIRC0e8HEZoGR2aoUbHtIceig6FwZ37kL7q7Tql3c5qPDNec1GNM3pyG0nb7Xm9me34UR"
    "RLxAOfTmEwxoaVdhOeUS4O92z53amEaOFz0+as3jqVZh+dgskfXMWhiEkT7ci55foiBctcFUdNo5kjvs+XgSS9jZngM3tV8iqYKN"
    "IOKGe0+PhpHXnpXozoW++euOM7B34/Fuwy7viYgCMDh85MAfOi1vNKTCNPgLfJ+0LcraVX7KcJ7DoOe1CsnzpuwAJbwZOBSjdNKF"
    "CZTgqenC6k1CZxDP2mZnXY8cOM8ANY4F+Bz04emnOm4cLlgvqy1x3DIbEx9TkMMbXDnic7tHFy+2Wnrr/KXSFIoZOKDpm6WUOfI6"
    "gnffSWzoDt++EkbWJPBU6nWd4TxzcjGmV5ZJTmMOdEfTi2Z2eQe+orfanPAEoAe7er5UlRDEjkQuHAhIJhDGvwBbhuyU2gxZ7QGe"
    "KfGZVXIwCwxhMpxrbWUcB4T7SzHcIxJLLhMf9VEAJ7+/ZNjq8Z4MC0cMSUxYw7uVSgYgY36iCEEPFw56LJUrVbfP6peHo6M5P+4Y"
    "ag/qQ0elIyB/j6F62Hd6GjZAC48cpKFsNOCMrHEk0OMe1ZQv3V7PGwy9IS07gzkEs5YzG8qwI9hygf5S0dLQ7ehbwFFjpfKRrG0j"
    "Mm0dTKGhoovKniU6l/ga96Yqdrl2SW4rgo/W2AX4lL+KDNvVyhcS+C4Hq8aQhOgSYQ2bz8ZzGcM+ICURu6LcVh1D+R/OM1CrVrUM"
    "f8FCtuYINDWaKAFuLYXCE2OJMRjemLjI09Kw6wDHpF5avJMogN3n+OdCfH4upDvJ3mlBgMannd9blNoF+urO4/WurrxdcH8kJCIZ"
    "U4UFx0VHROQm0EA2SsHdqWmnHwkahBR5DuiIaaiHwVW8NOvQWdU0mSXOLnwvCYwEWJN+w+SzEJdI/oY1xZAv8gGnb+oY2LPv2OwV"
    "pX+pbxtRDDsBCXKnM2Q3Wv6lG5cs62RWEuCyIRswod+f3z/OUrEwQBNrsTlP4MTMBWBloz67xtj+2LXzOwqBWluLatPAT2ywCkii"
    "p0IZo5DOM25djsU5zamchriqP40SNQVHt6xyG3h19Z4hiOIQhM/5WFgeuApH/el57ibIXuyMaIa2Fw6jEsmq5vIQDV0nbHb5YOJm"
    "C5W9M17jCfJVQffr3im72biRX1C50EITsCkQNFyUUdfz52chOVn9AvUi7izlzs25v7KPtJz+ahZLQ67BKCJWvpI5KtumCJld0tTN"
    "89ZBq1eeSgUSUR80l5qGaldOJud+zetfkE/rgI28JLpzHaDxBjkL/ZdLhorVGHYFOaKux/qLsIosSV6TOLsdjR6SI+A4OxvjHjlh"
    "CuOtewAV2nn3DGunE5YwANi/qBQxGmAXJ5ekuDIp5w+NtJUj6M+XrHrmDZDJrrL2BjGqA8w3WAs8L8ZYrXZpHaZ8JaJTb75yPrmb"
    "sZQqJscJAI+Th1v0GxcLl4+c1kquMocGEPVTHbKrUZRoef1clEQF2qNeL3vQYkaINmp5t6icdtnNGwc7aWy8kUbtaCd5FA6h9gAt"
    "lmCfVboqtT2pRtegt9hUev7xfAlh13KbQUhqAnuEkn/cAPZFPpZY4hd7m4ZBAwBiba5eSQQTAIxEwyqFCuW2Pz/72QOWdloSV0SF"
    "uqWzww4MUe7Dbuj5xwrVTRmi5GEiBoLfMpcUEdxO6rRcvnx5OQeUHH5KrKgPoTzsc45oR0W7LIGVlxhgLBv9yLrDQlG8qXLQcYbo"
    "YdPpuX9XZCUHVsU0448lppUhEr7AMQt9ZHOR5TiiaI3C0rbJH1xnCEAwkizmuaNHAylTql26PwS0imBhmC3nHNAICogMOu4ZmQm5"
    "5ruc+uZLuav3ViGkmEZitJuDJt9iRVi6m8n0ZvG1MQbN2l+mFzLjrsrB8TwPDpRS4SiTrVLRlihKODhdVEdfUA6HmIe8FLmA5wN2"
    "KFToT0x9qDNBw4P5mgI9iQJ0xggun3XYap2jzuCvicHfyeamJeW3Kyi/s4j+2CAB4R6dWWjBGS/ew06Sh1pKs1KfcJXMNdplOHEG"
    "Z16vtH4Em4HbcDJgpCBq3e3q+epeqi8qVIZddnyvz66T4QQYpaXopAAT7qr14aXeALwolGs7w+yaf33sztqh03eHBepsXvmIlD5X"
    "FLxIv3DanyvuVj5iLhIVsdcoWFWzxKryBZ90g0I5mGfpPtZQ3DDZ96V4/6g5P5ifVaSgin6rFa09pINquYSQKKXM4NKfl7YWnUZR"
    "DjkiapSwUdvxZxMghVxRzZ/O1xJrKzKMnQ8i5YZ+0dJJ5b+lvE8TBaKUsnVWDcN2LYNLykDeTLm9tu7hrLJSQckAW908nu0xBcOz"
    "JUq0ZddoZoDP3I7rJ2ZIIskcLJpUR2jNFNDGdq3VYpc9KpXnaUVujCTaTsstjQbr4BlqrNwOg34pVNAMe3HGBnrJBnprNKCgHT6K"
    "VQiriNSVjrB49ytrlnhVQYDC2MttgO35/VJ9rAmn5LsTZfIooF4LzStTYHXWwNal9BRY0nT7yIWyyH8xSZBhxMDsHMHpGEXuHtEl"
    "uiDlXLvWvLzTrF3e41xXibk8MGpM2VLspBQUquXd7LtHnpIScCCYbnCeSendx23YiVJrHDkoc4SLsKYNZjhA+49kPdtpRyTUWWdl"
    "NHpV8J4KaZcm6rgYWgEAGEOhfDm9TOUqDJfWKmOtcbzpc60CCZt0HpAQq1MsX7qgHw4cjFqlfDFVp2ouci57/r18kUCOWNhBMDjz"
    "PqT4k4wGdpc0ANcUKu7Su0YYtbIX8luIYetcywRm1pQF5gJ0K2djAD0ft9ViN9iKUtqR7YTrCbmI4RN8eu3+xYhcrtJiFpEZZkBi"
    "Aap5TOhoiIQPaVx1rSefztrKLl6+DG0tYVNTxX0Kct+bL99cdiEBGRq2ODuKshJVX0egoqqs1yIqVQEfdRA2x0tYGi7sqCSUPKJm"
    "WSh5E/Sb1P2qZbmVYi7ZKgsSGsoTv8lSmB8wq61tWeo+aO6Ye4+5oG1V1MMa7s8TwoMPIJbWxGsJITX1hins5/l6t6yqqb5jmdtO"
    "7SOiYWgmFlfTG4onsZbiVJWuEGSuQgJJ/Q4JCQAi0krEZeZgeIgGzjDCPbAyXgYrFFZYFAGH9jApI6W7PerCmex09/IgSyW4kFhh"
    "N3KaDKk6CxSz6JfMoIl2soXyxfwrQrnwWGm88jLuue0L6de1co0uwIzii3LQCqJhpg0h7sB2zF7RVbQjKHR22DpBZKlnj4Q76puj"
    "WbAEBwhT8ToG2jlcInyP1jVyFALKPDXw2hLgs6rcMoFTzg+IgsM8zCULBYNMG5+9+5fGpZTNsi+KjrRswUVBdGU/zGHD88yZMGrt"
    "X/qGsVHirbvM0FOz5aSEAeuINM9ufMslDmIB6GJdaZnD2hADW08llzb95GkQxp25op9X1dSZGC8hvtyNm0JdiKriyJDmt9xI6AOZ"
    "FCuXrFtigJUQB2iMVi2P0Wp1W3NV4ru+nLeF8oz7oBzWFRIpc2PaL+ywW1P04LtkEb99YQ2BHbejYfngyPQiNiClv0v4gk/qaJZ3"
    "OdLnTrCWaVs7JGojFrhf0gVzDNp4i2S2rtonJ6FSKUcG02g/bc4VqlM1esbLQ5oOSRPASoaVUq6CSlVE63jnUpZxE3Et6mYy9WTk"
    "hNF9iqlwDuRBoCwZ073ilystb7yuJaOu4hLrUzhKaCHTWi4qRqK69WyJkyDl9HrYSnemm3GxvVjT6A5ql2k7828mkgwDMTTULFXI"
    "ylzppJpPoMYLXNrNYJ2EGACH0dTNFjgJJ71DMo0VqF4KGacsCfIXGhXfQDV9MIBO+CutgOmldrFsPAmrdgYy+H5tiGGIH62Um/dv"
    "4burW/hiIFSxUhX54ewLlbVCubJ53m+Bwq1mHKv78OqJLbVF44PQlRNLuUVdyCU9oRrpUrIxPvF78m6vJC2cSWsbHg/Pgmp0eY1o"
    "ARB3PmvKlD00yvSFqLRQOLtSlZulJ41PW714LVMDbvUA8a5zx13eTfm5ZalC4ot8u3YGCRa/M9mAWtFZp87rteKJrqlOXiofyJFN"
    "ZDI71H0ZgT2fSBLLzUJHztVRsdtT7A4hPL00Lgr/TNhb2T1RoJWwFkdXGbQ9ps5QtVdicU2YJCcFEesixZ2B6s4iOij0vLVEnozs"
    "ZlXQVCrD2jefyLzvDcq20M48f8IZLCbka7ualxh6oMUmT9pHZBdTxl+rRrMGv0SVS0duNHGxQeq46fSaRdyBQqmAR01gU+3OFEdx"
    "J8+C8kyG4Wfhg7OdJnCB1hYlY2FizVYI7Wv5+jtsooxR6OJ2SAIUBpSG6XKl5TJTZR6sLcMUurKUps3ltdgAoN156m5V+tPNtdkl"
    "usL37b6JhwrxQxJvtIDHaA4Euar40sWaJK0g3zbxFaWj7Wiu+rVJYrHnDIauLX6kCaF2VIhiTvTCGe3NYRSRB9DPydY+nLKeK1ol"
    "lJLy+eAWytk0u6iHJovaauzGgy37I5Ssst+5xtEZJz2DvmaNNAfDeeZFIj+T0Z1mPrOtDCgYzNfojuMK2leVgN0hAhZbCkkDgfuR"
    "T7K7a7NfDLrdcaHszu+D6BQggYY53LgH24rWdWhIMlo6vcVbG/bn+RY0NdmpF83XvDRUslfxkFxC+MouCuVAET5VFeFTNR5JUIJl"
    "WSJHZmX6wfItxDItt5cnh2UFAHPnOVpKjIXR2tbeEFUGkhB15DOpOQcV4+TESuK2N3VbwqtGk4rsZLMvFF7F/ABMoyJylkscDEyp"
    "XN2tpI2PYeIF8iGMLxGcxnoCO0XrwSutMA64vGsWVGOSHW5MgrUL5W7rvjnPXeZhWfigBmb8VqbheNHaNmTKLbPK0205vWKudDbK"
    "dxDL1NUR3Z6aWGawAytVivnLjb2hBwWWGXWnfdNEG4Q98nCMLIQRNzKM1Nj3oTuQIuvskyO9lRTBKloLBp0Mm41Qoi+y17iwG7ti"
    "V2M/OKD3izvIg1uXa+NJfIYu6GyInG8PjUuwwzUuogyW4n8THSgWUNCeSyu+WgqaE6mFzZyMa65hTLAsxZII6qKDk4CZWmpmQr3D"
    "Swhnl6pkZGwb6ISjYw8wdRMtvY6csBR1R/0jXaNL/6s6i7/uuy3PKRQV5felCobLmbMYPM8GuPflyiVxeAXrMu4WzhfwA5o0iUak"
    "Tr66vas0khO7BzmfhNH7NvefYc5ACS8ZLhJBxReJspHGk30PQrfthkO4BVujptuCK5W2scCeYSSq3TfT8w4tzchSe+pZKTNCiyzn"
    "LGm6ZsVWV1bajsoimaHFhNNWfAdb7OhaqcOR1gqVqzvImvuuExKYbXj9QRBGDioqmdmVlfDXsZLsl7XEnhIhmnVY7Q/z7dpxNPCm"
    "9AyMJ3c4CXO+uDbbs5TZAL3W7ERFL5pte2xMeSRnMrRSHmuZPGY50+zNik8BE40zw7/EqbZU4XlmCSWUDA/klnNhSA84Vmyevvcv"
    "mHtZm7Jb6Q/31rDCYhF6MgehHfmd9gWnqThI5w/o0pIRpWzLeCtLLkBld1KLT00qYHCM6YKHeQYiGa9x+fIMRFLtYlQfbDtH+1+7"
    "8JFlZm/QS05FZS/4BGJIZy8AGi8Nl1oq51QskT3KzhIAFIRCGUi7lSZ4wRFwCkclxb/pA4XewgbLHgxyBKwH9w/ljIv4FBzzHona"
    "iacXHJPd0PYy21LRgqJIzeGkEpGndlznYrt5cVsFAeowC7LKO+ZejHEyYWkvlpyIUfnqZNCmeDtte612T5a+ltZ6bP1eMRc1bWSK"
    "YTzxATsXsr/Sx4t5VWvMGn/dG3JNjCYwxxooTrNGFYfDyoIMK3NZ6ZaA+phbcT2j3FgkwKM7ra1/ZGEgd2pWrVK1Lu5a5QtZhOP9"
    "6chpAqQk1+Lp4VtSkGdQvatpZdluSr+5ly9LYDXOovlkhpUhkA6KoCPbsibmbmPTR44WOqFztJdN/8oOlktTMkya+bhUsaYsxazA"
    "Ws/WIzROy7A4oyAtSbo6swXYxMwWSnlNoAlI6BLszM9oJZYJlVqEVHP9UBtLfaw0d3590GtI+TGNiE82p0ujEBXK6IylF2Eu4TnB"
    "fTKsO7gfHna4tugqWw7WC5ALk0p3rkxJCi7VTWg5w657Fr4yj1cVvQOt3z2TRDRpCn8mx1yl1/bZ/ZGlVZRiH7VGGJVtKWKgntv+"
    "/AO5NbJW/FH/rAZsceVhtG7oLFkB3dgzwHZxbugOr5M1pYzed4lfKYv4JqSgYasjberwef6jG4XI8XrI2DWBZBzvlLfL24WTwmM3"
    "nig86kFFGNpJoRtFg6F9/rxStNwM+oWPnv9r2F1AioDuB6hmcYfzvx6OBsijDQvFYlHIBbqzQRfaIvRswi77rUIRrnpk35m8N/T6"
    "HEWb8B2odKjbD55FsahLekH6pFRkswFUVUTeGQmKQljoFI6gujn/qMXd3yzGHFo2sQHk7FAqRZMS0+eVptAwcAlOb099O8t8+6z+"
    "dnjsTpL16V2itjy+qEkn/Mre91yHtlIrrCIiveXY2excBf6nvuXbnVG+5PQGXYfJQek13SI5janfsprUvicbRgo6qxK9X9ZfXkXl"
    "a3Z1+sS89NI9MgmVoGvg7KU+xabK6W/ZHR71RokxHpHo0sdI4Np75FtCZ5gYGFAjM6Lt9dfdkcshLLkAqLfU3wmiQ99qJ0JmOVF9"
    "6A48R3+F0B+TE9kfsrZC/Zzcd/UbYTpecwEsAMMMlCFhTpHuLbjjAS2WpP1tuXYhdPsYCzyGezgwvZZ9kVadn5FSxGgyKL4nfehs"
    "zaPO3IspYDtBEGMUceboVsqSMJSrF4bZRSKvj72L3D12c3TkNUtH7rOeGwIHZxUqFvDYVqFq7qmufXbK129P4zTtNO8pV2sUeT2P"
    "0GhZqMPnJKDF1zOpIl+USZuVUG4tysxLfZ7wWl+U+6WKJEHgCQhn1XKWxKv8pmc7YxY+WkA/nf5RqTrXb3i9HBXZSRTJbm+HFb60"
    "VuFLvPPKWqWrFSzeKyG1kKG3IDMJ3WgCFhDooHlCdQD0iUaxLMqMUkhIg9lllJBmiNclrWGN6+iWLsxViXZqHhdwGmgQV8IAXHPF"
    "No5bTqEsifiyDsWKXpQl26swwKxZ5ZKzBI+oXHEZ755V37HrLfUG6i3KjB+FWTGZ8fy+fAu0RkaD+X0xuaKRhH9YkG9xowt7RP1Y"
    "8TK/P23MAtgYxH9z9o/N3klzgnnSsICI2RIjZufZZmUDOLNI5lbYQ5UekqcPv9ToSzZE1XiZ7SVltnmZnSVldniZ3SVldlHWJyKU"
    "8IOTUlIRn+K2KBdFwtKJNYicnihEp0AvtF3eqdQu1dxtshwRBdHSOLs1XAD2Ya5RYhKs1beSu+ICAexCeN54cQ8qIS09Xo6AU3Na"
    "paPOPClwFiXpKy+ZX4qXYOuTXQa/xaVqy4rVWLlOEC3pk31lJTEh8JKi/DMrq0Xd0ooFx6LEkrboIys39pZ1yr6ykqjZWlKUf0Z/"
    "NYB5wS7lw/0AUPLyUheo1O6KUgj7gykcRWFyyxD/klMJpbfXK73NSsNduFZxugwHM2UsdOMtG8oMbuV1CuOtTHwrR1wZ3nVEyUmr"
    "5gyrOl4ERQrz3GDL1PCTByhAevJwrtsAxV9rT6L1lF6AO83JIqnv6tft5Ndt9etO8uuO+jXVs9bv5eTXy8rXWnJUNXVUaKmifd0m"
    "9bSghSninMZBVveIxhCUQlyUyGa9LFtlrYCpVc8qwLcMCfN5ik1lFZIEvC5TyymzKJOQhhkrMxlNpokjLQyiz7ZuusJeCXBJfIw/"
    "IHpLfGSvRAFCaokS/J0oQumJtAL0RnwGVJaoT2/EZ0Rgie/slShAaCtRgr+DIqpHfdLdnqWTUksAF8D4MbfnjoFsUOUHnHShD2ba"
    "ICXB5ZtW4rXCjivf0qxz8mPqLX+BpPkonMfsNf5VxIhGeyxhtHJNwxeVGo15b/Wt4LzVd5LvVl/GXLf6lvHcGtHLmWvtHbLW6guF"
    "CUbyOOYgVcMHLiEjHi4IUyYBmvbfEpY27Cm55ewtrFDPQqnwsWuJibY8yn4VBv3EqzGMWH8TBRYXJ1gxHFiSi7CkSs9ii8dXi+2L"
    "JeR6QqpW4u+Tz5wPsrgqtxTzshaShvhJj7+zt4T/lguOtDcHptVsu5ltWBDvHn+T36AoYSKfLvaxoLFY8+HMj5ypbXzU2OM+DENg"
    "ZHrAqmfXmJ25xrPr12DM2xnLn2FEKs2cX2uPy4JKY6c34rLPZEv8olm/a+USOcP8CLjXHqkU/GW3w87fWXtnojNZ60EogDST03Gv"
    "rBgO8f6JNlU0/cHnlRb9rj+7tFj4w5pjLBo+w1mJr5sPa1nuZxip6/KDDyaWd59xNVRZeLw1PdfvRN1V21JZ1uKKNUk0RVFBlrT2"
    "Ya0TURTrYzJJRqxfRxAZ69eQJMj6VWIC5SxQh+TL+uX5/X8GTMapoTPUQFpp/eIKJXVflc56TlOqjQ8LdyX1IkuGRKqROWN9beMG"
    "0kKGZdx0O4Fb+MyNwt9ibrOjnlt4AqhA5QP83A+ioHATqhU+/rj2eO3jn2Cv/sYLnY7ns9fw/LlR4WNB1PWarIHHXC+cBYY1nA0j"
    "t18aeRYOAjYt9FAthvy6bXzcjR4KHcA8hcfgGWpdcwCW0bpLPAc+3O0Otv+w+7TztyM2CPZ15FEzxNBZ8hcmZmVKcRTRMatqJRky"
    "y6pN2bN5MKXSsInvbHrH0uCea2/DnypPgXvOPYI/l0TuW25sHie9bV+EPxdk0ttz7Vq75rZ5tttzrgvP7TjD7Tl3B/5UlMy251q7"
    "8KfKUtmeq16CP0ciiS2OY2dXJrE9t3sR/rR58tpzF3fgTzNOWhtX1pPVKvlqz+1u7+7S1IJjzO/sbO84e1xgBiNptpvuxT3OY8L3"
    "C5cq26hVBq7WPlepXdppXtwTUj2YSgXm5u4JphdKbO9edrBx5DChucsXL1Z296TsDAbjtrepCc6C2uec6m6tgm+A5cYB1HZru3tC"
    "pIkV3Jpb2xMcuX3u6HK1WcU5A5sLK9DcdtzWnhDkwZBa7mUaEuOCYb6t2qXW5T3GdmPW68vVo9qeFDfa55rttkM1OF8OZdyLO5dx"
    "h3xKvOxU4Y/DH9mgduAP7jgGiGBv2m0AEvkGoaTl7l5yxBttplIJXGWpGrVczJUd0yLX2ALaWCU/8fzC8aYCD0HUr/4K91YB06g0"
    "GMD+uQ5sZ5O/OXZnyo5SmVZb2QB8M/ZarrrI+M4ZtXDhKxcu7+5e5u+8PuAyWEnnklPZ4e/Qcc4+V7uw+//1diU9suPI+T6/Qp7G"
    "AC/dKnVKuVRW1fS72OOLAWMOBuxB4x2UKeUylZslVVa9SdTJRx98sc8++A8Y8NG/p2H4X5gRJKUgGdSS9Xpm6a6UuIlkkLF+McF5"
    "gUf52wooQm46lyghs71Fk/BIkeR4Oc7jRJPkeDFOx1lNknEcz+MVyUM9E4ucNCQZL5JxkmqSFO/mkwkhyThP7icxJckkncymiSLJ"
    "fCL21FiT5Gq6WmfLhiQX63SMOwpJcjFerB/WhCTryoQk62+RJDlZLLP1QpFkslwu5ouaJHH9p5MwXoDT3DSMYkznrehzts4WD3NN"
    "n3U7ij6x7mwu6j6EyXQh6spc7YpY77Nssl7VxLqePeTjJSFW5UE6C8UpEMaxrl5T7nq5XCdTTbn5eir+01CuSkP+EM4X8D81bk3F"
    "68V9fB9rKk7vF8t12lAx1o3n92Es6iezsa6taXo1XYovr2k6SbJJnhOaxvqTaZiIUSeThU4NXxP4/D4Xq1QTeD10TeD22GUG+prY"
    "4yxOx2tK7LPVNMUFrYm9Jv9WYm8Iut7BfoIeT5N4bBC02Ifp/ZQSdL2mNUGvV+ksnZkEXc8fIeh5nt8v702Crj+iIeiHyaqpqgh6"
    "Mc/X6armNsCWGT9ClMmTMpM+RvXfk8doUv+YPibRtKT+FaYfRJKEYttNxA4mbhBWmdlMTGSs09wTVwmz2ByKRZMZaUq5TJjlxK6J"
    "I0Fm86ksKY6iAyYAgz8P2eOD/NPiMPDt2/4R0jjg32BeVD6wWimqzRBSP6kfJ4/K/29qn/bxoi40EYVAVR8s7EKTke8c7Wx/NuvR"
    "/hxsVKu73//+76+m/Q93IL7729/9wXkn9qKs99d/49bL1vju53/59//9t/9xXuMWxQL/9x///fN//pdTAPcrFhDVf/7nf3UK4ObF"
    "Av8A4Mz2a9jH+PZ3sHud17inR+9/KT2kd3+CLVLDQby9b6vDPlyesq/hd7jdKcBi7QYD71134+XGdJRcb5RDM1h/HCwprQaVxprD"
    "CXhrMZT0COLBTuzfzAnTlHkFQ0wSGUoAbVTwQuKYq5HgTLtiKUSUdqOandJNht6kh6WVvRAuhtF7edlEuytJ60QzPoFiWfrRS+2y"
    "IL4CnL3/CppRz3TqMf0TtNWr9PyIU0kf/vG0O6qnJAyhPJt5cMTPICahfuISABnLQLvHOkYsiwJlmcwlKss7E4Za442QbwRzWq+I"
    "VWrhT2zPa+q13YTMGoizRMW/350fawvrydM/Bp56wr1UQsyeEVTamduTS8VNcf3gB/hpvt+eGfRD4HL0NdbUpx4I32ysHgZAuiGR"
    "7zQtZ0vkoRygihxQdXTBJvXBdKZHL1oC0IjTa56p4hD65bbI+VLXPKMVEWbUIK3yg1cGr0Yh9SlGjsg3BN3gBn0qvaDHZDzudpKV"
    "b5nMKEuPG+toEWxj/Rowr64NUpiCgAeS4YP7dD0TRMuGZ2m2MJjT1bIaUezyXLWeqTQF5sOfqnSJEAJfesbBo98YFwOPXf5UfT3n"
    "P8JB/iUkD44vcAJ/cQ56F/JuMN25BGwBdlFYU7tjGyA4hvh7CpvhBKjISxDdK8g1KEMhlNObBlqiMyJExNWzOPGMWYExn75cFeEw"
    "1KJHMiPH9qyJshu/79Nlvh9yGgJ3aIcfpeczYQ0u217xb0IQ6BcVOHWQNdlgHdFeV/qqOnkVk1Zh/A6B/Kf+2UPILQwVgwjwI69N"
    "jgYDAs5C67Sr7isjCvDeAszG/JAW5HI0TvKD6bAi5EbVoA8iVDb44OSbnIsO7fbjhWjf5oSebJxgYAvLVy4GksldioVbckfELCjk"
    "3ZuCR9O/v+q4I2Z5Gi5ANoOrXEf7yOAmHAbH45jeyYWRMrkHadA4KkCjQqClXnDy0sOw/QBj8ii3ZUw2cmyg41MhcTnMbLp9Q7mw"
    "MoQqnTEfb5Mzd2IBQCn4MKM8dtrAi0xJiXSzudrHSf2GxpQSisK/ORciWFjwYHaxcWrvfMRt/D5A1xiV5IigSJEsK3M8+etBA2zO"
    "bI6wOWOAzWm9S1quIJP1nZpoNmOpBZ3BP9AmNx5PMwoFVX9iENmJjrrwwXUrD2agpMGF2w58pLPvoUNVBTHF+D1q1Ami7FTR+Ajz"
    "C0oT9G/BLqoT0lxXVyGFHchv1tYIorOu1lIJTzoeC61uJ+c86NzRSpobMlZ6O0hKECwS6zGdZmb92o1PsITHtqBJlF3tC+AdV0ul"
    "sW6IbcHmGna2P04ZGbloC+Mo7XKn55Gb9K0B/NKuzFB9+VIyegU59pYmGs9lHAPMnSOJpllrE7WHeZlbuFeMmoMXaEk8rSGv55tA"
    "SaBuTms/Npobq8zt8abxn8DWqbKK5dmPVfGSf7n6xE5LSWPMi1bjqtMonnoUcMHgzvWRKBjBZXUs+0IYG5P5uqtWW8dpmaMpA80T"
    "jyFZOUBm2rr41atI6hGIyKXvHw4AgLvW62PfzQtHZHWImyOdovKEv8ESZAPFWdnAuTn3Yg9a1Ur3kT2K1rWfZuakPaJEkmffR46+"
    "hcQutNTQ38qhn8SIfvLd8u/yKtqmTFrW5l2fJJSIhycmp15/NXv3zeTd95s7qfaLTueyKnbn3jiKhhS46MTcZRLXk+Om4fFsFtn1"
    "31cD/Wzkwv02vOyiS+T2ckmcb7oaaBA9X9u5gJiTheb5gTRxOte4KoqbMSZDFhjIQNC6rTcyd9vI20Q3IY9GVz9D7+KmO8hnbEuH"
    "1vtbvyQbwA4Rlt/M4NAhOJDePjhtEUgenGM/py006RRg/YowKt4ATQd/8Dl01ZlKtdxzXsXLH/VMWns6AsD4I2MIdpaITs0rvpNn"
    "mR6PeTGM9zcS4ywYTCX34tAxhDdSuE179NqWXyDz7fhWjv98Fbwm64v9ccNmkpXF9Fd1rkn1iGHLLExyHwD6Id0d2eTtJmiLo8ua"
    "6uVAaxGjL0nP5+hyBwkkAtlJK/DLBHiUcIoAoCYyp25peRKL06cpXU2Gg94g6o6ePEGkbqyMNhGzM9cCNutQmtTjXM3cbcyyvBtw"
    "tnJPwvyU29Mrj3brxdpdKKxdRUDyLp93Yu1OxozUP6dS//idQZ51h9oBT8tAu04VPuzArQW1wsmC2VrW3lIBjR+ZsXvoJpwt6Iwl"
    "xozdJSqlApmyJPeKJtwA21p7ML4pyor0FY8M+CUmps5VocQJ1CtZAw++DzQLS7Jz0/OEYqTdG0YG/EkO0DEeoI1NAliZ77JtnmbX"
    "j6UzsU0TwUDutEXD4KoyztsmxUeiQJcQSc0o0wdgq99HyU6mfT8GOoe8h0buKxquWuZpsdr2Zvi18n/exy7lVx/olDEehTGvBYCB"
    "KsG2S7FgZMw0k4GOa/BzCQXohISegBTcg7rJsqV0+4HDmqi5Mg3phlZywM5zRP71xkwsjgO1mO6Jpe6UrZBzEmFCCiQyZ0cNGaln"
    "5VTbQVTEfbdUU2XvGov81pMbUmqpfqqly2WOyVubY2pOcZmaSQ836cGs6iRmhq7Y1abKFs9c8rs+Ekzd+IeyKTw1rEhR7WnmFzjY"
    "36PVseJipF0Z79LrDLel8YZjtxxG+m1IC9LoSWY7qu/ZVoaeCqAXuRaX3coMx16NrDwCuiCbcewDuxTblS4XoWCI6h9eh4totbXz"
    "6Th7hAcjRwXd+rTPPmMbIf4dyPYcL6o7nduqdJe3Mw1hfWY6SqOpzDEpfY78rkL8cagGE0Tl8Wrbfb/tquh+8rNYFMg0B0kuXH86"
    "Vaza907147pUKD4KTwZsLyorwdFyeOa1+JdxNl3bPq44LvuQrQlQZfu0tIUsgKgEhHnijgNXJb0pzlfDTAdr/qDlw49RO6d4NpzE"
    "Suw/2u6Ae6cTPJmqsXWRF1QXt6xboJTJS8EgeOx/28nyB1+eQrqFP5I+EnqBpKc+paORtwsKp5vTtSWZkm0IwzqHvEo7WSVF4R33"
    "4szK5eSzeJhEotcQSARC6nBmLTgEA/ziyaVZXR1wU2rPv7l8/nIskKCPB1cd36JpG65/F9QzMvQy9369jLjhWJU3NSFVAEMPuckq"
    "0M1V6SaC31cHg6lE+BNaTvy0r3lZbnU6f90BqHxTVj1iHIihAgyFlkZkGubMrJQShJaVT2xEFFXaajez261FBr0pSFlAeHXG4DX+"
    "kY9wXRmV9PuxpAVEPn4gorPprjfvaZjDXWSscW0Ss0ib5bSVtPoRe7nUchKovZd9mQcx5D3RPtukL+K9jQWvM5KOLEpm74IdgtF8"
    "U1IDVs64pGZ+Ulvv03Ibyn9tKQQhPAgEU1IGOurFSBwDr62kHpa6ty1xR25gOWPMB9omHDitDscSMNKbnnQL1biTv54LaTDc9BgY"
    "b9kSuPISh6aEGG4Tq5gqMiWe51N3axPlhvf+NzTQ4q9Vzl0sgnIQJNzjWOUXYsGUMdSVHqW1eXfORgn8xF7ajRVHJd4myrTZB+01"
    "N1pnpF+L1a1sLfpTXpzYcxffylNadsjb0MVppVLX95i2BpErHbQ0dDuaGqh7NsVfyzk558MTnK1KiTmqTBREA9rwiQUEg0+9DmG5"
    "oY60OvlOmyceNwxB07xSBe+DJdHQ3Eoa+PHJA5IGF+21v77vqQ1KE5ibM8OQKxzIJx5HTXJ4Q1SOkn3oVUVK2S2Mp5wCZGoGjpvw"
    "We69Om3u1ffoeXfMWNqgXEWrwpKX/7pESNEzZpQdss2fMb/s0B37jBlnh+3YZ0xCO3TDPkOowUAyfL5lX64G+WJPBvCIfZauU4nP"
    "0cWqPSvO6oxnnkvAcJlwe0FUgGRdXqM5vxdErXZbO+9T4TfAiwbbjO+cX6xfI7Pe/9kpEe6nm1zwkxGjWVvvuy6VgeslGuw6AJkW"
    "QerjCUe0BxklWQ5EvDMPbm/QG7GtOKYgb6DEL3ye3hpIwTqIv92SFLlFEdQsaPEWWcJ0fRIWDRO7IE5H0w8xsYzWj/qUD+BtacCy"
    "rBmJqzPQEc+T2W8Y34jm8oWyKNK2RCPDVSwEQNTl3IkGQeDDH2iCQyXOIafcbwvvi7vzxj3h7j7T4h6VZiKiuEVD7NnP2EaLFka8"
    "9KqvPeoKWeso+Cl+f+m3UXk6Ded7y9e7l2PXRw857ltneS5R4k28duZAejR8QZRPGXXpG2Bqkca0ORlHorye2YAY6AYDV270pJ2b"
    "CQzNEPhb3KzqIQlWY+lBPVYlXo5WiXqTyALrfdWpol60qqfrTCGMH7IahHSioEG7xKf0Pcq2u6NJZY56m3zXPt/08z+YDtOZP47r"
    "HSB7CYZ6T6sIg1YnU4sdtLbERLYgtdE+1/rIJwHLt1oa8rmSiiKoatZbDPUKRtI8zDKGBVs4ElWAFRqV5vpVGQj8udFPblr0O2SS"
    "l8f0YnjAtemWmgUc6+UT1aPT0UpQA08DZFs84aiOY73yFb0gq0N9RC0nKN1AHy20sqw3VzO2Xt+uw5XKl9VINxKtet6Z+vbR1dz7"
    "SUsfWCK67EqO88euGw+5bm9YcDeEqb1DxkX5dDZPeQdEUPGOmlyx3RHCDVRIo44VTV97+JcaY/8z+cA62kgxliC6bD/kg1S3MsD8"
    "+tQSjj5Tk6iaRBHX2Qr1+2/u91G3vFp7XY/qMtpXqv3gJxXK/gAArc5KHn3AYJUsK5s7nkSiYappoMoPvEjE3O17Lz35Lpt3eeCD"
    "gDwct+2+BaMw43Li+nF0/Lb7xJ0j1U3RHV4ky97Ai9fVnH4a+2JttVvMVAWvQICbEly09cyQ883GHRmbYeIZuN0MYNwtBqj2Bp5y"
    "wVZTCLaCHqLqlKVfeaYS3ku+yY6iGGKNNTfblJHK8vIWvl/7WlAXqwXr17Nod7fifE9NR0McY5fvjHSVOv7Cjp3Yi8/nqsPBKi97"
    "uFdVVAwzuF1oVrP9HLPbX7lhONHLfD+DrXXKLeF869ZZcJmnlS0VMyhzAp7twHWbnqLVo4v4LI4XZWg7eC07fbiWvX2uLPP5B3Yl"
    "9Flt+rhH+fco0pls6FF6BZhBM8uz8uDxWip0mVahiRYkopNKhSdFJ4+rPa0m59gCdONugCXjcTWb1c/B6NY8p487/buw8O1CmfT0"
    "81XU4FNc3e/Ad/Zq8eVSVls3fG6Capj5oHgUcWEWEE9+G00/9YARUD0I1pMCQ/Tj5HRdP5vGuNzJKsurG97g+JIP8rHS30xdWhes"
    "mZ8qgxGr+rB7+7QTTH+xWYY1vx/E89+EZLPz0J/MgHnhYb0NtjpdLp6vY1sdh/EbNviVzancReM4P3iAXNbpqir7q4+YSey1YbCb"
    "wOsAyM9NMdB3g6C7JaYaxBO23yLdyU+57XJ6Jx6UPhu3F0mx8ar0GpM76nYe3V0NDDK7udV9N4LXbZL39qyV6Lx99T3qtXMXnZ7E"
    "Mq7tnFZbzMnaB0LAC4xktAu0+VLCJEi8SKS3DXymDkSf69N9bMXrtYXLpdnIF6Q+yAbh4kKU+aq5ecb12PBFsJ0MlJxr7SMTQwjN"
    "KXQ+S4qwnM3ZwwTw1q+e6VHo7N4pcqZDAbyPnFE7SigoGUSHbY84rmUq1nxHIPcW/aIw69G3aVEk2vyoGZBWJpCTjD/sVYVlE97p"
    "honK/S9ROecmOjXlWs9FjpTm9gQPMISwjjE0ZhMldsd0Lkcm6CrEP32Wesaikl9ANRBGFckAPUwT6UVvcHZAfmkIBLXJdElb4eBE"
    "zcf1rgDGervbZxRCboxvoywvq1t4toWcBNlA0JxjREYgh1KiSgsJ4XT+SHeAZTgEbQVG+NIidUCTL/srrKW6NBR6I2F+iGWZ3Qir"
    "YL9ziXNhWTURNUZPz4J1k3ZhZtBfjbMGnNDDjHUkO6HLGm+0O6GTGe9KhrO7ZvWAPFljhbcwerv2AA58La/D/UlaDeTd1uz0mH5b"
    "yqRndcKd1aLHINp+JKq0nfXrlMFwAPwi9jursYG3aw91OpY8lJsrExrbgc0oKQcaqACmmx4aDdu1T89l/qj/8NVvAsQX/Q9GO45C"
    "FFXNFfS4hNbNE1N2GWlYOglV1BG7xvtj121dAvQVZyDyXuzoByuEmhdLm0XjF/iyPlQtURWMSp4GVtSH+eX0HJQvB/H4q4Ug2w0j"
    "atlu3nETROvdPi9v2wqkgaDaXq2YcGc1+nyvC9j6IcI0Rmjt2f5wBnz4j9F28bhPmf2rGh5bAwE9FStQWOoxp9rLgc4y7tonT1IP"
    "zjzk+HFa7VcHX4oQbvEY6jLnBERL0WxoPT08F6dXmCTmeLOKnvOjnE5/pJRZYbuHu5utolBW3Qri3h7ah7jO2SrabRw8+BgjrM1p"
    "0IZVCoPTqXcKgy63Xb55hFEa4n99Oi93jWKm8WNwYJPiaLIugnjNW4tRym2wRubS9wkbDyLogeYWMNHCmCiwhMkFQbDfamcJ+0y6"
    "KVtCMqIDpeFsxJ1JWmVIsaUXij6eWUXbkev9rlvt6VEK0SrtJtqcrm0hXK2b4Sjdr4zW1Ljdco29937m1BGzhzmCTDdbo1D/HCfj"
    "+9ET7yiWX/zCW8d5b0Oz55cuC1J+6RB3bpbA5lLYGS6AiRq7PpZVn5ARRK/bPm4kTnIEqFoergzOkFsuq4Z24eewoL302M/zRZaN"
    "Xj3yGry2nGhYS4W4OdJ9A/u23r3l2RNm2Ta9p74bp+K/q/vJk1dCIYeXJxa8jvi9bOWRqOFrYgoGAcfne5Tt9RGFEG0I4Q/M3eib"
    "+HQp6xTB8msyy7kI/rVVS81XJAaWB9YQH8b1EHH0d5zeLfGCfao6n7PdpUa4FE982GYYpQrvQY2y0kWmSu3QGTat2p5cTVWnllOl"
    "HjWgkGbyBlz0k5L6+mK9R7bjcAcSuFSsWBakudjuRdGF6z9pPg/lzTGrHgRYjF2W9GIWMN+DgapIfNO7jU8Tie0hekOU58djtZXc"
    "96dTJu6KbtshwnL3sihIa6zdt6yPfpW8KyVnj6A7dr80ThhsdH06WWrBdty/np56SWJvxXlPTWYhWPUQcDFeb1xUGWNv/qMN8chE"
    "EpBuXdC7p8NJV4dC4M/6Dt9tpx6pnc9DNprc1mp704fnqo84jgWpUDuRnmuY0WEs38o0kfinQgKkQH+nsxAQrl5x3ynaJePPOmX8"
    "xFLOziUfjG2bH0LesCMXV+zL2bCsUYVxq9jguerQ78NrhLUJVY0gENSvBmEY9pSDzpgWjdJ9ZSeTMeIOcASUSl2/VAbcFi/30RUp"
    "1UclUiyT1BxEZ7GOWFC+f4x/uIubHe1top0QdRdZSxfycvB38B4dy0N+dQCk54wk6UU8NZb6wymnpCOxGBVA9Heip3Os5rEcaKci"
    "qroW86RoVghKp8wjycsCLQHLWGDb3+/bhmjr4/+sJi/bBir9rCt9dJ8XfSH39YRIve4QsAE1U56KregBR9uK58zX/QD1uKtrP4KR"
    "72iZuegRkahS0ekZCzLboIoAluvIQVThy9R5KYUb2feW996x9dKycHF1QeFMGaqXJHcsV0We9XFTaouvdkD+26bebwPjFgWGp7CG"
    "jexux5JyGgPHbWRlxJZUFw7ZxInqbbXdXC3fls4cB9/oYGzmYrvxWSTcaAQs/bK/8obe5ta0ZJR7qJpuijx3Ppfpw82sdJunkNrY"
    "fzwtr623z7jxfG7jpb8r3jCzQF13rpC7MDvjm5Cnr7dGVvEyvdFRTOx0fBwWDGI7LBMomVOTb5d3GN3QxVtrIPmCy8U5tXJxkgiJ"
    "biQqO7xZgkm/UQVRwgWIeDLgvb32c1Ap3tb7dFPefAhYpm5vB4GQH2+IdTHsnVOjvfXSG+IZzdjgTqOyJ/GdD7nDZ20wW4yKu/6+"
    "kZ64mgZ24k0CNjVZ1w32uy1dJdVlMR4kfrzzN+mXTi0oAyEgG4JrFmTOoSyRvlpNFLocGLp7bOknKt8EsdFE75PWk7ZbNRSJJgyX"
    "fvkaclBsNggqaiyds498pj6VduhqHeo3yg4tHIFOb7Qfgmtf10Hd/i8aBUhTQDmeYuoWnhqDSrxbg7EN2yp3PO2L9KtzWQ+Xgxy5"
    "R7YMWfR+AdllcB6GSfOxMKSgn1OWqvARJxzdRKM1mQ8Mj9YtFJCgDBqqCXA6I+37XBXMIpCegMcXqst8zHWBNlWJs40xdNIC1Lnn"
    "UaV0bBaqOPjTN7whrJXHMXHsevhySwNNgHOi4Yf41In5TpXDdSN4lNvSVv0WJXxWMm2K4Af5MJrs3O/M+d2VyIScov5rcHPSHgjE"
    "1D9NHHdxGsXBRln3t1fr+GTsPDqeqrzNva4GDiveirz0nFzG0cQ7U9t7QTQW+TE+dYn20DssM8jBsSXUZUJGNsQHV1fp6XSrxlx2"
    "8agK9cNKcqtri2kKmx+AnygonnfNrUuV6SH3HEaqBORYJs3mRUF+lc+7s4+ksMi6v6uuqnHwDGe7KyteoLU2ERQkYvOcE5vjBZsC"
    "o3gzI0NbL0uD1W3ukt68ciOS9rChqpF9JrwqAX9JFrQMteuqZ4NBqpHbRJtvcfmYekDaF8ZNg0PRoC1Lx0C+aEy/BcUu9zxUwahN"
    "OZsUva4RqsLqpRh02shjsMNj0FQSLMh37JES6iiS2fiytYJIBvOOtO0P8lpNMw2/NRvMb5FWhrFD/XwvdQ+COoy4Lq66I8K+g6+m"
    "2LvPfZOnGW5646deqZ/+6WVXnS49/GV02meaPHLcCes+FAB/ygHgyzEOOFySsYN/j5xkdUrFnra+FU9qRLGSJZH/5FKB383AWaex"
    "8qEbD0mqabq2LXqKsGvbjsEEBlrp0IGqp6ZjT5OekvcCeTJRCHAiKBqZnNEGMLPaHYMoXvDJEsTLK0n7MPbOVriAzJPeqNNtVnhy"
    "unqrLL3g3i1VbJAEN0vvgFBZCzzBud199VTSmuEVNfLWwJmSoeskUB2OX19h6TRneMdh9tHVeiNO6fJq3LFB4wlU5vs1dZPjcr/q"
    "RnSWPiJNsMYCURZ08j9J7cIXCz+jrPIzxhn6bCxmLuNhNxQrMC1l2jLVL7iY0UAYk/2geCw6UAZqOpiNvvOST8nRB3JPQ124HAfn"
    "N+bPJuPPrAOfwcp+jFNyllfpbl9GGEVq+UvQdzcGzkgmQCaFthBYnfHv4SO/oHNj6H0Jz8+2NpMG1vumhW1VR9XXjVpDfJT+MztO"
    "Pc/h1YOoI/2G4D4VA0qvYi/mFcteekYj63tetjSLFmvgeULMEhJKHOQQkksKCU1iNR5C6dwso0qAI8PFEg3sUvFvwVjlxW71KN6+"
    "7NMCfpfv0RaAW1gFTL0ZGQZX1mOhdeCF8kwKo9M5S78OzLWqsF9pguCxThCs+AcNKSlFE6XbtcXtcZNT2NGVyhyw+3QpPp5jGI0c"
    "sUbMIkyKaFl50MHdSZxOm0+/ktyx9/JlVohL5CC6qcSdC/YBzDpvTZ5byDmvH1hnpziZSm8n0QQA627QDOZdGjo+WJB3Iw1TmokD"
    "0eQu3AIv50724w+fJOtB81WdvNXKVbrPP0UPU7NGKS6MHCX5bnYncfqTtQXRH3uM9m7uDBeukPIk+7aHGpNwjtnsfSFYrerklEqi"
    "eVPOnMdyuzsIojTbJsyb9Po22mzeypdO+qy7E/3QGGrznQtW9a66revkwe4aWdm73hwp3NOjQC/4vWhLbXM2HaU8CRXTkL0Ud/FI"
    "/dB88SikV0Z7yQYUrbWY+gqjkBrloyDP3SW3o3DcnXyPUH6boGe1OkMkHOQhcNk3T0e/j0QIODkqZvSLWR3IQTK4ybOBNJs4zQZC"
    "htuqqjKcoakP0QhG9YmnOtlcsk4P+oUDv9lWMP73KD2fo8sdQhEHynwa4kOI9tujSe9EB9gcNz0GWTMXdn04cLrnqPmKu1OxAwZW"
    "cGeBTBtdC4dEHFRE5m24PBfivNJjW5ev6dleupdzn6VT3D9uVS0CjG7bBfmFRCDcHb+fjFqH5J1pX0pB5FAcFERVXmYf1bXcXKRu"
    "tgqvzsUGjVJSwO64FVxV9aRY5rv8IpouFd9k5j28O5HvnPq+E/NYGwNW6azNj9CqBiHaQKZHZgLE4wi+bMA3d8s3IGiQbFr6dgwS"
    "yKhlf1CTYQvGAraFbzwaJ2tmPZ64fTyIEBoqpNAQM5ngXod0JqMacR3uwL/YHc6nohIMtM2p/OMn2f45HI9GLiXjCaL1bxwkZ9ue"
    "N5KroGpsTAZiZFS5q2ROFdLC7mh/rgFl6XDDxuvHZb6WoEPDqETmdBEitVgvUe8Tpj2nIIBhsVmmn5LZLNT/j+LFyIQJJMeoZI3E"
    "ty2cfDEcsXVoiqyP++C4x3Nz3O8k97t/mRNmmcvXXbXaCqGtECMKm59bQK4c1J46+8MWPoEdQL7hDg8UIMQ/4JS5uuuvQlW1shYT"
    "puIu7QsHPrKUqSrLilKlxtNhJCM3PHsGN+ekV6VCP9UDO5zImYq2aQnFaqHMAd+tI089RgJCxZY+onnDdfUTCPEKQC/PfqyKl/zL"
    "1VZOaKnwXOTrvACrcPayyrO7wwkHGcjfQkZsOLOwH38UakYnlFxFyFzrYc2yiPpIx/mdut+bB9iE/kEkO5e1iOJpTfhwM9L5qXkj"
    "r4GglVMPWbZXaTbJbgi77okQ6T7sS8Wwc+VHxqB6oRd0aF2RIX9umfI8uSMsfgiJcZL8hk6anyGqK5MBRvOyOY3vqt0Brtb1y1EG"
    "coIasvyUhH98OZxVVpj33/6AmvvPv/rtD8CuiH8vT9lX8a9sdwl22Y+/hi3068+//UH8hkLq7Q/b6rD//Kv/Bxn+Pnk="
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
