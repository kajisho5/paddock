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
VERSION = "1.17.0"
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
    {"w": "演台上げ", "role": "op"},
    {"w": "変更有", "role": "warn"}, {"w": "演者変更", "role": "warn"},
    {"w": "演題取り下げ", "role": "drop"}, {"w": "取り下げ", "role": "drop"}, {"w": "取下げ", "role": "drop"},
    {"w": "会場直", "role": "direct"},
    {"w": "会場取得", "role": "got"}, {"w": "取得済", "role": "got"}, {"w": "受取済", "role": "got"},
    {"w": "受け取り済", "role": "got"}, {"w": "DL済", "role": "got"}, {"w": "ダウンロード済", "role": "got"},
    {"w": "発表終了", "role": "done"}, {"w": "発表済", "role": "done"},
]
MARKS_V = 4                       # 目印の既定を増やしたら上げる（保存済みの設定にも新しい既定を足す）
MARKS_ADDED = {2: ["PC持込", "持込"], 3: ["演台上げ"], 4: ["Mac持込", "Win持込", "リモプレ", "COIあり"]}
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
_MK_NUM = re.compile(r"^\s*(?:(?:[(\[（【]" + _MK_CODE + r"[)\]）】][\s_\-.・]*|" + _MK_CODE + r"[\s_\-.・]+))*"
                     r"[(\[（【]?\d{0,4}[)\]）】]?[\s_\-.・]*")      # 先頭の番号（00_ / 17- / (3) / A01_ / S1-01_ / 2026-10-23_ など。くり返しも）
_MK_TAIL = re.compile(r"^(?:み|済|済み|有)?(?:の?コピー|copy|\d)*$")            # 後ろに付いてよいもの（受付済み・「- コピー (2)」など）


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
             ("有り", "有"), ("あり", "有"), ("アリ", "有"), ("無し", "なし"))   # 音声あり／音声有、動画アリ／動画有 も同じ


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
                g = group_of(k, sig if sig is not None else com.get(k), self.depth)
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
            for g, keys in ready.items():
                lst = []
                allq = True
                for k in keys:
                    p = self.pending.pop(k)
                    new = p[0]
                    allq = allq and len(p) > 3 and p[3]
                    old = com.get(k)
                    lst.append((k, old, new))
                    if new is None:
                        com.pop(k, None)
                    else:
                        com[k] = new
                changes[g] = lst
                if allq:
                    quick_groups.add(g)
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
        pend_groups = set(group_of(k, s if s is not None else com.get(k), w.depth) for k, (s, _t, _f, *_q) in pend
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
                if group_of(rel, sig, w.depth) in pend_groups:
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
                g = group_of(rel, files[rel], w.depth)
                busy_g = any(group_of(k, s if s is not None else w.committed.get(k), w.depth) == g
                             and not self.mgr.marker_of(k, s if s is not None else w.committed.get(k))   # 目印の出し入れは待たない
                             for k, (s, _t, _f, *_q) in w.pending.items())
            if cur != files[rel] or busy_g:
                for did in work[rel]:
                    self._set(did, rel, "wait", "NASへの受信が終わるのを待っています")
                self.queue_n -= 1
                continue
            self._copy(w, op, prefix, rel, files[rel], [d for d in dests if d["id"] in work[rel]], gen)
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
                        b = fsrc.read(COPY_CHUNK)
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
                                 "img-src 'self' data:; connect-src 'self'; frame-ancestors 'none'; base-uri 'none'")
                self.end_headers()
                self.wfile.write(body)
            elif u.path == "/api/ping":
                self.send_json({"app": APP_NAME, "version": VERSION})
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
        if urlparse(self.path).path == "/api/handover":   # 別の版を起動したとき：この版を終わらせる（専用ヘッダーが要るので、ほかのサイトからは送れない）
            v = (self.headers.get("X-SW-Handover") or "").strip()
            mine = getattr(self.server, "version", VERSION)
            if not v or v == mine:
                return self.deny(400, "same version")
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


def request_quit(srv, why=""):
    if getattr(srv, "stopping", False):
        return
    srv.stopping = True
    if why:
        print(why, flush=True)

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
    "TIka+rAvoRdNZdHu9jA6dq+/dnR0Up6l6i6JKIx6UaWsrx2CUWTepyBg7nb0fT+gvsxR6WlbmCWW1ZWVqWyuNH63rVZrpQ+t/VYO"
    "WvO58sx8aMx5ttcv8jSF+l97rbH8jeKLRCq1+3qRG84h5tEqawuiTo9QkBEjllfsOAe+ax4BUPqoCSojBisqVVlSybEJS7D0ma8g"
    "b2w4cAWClTomkI4oScryTEgjYIMls4aE4p4SmGSM1TLUi6EIApcm5aC4D8sZjcbxoBWU1REUVfavbBpBUWX2ChNpAplcGkTDkORv"
    "Z1yBq2pg6tq9uDFeGxMcmDJF3BvWQWDSiEJaHGS+nprRkzGGsNS5ncazlBFwopgt0lLJV0O3LLUig5Tp4OjGY/e/Udesx0UdGR8i"
    "/h1GheOyY4zZzCKtTq+S/2ii4aUyUbZsipH0qr9bgUquptMq0d+bSkarJcuBk3tpU5OZezE1bwjRjn7B+ZuPqeeLak1Dqbq2Ipg3"
    "SRx5z2L89yX8+w2JVit2ETIHsrLdqb6s1VbktKOk1wdOK+dfF+hubWFCsFCjv5aM7xsmZ3l5yWOaHr9qiSOGLKrDl7k3hDVQwlcU"
    "D79SnoTVxdkKXuG+KT+8SpYoGadKGlbW4hHgIirE+wPu2CK0ST7Z73/SKt96YRQqo1HN/LzC3W9v2+wtdjpS2lbJaEVrjZ6HfOP1"
    "lIzvl0s1q+NcHHzMDlHTdDApDsMEWEArMiGeTRPJgyRK8+NWAOinH2X9GNAPUKn4lObwGolJBlCTYRGdxS063drOVD7EgFMH1Az6"
    "pFa/O08Gca5qRpNBkktpVgqQK739bKxTDKUrK/7X3rPxQXpYaUA6JVP75FhcG9jZsWo+OYuO9QgBZHxwvxELBjiIEWCPqXKZHx+n"
    "9alLbuJpHwN9UDtJBpxAUmtK8xLF2tHHAjk8FVH08mM0fgb0fjJK42BpKVk7Uw/zKxqzzMSLxo4lxZ/4WpqpUQBReQnSkEmd0NPk"
    "ewIUXTdvpJ2i0NBOvWINR6EIIUW9JmuLSB+osNReXn5ceM53IiKtTHhg+xIRkNesP0WXLS9XOwSy7LfWJ7YF3daJM6J/NXGWLybO"
    "YM2b+cwXBSrT39M2odHbgm2kWvf6XvOhkRdrRNxd0MgmJgsYwcJhBIuwmrKqYBHOHZpOWbGnJoMgzP1WLw2AH0WX1vsqa6CQjm1l"
    "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"
    "96vx36+/ubi38+JvgIQ+MLXXJQduPPJV3PfnxK5uKtDnr4LG0M955/IU33pGiZtC9QElaj+9I8QjxBZTU3vbvswW9Z9F47F47eHo"
    "7h6Oz5eb/isJcAlfqscdi3fL08cNFk+Qel74Z49g+4jFdy79/uuFcP/V+6//9fuvf/z+q7/357+5MJS/fSfZP/jTn/yzP/ud39SZ"
    "Oyu50fD94m/dyfu3H8n4FYtdWv2gNT41/eP3X//mremv/uD914sY+Pp2sbTx87v814/C4C/+6D8/8rC/+KP/8l9/7e+9//Hf5MYy"
    "LWq//g74Hf6W/FF/Z2nk6Vc//ltLC3cZ8+/vLfzWnQUtrf0fN4705V9bWNBTUueX/+H9l394Mwr+y7/785/+8a3f24T+7vuvlnZ+"
    "+v6rL5euF572sz/8w9swbg3+w0cWemdZ+Ku5Pi3qwy8A3l97xQR/++YNeFjdHMj3pTw9nVH0ITGrfGZ+z8brqX7MzL9vjfr86QcP"
    "tn/f1fsK3PWtcuttu3Z+u7htg2s/cgHVn7S/jKDQ9753D0K45+Z2VMC9XOpxeTa++2Xi5zxylkfT8uhDxwtive54uf15/Wn+cPPn"
    "tJ9+6O5h/PSl+Yfp5dr54nnk32RW9FN5KO9WvrTO3tqf/fD9V4te8Fs3RPnq7z3myz6L9N9+/+Xf+Is/+ulfekm4ff/VV4uRd3v2"
    "1V9/fGNZ59fpuDd8va3NP7krFTfM+pN/808WBPmz//iffvY3/uG93Z8uysMdmxf0XGTnX//Tn/yHl/6WNX//469+eC8p9N8d1ptP"
    "/weG/khLN33lWW5+YwK3/t691sueecYttHBP/XzirE81It/m34mfCooWwXduZYieStEtlJe/cJHXatAXHwIi/1NhkLsn9tWhIjfh"
    "9A1Z56bp3RnwTRnn33ib/zyq14y2Kj52qT5FVJ+yHm6h2Bdn3z1i1d8//ir02fL5KfShnfI2ml95cy9T79fL+G8lmJZfP10Nkb9o"
    "D7/64ltYBvQivL8VTPKfA0kfpad+QPYvHj4vbzGs3r/Vt/Dcchmef5/3u4df3OrHY8viF2P922/e1a6XcNa3TZFXNsMi4+/6zCvN"
    "5INOdE9gugnIp+DAN3UT/xcqI3fM+Niomu45t6/SRL94gH3k3cNzk+X99LzHBv37+6/ycl9KyN33h36I5X3c7cPHgd/PPxLZz6T7"
    "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"
    "zeycf8fT2+92u/GxL+OfZyfxCsAsnk8lUq3ihN8rxWvhcakVXbCe2EDazbIteSfIJqZgWrmz4TY/d7dD8dCswLbn9Qnbo1rdRHc7"
    "lchHk7G4OA3buYboDdQ4P1NrukT3cMH1Ktmd1qDbn0lOlh15KJ6totOLpd1yM+fL7oNm0/XImSQ6zcJL24PcfJ+rDBqzYpFfdMdZ"
    "f6tTrgT3pVYmHioEu6FJ3H7gLDN+d2AQ362EmUQsWGFmVTE77ckZccgN+yng1e7txFyyH9Q8bdCRg5PK3pgNNsd2JproUtNYP+aK"
    "caVomeqzSTDmRnuMkOvvD/vbQ97LsAt3LtSkpr1hviDmB/3MopjbZrwBNpXrJ4fRZDZT9TMDytUrx8v28H5vHBzKtfZ+x3/gSwuF"
    "XnhvtnD3i+VoMZoRYvEqO2350yMp0EvQk/q0kNjj83JicLCTl5r9TN3HhtuhjB3s4DBHVz0yy+zOvGGnS5zmymm5avdh2doXxp58"
    "O9YBCRPd249CCS9wR/u+i42Omb1svZIfsLEClwmm8tHiEHTR/jjklDJOT7DgKjFVjk4WRh5/yisO8q6Ws5zpBoKB+KAP2uQgnKqB"
    "zbcj+Q6ylcJOio5GazvFJu32gsZxkJ9nGr1OLbyzGz9oxpwSE/Z6Z65erZaspIpJju8V6v7piK2LvW6M3xen0W6ssb+d79fkNLeo"
    "MD1X19sKZfvZ+DYTPqjTo8ZOblBAfEss0q4yO/CyiT5T81JpSha6/LzUT2fZVDZRam07gxkpQaeRP4Wj0hVud7u/M4oWm73QXma3"
    "lcp0o1RqNx/1xaKeGBNelIQhEFcxKhcqtboYtmd8e9uVfLI4q4zjHlcsGx66xYGzxsWoEFtlMotsJllrhO3DZmwRpqLRhRxK5mpC"
    "aqcSbycbQSDt3LAWLE6z6bCHne7bYyW3J5QouhrBjL3nKlej4iyZ6BZd3VS9lGRyNF8GsFLpaiLRSIQ9vb1WsmHPUdzOfjdQm/I9"
    "V7GboNzzxo4n7q/kMrv1Jptw0jvtWieValZiA7CC5ztsRq4lEhzD+CUPEE5vtj9Piwt5sDjwRmP2TImP2u1OqRKNuQpxUTxI0rHk"
    "IDPzxARvc9/d7wjdnUQ1kJyFOtWA3BDnJftBuLmdqlVdUXupKTdSPUosNnn3NFTfbVWrHe4g10ixi3CgHhiXt0fVvghDSoycfd4X"
    "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"
    "Cf2TTa1DTQLHmgGW1MylurdxirBilJHmFeiO8bFAQdEmcqQEs18kVSHRI3Rr79qXO2/fkDR0c2CcBgd+g7xLCadcYE5K6O/sXLv1"
    "zaUvQA4W1kibZIlw+TjHPCpai3hRI8sKn2acLXtlFHxkUMaTTuHFBxJ8+EwYKLoIwsBoFaVWdJrlRmOYLVjYbWEoL6CRA+jq0mWY"
    "nXzQC5QUDx3XDmmQRkDuG5zqhd05iLdEluo2rAHQDj8OLHEd5ekMv+iyUJA2X9l7e2PvtfeZHeqHauJrRhJXmkMBj06gqJYbfChB"
    "l0vAsuEPA9POU7lbIWYPLNDaXMhECj7iafPVuzDfSH5GuN1VOBfubF5j7VMqi6+HYbVwMjQ5e4Yr7KbMfvStc6RNJWfUvonLQc0O"
    "rXUp7Xy+E32f9q5mHo2Wa2vpmqueU3VZCyTQ1Ko+VxQO/G6rMrgWdHyG7772Z9p7qJneXX+VSBuGvaVNqdqcb0jjm5Sulu7f9jQY"
    "RcqGZIqA9Rfp0AwhsPniNz/9cOfKa7hS0eNEeU5uGhnTkXjM9NAjZzlSzHdJqiDC8jNTbDI6Zelsa058nE8B0zbarmSqzvBUzyar"
    "BtDLGR0cEI8p1CW9JVAl4R91AUEDS/SvuoRrX6J/C5ZAgFH9kPcgtKamMuqIKTNzk4rqE3ENQ72SUYoZKNPk+Wbh1vsFVQ1CRjNJ"
    "yIiePv/rMse+Tv9mePrD3narMpPUXryPGy80VGXYUpW2+668tvfqbQrZ+ZBs+7fg8/FTJ+Ff3oB31zeQPcMNmpVw77l3d176iyW7"
    "LnYOv+Rp0JTcANR9PB9yQoug0jOdex1jdIio/Hzz1c/RPkcii7Wfja46E0mZ1rc+rBMZINgWI298YDI3Ao4E7H48UrpYEnY0CIkg"
    "AQ09W/ft1SVgEQhpK0rLtxsppgC8L7N0cJhCxu2QNrb31naob40IDEsiAGWAZ7JAVRX5LWexQLACdzrnOjCitlNNCfxb6RhCwcbb"
    "ux/9moWw2IpG+Elo6+3rh26n22yW/YtMkdkZRWlra9DF1jmxmpO5o7CIIfVFAC1mWMY7Zp8OYzxOFk+2546B5DsPxIC57vjfvH2m"
    "iNfI5Oeh1we+NarnMKRKSCfnsV50eDXXz/z1hVcyfFEWkeZP4gH1QwJK8KgoDV4744G2chI4v1AkT84dnretsu+WDzJuD19RbZ2E"
    "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"
    "ZhIlLGC+B4tVkWDTu51PT5LbQ/SGLM/P53ovpe8vxUbcFd2+Q6TljvIoSG+s27esj7hKHkrJ+SPoij2urBMGG90WhWMWbOf9i0Tq"
    "TSbuUpxHWjJLIaqnwIvx9uBHlTH29v+0MR7ZTAIS1gW9Bzp86upQKPyb2OH77TQjdfN5yEYnj7Xa3vTptY5Rx7EgVWqfJHINMzqM"
    "5FOZJhL/qZgAKdFfcREKwj2o7ntFu3T8WaeOP3GMs3MpB2Pb9ouQJ+zIxRV7vVieNWowblUbAlcd4j6CTlh3o6oRJGL3q0FYjj0F"
    "0BnRotnyWLvJZKy4AxwB3aU+LpUht8XLfXDHnRraJVItk7s5yS7iO2JB+fx5/HU4Nis62ET7RtRdbFq6kJdDuIOP7Fyd8rtHID1n"
    "NMkg46n1qT+dckoCicWogKK/kz2dEzXPVU8/FTHVtbgnRbNCUSo2AU1eFmgJWMYC+3jct0vRFoN/VpO32Scq/ayvfXSfF7GU+3pC"
    "pF23D9mAmqlAxVb2gLPrxfPm61sP87hvaz+Dk+/suLnoETFRpbLiFQsyy6DOgJbrzFFU4cOl91AqN7LvPY/ece3SsnB590nhbB0q"
    "SpM7V+sy38TAlNriqz2S/7apD/vAuI8Cw1Ncw1Z2t3NFJY2e47ayMmJLqgtv24wnqrf1fnd3sC2dOQ5+0cFo5mK/C3kk/GgELH09"
    "3nlHr7k1HR3lG1Rd7so8916X6cPPrPQYUkgt7H8Xq3vr7TMyyOc2Wfq38h0zCzR154q5C7Mzvgt9+v5oZBWv01sdjYmfjo/DgkHs"
    "+2UCJXNqy+3yDqMLunxvDSRfcLk4p04uThIh0c1E5YY3SzLpd2ogmnABIoEMeO9vcQCV8n17XO6qhw8Bx9Ud7CAR+uMDsS6Wv3Nq"
    "tbddBUM8sxkb3GlVDiS+CzF3hLwNdotZOYzHRgbiagztxLskbDJZ1y3xuy1dJbVlMQiSMN/5u8SlUw9KTwpIs+HMB5lzLEukr1YX"
    "hS4Hju6IJf1C9ZtkbDURfdIG0narhjLRhAXpl48hB8Vuh6Si1qfz1lHI1afSDt2dQ/1B3aFFItDpjY59eO2bOmjb/0ujAGkKKA8p"
    "pm7hqTWoSXBpML5h1+SOp325/Old1v31IE/vkS1DFr2/QHfpnYfhybwsDCmJA2WpCp8B4egmjNVk3jM8WrdQQoIyaKjZgNMZaT8E"
    "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"
    "FFJPv+7r0/HH3/4fWiO7Vg=="
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
