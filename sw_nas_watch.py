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
VERSION = "1.16.11"
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


def request_quit(srv, why=""):
    if getattr(srv, "stopping", False):
        return
    srv.stopping = True
    if why:
        print(why, flush=True)
    threading.Thread(target=srv.shutdown, daemon=True).start()


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
        srv.serve_forever(poll_interval=0.5)
    except KeyboardInterrupt:
        print("\n終了します…")
    finally:
        srv.stopping = True
        mgr.stop()
        srv.server_close()


# ---------------------------------------------------------------- UI
# 画面（React でビルドした1つのHTMLを圧縮して埋め込む。dev/embed_ui.py が書き込む）。
# 旧画面（下の HTML）は --legacy-ui（または環境変数 SW_NAS_LEGACY_UI=1）で使える
LEGACY_UI = os.environ.get("SW_NAS_LEGACY_UI") == "1"
UI_PACK = (
    "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"
    "BeDJmavceC6SymnJhXOUnYjvv182Ha5ibqRWeq/j0BxbUUi5tdrs8wTL4+bd9gWTvFJABuU25DevoBNrkGKysZ22ftYe3/+D+JBJ"
    "tbZ9FlSA7UdjqKuCCdZdB98ML/fCGWYY6ZZug777WT1LNrNaelt3arcuovcxNrOo437SPNIld1EHSycS29yVjfNjigN1yZkJHqo1"
    "fJcyWQZ02vOYVHHrJuz268Qzbgjr66iLU/NBvQci+iYcYqkaMymuNVSX1gExqQYxxZWLz44XTEVvgLq4KQyqenH5UUs+dW/1aV1e"
    "ru9I7i8G03kjmE5kOlymfVALblZQxW5GX0geVpBCZargLSq3MhrnsEeqPkb1tS+p1GJtcDw2AuciBIAW2tTZt3xfbiUq0pSLCd/H"
    "OUVWBajM4YMkQh4CyR6pEZ3HxkffRMTMl1dzFe5yM0jDdRW3Uga+3IaSHV6yvalCYq7vyB9w5uSPrc66egVcgXrX3lS1Ntu3VLWd"
    "zi1dDyObyJ8b6ze3VU2ppJYVSF2lmtpe72yq2lvrm+s7O7ozSvOq+yM5v+qSBE3qk52NnZ3ttv5m++bNm+sd9dHGxtbW5uaG+mr7"
    "ZqcNVXElNpylgFHt3GzfgknCGm3vbG5sbW5tV2J8pmF7noYpAsrxZExJIFQegtzvtTEot/S1xj90lCXtSqbE5ilMZfz2lNxUC7Id"
    "RkcYDdW/jjy/eq07lWttQsvw2Jc9z73D1QsefnTsJNDeS5p5vsKhhZm+9YhMGCEuZOpz53QD6Ynmp5SKfpjV8MJn8UGcrawchveg"
    "jv79hP2+V4p7yNQkA/EE/+bncTFM84/iXiktmQmwFgyWWsYXTpoTjOHDxMbUcXJSuCHnnUQoNh8FZmQxsTHdGAhJXYVUi48RNqs7"
    "0ST/HgDNj1ExGKNXIbGaxm3QPELlQgZubpM7YADUaZSkQUl/niGITecAh9dYcwpMqhZUePy1epNEFWOjmMR8DdsLS/UDGw458/7V"
    "p5W8LDaqQLyA7VDKFWXBYIl9pB44+1QAx1OEQMDP1h0sY6MH8jwxhsOKA3TOiE3s1NgJH8uMdpq5pOVlOhjoz2ZVVyb2q9/00g3j"
    "GrthXKVDZj2MK3FeNhw4pfVpDOQaVwO58gLTADMfiqtBXM1BJfNuHcR1OezgOIgXLByKzm+iOuR8FW5IJWJowbDpbLVozUtDGMvs"
    "C93SZmkJmZEQu/IU7ZdFvQ4p2HBpGBA0K7f0YWo60EBKgZ7UfiJKh+z0BdzHTKBxP8aJ8Rnobr3XV8MMn5xuGzvppu4xAiT+qflY"
    "s6RU5/KyrJUwvzBSdojdxnM51LbiUiqjLfPjuDyJi1agZySt/PEfhfkraKdpG63BSkVqpDS5lw5lz9l+ZuSl3AtqBYanYqawGY9E"
    "zjKKuNmQ3AxQPgU6UaIBgUYY3JzCr6Zl4Q4R+i6qK1fLo7khOetq7GUHZGC4a2T5YweaWbYDYzBoetNeWnbWY3sY7cFsbpO15B7c"
    "hRs1MQFF1GXMWEKEjeANRkMTKFRzqJTgFMsdGi5A834Z0Xt5mdT+/PVmsB9Zb4V6ojy3rXagEQAZ4B5poWBa1dUpC9uvvLuAztxE"
    "XH61QN8b1cdGQLRqVTRlCFdNItdtLXsSylncstzxmxgXc87YaesZiV/Q1EocmhMumBGT2slA8gH175yJ3ZITqx5zotI5ZiNaXU/T"
    "oN4unwiFX60tEZMapVUSIJUoniVSUGHLJPSsDB32SIUe53dQEtmaIt8IKqZjbWGMweauAZ3yRfx6KF7l4puhOBp2vx6Grr+bDZ+t"
    "MXrpgGJtibqFMdxVxkDA7dEILxr5HHkskxeL7YOVlygbZFmBBqWLwku6xnUUXloMLBF42YjAyyoC5wVqO7vS8JTwd1nF3/oNhybz"
    "efdVzg3C591v3JVzXYlq5oN4Jri3FWlJ3LD/2gQWZ6JgTakQf5KNJmULGJtxLlmSQv4qkGU/OOR4axynqDLHuuS8mgrlDiGRFoXa"
    "lW+K2ptqWwhTInjE1hLTc1LvWaNA44GSZ7tpgplUGlS3hX5b80rJsz6VfwCiN8qlOyUppro6Cx9s+wB9gFOyRyzQzvzFRwxqP4qL"
    "8sJDy5u0sfBgcKj8/+DDQUhZMi/SWPkiRCFWoOZzbD7yo2orOUreSooTdol29wf5YdhqKdMtPMutQZQdx0U+GacXe3H5JAPI/Xj/"
    "2VNlH9XShLd+Hk9GI4zET/xbVj4YJORC/TYqMpm906n1mEAsrFTlfTQp84d5fzKmFWxYkF4CY8atIkFRQulQpWhPymNUomta1UJH"
    "iCpwNWSWmN4a/BaNK41GGRGGh15SNy1SS1xdY2xJQha1uksNyzub9aHJpvKGZbdb1ff7TVsVQUU0lIA/9X3DUrVz+MasEOon5MqU"
    "qKEP+xJ60VQW7W4Po2P3+mtHRyflWarukojCqBdVyvraIRhF5n0KAuZuR9/3A+rLHJWetoVZYlldWZnK5krjd9tqtVb60Npv5aA1"
    "nyvPzIfGnGd7/SJPU6j/tdcay98ovkikUruvF7nhHGIerbK2IOr0CAUZMWJ5xY5z4LvmEQClj5qgMmKwolKVJZUcm7AES5/5CvLG"
    "hgNXIFipYwLpiJKkLM+ENAI2WDJrSCjuKYFJxlgtQ70YiiBwaVIOivuwnNFoHA9aQVkdQVFl/8qmERRVZq8wkSaQyaVBNAxJ/nbG"
    "FbiqBqau3Ysb47UxwYEpU8S9YR0EJo0opMVB5uupGT0ZYwhLndtpPEsZASeK2SItlXw1dMtSKzJImQ6Objx2/xt1zXpc1JHxIeLf"
    "YVQ4LjvGmM0s0ur0KvmPJhpeKhNly6YYSa/6uxWo5Go6rRL9valktFqyHDi5lzY1mbkXU/OGEO3oF5y/+Zh6vqjWNJSqayuCeZPE"
    "kfcsxn9fwr/fkmi1YhchcyAr253qy1ptRU47Snp94LRy/nWB7tYWJgQLNfpryfi+YXKWl5c8punxq5Y4YsiiOnyZe0NYAyV8RfHw"
    "K+VJWF2creAV7pvyw6tkiZJxqqRhZS0eAS6iQrzfcMcWoU3yyX7/k1b51gujUBmNaubnFe5+e9tmb7HTkdK2SkYrWmv0POQbr6dk"
    "fL9cqlkd5+LgY3aImqaDSXEYJsACWpEJ8WyaSB4kUZoftwJAP/0o68eAfoBKxac0h9dITDKAmgyL6Cxu0enWdqbyIQacOqBm0Ce1"
    "+t15MohzVTOaDJJcSrNSgFzp7WdjnWIoXVnxv/aejQ/Sw0oD0imZ2ifH4trAzo5V88lZdKxHCCDjg/uNWDDAQYwAe0yVy/z4OK1P"
    "XXITT/sY6IPaSTLgBJJaU5qXKNaOPhbI4amIopcfo/EzoPeTURoHS0vJ2pl6mF/RmGUmXjR2LCn+xNfSTI0CiMpLkIZM6oSeJt8T"
    "oOi6eSPtFIWGduoVazgKRQgp6jVZW0T6QIWl9vLy48JzvhMRaWXCA9uXiIC8Zv0pumx5udohkGW/tT6xLei2TpwR/auJs3wxcQZr"
    "3sxnvihQmf6etgmN3hZsI9W61/eaD428WCPi7oJGNjFZwAgWDiNYhNWUVQWLcO7QdMqKPTUZBGHut3ppAPwourTeV1kDhXRsK8tR"
    "8PnnHz9+XPu4sZYXx593bt269fkUSXaZEmAPHZf9a9TulcTs9ItkVAJDEKNxO0XZV/kJPYBN5y0EyInmG8LWbVn/zu0ffK5+tVR+"
    "9LP8PJaSFJXwmx58c8IKwEfsUNe7K8VlghmFk/GcFIW1976QI5ZbBZPNMSKNuca93PyE00jk3reoHs3pRyifAZkFtaaf71EcWxEr"
    "oB0T0C7E1xIxLXXIbpGjlhjzz2odeNjPVeiYxTA95jCdLkXx68H1+re/BmyP/W6lkTp8bxjktWB8zGB8vY0mON/Qk4H1JLNJjdyI"
    "A9/YucD6zlbnpe51fDUyKBgySBdKmhb37qAJNebkqjFbrX8hUUiKPisSfyRS3IDyhyqQTEw47OggOSQVsWI4ew/g4gFPGiTfne83"
    "PPGubEM1Umfo2f2l9Jl23tKHrNVCu75CDoR9ZDALvZNcfnItLj/5BJefXEOclPg9M8PkKq4/MNVGEUVj66OR5WJ0ExO6QbPPpc5i"
    "dBMTumk+rYVUdSwZTnMcl3dLWOL3kzL2WvRS4szSU3V9v/l8W9jHTjNp02VUjkTFcC5QcODWweEHhfbLf8NHVK/t1mOIdpE49UqB"
    "aWVtYdolrgtf6Dp+tstb0GzN/jtJsiW8IvdSXayHiF4H83lVuJJpzqOCo5vdgRcwltuBDBRZZ3OOJDapiNmR3jRRfW2cFiM3uyZD"
    "Q7yWy3+JZm5G6cdchqYyJIUHyUYPqRJ1JKSbdBx+Zfk5n4uerIKRKEHzJbB2Xsy5n4rasbIk1yIzr2h8njRQWDdQd+aSWHBUXRLL"
    "V2TBPpwvXBqKGqXWgu9DsWjzpfrxyItRT1m3j/+E7X3NtL+upKTt+2x5+R3np7XV4pLjROCfDT2p47WH99bO1nabXA6MhisJ6Vww"
    "4rRY0G3MM7Ev1bK2dnbkMazlqoP+WKyAqldGQ0MY7jqRyy63jibhzo52uCF2ALPl6srdwdnKZq4QcQhya5fzqtjFkk1hLwtcfbsZ"
    "CRrG6XwIGdmi65WkJfUWbq51uJBwSGoT1eDR0JHZo3KJENMQ9+ggY0Qj+LHhB2jdR5bPjO9o5DmYHMfXmnydrRTXWot7bPCEqPAW"
    "a/lrYqFOWzf3IvIq6v6G2jevLYyTanB5wZoOmqvlZ19L5XnNySYPmXWb0Ab5PunQn4w9wowGPI9wMdtu+Ajb3lUGZXlINj8id2xJ"
    "HOMC3Rua2DuBHhyu0WUo+Y5mrucDSqVL0aQOTzAIMJntKVNvJVvepsWw9krGO6HuDqOCvWjnAm0mWBlAJZaOrtVgq57UI5YkrumP"
    "7sGGJ1VG5HxoORdu61HmykBIj1VVahqu61dSG39ewZI1Z4vqaXRm5W5qIl3RcyUcpTRodrrV2dvo2qjHuJR5IHSsHclrK782zXrL"
    "x3lFdaKMQqqGJrN16zzHrf+kPac5fv3Y8++cjx0HXTi4SGDZ06uBoTKgthkLlgqfcAhchNxnmVxJZlttrqwEOykX3YHSuQNyFG1f"
    "m6Tqj5hhqo0NhO6h9rjD02d1sCHxxvr3cOqrTXawtB44Ouut9t3Wp+uY3/ZIWKGUVBUDw5ySD0qrW2HDUFnLscDU1La5uaFSna3E"
    "bIiywDX21ctm1H3Npr99mUfO8dspuU2utBbt0ckKpBkVjL2Gcuq2QF9J6/RmrxLxKUxaVZciDvUxYrFxOXwTLzv7pIbkqt+2a234"
    "QRUNrRt0ycq2eNm8alO4rXRbzOxxqNKpLdSALVZSIaKRerpYESh6zGG8vIolN2dksiaz9FQ0Wc26q1qbSFHGhNuu07qZ/qtoMVF8"
    "ldPoInI3q0UOrKU7wUzwSCTObWKX7748QFuoz+VY7RuXOLoumXOV1Rud9IXnybCp7DyRDdyXFIF8l0K3jZwQrXtxWQvRCmUBBrnc"
    "V6oJfe7iMY+TRfo24h+XLPWjfd6doCEYXbZUCSZlONnCv0yVib62THETSdqcaLmJy0qtNLZAc/w4cSI4nkyNncNpHp6neISQsbmL"
    "AaypWMkGoDLBqBYlW5BzuxxjSYBiFV5FAFDjhQ+ywVwyRHFwWQKfiF4jDmPIwha+SeKPs9nHJBvkH00qSIySoFvDuvxZJvkpkLEq"
    "UCy3K4MLAaN6iTrhKOuf5AU530stqi56MRyijxf5yaFwQ4aI1U/yLaVRtGwtAGz9U6W1K5lNxo1YxvZF5/JwtSP6+M8Ankbw/yHQ"
    "c1NlFELy427XmlUedylI2mymfJCGpht43iD/9HwFuCislcxmxYJafagFLPWQs+EbKKFfCYeWoVcCa194x1DMVAmGhJ2GQxjvcVcP"
    "E9PNok2GcnSg2KsYfaJcXl5ZQeW5dIUGugNLEywdhRJb9LGUOuIeSPomKLPNcAofDtcwBGRGgoE59D4vQ7QQWu3MZn36q6gzeeQi"
    "OmP9uc4cJHECLqGq0KYKbacCTehDHl7SDscDVE9gQGh9kl7h8cG83ecpQgC41919S9cDpAz3hTVQ9yqIrdNWXI812feZb/o+KjW0"
    "GQlr9xJaNSmwMVqOkznScFQYzaPB1rxirdHZChzrcrzVThTLD+Fphcz+yEokyjhxxFeT8GRRkBLPCfREgZ8QsPU+sIhPH3zxEZBH"
    "NStBY5iayZwNfoOs2c/DhWxx95yf807vnKtGw1YrcN7fWl4+XxsoeKP0UljEFWu1ChU5mhJAKpyleeuKdLYiPNzAdB0SFu8SLM6M"
    "Q7PY9aVZhCUIY+bBpE+Oro0HSLqw7JtCjZBPw48TQZBdnDLPsHHVMojR9pJl19xvr1ir5u8uKplWETTiJe4OcoQIHqU0WZaZaLSP"
    "XarTTXfNLxV/lpKY6qi138oAUYmPHpnUqIq3LA2ime1Ylhj0lLnjd0M7VwefOYOH6x9mzuDL2uARzUjxZLc0Yy8Akeqkn2qIhMb5"
    "EB/m3LxNIftq/zwGTINEdyvAdHHuSYKSeVOG6h4mCApYomk2lu8vSI2aXeFD9H00rfOtbz3xAlVmPa7EEdD2/irotgUXrCdqIr6R"
    "oahRmIdJwR72cvbwzRl7ODo7pEG5IgkW7EMPsyrFiJvEInGjC78b+kLPs9phVXbC0rcPWdrE2LpA6J8b9uem/eo5xTGPHSLgum6H"
    "n9ky1wOLuR6SoOw67ofdWHlfbCFzIH9u25+dHT0IZdZWNZdjs/O1SwZ6QS70vZyTw75pz4bytYvOzvKzvBq5HjrTMethlQvpZOKe"
    "vp6jg9jplYyqWEso5ZtEOQRWgrKhzKs04aHzh22F8hw735RovZyRrIQ7vMS+FA8pP+08J9xE6EvnqZrNMq2tM8FzvYwr8KyrTCHd"
    "ZLzYBg4xOiLccrNc7hYbOqPxPcvE9GuudtOauqtw7Rk8/sQMGt8TyX2qLusgc3ibN8bvUbqWljVhbTzSTXK3HsvJjZjj5PPMWNk/"
    "xz3azc/OkvJh8j4uXmdn1bCaxM0tqOe9wxAkOjG2VtE66GA3hts1piz0Wu+pcuCivfAg6+opmzmKU5Q6wwqk8IsB4QxNj05jOUGW"
    "Vso54zG/JpwkKv2gWuAHp5Ui5tnlOtXtBN99KPuA8fl1oxFwQm95GatQbiJU/vsBPGKji0YBvL9eNVyjchE9Saen3bSgvLUqwb1p"
    "CG8EbruxtKlfpGFAGsqSKpbE8jEzDiewFDlFOgNNUiUkVTwmLYfJtZEgXE6WN32iqjClQ+6LZqrKzKxb5RHkuNV5Q81GPXNcUQmG"
    "2XDi6cgXOklWVeetgi2WVc/RxnaN/CIimhmnFS2YwHonaC5fB0ikM3HsxpjsbTfGwKzN0k+77VC38GttaqrMlHMHhwmnuio0dsZI"
    "+iop0a0Th2XIvEMcaiT+eGM0JQVsXjyIYG2MS4txMXzuJlMpfCBlMelKQf5SlHQFVe4yvUpKuQ75PPqZG+Dd0ICO+Mo6mLS7xe1S"
    "278VKyt6GOVBcWhY2iREXRfsX5h3FdETWeZXAb/IAX5w8SJ2AiVU56YnwBy6dZpusvvF5nf4Yh5BTUVNIQe90DIE5aKAIxIZn9vF"
    "QtKMjEUo6PYtHOhzMta3ziBEX8qTP6CTj2neB7BH0vTeETes72xt0mZkRgvJ3I1GHuWHZ85FjKkauQJKq5REvE/UWROTciXo62ey"
    "wwvkTkQBAIkkkcCCbojYkO0woAQL9PX+oMSThjz9APyW/GyLf3ZF9bkDzKrD2Oqs28wEQNsiiNOuvBXuvmESV35t3MI31puyBeI0"
    "Mkx5if6gVwyfZJebFHeD01ap9ppsTj4CV4rpqJxXQQJ3TSbhEv06PKpDIaEPJgFwikgkTcNIsyexbquI0PIVS7LozJivfRxQTk/R"
    "z70IEI9yyaOnRLljApTIb/c1lMhXQrVaI3K4FEP8s9I57I5cW8tUDP1gdKWt5S6vZY0padGxOIK/IzHE+6PBjGtiWOReLcCHMX17"
    "Pqi91EZyMmh/6pq8rjGL1+4V70LuGqHikScqIsOxtSFMBa8njsmGEMNw82JyGqibFTZ8n9SsCoOmSsbW++AwaLWwT3+eSheba17B"
    "7QXAgE7eJ03t1jFPmHMP6ml38JCmVpx97ZFtNI6M3+/yCgcvuhspGpVUAusu7tyhQZ2OKyE13EHZKKDaOxG1pOQImzbTLilDa8n4"
    "Menfw0QsJbNZ2uBvycoa2wNa4U1EamhfLREROBXiCg12woVrZ5TKDgk2kCTYSOgZ76K7bg1ok1b4ktzFm0co+FmyU0bP36UR6a+l"
    "uSICoH2gP0bGa3NkSQ98OQz3wxEXxitAMQ33xXE4VfswvRYSBJy1KaZQuQG7dALAHfydFPZPGb6wWsHTT5Pal0U4BTZKtyeRDXAr"
    "p4r6rlqcnirqu6odPr2a+panGqPuVu7SVnU+tbMxbbbGu7w78Ya+jeAxPzZGE0ZWNRX74bEfUM35KBwZAkaSjyN5BIZhrHVTWvJG"
    "TyNjRjkKhxJYhENOTfboIhGmMQlw0S5c27M7slbnDXrsjEdpdNESrQwWDf4ksHpFGWVlyw8AxsrXoXzrB17kdN2Hp4olLo0iD41h"
    "fC1sgenS7/V1+1LEHcmvTad3B2x8aFd/BVica5nM0ERrcdYOl42NnEHbQa/VCirTuKon3ZHsCTZ7fR01l+r3xmw2bAy3DeUkmse6"
    "lShRrngRNZXDhrgwXGGpQrsNG2Wsw6qMlRXYBnBl0Ft2pCh27FRxCLVXVdmrrkkfmdAxbvChBrxUB7qdiq7J+YjxcfRs+FFJzyMD"
    "sbwuifI4YAF9YgNDHJPKz4YmJVWhVRPAGfEQOXVmSNNZhcPOabU7S8RqKGfUHygiWRQmOO7Gho57Q8LyLkn+MGVB18HnCrVKpXux"
    "kLeLVCskASUy9WqVXceq7PrVI93357Ed5jxbxpCWNnkyFELBTZ611HjnIyIqR7hT5mU54gJKudausT3HTXId9wWCL3ngKbatvMB4"
    "rQqd1itdgNe/pOy7S7mJb8NYv34YGWQeLfh+N+5G4ZeFIvN3CWl9WYS5QOyO6WeWBgrnpmzgOYy5bwxDczbgvDm+8YOJl5KzkMIM"
    "hlvOATP0/YDeyzudmF72geKB9UzQcNkE1O7CSMSXGLAXKY35Lp4DlbvW5aZ3bmLuRR6iXnWZQpeJH8gv7c7R82VVlS+v3D5X3GPD"
    "VqJihQF4D6vVrqXfR8kwMNFbokphaB2vQ1Lo9gGeLAHtpQNmkRF3PS+Up4yxdSbmRu1+ld20uv7KG79bNKRPgctelwFewzrAn+uA"
    "AA5Da81nMRtH4rqXKyOCvK75zrkFXKljJzqYxuyGxDccohm7b7bYzl40VJj3ZWqm0ncJKXkTK9tmpYBmA9GaSSfiWxAUQdkw/nqu"
    "Xn3r5oXUPJnIeA0xCNbGRZ/yDcPfkJ6qDKDD9/BlWQ9qoQSzRuwvL8ygagwzcJTqo3BQjegLFIxTZQjEozV67FrnM2DkhkgGVZCw"
    "sujQ2LZqXKjtUD9t8UGXVO0cCZEeYk4PhVSmVTuQqRLwSWOEfWZSNlcxPkwoSxYer24fUtbtQyzEuvtJiNXQvYZbGpxyOfB3H8KD"
    "K4eAEPFaENDmH7W8TwK8l1ngvlrgEtH1p2FkXcPRlCfP5qdn/TbC0MooMHHGfG4zWZuP+ZnQlZPKkLcMAPvEhzn1UinMGNlyxQ5H"
    "7g6bLCaXUcMORw07TAKxafgsKk/W+nGSihdpNX34feBMcGxxIb6MmnOLj7Nq+T38YjfPhsmxeBO2xbmWsKu/HzBQ9hv8JxuHo9Jr"
    "+2KET1MZ/ErsY/ioMoF/HkXwz9fKyOOV1p1i4fk47HzeFk+VSck9Mv17nSvJikINj8gw+PuqzpMUvvsGnVq+UPWSFG09c4wJYNPY"
    "xp4xDnmzvN1DgUpATgKrnV6Swk+SsdjrkZSOOYk2ql8G8PGBXKN6H+Ll1Q9x8NkZS0tiSJY8Vc5q8OPZAHNY5jIi/DuhHKvgt7Sr"
    "XYvPZcSL2OYH72wHbzC2BKEQzAMfdFiiexY3DU7IVvv2N2MlvHPWwUDBnS3f754WFKe78IW35ME8fOnbdR77yuXuHCWY8hWilGSG"
    "0ciI1gB65Rvs8wOO5XUsPf1Lqf59I+fppj+BbcTVXNlqt8X3AcKfYBZPHgM5dnUefZUag4DAZyc231kRHmMUZjk8WPGg7WsziLZv"
    "5V2v+hgww21Hi7x02csiyYukvAhtAt4sLJZXi4Y6ZFV2KeEr7wHvbMfXhjbt3vfPvJcTJxWAHwyHtTLx1ZnHApPiGm/7clXIa8lE"
    "E9cg9zGqBo1fRBmeR64OvQy/HVSyT5ThNG3OwlCGDwdVJgsqA/c4GXmlGI/cwc4bliyrrm3JEMl4ZKwC7c0TOMWK58L6TZXzs7bl"
    "KAsG+gaFhbycnLC5YdUnj0QlDnaxvAE3rYBm4+koKXSOiVnmA45L6RzLdYeToAzS33TfzMJ1xfCmIyC6vHMcCNAQdO8zPN8aPvFz"
    "fr+kZfC7g/wG4oWLqSbYrPa8wKWKfGUJQNEE0DfiRWrsBxMArQhSjTFl2A68cw5hsxBAwlzpstvKGBM4OFJaneUktJaGzx7F5Qnf"
    "yrCwvj6+clfgCBRyzACn6XYX6m6TrFmUmgrZ9tVb4xpKMnE5XsayLtFqI9t5PPUoeptZY6EHmKgBJmaAiR5gYgd47REategwyZLx"
    "STx4mxcfQrz0ukD6ShZ4PB36Jag61SCEVIH4PmKXr2JAQhXuBaauh4FZ1Dba7fWNzfVNX1nXZ+GbCE/CKvmMddq3VQACOq5t6a0v"
    "21Nr6GY+EV66XPgyBjFiK7SIBBpAn9la/WUTQ3+tTM7ifFI+jrJBGofPc+9j6ZgeyMkYHnW+YIablRmi2976Zpvmx4I6oxiLUBY6"
    "yGFKi9VOt3276Gp5x0Zn9QzNILpJ2Ll9O0d7A9Qt5ndkPoMcJWrh7ydzmflHFHSFVjGTmNdZb98pevBvsLmDv+DfoNOmn/gn6NyS"
    "FeBPsBFvwE/4N9jcoFL8AzW229+bTr3ic/zlY7uwExjW+bqrVHxilbYaDkgz97GxfguFVybCtz26FWgKYK5XAcOBa9z6NucI8+ux"
    "DU2pL+JV0RA9BZtYMkk029tXqeoR2JDsL3yF80LbSYNZv8ylPbIdypdkYf3KuOnCrzh4FVNAWDQ2TC88aIYL1gAexFaolhlVgXGn"
    "wPRGVixTEQ6UPEIr2kLlBZy60jFW/LQFDMnpmOdEF62ypJ5XCX+WjjMvgWtn8gUudZRRoHmcaw5QO6u6NiA4DavB9C1HBnCtNNCT"
    "ibKl1CxrlIRnVUl4xiXhakjtruUG5llV1G34BG53Mtef2v35hsWVz+BqPooE/ikTUYU5M6IEGFiCatKKmfArhS8hqAAAIevqLZUA"
    "gWzZACDAShyUh0gnYCcFIyReEkcKc19EOyCN0JVnSAFVlXWMJRxjt4wZdamj3tWpayT+QRJ2XYvVCTN1lTcXkoZAmL2VUa18Hdt+"
    "MfLM6sizJOTZhGjM5XXwVhNSrWKyTDDgIypzZTlZIw4uiKTpSBZZ9YwsK7QMQOji8g1ceEXFNxPubIteEVf0fQsfvp9pYhh5AEnX"
    "sm1SXctxjDPGKcFheKevnvNCkjrvMHewMUn37Gjfhcib8vo4+kw4RDXzugH66hKY0mxsPLaPvGzMoJOCjZeV3VDcg7v8bUO+OshE"
    "g6lVil5SQTRw0N+dUZRCQ9X50gJ60KTt0Toe6yctjQS5nzQmjUL3WwJDKvwBioXHaMOqbIFSr0K9NPpBu4jtVeQGigSKYFpJm9LZ"
    "CMhhuJKuo17WDl5EXlFxE65oprUoDzeJK7NgOYHkjVGyEFOSGLN3UqkHdDBuqSteeBSFZRKSkAFQkpYuPCjdKCSwhdntBwZLZIAl"
    "6Ko+KA+yQzK2TVDsncbReTxgXldOuTUXTZWVMKCXUjuwUFwgR/KJdsNkSyz/INEjf+Rz81VYzB+UTp4bhnMLxWIpW2Q8OvruEAMx"
    "tgzE+1Q8TbkKq2pXYvK3GSVWsfYNIVsnKYoellxxbQ09f4oSGdygJ7jQ0zgcAr2g2JN3Y3LVLjC9SeS4RpuMVW6qD2kYEMNVx03U"
    "giRN1gbMYtUk/IBNFv0wk8zJB2CmNE1DiRGFtepkAflUiElbRia3dXHiIOyLURgJFFQrf4slb8TEGqjGbktleKej/m4pvewUPrLy"
    "8WkPPuSmfVPHCH1UEbRX7DPgvQycMZV//aDSGq3pqCkk1FzasJ1NvJyw3bE5iMdOttPpxDsWOWZVR9R1bIIvnUy8RAwERcI/hpUe"
    "dLUnbIUsOw1dT1a0iN6Ly+4HMmzuVwIzhR+kou9UvTUqbBMxRSLxS9v/1wY8QbW+zfC5vu0zS4bPSD8qd4hG8tHO/aOZ+5L3kQe4"
    "wr386BDDsBwf7XLcj7zjsdcHTt2OYJ6E/VCVCnLy3pShqNZ9FGUqYhh+HSSHwddjmR+B9J85uhAocJ44geNM6lYaFdJDq5mO5aNz"
    "L56ErwGciD5SLxEuzonv2lJ3gijsU9VJKC1ExXmYuEL1JS9xw4mpmzBBkvh+XCTn6hA9LPIzWml+O2az8+q1OndE7btIJlciH6b2"
    "yi+l0vD93EfXiutMejf8AicdmUnvOhuh9cFKjmKA7TwfedqVx9tDZ+49IdkrbljoofwqtHbHxlBFsX1aNsMywY08ebji0IpqNBX3"
    "woG9hi16nwYMgONhvvRkBLPZTMYCUH9J2gq/Nn2UqJs18/bLZZ09dQulKl6ZsILZDMjOcxLJ2l4UlcvJvnUlM/uUJKsqvTqvSq9S"
    "Jb1KufRK4x8kIdk6FIzUcenfdbTn0CvniLVGbLWwc6mZGliHs2QEG8cme1GvBKv05QmMu1Y3GVkbnP6Ie90C3/8GveIqfqquN6rQ"
    "2KqXY0MBIqoqirOd5ayzuGtQdkV9GjP2zBjgAApTOvDhVLr/cAWfgt9Y7Saea30E5yzjnx+7CDGuRv6qOhNLvhTO37bBv1qRZPKC"
    "hQMaDa4UG1BlBIzJZA7f2KauhL/DWB0fU6XL4/ptsU0jToc5Qb7DYMWc8pdKymbe4dSkAbesg1sV65nYlu4Oso+B5LpB/Iwc9fft"
    "sK/gU5FB4MxEVzskONxE17H/qCRwvA4zQlSVTURXUX3fxJFcWyUiSa1SgeGSBZej4ZyRhFYYNRG0xW8vBqwsXWnIent7U4It7WGM"
    "BbPZo2I28x5RnLDJyJumgilG1CL0deChuY/407TQ2bp1q60SSlREL/hmNkvg8lS4zPrxkOnKgPl8pxjTSELKzRrRStF4UOuDahI4"
    "+o/PvA+5T/FIlk5z8SEPT3OzpOrDUpxNUVP06ITAYgSHLK8MIpEXi32DS/wIRchGsxmjWpMidRpIpCL9qbuSmnSEJ47LpyMT4Owm"
    "OhPl2au4jxmiMew0HRRM6dMtb2eaHyqBH0rD7KAEXshTAjJxaXA90Aj9DwFZuPc/iEFyHI9LeJQ/5nQn7mmQL3W3cfg6NwrcWEP+"
    "JynSmkwSQ1ten+xyp4dH7ou89814ZSXwtHoTYDD9RGa/IvrAlhCEft8N+hCHjwfeEwyZWjkg5afEENt3YlTHxrgtqkUJj1RcWRkt"
    "9vuZq5BuAA0bHd83SibcEjp0+/YGV+0wgJsll1NjXrhvBKYmqYbrFhg5zK40T2p3+7cjvb99LRUdhNFBX6bT2wciv9LzKNzXAojR"
    "ldYfX429HTHC2CHawscMdmhOn+b4RjDZYXPYHexQc1EaiRzDbyUfwf0ceiMgvGELBnWrnKmZtzaCB+ZlP5wa64jjubSLOOVRP7uN"
    "AXnMBD6YV6c87bFC6B/DD8ZM44Mbj+ND+FEhOdPEHMaQkPg4qYPJ5WVjAJfr4Scw/FyH6aquFgUe3jdBTdfbmzt+A4PRuF23gMVJ"
    "jCef5DASbnByYqZ9YgZjDU5ODB2+b8nwueQ+7EGWx2rCx5yrHT7Xtqdk+Ne0GJrZ8M+5pek5X4zcbZvSIO5rWYBcD2bAFF25JlkC"
    "axIZI+M9staJhLa2EXsk/UVHvNw9eCrC2C46strl2zXLt6uHH9nl22XLZ7xasX3U+hI0qwY2eJljhFMTtAAjVzRHNmioiKENYhPa"
    "AHGupncKJk8tq0jS6AiYzcn9iSbGMuSCSykheC2jvFPW36LUv7NQ6i8tx0W2Jx0jJM+4LYiKiFc6yeg3fOoQ0S8DGNmSqyHRdS/v"
    "ozVnbPzDDeWqq3Rs0KUmYzMVzfB6vHCjgdo1OeACGeBYLiAFiAQ2FwdOiwYLqH7HcgEzZwFhaYXE7+hmoGc6z5ps+z5Mq/FDUGez"
    "G/VPrPhPxj7HAD8UwTK8ls65lDwqkoAf4uXSl7y1ZGw3NWMrXzr6cXhe3mq375Cq903UU7qT4FFEVkbqVNgJRErgmSlyx3quZeF+"
    "IfaL27eByAcmmevhod5+YYLN+kEG+64E9ji5LtAAmdV48qNJoQZeq/AxjAOZctcNV0SHhFPmJI/EbSgucJ18QeMvWVPPp5w1bzd5"
    "dHc2Ar1bzPO42jGX0pZhyjqtiOSddq7WU3dgtebN50JPhGiJUbc/quTudLLYU9Bjl5Om3Hacl57NnlmW5SEmL7JZ7TwV5nm59GsB"
    "/hXgekjhQE3G9y4+2yhGnY1O++a6ciqQVT+zVtsdwAtbN7eXl0d463ZTCh40iKe+NdnW6bnd1Iw8k3s31Vrzam5HSdqNxtD2SzvF"
    "boQFGB8lfBZJ7X4mCrjnqTD5pB+jqNONtj+D461zi3ARdlqVxOn05S7wSdc++0xWsDaFChp2RFMugYq4looeY04IdNADXu15inYA"
    "AeYXqH2vPF6ZS6t+Vj2rAukp94Qi5qaqOziliZNuAh1oXf8D1Ho+xRh1hZDsWHgvtwsJY0tU0CeaXht3PFlefkDdPI11zVR+qnT3"
    "8NNYzhWubwVLdrVoqzGD09oRMOOlKMLUg9+j6AKTQFFEY/TPKDBFHo1nd4oKvDicZF5ByZ8MIQIgN+cHoqwJdrPwYnJlDaxyfHWV"
    "TahyzqrgOFQgdp/VrjiQbbS3oW6r5Zsow5mOuMMShFIzaX1xqr4qRS8NaP7Af72QcaMKef7dyM+/bpsXk1qbGwFsI9JVGE9PLIql"
    "vIMykmqS1oZcCynQuqp7cTGUh+JlSkdSqrdUEvTqh9IwMTffJq4XO9Hxl+plUAj+MoCL1keEHQC9jH+FGuMeYeRxfC+fZIOoSOIx"
    "1Fj4TljCDuuxp7l75dfew7LJ+5zUbngieDrVyxQpGKuQ2UBZA16uU70PpfEOVCoeHXEsrX28eY2Pkfh7F4fjcnFaDh46V3yF8tnP"
    "EGyplCeArY8R5stQmgQJFEtXdktMxizDZWtB0+rGDD0JnXwCGklRehY0Nk2ROnntBiaCAT+N9TT8uQE3lUtkooefOqcTgFYuzWQW"
    "XYMkNIahFTwrYWuunREBJ4iPOd2OnhS+BNY5i14kTmLujXVfPFIHW80gZ8uknYlMxHF3wE74c1Xn3VCvjBtVfD/ynPxC1ewqtdto"
    "80GoLTsb850M2IK7w+38xnDluA5XTPYW1W2lveoYdq6sbveqNvb1X/fDtgJ8es7G+KLpNGW1ODZa5veVdxetFI4UGUPu5n61AJMv"
    "MNIPDejU57k0fU3MQPHCmAcg7hgR2HiN7MVPjL2dPcHWIxRtulzZlRSK2UCkrlzMytOshCxy8oiYyFCSy+ybjNZkmUuTMkxlP3yV"
    "eatAqS2vwkb06cW6cshNqhpz6zA3CAdr45OoiKV2HX3ntO2Idvrv9aWFSD/w1K+RNDQZqXJfmI/C/nxuFKhoHsEz2zhxrnQdwF65"
    "WUNBzHxkXmq1Xyg7tnogM/G2n4cmGJFyRJUwRicEqn6xozIDmT7zRdkNUEia28lEIctbIqxTtBe5k8nlLHIry5LDduSnDWI2K12A"
    "mt28ksiI3EDyirAxCXObM8R6rhphlZ1ioj7KTeEcPtYoInVv8QJcYfI0pBqIVSGkbcayGmnmSasdj2cJ64jFwHKzAVgSHHQ781Wx"
    "quKL8zqM7Bj89naogBfVrsHKakasXxdOazpdMziKcYkZ40K8oF6fx0Mi3eBLxVcQc1DhKmI7QLMHX7lIbd1A6S/1iytSoVhntImS"
    "bugcIoOK9GOP6R/Lk2RM04Lx4M8P8QXmusKfWuhMD4qcwZ/qIMo6hrGSDeHi0S++mpJEwlLih1G/JtsZsldueGZZ5gR8phKXbqQi"
    "J4URr8MiPctySjeo5sa11lQyVAps1bETENuugFSN0rPm5enBDbPNou8xXzp98dCSiauPjZ10xF0CUahW5GVOB3bJW4pnsyU0vJcu"
    "k1o2yD7fnSrzZsW5x44cVzVLffQ6AeXn08k0pYopNjw90URnkf6m0+mqjIVTW7ap4cg6s0woF4Qa1MKH0qRBK0NcGYpwiibfcOpU"
    "9ChgGp2zE/MneFfKQhWCgCWR5lFM2XagjbN9Kinic/WoVRo1J6Fq21BWzoVvKhsBkUz/tim4hlvHo5JKx1JnfFMpx1RNEwesrJmK"
    "uDRUxRWjLjh0LkRciaLvBlGnGfGY6k250bKm3GiZmxtN2NRZsfVfV9c9ln8pmOJQRs0XJZPFpvouCIzBpyxa1yVva6I2uaeZjjEl"
    "Le/YkNOspsr4CnTEltbraImoko88MhmBnpZeaXFcSiZ6Ev6eREEe7oh0Fu5w4edniWVU4BR31pE2gFrrKN/mZ/cz9HCQuw2/5Mdx"
    "7n68IT+ufhrn9U+zyqe3mj/NGj69GOhPxwnmx5aT1OJad+2MLDCuBMewAEKt4fEA1qdTib16joW33LIzXMhOJazrlAo33cJ3GRZu"
    "i8JVhFWw3kYbQZTkU3WK5NgVJ+EK5XqBXOQeWylaZhYqswfyaVmD2bTgNzHKLsnrTJJSZlQ2Tpq/Wl+3n/FRXAx4OwySXeoQd8FS"
    "Z857eJtomThvfxual3TFgoF9Wf2M1mZT54CAQ295fl0SHBwqqJzZNHulI0i9dBjroBqHScHYXd2g9Jw/G8kVIE8e+MYtmPNduDu1"
    "YIGRKYoycDrTtItj0ySJCq2WUkSMtohhBIceIcP0NQcL+bHjoMxbUAycGRg+MLqhZg0ly62PY7iXYDQDWeo6OuGr1Y5+B3POjtOY"
    "UyGuzZakcyaU9x0IBV7KPZTt4jgFrjLOmeNTTuzoceDGOYNP4NSWyTCJi5cA5JOpprbqhkGhpsnkWPfySdGPH0THcWHyVN+PyqhC"
    "TR1FHFWQQXWf3wagrMyxwVfS4ReVeh2ybFoi1ysA56S9w+TNcBM21PUxd8j6SvMkqXEtR+kiyWqpBKvyCDD5qDSrXyhmpbmi/iJx"
    "HCIfVJStG7ej4pgSF42V2Q1mFFYlBxuHVi/CSwNmenmp4XjwZSngkgcFR/ut1kohDCAADt+551n1EnNX/cFIkaBLxreqX1K6korK"
    "pSuFSM/Q3UuaDJtEJDU7w7avvb1iZumeOZbuWS1zFEpaKuoO6NDmfkSxEP+mEpTqmdrpZ3EBd2SXOUJZERJTjVdtTqtz6Egfv9i1"
    "FygVzdmVIyuNFnIwpFgamUVnLNHl6Mo7AFek1AymfS/MooSwR4p2tQY1gG5JPZ+GSYnWhQnKnYiBTQz4CrNeT0pFoQrF57NXRSGI"
    "VJC2OzWO9IVzkAuGIXV4HT2ARA4gxwGkvuUXBiNPihKMkEzLajXQDbIaHIZrD+NPMDkCvJSqM3tb4zkKLqzekg594aaGNpMulOlJ"
    "KnMtMMU+RUlJYX3htpap/I1hWJgzY6puQ8xWekkhWcci1xBY9ehj1hG7EoKskteyVoFdy6cTE0Gjzi98Imcoixsp7QC67DeFBEZH"
    "19tZDzaC56ZSHqKqa0EdGz4MSHf1gnnnTq2FLkFCEl2OdF7OIsbYqzV7mR4rD6zpgI/UyThPgeSiOxhz8chnxGcT+jlK1H0nu6d4"
    "niaW6daK78+iehnvScKmenM6wEWDGHKzfQsVg/I+GOwDY3T6n6hYwM4AdCEza5b2p80DsLF4G+ZrzJWRL3TT7b0qeUQZGKkKYsAG"
    "C5fr4Fl2KFE0W940ud7yTrIx4f6jMSDLwSSNDeZ3ljdhWc7eDsjM5vJ9mvc/xIMXiqwsAdHFcLHFSJFYcBS7NugpWiB/nRlcmckz"
    "m0HZQXm4pr8h2+Qu1BuP0qSPaUjapMKWFkKPBhQSkuV97VthjZTOxDxDJ5kfs+dbledOh7uPJL9hW2TBxEp2dAsqTnzYukHYbZXO"
    "zuooh31Z1et/o8Vtkt5PYL+ZXZ5DhWNgES5iKupOjklYdIvq6RyEr1JymiPA6g1UiLQ8HI6U3UVbnqylDv6v1RLvJ8yNvSGpVghM"
    "Lp2+3EDWqPCuSHQUwF6+QgPInHKmUeB5TM5DqL3ru0mOpPvF4klGCyfZ97uRO8l+SFRrGydmCc3rT7SvJtr/bhOt3F7Rl8JGX/SZ"
    "vC7hm6tdNBoGQS7HxteYrU3atDYpLG5lbfrqAKi1weh1NKpckMeXUqXcl25AkoLQq0Ifzl8PHKDQYN4mrduc/IQyJuqnI5hoLPdw"
    "7GUOw+N3FYLzLlCtXM46ykBSOkDomABOWAMVi8z1aXc3RNLxZCzYkcGlKtk3yZxwShY9ooMLBPtGGLWDMOg0qgFITVduaEgpG9/Y"
    "XO/cvLm+4zdlqdSdkFGorokqBtmT+RZ6/GLw6R4poB2AS2UD6UaPlDPWPZZC5ahWVAL08HYQ1h113s27Xw4cg0A99nc82sQ7lOg4"
    "IRxKhNR5zZRQsw5uYhBc/1x54mD2z+jMyJlZKpRsiXk+AC7r8jSBXb900gZ2dQq6byZxcSGTV+fFXTj5stMD7CRsrXx/78XzNSmr"
    "TIYXHnBemb/yzw8PqHPV9eE/x3FhWAEnqoAO5HCQHeoTFKNpJfR8Rm5b+EOfp6OU4iUBX1alRG4hd/VBZoqS9hxOoFQ3RUrsZt0y"
    "wWVx2aRePtPxIQrMRru0VNp8IxkmGIF9eToI30Xd9wAtS6I9nk7Dy8kYyfc0wWS8GezsS0RQaKH0AGUk4+DgYyG+LsVRKl4OxP2B"
    "eBcdzsX+OLyELR+QOfq9i8f5GLg3uPtZPw7ulgBYUXqDIDLAWJLFGJnVVmdnbWOt0xKSjouLl0DkR8fxc9iPoCVx5CA/a83FexgW"
    "a2J/vGafTHNQqn42Nrg/XmsoNlVlrEteS0W/RElJkQzix3n+Yc9aNtaK75MZ7cuoPFlQ4VWMB61egZv08KJFDdLLamPjWJLdUkxW"
    "mEIt2XDLFY0nwzvLsn41WOireBgsjiSKe803+d4F7bxD9Rs2+AnSa8y2B3k8nnlULDo5+yRSa3o1m72c1gYxfpjjsIt4fOJOtLkQ"
    "kKpZJ1XDWSYgY9XE5dwkwx0Dbd5PoNIb9xivov3E6rCzsbEz3GnvtFfX2+ub7c317dac4eijo1cP7u7uH91/8Gb/xYune0ePnr64"
    "d/fp0eMXL744OrrdmijE/aYIr65KAORNgagzGSPlOFhehsfxZIQs2JhGTP4i79IQq2WoR/DeT9HpBAq0n8j8CKUtew92Xz3YP3ry"
    "fP/Bq+d3oav7L46ev9g/er334OjFq6N3L14fvX3y9OnRvQdHD5+8enA/fDrtwocyafNLTMORNmKG9SulY+uN0rF1JR0jwVUf9fkV"
    "r/J223qVK3Gcssuc20ERj+MOSTUY1xq8dcuEqgQoV4RACKbhaGSMtJesKMKySYAn+uUzGdCNJJnwcRtFHFWxK08ZiTYP1ff4TV0k"
    "y79C0Uy9BkVQJGq241KzJT6SvEjSqtl3oFVRaPsZGlPTUuL9uv/iGUlcqyTHIldmni/UhHQyfG1V8qi4cjlVHW9LqZAabN17Nsot"
    "So1hFC9IP4bKEcBx/top4CqvJVq+sEEIdtCDxtL1CI3IDnMhPBKxnH06GZ/sXWT9sAGoUWwsqqbo1iZXiSXgJa8+v7nl5VFKWDpN"
    "1s6wbrbpFG+2t3wdRtcEsi11UwMp08doqBRcGQ96ggc9x4POY9965VWHPKVDXl55yJFtqR/y8hOHHMP+LDjkxJeqZeqIUkk+iW0j"
    "sWLTMcfQjpSOGyMA3y40sRYDsVaGxUF8CGsA3BWAeAXG0Y4K5n40poXCS/kpbYgWfn6q3kEpUoBpn6ong8iQPTSzTUkTfRlrwq5f"
    "95h19DFT0itjvnK3bLrpSyQQqZ02/2pOuee5XJYegRoGDIK9bOa1ZVUr1UJ+GbPnLXXU6NUpfU8kicpxMUZ6lr+Vy7YnbUcA8OS2"
    "A3cpVYBtnG7ZvJgW7KFEp+q3UoFi1u3A2QbZFQJouQeKYg0/SURYYdfJSDq9L12PprgDNIVxZLy66hqsY//D/d0HS7Xkwtf80DsZ"
    "6ZA8TWLfOY5djAao/0QqJTySqOHFNLSF4mwkXkzCF9Pu2Sh8MWEIHYo5bMRgPuPyBgBoFVt97+3RvRcv9mezyzL/EGeYR/EDvAla"
    "H3FELYFeD1A4F2U/JJogvANs2hKBfuj4bVKeeK2jo5bfA6JYTEdhCfRHf40aozxJjxJVhM0Ssnz96uleHBX9k5dREZ2NvTTv041e"
    "G1Opj36mXgurt/zZTA3EF3tF+Ah1oC3MNRYBOwpbJAuAvoxHEtk9SszI701VxzgFGsrbcK9wGgByVRXZJkSUhG97rZd3799/sfvF"
    "jUd39x+0guPYluzB36dQZgt2X7zeb4knU/zu73/6r37x3/+1/OIX//Iv/v7v/huoCefg/o0Xz5++a3WjMWDHG+ZgfivpLLkrZWgR"
    "e+9S6mBbWb5KIV1b8+DyLC5Pctibly/2oMOTOIJrOg4uW6Q4yspVJCKgOwwym8g1/fx0jHNqfbW693Z1HzelFUxHwB3mg4ugwr0D"
    "0ARKLvoYJeWNYUznEfll4KiAA7+cq+x08n2xhg17xncaOXiiBiZ4qzfbG+jlFktlR9ii09BSt9xsdxGjXsuTFJS8+y1Z1pK8frGW"
    "f1Af2SqqWTgYj/f3X95oreh+DchI53I57wK9kvUBPL9+9cQAbHEXiJg7l0z6skcL4MW9HpwRoMWKsyhNvo291vOHuzoZbrUuXEsR"
    "xeElnlTaQGxPbyJOMN2DPQN8hWf5SRmfea3xx+zjWmslZrpBhQ3lPgBROY5NdC6jSIKOxrwTp/FxtXFR21KzQ1z2/00jRdpqaegQ"
    "HrTuwaH5Av95hv88wn/277UO6TRgZMMiVHnqijthBwAu6dAUybDa6frF51QsypUVNWGv7BUAFx4m03jgFbc7bbTi9AO1pEC2rLRg"
    "N1GlofZvN8OtMksOK4Siz6L01kWrDUfEGo4WGnLi2PGo3MfUTfH3OvGGWe5dTPwEu/EYaImxh70FrRVd+CzJJoAIq8V7yLgOsJjp"
    "F+IrOsNcBapEzzqDOeOzmgd5hFeKMEmhHAbc4xPPX+mstD6HpSCHe2yclsZfueYUmElXn4+VEp6cRVOvLbBVOOofPf9zGPaqPZTZ"
    "7e12jyoO0xzjgUInv/of//QX/+K/giHe3thuu28/325DhV/86E9UhZ3tzWoN/Abq/PIv/+gf/vzHVM15TV/g+7/4H/AlC4pNphgx"
    "HzX7EB38nXmpYtkdbAMv/F0sxKHiqf3d7bbZml6ml7A0B7G06wr0huzj3iT0YOfuqKWEiz8HGtuTegcoxouAFyMByjm5DVwdkMzx"
    "gWxwbVjkZ7snUbELkMgrVxL/MNRnHh7mZuW9ThtuDFDrHeSJ8anjPK3bp1ubW/DTPm132KubHdGmIAlzH2Dru4JO5LNoZO/Ltyk/"
    "Fg78U/f7XUFI2ErBFZ2mQRfhAnTpd8DlFxZewru5gXNoNztKo37sfX7ws//2f1/92b/+8c9+/O9Xf/bj/3j4+THsyZ17k4OCCTbo"
    "MShw8GtjaPvOegzwBR76KVAInizH4aHIu1R7tD+liQJxma7t5mmKCN5rnUYtcZlNzmLgygLgFscxGTOdo461hYRBCyjkx6Umbfan"
    "FLUC+HuPFkl8S94Rs5l3F55u34WH3monwIc79IAgzC5smbnoPCZdLBAzn7ek45597Oozg1l40tvylAMjrmXkQvNfsCUoLZdNJuHj"
    "0isP0kNRwD++VGupdU7MgmswrJtQK9RPEJ7i2Nk4FPt/42d/8Lc3OEx9kfEzcrC2tqYCmELx4doYiE7Pk6e/WCVbnINDMyUZad7E"
    "zMKAMTjPQiKMdKVzmymzD+D5EMUKMKEVQBwwW1RNIGNHXqS9DA4DwId//a9+9Vf/M8AYevr5H/wEUUVqX+D6Qkt2DeS8fv4Hf9hi"
    "APHVdPEGGbwM0GakJ+elRmux2pnNsh5gnqDVAWDMHR++ndoA8QpBdku7p7He08zsaSnjKmOkd9QxwR8j+IHfB21dCr96quS2foYD"
    "2AngHGD52ph0/RgfhT8xRlMNXnfN4kOOmWwmi86TY7wycMeS0fs8KgbLy4pFSMaABydFrMyTeg111z4WSRnvw1sM/4gn5SVAvQQI"
    "GrqkBnIW4SDvk9BSsSgPpE2TZ/U0mIeRdDEhplqUSYNHuQq90xoi9dAyL/JR1EeLVNgVYVpG2hYTLQAXK7XhFCBc6no8Tc8udRQ9"
    "az6Lp3Ef4wNF2cBr9fPRRctGBlLKdbQw6wHVGwDssTSrrAustrpnD0MPrkuMnNLaMEGTIe9eDjxdlJnbBsf14TT8/Pe8XvCDwWVH"
    "bMwPjn6w+oPx2uGK34PCQXTxg/H3DlaP1g578MOjSutzf2Z+QSmgTDj5s1/9h//Aq5gXPbfyT35Ur0U1NukJ+/rF//HXh5VKWAyf"
    "Hta/7fmfJxZcnDvgQsLOMnw4pVVVeGTJzVWkTwQynkEJB9tiid+rLsrnyL+tAaI6Q+dyDKqXqbNOH6pbZXBpedA5BP79YJ3+3TgE"
    "wjMLV7xqMezjwSa+HJA17Fmwgs9igH+3DufwdvsQJdDq/QWWbx8KqndT1ds5BARSqJ1/MkE+yWbTLfmiPJkcxGvJ4FAmN17OyJkE"
    "FZ3HRT4ZjbFkADzoCZXRL996Oip4xYghT1WazTo+GlhTLl7Z1Gx2cOgTFBuFd0Yo6PWrB1HdAqDUNcwaAcwa3S6Bb7sNPyzKGZrI"
    "1VhTlh3fQLMSXeM0PGZg9GB02D3VktEhhbM+1TdjamkRQuxYAf/eDjc6y8uIZIaHaFZeXHjHBmachnC4jg1EO11enhL2P0Uhg/Cm"
    "RKnQA+BpICVhLaDO6RoeE0Z4/GAMh2nN8//xpz/6x5/+i3/86d/940//z4MfHP78j/9OAJL45V/9BI75r/7w3//yf/nrX/7k3/7D"
    "f/Zf/+In/x2cciRQ8OjJE3Y73Jn7cqBTCaSA3mYjlqaxJPMd6TknHDOqRab1xeSfsESJxHUjTc+iQ67s7U643kvgeAerHRG5pQbQ"
    "BwntZB/hGRo33W5jvG91H9QCjvQOwknGQzEN70z5hkXQx6Evj8QQB4iq9wcR5v6ETZguL8P6TzG3+coKmt+EwzvQyfB763coFuG3"
    "sZroIARkMgz0IRR0OgN1SsUgDVJxnga5GKdBJMaDoC+eBqW5svp2hAMxsDjqi9jF13Sj4KgrmjXjlAxJp8/TO2juUhzgT7jmrRZl"
    "HhinNPMIqJWD6NDcBniO9FFF12lNAKNgfWBbGsiWZDZq1BCMB7hv7ipHeExxu/xuRLL5iI6kIkguz+NsEsMSAGTHNYjHQaKQAQ4d"
    "nr9AM3a1r20BN5q9Rr11UBwUhhI5ZJaq56PrrxGR83KRNHBhS6VOYEqzl2aDtHSy1x7+xuOo+acbSIPidyzA9oRDvLhHaIFb7t8A"
    "novAKUZbwr9rF0BVaSaaRH8PofY7ovN94Kk3V1S9s+912m39MAD4r3SM0F4W3NL/CTrxLXUeJ4mm6oG3aQcAJYHhw7+zGQ1zFf7N"
    "4OGxlK5YsH06diZB5z+WGCybzZbkEEwOJAObK4z/DT1uYvg5c0+QnmahX8nJY3ZJtijql67DlkVN8GKE9DwaJtslFLFbd6W1Sqxs"
    "7IzALZa9+2wFHqZcVVLabEoaZ9MZM8cATgvCnSU4voPeUjtQtxYmQKNXwy2sAJm0pN7pGFY/U+q1R7k6sGtF9PGHhtYAWijwDtqr"
    "W4c/GPizX/7lH3m9pX/48x9juSzuQfkvfvQnPb/n/1A8m/JGiHz5fWAVfv7HP/3Zj/70Z3/w45/9wZ8drkDxD8VjiYpexccPpiOP"
    "99y7vQRN/nDlUb7ybAr/+uL1Ner64gug51QBjKwD452twwiByjDjXzygRV/AbOHfz8Vbajz4vRlQRONDf3H1ECsAnjucfeZ/zjj+"
    "subXwmgwRbBJ3l95LmJEAVsDrpL0wzBYeRCu5JgMxAWfvZUo6OuivirqW4gxuB2iqHCEUqbB97bbKyPpNCRDfT825KJfhAmRawKp"
    "NUHEGjp3eESgIXUmkBRjrrPhF/zjFfwW27+xQg2kWLJhSjYP2Yevr+zVxr9Q6PkGxcO0IBXZOGjlrWol9+EeU6e/u0UZNy9ro1FB"
    "L0xMB6ZR91K9eOltypmYKj/ty3FQCMAfhsmYlHj5HdEXyeKk5AqlXL54lmKd+E7oyvRUTSmRa61Q5R7+Q5I8aKHlB7H8zYzi+01i"
    "T5R3MokkztEVRq64clToWViBlOHEbL4vRXiQ74s5a0j8AH+m4D39DuKDfKWDvDH+gRJpDSaJIeC9sdK45/XDtNdKMYweTAv1hGim"
    "ggpRTx3cXnk7ClT1lc5O2+/1w1aanMetAH4M8iwmZhNop4S8SS+B9egLRN7wgQAOE2gZ4A0D3VxVWon5pb1oFePv0a2aZGWSBvYV"
    "tYOxcUb9MrCX6Y4cv5EgAOoTnPYvV6mCjzjxc2hfPqlOSOurWZK7YzoD2iq4R9wqupYDZXb24WhQ5KNeC//VBTDlnpy4LDjOy14L"
    "/sFHIJvi8Z02qnLhTRH3z3uoOTvX3ybwALXlX1xxWr8vp4YAPZDVBTUo1Prq+nDFBySiMsfs7pihmS+nFCIWUTaqycxEAPFQgMva"
    "2NRP6Er9wu70T+rSn4tH08U9Ujc4UtUjDbe591o/PlroyaVXxGYW3gH0rtbcF0kf3y6ZXYCGBmg1IPJ+eAltBUqV+It/+ee/+L/+"
    "4pd/8yO0+eyfB0qrCAU//8P/2BJqHEHr53/0v/78j/8MMMvf/83/1BK48kHrlz/5d0oHKQZU8Ku//Nv/+9/821/9b3/093/7J1AG"
    "3UKln/7ZP/yb/xK6+fkf/ed//zf/xc//8E/hDS2PHsKv/uqvW3PRT8OD1u9s7LwfDHdg034nurnzfhjhr43NwcatW/hr+P79cH2T"
    "fm3eXH+/LcturW/08df6YLD5foi/djo7fdnKcOdm52aH2tuItze2WofiqyLsA+JJo/H4xpup3JpiggbInnLL2WPeyQ/Z72GeDuLi"
    "QUH2aLLmg6dhFEuN8jhOWypBGr178+D56wfmLRHoLdITy3ZfPH364m34djY7jntLnUDXgz7S/GNLLGmf4fMk/mhbgQdoJE3GZQtV"
    "PS0Sj7V66m8g32in4vTitfmSnlpoY2zfPnfePmdvUQBrJwYP0ClyCXr035gVeG9/3r/7jq8HkGfOesCM74dsmoOWuJzrtdp9YT88"
    "7+cpe5fmxy8AvKB9lIw9A7RRXJjHs3wQpdw5PY/G5bPxsRkWFezF32jvbNjwDCMT6ag24xPgjcYahsjiV3f3H6AWRm7yFw/e6o/f"
    "a78wNTZo+slAv8SnNzA07REPeHhwYQZKddE2JeqX5gtABa8zrKdL5P7DiBx/+/4HE0hnNHqjDVTUBL+ZJKXpRVuv6A4qExtP3o/7"
    "RfIeU8Hc8VQVkqKgEyLiRF1mYhDrfRhn0SjEKryfeXwGhIq6N6psZUX3bRAudJZRJkvFWtCg3kwt/k9i69bwcm0yjtHK78FUWvKg"
    "Pjr2LuzgxQWNxhcXc8TIryZhm6kWkA0IN9BA6PLCHgf8SB8FGOHFmhy5IKXPvoxo4L2a+AJaU5JpwMv6BS3NhXO4dAtz9NCQ83qE"
    "Jox3Ltb2emsFHBRpKk2TX0sGlDhWnMS0hgDVodryMvyzhsBZ/l2LM7IbBqagpGonsCw99W4Qj6lFgvYE+XXtAEVAevqjxPONIhE+"
    "1diGmkKRNg1tpTVD0gwfCTIhn+0HFxJoMYf10mX+sfHuAqZNhbN5MfSgbV87V5ZG5lDYxL7KyFQl1kU4BnhvSVctVkw6WdN8SlPB"
    "+J/EyaZm4MvLMcU2VPPyte51hbRPzIrIfkKvDOfxKGYoOemdjzyM/RLakeNwAk6SH7QPK69ZMIIxW3198zK5bpbKL5HKx2OCW0sn"
    "BbbQV2n4ljOzZJmzpD4tZzLwpSZIrTs2VXLJLNnKoFD2Ui/dF+itKcuQae6SLzPeefRmkTNHmWOsFG+ThE3ormP8cKGAPJNWAB0k"
    "ZQQ4dXTfVnKrqtVHiQIsqC6FRCj6MVbc2VpU+kaFQ4RogWEfPG/FyG4uRiht2G+3A/pfy1+17/B7552Pev94S/qO3WnblVCigcSQ"
    "ZDmJ1aw54PJyvpbR7mYrhcyoYyyqU5NKHCM29dMJ3EiaUQ/+Cbic6pSMC/RihXHv8jyIRVQGOIu5JNUjsq9RaFJX9S1UscmEp7Ix"
    "SU/E5kNFUcRN33ylviHigX1C5AN9wbAq+XER4YCOfBa/NjV8NJYA4eIgPgwz3TC5sNcrf61GoWgdOw5N5DSO/Rt0dEewjjEDu/bk"
    "0fXP+NkvJbNMF4jED2cYnWHtPL3d9nVWQQOeuI7Zcy6MhqlwKhJ5SVCYC090b1QRrXZNz6F11Y8p6qNunlvAXxBt4/bBoBLe5xW6"
    "3LpT+cFBgiJzO9XEUYnkof5uJemqD/JDuIjmN5C48qhHgGtS4mwiNDTopwcpSdV/t68Fr4ciJWBgvkVLfMy/OAfgak4O0WRqMhqN"
    "R0bkZhAEh6ZLJQIIKXmgpcx8jWxkKJcHhf5e9R3TlDKU+v5O1IH/Av3/gcy0lpboGN2HY8fsIdRhzHrmZdgJJOFywxTxUzfAOWB5"
    "08F7nJpM1IpsKWFmpvGy3niJ2rnrNt/vu7hULhUhU1wnTM1Luozb6wrgAFbXhzdzFREHhyIJnSU1CAxxI2l85FomvrH0uNOpvFug"
    "DoAO2H1XpgfS7ADvo5yFWaKC6CJajeKQMtPxBSoOBTnhIA1pD5OzUiwmxrRCuXCBIhxzosPJrmzVNTDrcrmRq0okEBErEHEV1ryU"
    "FqFKjlEFH6m9cIRHu5nCn4aMgE/fX5ToztEWOYweOYiD9FAqdRAIqoLw8n2QiDKg4YtzJZ80OVC1REpOM1+jIBXR7c7aVnVIcPcS"
    "qPDe/zzq5mvnYf9Ouwd/8f/fW9ta6cM/QT+I7mz32gGUCagaJvBvKdueu0AKR+e7556ARgkww2wpTQHP/LxiZnzCaU5pwfstnKVo"
    "lHxOLjxAbhG1G0v+KcTdpZ9YBFzDbXyGvwTB9gBR4FEQiAjglBAXRW8UP9VG9CUZLxmj4IhChf0/tL15z+Nofhj4fz7FTG0wqALf"
    "NCnxbnvS4E2K4ilKFGUYMxTFU7xvsqeB6e7Aa+dAbhvO7GY2xzqJE9sJkmy8G2f9XVIZH3/5Kyyl96i3umeQIMBWoVQUST3H776e"
    "5/lBfFke3Dt47OfBD2+r0Kebl/69731XuLkQy+WjnXhXdTfl/JEyfuXDT0+u/7uHznv7gZ+fm9uWb79727XoxhjzR/6He1s/8ZFX"
    "MS9exfyLvIob7D55qs///l99rs8f3PqWFXr3cHNjnqjiWt4Y/y8/RpSu5RMrv9655Tbhj6zP+/rgx+UtL/hYoJh91iwGzG2F9TMk"
    "b0dVLhR9f3+7mAJ+viirN36/QOOVdH9VSXzPH7k3vD6h4iV++HznviZp4ftbzeMXt82Qvt3+Mogiu4W5br3k4dtvt//u5//wsST7"
    "vzu4hXemJzpr7/9/90Z6t4t3n3+rTvzVWarTPUhwp7mnaMEd798WIE+mx7OQWEisvk36ZmE/8ZfbNHGYv73t2PBFe6Px+xCeIgWf"
    "vX25/P794cONeG5+2JPyuM2+yB8L3Z9c0McBrZbx3Pz+GwN5adH4r0j0VfL2Xtn8+aI7d4uKuTlz9xE/PCXR3z3y2yIO2jiYPnnG"
    "xjLC7y66girvCLpbacPNoH1Q75/3IX7oog0/dhAexXb+LLbzx338biGlzL9pi/rJFb7Baen/5fkTNT+83HjSWgh024zmpZUoDm4b"
    "SCxTaJu/+o0649V6efXbs1xYvQnv+6HepnSj6W/M6OnFl/V2LzVb0X2fyRvoXu64Db9c3+qg7xLkQwAHAB6Km7x593AtX2vHezHx"
    "HWhPbHyLRdzyqvcVK80NgfeL5zT409dPf+XxYjFP75Br73GFJ1Q9lvUt8ucD69/n8/l3n43tW6j4PqlnL/sDqP7K9FEo6pdXqA//"
    "6EdPvsJLSPE+uw/BKP9D1OCp4YfvPrsK726/vgvFD/L1juH6znmPN58G81yP9KMf2f438PTw0Znfavmyk8areTxT1Uv2/FvDWgTS"
    "S0zvOa717TjOh1c+HLX1IZ6zxj4I3d1d6J7qW+XVTdYfiu9DD03zOntZ3xH6phn+ym0Ur6Mrr0b+2Zv/5c1z8cq7B+Ypt/6Jm7uP"
    "PsgdyfdI0U30v0Is9Y36i/pWc/FLj3Wwiyq85Zuet5++0faNV25085REiP3Lm3f3YGn6fGDqd37x29MPFlFzf/+p4W++/6FQ+FQv"
    "RPi9770iq/udX4Z99H7YwqPNcL9327T42W9hynuG5VfeXG6a9s1jRP0Hj1+KIEjj3H/zq6+969vobmcEFcuAiqezEO6tfv9D17+0"
    "e1KGn9/XlvkP46f5Q+uGn7YPzS2OcNu97p7cfDgUi8hZUPhtVRyHDwgKfXQw4keCbTHGX5z/IfJr/wa6e6de/Pbp1rv7fnp3OfZJ"
    "02WZW0/v7gd+t26cvrxPvX2+9e6279sHEnhlfb282t4TT7fE63cWimo/udWx3jyF22/e/Nm/+Gd/8o//zn/7w9/7rz/+nTc3yfP2"
    "JZ70YvN/QxC8exnGm195A1BPLPiD1D376dLLr96qgR5dgR/+pR++3oLrZlncaP+Xns2LBeZPO4E9HkT/Evn50Y9uMbqFwb/JrMvg"
    "Hh6P5n7lCt/w81Q39FyzzZW3I5Vv/PDokT/R551c3y4EFH8y3knomV4efh4xvVDzK2pafvhIT+/umxO9UW/C9Gkl26LqvvNIFUvb"
    "rx8sLkGdxc0tsH0rOAhrdxGclzcfT+5D0vmD8xjfdN1jave2jXv8sqQkvcci6g8Vfvco0zPG4A88dmvz9VBeXgLe/Lf//H+9//L3"
    "f/bPf+NPfvIf3jx8fl9vl774c8hjNKFYREyxzPlOnJ8tdPry5bbi516Sf8vGL2Rwe9DG7Z3SvnOjtOIF7DcT4HGt4R//k1vu79Pb"
    "u8/U/e4DrQAfpoB89sO/tJDkDz+9Z7sWPrzJxvPjssnaX8yW2n/WPrfdOr773fyT7hYVib3r9NAs9H7b3Obp5o0+7rHh53UL/qMK"
    "/PS70C08t1hHXnpLjyxz/bz4pKzvdgL7uPfjYhM9MXrwqLMf+O7tfc/OR4vpuTrwi/Q10j7/UCg5PrjfRsICm/t2pj9o2qIs/ctn"
    "b37lZ1/+b3/ye/90gc4LTn71CbRv418EyE+f3yjuVaSfvXn/47/zs//0+++//K0/+ckfv//y198Ajw+ANz/7yT/+05/8/vsf/90P"
    "2HrE1TPew7fFI5wfKe1/EsRPVx8gfDtS5YvbnmTPMPZuwPnvwrh4bU199nbR88Wjni+etd+928cm7/ZGG90V0XKzaH5QlLcDii7e"
    "N3/17tM78twX5H3xSjxlNwf0fuTw4oC/be5Jr7dP46K6S1w8LS740Y+ebg7++Rq3rx8tIqF5Oq/jNqqXvZ6XoTW3VN5C8v6HBamv"
    "Iv4ve/re8z4fAPokBZfx3Eb38N2mefdNidg09wqXp10SbqoI+ARa32qtn7am/RBa827v3dc0aI0XP60/evdwebktuAsjLiLmcWeu"
    "N81dMnqfBDdq8HNvelr1kD5cPgmXV2+S6b77IXXv9+3K/yu31ZTxu+fnt6XftxWtsZuablZaxeu3P1mvby8vo12t/8d+8dw+UNwO"
    "aro5MbflEpfbj5+/5PcUV5zf2ez21j1Oel/Tdv9SlG/vDSy9ogvv+p+9rd/iCPQAPSzDefdQv0VIZLlc/sH3rUjqtyRB3J6usNvT"
    "Fbwil2t0efzkt4vNa7/9Zr3f8Cg239JgL9Ho5RcfTIc7gy1QfTQqbxTwDcdhIeOf4zc8xgZefiw27x5uA3mYPs4G36IOz/Jp6dv/"
    "sADlzvzf9z97819/629/509+89/+6f/+4+/cPfkPvshNP7z5VL9lGx7ID8as/pjAfR1ku6eguvuvftAWrZu+VNO9XXp4u1i0wJt3"
    "T6LKjV8forOM7/MbrN5+Y2C3Xr8VIWLLJwZ9jA59pGDvFNq0+oue/cBmd855Mcy/0ab7hLBnZH2uvX2qKHn/1e++//ofvf/637z/"
    "+o/ef/XHt8+v/+n98zfef/kv3n/5B+9//OX7r/7v91//q/df/fPbza/+0/uv/8XthS9//8+/+t0//71/8P7Lf/3+y999/9Vv3D6/"
    "/Gvvv/r191/+2p//+B/96U//z/df/ss//+m/Xxr52f/6/yzS+v2X/+/7L3/y/qu//+YB+7Ae+BZFuA/+FxgZ3/veL7Ax7oVAj6J1"
    "kTyP0LoB74G7B5z+p9p7sVk+ig19pNTceFH877/+tTtUfv1xos92xZv3X/79G2CeZv83/+x3/sain95/+Tt3wPzN91/+2z/7l7/3"
    "s9//R5p8B+5vv3nR+a1/q0Z5UTcfCcgvbiGnZ81yp8pv6BH/g6S/W/0Ldj8M4V/+u5/97T94/+U/vPd/H8gzGv7ij379jp5Fk/7x"
    "z37tb/3pP/jpX/zRb7x5QBbcvDoq4uXQ88cg4Oc3VbM4DndV82n+xccBwfs77x6eYuEPP9dVfs6aQY+Rw+XfzfPlX5zhx2/PXvA9"
    "qfCYB5w+Lit6iTPeAoyPYafPPrmvyr/Vby8K7OeHIl7Crb6fL3j7xnTefdJG/oLk/DnSeIf3F49S0Cluku1DmuJ1DNEpnr2e+1sP"
    "/jd5cFt+I/rznBv+WNXdj+d+dozzJ0/97sM+blT5EjT+4X0WjxD57A67v/w5dQvo3YO2X3zvEYBP9x4Ngy9++Ly/Sfqih7ntU0zi"
    "Q6+vwhC3PPqHtMJThddrPKSfZH7TuKH/go5ntv4fa/weV+O/X38Tubdz22+AhD4ItddL/28y8lX+9efkkG4m0OevkrfQz3nn8pRn"
    "eiaJm0H1gSRqP70TxCPEFldTe9u+zBb1n1XjsXgd4ejuEY7Pl5v+Kw1wCV92cTsW75anjwsdniD1jPjniGD7SMV3Kf3+64Vx/9X7"
    "r//1+69//P6rv/fnv7kIlL99Z9k/+NOf/LM/+53f1Jm7KLnx8P3ib93Z+7cf2fiViF1a/WA1PjX94/df/+at6a/+4P3Xixr4+nax"
    "tPHzu/zXj8rgL/7oPz/KsL/4o//yX3/t773/8d/kxjItar/+Dvgd/laEUX9naeTpVz/+W0sLdx3z7+8t/NZdBC2t/R83ifTlX1tE"
    "0FNx5Zf/4f2Xf3hzCv7Lv/vzn/7xrd/bhP7u+6+Wdn76/qsvl64XmfazP/zD2zBuDf7DRxF6F1n4q7k+IfXhFwDvr70Sgr99iwY8"
    "rIib2r+hsno6K+hDgVT5LPyendeqfqyQvy9R+vzpBw+2f19d+wrc9W0H1duy6fx2cVuO1n4UAqo/aX8ZQaHvfe+eDHDPzW3L/vu2"
    "pcfl2fjul4mf88hZHk3Low8dL4T1uuPl9uf1p/nDLZ7Tfvqhu4fx05fmH6aXa+eL55F/U1jRT9s0ebdtROvsrf3ZD99/tdgFv3Uj"
    "lK/+3mPd6rNK/+33X/6Nv/ijn/6ll8LX9199tTh5t2df/fXHNxY8vy6LvdHrDTf/5G5U3CjrT/7NP1kI5M/+43/62d/4h/d2f7oY"
    "D3dqXshz0Z1//U9/8h9e+ltw/v7HX/3wvrXPf3dYbz79Hxj6Iy/d7JVnvfmNCdz6e/faLnuWGbfUwr0E80myPu3V+Db/Tvy0sWcR"
    "fOe2HdDTlnAL5+UvUuS1GfTF9FSe+EFSfSsce+v+Sfc/a/xnL+vhHol9dbjHTTl9Q9e5aXoPBnxTx/k32eY/j+q1oD0VH4dUnzKb"
    "T9UHt5ToS7Dvnjnq7x9/Ffps+fwU+tBOeRvNr7y5bxfv18v4b1shLb9+uhoif7EefvUltrAM6EV5fyul5T88haY/KhP9QOxfPHxe"
    "3nJJvX/bZ8Jzy2V4/n3e7x5+casfjy2LX5z1b795N7vevIziW67IK59h0fF3e+aVZfLBJroXEt0U5FNy4Ju2if8LjZE7ZXzsVE33"
    "2tdX5ZpfPMA+8u7hucnyfordY4P+/f1X9bEvW7nd12l+yKl93O3DxwnYzz9S2c+s+6KCbhbmLRTrf8tCeFk6o3Tf//y+R9inb25Z"
    "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"
    "HfizI5N5ClPeJItnfxv+bKosnhf6zX7T64v0nRc8D577ScrOC94G/KlrqTov9LbgT4Nzc15o7MCfjszKiePY2FJZOS9sbcOfvsjG"
    "eWF7A/50kyycSWUz+6aWgPPC1vrWFk0tHGHCWnd9w90VAjMYSbff9bZ3BY8J3zd36uuoVQau1rlQb+5sdLd3pVQPplKHuXm7kumF"
    "EutbV1xsHDlMaO7K9nZ9a1fJzmAwXn+dmhAsqHPBbWw16/gGWG4cQHOrubUrRZpYwWt6zV3JkTsXOlca3QbOGdhcWIHuuuv1dqUg"
    "D4bU867QkJgLhvn2mju9K7vMdmMa3yuNTnNXiRudC91+36Uagi+HMt72xhXcoYAyyboN+OOKRx7UBvzBHUefeH7T7wOQqDcIJT1v"
    "a8eVb4yZKiVwg1PTGcll6xtVi7wLS2jDkv4kEqYmmwo8BFG/5ivcWw1M49p0CvvnubCdXfFm5J1oO0plen1tA/DNod/z9EXGd+68"
    "hwtf37yytXVFvPMngMtgJd0dt74h3qFbknOhubm1TuuCr7zjLp4IBrrsocRU3akzia/Ekax36l6jKY9kfafu1nvqSDYaja1GV0us"
    "uwmb3EyOZGOnWW+68kjCt631de1INrzm9npDP5JNd31zoymOpLcOMFWXR7K70e33OsmR3Om7dYIoOpI79Z3+lb52JFVl7UiqufCR"
    "XN/p9Po74kg2O52drR11JGn/N9atxg4aJW1YdoPyE4vzudnv7VzZkudTtSPOJ9Xd3IK6V6zmxg7U5eTT4rBu93rr/a46rP3NK169"
    "ox1WYaG3aQEWsBoNWV2d3H6n029uyJPr9Tfgf8nJFXmVr1hbO/h/MW55ivs7243thjzF7vZOp+8mp5jqNra2rQbUb27WZW15prsb"
    "HZi5OtPNZm/d87QzTfXXN6wmjLq5viNzXasDvrXtwS6pA66GLg94euycUlsd9kav4db7+mHf7G64tKHqsKvjv/SwJwdaQXDxga5v"
    "NBt140ADHLrbG/qBVnuqDnS/6266m+aBVuunHegtz9vubJsHWk0iOdBX1rtJVXGgd7a8vttV1AbqMhsOWvHvCjWpY6vf6469rh42"
    "nKa9MdPtK0w7iGbTArBbBwjWzCBSZTY3YSEbMm+3ZiphFtvCYvb6ptaUMJkwywHUNGw4ZlsbXBJQ0YQSHuHPSc+5wj9TFAZ9PR47"
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
