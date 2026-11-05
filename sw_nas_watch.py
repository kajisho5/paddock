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
VERSION = "1.17.1"
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
        return [{"key": k, "loose": sorted(v)} for k, v in sorted(out.items())]

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
                    sdirs = [{"key": x["key"], "loose": [list(f) for f in x["loose"]]} for x in w.sdirs]
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
    "K8raJdeEV0KJAbqVRCGncJAFuAJTsu4h1AT9guMEnoUF5+YDLSOWhcWBYOyyQHFxNquOXV3i0mPBpUMRw1muYNkTi2UX3CQyTnQE"
    "cVhhsXuuSBFSVzooWBz/YDXHj9GN/GyAHP/AZp9D3ad+CCldTBZc4OCBA8FAkKjVB4KBfxfKg8DA76ndXxwIBnQgCFccCKzKwsVP"
    "sNwJsdyxZLdzxWhnhPhCvr0rT50r1i3QS135ZMwu5Bz9jlwBHBWc7w2MACyEvXGXaEibfZQiLKKrDNopYCjy60JOkKhLRI2S7DJM"
    "UOgsKTFvqSqsjoyxI6LPXY55VMUBN4NSK2Yc6aj9kCSFwTJtG0etyziNGtQLrqlDKmTmsNZMvSd8GCwJl9xNBTNL6ZuTmy+fkW7G"
    "TDAfXUGJ4uJ35IZ055G+oKTt0UpuAR7T8BZF8d07uTd2mx0mdz6E0QVex3SPxtQIivUq8qBqlfOxOg0OgNgBp9ZN9UIQ0rqUqoLG"
    "8vKT3j9XgLZIWmZ/7TlfKKwq89s73oDzTZzCory9czOIRmbAcKH850LTRODHdiH7ZTi4WjkQ2OgVObHzUpaFLP8w0lcKi4yQLkvu"
    "8cvZiLDWRgSdSBcNUSX9ocqd7KaJt8Mh7Gg/MzSR0x7YQbSMn5VCB8CHqNyTKYpYYct8F6ZRwpd2mNUVVErJzKpO2PxyrOPnh1Ep"
    "Yo/nQwg7UfnzVdn57XoOH8L6SnnMZ5c74cCEAW35KcDIzC48VhOBpZJDM/9Vke0DZYTQ05S6TQdvb0qew1I6BUr3k5O5VMzt/arV"
    "/UBNJqvArznPCyzndV62Nlsdr5dFLXkXFfxGzMTHwET94Faq+a24aeawr8QT/j/vhmp3HHxkb8ePXlNt/+Ai6uP4hyLavXGwO/4X"
    "eNLW0smGfRj/XdnuzY9lu+WSpLb8kQj3IclvzwiH/Y9jR8r7YfwjKe/jkta0KmlNV0ta05WS1rfjn5C07o2NpPV7Yo4k2+MefMJS"
    "CG4iGSowGJuV9T2hpVUEJo6NKrfAFxxhP6/E3kaPXg4XcALGa//8f9bya9h0ViNr2thhhwJT3wc7Shi3IwR6h36PdxEdeu3X73si"
    "V8aD983OmzdvOmzCg52zjJ8jGrVfJ40Jh6p8igoO2c7Z+/MAot4HGRfHAZKh4lnU0onY0TRWNY5yFcF77Zy1z23NgR06Xdn5lFiE"
    "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"
    "rfdU1kAhHdvKchR8/vmHDx/WPmys5cXx551bt259PkWSXaYEeI6Oy/41avdKYnb6RTIqgSGI0bidouyr/IQewKbzFgLkRPMNYeu2"
    "rH/n9g8+V79aKj/6WX4eS0mKSvhND745YQXgI3ao692V4jLBjMLJeE6Kwtp7X8gRy61CB3aMSGOucS83P+E0Ern3EdWjOf0I5TMg"
    "s6DW9NM9imMrYgW0YwLahfhMSqSWOmS3yFFLjPlntQ48PMlV6JjFMD3mMJ0uRfHd4Hr92+8A22O/W2mkDt8bBnktGB8zGF9vownO"
    "N/RkYD3JbFIjN+LAN3YusL6z1Xmpex1fjQwKhgzShZKmxb07aEKNeXLVmK3Wv5AoJEWfFYk/EiluQPlDFUgmJhx2dJAckopYMZy9"
    "t3DxgCcNkl+f7zc88T3ZhmqkztCz+0vpM+28pQ9ZqwVAvCjkQNhHFrPgO8nlJ9fi8pNPcPnJNcRJid8zM0yu4voDU+04omhsfTSy"
    "XIxuYkI3aPa51FmMbmJCN82ntZCqjiXDaY7j8osSlvjtpIy9Fr0knDkpPVXX95vPt4V97DSTNl1G5UhUDOcEBQduHRx+UGi//Fd8"
    "RPXabj2GaBeJU68UmFbWFqZd4rrwha7jZ7u8Bc3W7L+TJFvCK3Iv1cV6iOh1MJ9XhSuZ5jwqOLrZHXgBY7kdyECRdTYnk2xORcyO"
    "9KaJ6mvjtBi52TUZGuK1XP5LNHMzSj/mMjSVISk8SDZ6SJWoIyHdpOPwG8vP+Vz0ZBWMRAmaL4G182LO/VTUjpUluRaZeUXj86SB"
    "wrqBujOXxIKj6pJYviIL9uF84dJQ1Ci1FnwfikWbL9WPR14Wk5lK1T7+E7b3NdP+upKStu+z5eU3nJ/WVotLjhOBfzH0pI7XHt5b"
    "O1vbbXI5MBquJKRzwYjTYkG3Mc/EvlTL2trZkcewlqsO+mOxAqpeGQ0NYbjrRC673DqahDs72uGG2AHMlqsrdwdnK5u5QsQhyK1d"
    "zqtiF0s2hb0scPXtZiRoGKfzIWRki65XkpbUW7i51uFCwiGpTVSDR0NHZo/KJEJcQ9yjg4wRjeDHhh+gdR9ZPjO+o5HnYHIcX2vy"
    "1dRIrqXFPTZ4wqDwFmv5a2KhTls39yLyKur+hto3ry2Mk2pwecGaDpqr5WdfS+V5zckmD5l1m9AG+T7p0F+MPcKMBjyPcDHbbvgI"
    "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"
    "5w+U8Qsbfno0/WfI7r1+v56fmpPK199cqhYtC2P/gf3hLfsnPrAq9rNVsf9pVsVCu08e8/O//QtP+fmDWy9RoTdvFzPmkSuYcln4"
    "bXj3KDHl41L+oHJL+BH6vO8Pftje8jwfMxWzz5oZwCw7rJ8oubyqcubo+/3bGQr4+aysXvn9TI0X0v1FJvE9fuQu8/o4Fc/+w6cz"
    "9z1JszBZch6/vxRD+nr78yCKbHFzLb3U4euvt//mJ//wISX7fzi4ee1Mj3zW3v//5sJ6y8Gbz7+WJ/7iXarT3Ulw57lHb8F93r8u"
    "QB6hx5OQmFmsXh56QdiP68ttmjjMX6f37fwLj9+H8Ogp+Oz18+G37xffLsyz2GGPyuMnP/15mnHfo0W6GP/3gT54AZYXzHpp0fgv"
    "WfZjO3bJTHpkxsd7n7O43xLLvpp7v0X+kGD/2NEDIVZvH3paFu7H/bwIGtdLRvXns87ezaptMSLvlHr7GLx/87DOZzHUxsH0yRMX"
    "zJT55qyjtuWdMe7okFuA9Fvq/nknzfsu0vBDw+RBXeRP6iJ/qB+4uLIyf9FS9aMJvszP3P/z9cdV9Pb5xKO2RKClCM5zK1EcLIUr"
    "5kdom1/4KL95tZ5v/fpTLhvvwnsd1uWRlrX00RM93vi8z+85Vyy617ecSff+jNvw8/GSf32XXO8dRwDwtlvk3Ju3s0h4oZXvScx3"
    "oj1lioQP8dz7TplmmcD7wVP4/fHrp7/4cDDD4jvl2rs/43GqHtIJZ7n3XuTcn+fzbz6B/MVFfX+oJ+v+Pal+dvrABfbzK9SHv/e9"
    "Rxvl2ZV5f7r3TjD/vbfiseG333wyUd4sv74L4/dy/T7D9X3FP5x8HMxTHtT3vmf4H83T2w/eNU6VzxU8XjzHE1c9R+2/NqxZED77"
    "Ep/8aV/3H72/5f0rvt77kdbYe2Gv34W9f98Zs+iYU/Ft6G3avIyaFvcJfdUMP7uM4qVX58XIP3v1v7x6Spp585Z9jOl/4ubug+1z"
    "n+S7h2pROS8mdvtR3kex5Hr83EP+7SxmljjXU9nrhbeXtbLwzWPwIvYvr97cnbTp04tav/HT756+M4ua+/2PDX98//sEZT+dmfBb"
    "33rBVvczPw/76P0lDw9Y5X5uKZb8ZC+x5T2y84uvLouGf/Xgyf/Ow5ciCNI491/90kurfhnd8m6iYqnm//gOhnur337f9c/pj0r4"
    "8/ueNv/t+Gn+tnXDT2fosfgvlqp596Dq21OxvHW5+AkQwAvfIij0UrC5Hwi22Qh4djoMkV/7C+keUrri14+n3tzr+N3l2CdNl2Vu"
    "Pb25v2i8deP0+X7u9dOpN0u9ufcs8AL1Pd/a3gNeS8D3GzNHtZ8s+bOLhbL85tVf//6/+st/8Y/++5/90X/7we+9WiTP62c/1rOt"
    "8ZEgePM8jFe/+ArgHpfgd1L37KdzL7+0ZCE9mCDf/Znvviz9tSCahfd/7gnWzDR/rEAGPVhPTx6n2bidtdH3vmd/vFjnwb19eCX4"
    "CxN8mZ/HfKWnXPFzubzKeVkPD56AR/68s+vrmYHiT8Y7Cz3xy9ufxEzP3PyCm+YfPvDTm3tRpFfqIkwfd9DNqu4bD1wxt/3ywmyK"
    "1FncLA71JdEhrN1ZcF5effhw74Pd743WeNF1DyHlpXx8/LyVJb37QOr3mYV379bTjMHv19jS5suhPN8EvPrv/+X/evfFH//4X//a"
    "X/7wT1+9/fy+zy99tiORBy9GMYuYYn7mO3N+NvPp85dlp9F9K8CSBTCzwXKhjds7p31j4bTimewLBHjY4/gXv7vEHD9d7n3i7jfv"
    "eQV4/wjIZ9/9mZklv/vpPco2r8NFNp4ftmvW/gxbav9J+yxVQr75zfyTbvHGxN51etvM/L4U1Xk8ufDH3Sf9tF/Cf1CBn34TWtyC"
    "Mzry0iUsMz/r58UnZX3HCexDzckZEz0u9OBBZ7+Vu9f3WqGPaOsJaqYvJ+3z9wma41v365Mw0+ZeRvU7TVuUpX/57NUv/viL/+0v"
    "/+hfztR5npNfeiTt6/inEfLTpzuKe/bqZ6/e/eAf/fg///G7L377L3/4F++++NVXwMMF4NWPf/gv/uqHf/zuB//4/Ww9zNXjvM+C"
    "qnig8wOn/R1J/Hj0nsLLq1y+v9RCe6KxtxDnf0jj4iWa+uz1rOeLBz1fPGm/e7cPTd7xRhvdFdF8smi+U5TLi5Ey7+Nfvfn0Pnnu"
    "8+R9/4V46hfD957oPxv+rx+Cba8fx0V1l7h43NTwve89nhz88zVuX15a/C2P7wlZRvVcY3p5i+QSQpxZ/iVAfx/meq4lfI83vSfo"
    "oxScx7OM7u030+bNxxIxbe6ZNY/VGRZVBHwCrZcc78eSuO9det5y330vhdZ48eO+pzdvL8+nBXdeiLOIeagI9qq5S0bvk2DhBj/3"
    "psfdFunbyyfhfOsime5VF6l7v69X/s8uuzjjN0/Xly3ny07a2E1NNyut4uXdn6zXy83zaFfr/7lfPLUPFMsLohYjZtmmcVl+/PQl"
    "v4fW4vy+zJa77v7Z+166+5eifH1vYO4Vndeu/9nr+jWOQG+ht/Nw3rytXyMkMh/O/+B7CZT6NUkQy9UVtlxdwStyPkbny4/+Arl5"
    "6S9Y0Psyj3LzNQ327AWff/EeOtwX2EzVB1C5cMBHhsO3vvWT7IYHn8Tzj+VmFktLyfLpwyj04u14kk9z3/77jS/3xf9t/7NX/+23"
    "f+Mbf/lb//6v/vcffOPuQXhviyz64dWn2hLleEu+B7PaQ+D4pXPvHvrq7r/6Tlu0bvqcxfd67uH1jGiBV28eRdUlfvnynnl8ny+0"
    "ev3RwJZev+aZosvHBfrglfpAwd45tGn1Zz37fpndV84zMP+ozcvjhD1N1ufn14+ZLO++/IN3X/3zd1/9u3df/fm7L/9i+fzqX94/"
    "f+3dF7//7os/efeDL959+X+/++rfvvvyXy8nv/zP7776/eWGL/74b778g7/5o3/67os/fPfFH7z78teWzy9++d2Xv/rui1/5mx/8"
    "87/60f/57ot/8zc/+o9zIz/+X/+fWVq/++L/fffFD999+U9evcXe70NevBf3wf8UkPGtb/0UjHFPQHoQrbPkeaDWQry357uj6+/U"
    "3jNm+cAn9YFSu8Sz4n/31a/cqfKrDw/6hCtevfvinyyEeXz6f/DXv/frs35698Xv3QnzD9598e//+t/80Y//+J9r8p24v/PqWee3"
    "/pIF86xuPhCQ319cXU+a5c6VH+kR/72kv6P+eXbfD+Hf/Icf/8afvPvin937vw/kaRr+9s9/9T49syb9ix//yj/8q3/6o7/98197"
    "9RaZ5+ZFiOH5ZesPzsfPF1UzGw53VfNp/v0PHZH3e+YBhU8Btp9gKj9F66AHj+X8b7F8+Wdj+OHbkxV8D2Y8xB+nD9OZnp1Fi2Pz"
    "wd312Sf3agBL3viswH6yK+LZzev7+TxvHz3Om0/ayM9fe/mTh/NO7+8/SMHvFItke59D/NJ3+Z3iyeq53/XW/3gNSuVH3p+nmPSH"
    "qu7+WvAnwzh/tNTvNuxDgcxnZ/V370/xQJHP7rT7e59ziyPx7iz+/rceCPh47gEYfP+7T3VV0mc9zG0ffRLve33hhlji9+/DGY+Z"
    "ZS/nIf0k85vGDf3n6Xha1v9zjd/9avy3648nd3lf/EJI6L1Qe1nSeJGRL+K+PyF2tUCgz18EjaGfcE/2GN96YokFUL1nidpP7wzx"
    "QLHZ1Dy/bp+fFvWfVOOmeOnhKB983fNJ/6UGCJ+rx22KN/PVhw0Wj5R6zjZ49Ai2D1x8l9LvvpoX7r9999UfvvvqB+++/M2/+a1Z"
    "oPzGfcn+yV/98F/99e/9ls7cRcmyhu8H//C+vH/nYRm/ELFzq+9R42PTP3j31W8tTX/5J+++mtXAV8vB3MZP7vIPH5TB3/75f3mQ"
    "YX/75//1v/3Kb777wT/gxjItar/+BvgNfkn+qL8xN/L4qx/8w7mFu475j/cWfvsugubW/o9FIn3xy7MIekzq/OJP333xZ4tR8F//"
    "w9/86C+WfpcH+sfvvpzb+dG7L7+Yu55l2o//7M+WYSwN/rMHEXoXWfiLZ32c1Lc/hXi//EII/s7iDXi7WhzI96nMH1P83++2Kp+E"
    "37Pxmj5k5t+3Rn3++IO3hn/f1fuC3PVSuXXZrp0vB8s2uPYDF1D9SfvzCAp961v3IIR7bpZXBdzLpR7na+Obnyd+wiVnvjTNl953"
    "PDPWy47n05/Xn+ZvF39O++n77t6Onz43/3Z6Pna+/zTyj4XV7bE8lLeUL62z1/Zn33335YwLfnthlC9/8yFf9kml/867L379b//8"
    "Rz/znHD77ssvZyNvufbl33+4Y57nl+m4C78uc/O7d1CxcNZf/rvfnRnkr//Tf/7xr/+ze7s/msHDnZtn9px159//qx/+6XN/85y/"
    "+8GX372XFPofDuvVp/8TQ39YSwteedKbHz3A0t+bl7jsSWYsoYV76uejZH2sEfk6/0b8WFC0CL6xlCF6LEU3r7z8WYq8hEHffx8Q"
    "+TuFQe6e2BeybVFOH+k6N03vzoCPdZy/yDb/aVQvBe3fKz50qT5GVB+zHpZQ7LOz7x6x6u8fvwB9Nn9+Cr14xckyml98dS9T79fz"
    "+JcSTPOvH4+GyJ/Rwy89+xbmAT0r768Fk/ynQNIH6anvmf37bz8vlxhW7y/1LTy3nIfn35/7zduf3uqHY+vjZ2P963feYddzOOvr"
    "psgLm2HW8Xc88wKZvMdE9wSmRUE+Bgc+xib+TwUjd8740Kia7jm3L9JEv/8W9pE3b5+aLO9vz3to0L/f/yIv97mE3H1/6PtY3ofd"
    "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"
    "LKF/fvvjd/E3FFJPf99Xp+O3f/w/di9qyA=="
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
