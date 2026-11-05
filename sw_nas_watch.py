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
    "Lr9AiPnw0U68q7pFOX9DGb/C8PET9H/3kDpvP6zn5+aM4u13l6pFy8KQvoE/nGX/xDdQhTSjCukXoYqFdp885ed//68+5+f3drVE"
    "hd49LDDmiSvIYln4iX/3KJHF01J+Xbkl9D+yPu/7gx+3t7zMx0zF9LN6NmCWHdbPlFxeVTlz9P3+3WwKuNmsrN643UyNV9L9VSbx"
    "PX5kL/P6NBUv/sPnM/c9SbN4XHIev1iKIX27/XkQebq4uZZecv/tt9t/9/N/+JiS/d8d3Lx24ic+a+7/f3dhveXg3effyhN/9S7V"
    "+O4kuPPck7fgPu/fFiBPpsezkJhZrFoeerGwn9aXXdehn71dKjZ80Sw8fh/Ck6fgs7cvh9+/X3xYmGfBYU/K4+c//XWc7b4nRLqA"
    "//tAH70AywtmnSSv3dcs+zGOXTKTnpjx6d6XLO4HfNlXc+83zx4T7J86eiTE6uGxp2XhftzPq6Bxfrf8Zp29n1XbAiLvlHp4Ct6/"
    "e1znsxhqQm/85JkLZsp8d9ZRanFnjLt1qC2G9ANz/7yT5lXysf9NYPKoLrJndZE91g9cXFmpu2ip6gmCL/Mz9/9y/WkVPbyceNKW"
    "CLQUwXlpJQi9pXDF/AhN/Vc/ym9eredbv/2US8l3/16HdXmkZS199ERPN77s83vJFQvu9S1n0n04Y9fcfLzkX98l1wfHEQA8FIuc"
    "e/cwi4RXWvmexHwn2nOA1H+M5953ytTLBN4PnsPvT18//ZXHg9ksvlOuufsznqbqMZ1wlnsfRM79eT7/7rORv7io7w/1jO4/kOqv"
    "xN9wgf3yCnXhH/3oCaO8uDLvT/fBCeZ+8FY8Nfzw3WeI8m759V0Yf5Dr9xmu7iv+8eTTYJ7zoH70I939aJ4evvGucaZ4qeDx6jme"
    "ueolav+tYc2C8MWX+OxP+7b/6MMtH17x9cGPtN58EPa7u7B37ztjFh3zg/z70ENSv46atvcJfVP3f2UZxWuvzquRf/bmf3nznDTz"
    "7uH6FNP/xM7sR+xzn+S7h2pROa8mVv0o76Ndcj1+6TH/dhYzS5zruez1wtvLWln45il4Ebq3N+/uTtrk+UWt3/nFd48/mEXN/f6n"
    "hj++/0OCspvMTPi9771iq/uZX4Zd9P6Sh0db5X5uKZb8jJeuxT2y8ytvbouGf/Poyf/B45fc85Iwc9/86mtUv4xueTdRvlTzf3oH"
    "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"
    "feWGWOL3H8IZT5llr+ch+SR169r23ZfpeF7W/2ON3/1q3Perjyd3eV/8Qkjog1B7xZTTIiNfxX1/TuxqMYE+fxU0hn7OPcNTfOuZ"
    "JRaD6gNLVG5yZ4hHis1Q8/q2eXla1H1WjX85f+3hGB593fNJ9/W+N/+letxfzt/NVx83WDxR6nninz2CzSMX36X0+6/nhfuv3n/9"
    "r99//eP3X/29P//NWaD87fuS/YM//ck/+7Pf+U2NvouSZQ3fD/7WfXn/9uMyfiVi51Y/WI1PTf/4/de/uTT91R+8/3pWA18vB3Mb"
    "P7/Lf/2oDP7ij/7zowz7iz/6L//11/7e+x//TXYokrxyq++A3+GW5I/qO3MjT7/68d+aW7jrmH9/b+G37iJobu3/WCTSl39tFkFP"
    "SZ1f/of3X/7hAgr+y7/785/+8dLv8kB/9/1Xczs/ff/Vl3PXs0z72R/+4TKMpcF/+ChC7yILe/WsT5P68AuI99deCcHfXrwBD6vF"
    "gXyfyuwpxf9l3rjnt/e9pHpkyWNm/n1r1OdPP3jQ3fuu3lfkrpbKrct27Ww5WOrqNt9wAVWfNL+MoND3vncPQtjXenlVwL1c6nm+"
    "Nrz7ZfznXLLmS+N86UPHM2O97ng+/Xn1afaw+HOaTz909zB8+tL8w/hybH3xPPKPhZX8VB7KWcqXVulb87Mfvv9qtgt+a2GUr/7e"
    "Y77ss0r/7fdf/o2/+KOf/qWXhNv3X301g7zl2ld//fGOeZ5fp+Mu/LrMzT+5GxULZ/3Jv/knM4P82X/8Tz/7G//w3u5PZ+Phzs0z"
    "e86686//6U/+w0t/85y///FXP7yXFPrvDuvNp/8DQ39cS4u98qw3P3qApb93r+2yZ5mxhBbuqZ9PkvWpRuTb7DvhU0HR3PvOUobo"
    "qRTdvPKyFyny2gz64kNA5H8qDHL3xL7CeYty+kjX2UlydwZ8rOPcRba5z6N6LWhd+5su1aeI6lPWwxKKfXH23SNW3f3jr0KfzZ+f"
    "Qh/aGZfR/Mqbe5l6t5rHv5Rgmn/9dNQH7mw9/OqLb2Ee0Ivy/lYwyX0OJH0jPfUDs3/x8HmxxLA6d6lv4djFPDz3/tzvHn5xq98c"
    "Wxe+gPVv33k3u17CWd+GIq8ww6zj7/bMK8vkg010T2BaFORTcOBj28T9hcbInTO+Carie87tqzTRLx5gF3n38NxkcX973mOD7v3+"
    "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"
    "sVxbrg=="
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
