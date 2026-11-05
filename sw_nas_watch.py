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
    "fPiAE++qblHOHyjjFzZ88mj6z5Ddff1+PT81J5Wvv7lULVoWxuED+8Nd9k98YFUcZqvi8NOsioV2nzzm53/7Hzzl5w9OvUSF3rxd"
    "zJhHrmDKZeG3wd2jxJSPS/mDyi3BR+jzvj/4YXvL83zMVMw+a2YAs+ywfqLk8qrKmaPv929nKODls7J65fUzNV5I9xeZxPf4kbPM"
    "6+NUPPsPn87c9yTNwmTJefz+Ugzp6+3Pgyiyxc219FIHr7/e/puf/MOHlOz/4eDmtZM88ll7//+bC+stB28+/1qe+It3qSZ3J8Gd"
    "5x69Bfd5/7oAeYQeT0JiZrF6eegFYT+uL6dpoiB/nd638y88fh/Co6fgs9fPh9++X3y7MM9ihz0qj5/89Jdpxn2PFuli/N8H+uAF"
    "WF4w66ZF471k2Y/t2CUz6ZEZH+99zuJ+Syz7au79FvlDgv1jRw+EWL196GlZuB/38yJoXC8Z1Z/POns3q7bFiLxT6u1j8P7Nwzqf"
    "xVAb+dMnT1wwU+abs47alnfGuKNDbgHSb6n7550077tIgw8Nkwd1kT+pi/yhfuDiysq8RUvVjyb4Mj9z/8/XH1fR2+cTj9oSgZYi"
    "OM+thJG/FK6YH6Ft/sFH+c2r9Xzr159y2XgX3OuwLo+0rKWPnujxxud9fs+5YuG9vuVMuvdnnIafj5f867vkeu84AoC33SLn3ryd"
    "RcILrXxPYr4T7SlTJHiI5953yjTLBN4PnsLvj18//fmHgxkW3ynX3v0Zj1P1kE44y733Iuf+PJ9/8wnkLy7q+0M9WffvSfUzyQcu"
    "sJ9boR78ve892ijPrsz70713gnnvvRWPDb/95pOJ8mb59V0Yv5fr9xmu7yv+4eTjYJ7yoL73PcP7aJ7efvCucap8ruDx4jmeuOo5"
    "av+1Yc2C8NmX+ORP+7r/6P0t71/x9d6PtMbeC3v9Luy9+86YRceci29Db9PmZdS0uE/oq2b4mWUUL706L0b+2av/5dVT0sybt+xj"
    "TP8TJ3cebJ/7JN89VIvKeTGx24/yPool1+NnH/JvZzGzxLmeyl4vvL2slYVvHoMXkXd99ebupE2fXtT6jZ9+9/SdWdTc739s+OP7"
    "3ycoe+nMhN/61gu2up/5OdhD7y95eMAq93NLseQne4kt75Gdn391XTT8qwdP/ncevhS+n0a59+oXXlr1y+iWdxMVSzX/x3cw3Fv9"
    "9vuuf1Z/VMKf3/e0eW/HT/O3rRN8OkOPxX+xVM27B1XfnovlrcvFT4AAbvAWQaGXgs35QLDNRsCz02EIvdpbSPeQ0hW9fjz15l7H"
    "7y7HPmm6LHPq6c39ReOtE6XP93Ovn069WerNvWeBF6jv+db2HvBaAr7fmDmq/WTJn10slOU3r/769//VX/6Lf/Tf/+yP/tsPfu/V"
    "InleP/uxnm2NjwTBm+dhvPr5VwD3uAS/kzoXL517+YUlC+nBBPnu3/vuy9JfC6JZeP9nn2DNTPPHCmTQg/X05HGajdtZG33ve9bH"
    "i3Ue3NuHV4K/MMGX+XnMV3rKFb+Uy6ucl/Xw4Al45M87u76eGSj6ZLyz0BO/vP1JzPTMzS+4af7hAz+9uRdFeqUuwvRxB92s6r7x"
    "wBVz2y8vzKZInUXN4lBfEh2C2pkF5/XVhw/3Ptj93miNFl33EFJeysdHz1tZ0rsPpH6fWXj3bj3NGPx+jS1tvhzK803Aq//+X/6v"
    "d1/88Y//9a/85Q//9NXbz+/7/NJnOxJ58GIUs4gp5me+M+dnM58+f1l2Gt23AixZADMbLBfaqL1z2jcWTiueyb5AgIc9jn/xu0vM"
    "8dPl3ifufvOeV4D3j4B89t2/N7Pkdz+9R9nmdbjIxsvDds3am2FL7T1pn6VKyDe/mX/SLd6YyE2mt83M70tRnceTC3/cfdJP+yW8"
    "BxX46TehxS04oyM3XcIy87N+XnxS1necwD7UnJwx0eNC9x909lu5e32vFfqItp6gZvpy0j5/n6A5vnW+Pgkzbe5lVL/TtEVZetfP"
    "Xv38j7/43/7yj/7lTJ3nOfmFR9K+jn4aIT99uqO4Z69+9urdD/7Rj//zH7/74rf/8od/8e6LX34FPFwAXv34h//ir374x+9+8I/f"
    "z9bDXD3O+yyoigc6P3Da35HEj0fvKby8yuX7Sy20Jxq7C3H+hzQuXqKpz17Per540PPFk/a7d/vQ5B1vtOFdEc0ni+Y7Rbm8GClz"
    "P/7Vm0/vk+c8T973X4infjF874n+s+H/+iHY9vpxXFR3jYrHTQ3f+97jycG7JFH78tLib3l8T8gyquca08tbJJcQ4szyLwH6+zDX"
    "cy3he7zpPUEfpeA8nmV0b7+ZNm8+lohpc8+seazOsKgi4BNoveR4P5bEfe/Sc5f77nsptMaNHvc9vXl7fT4tOPNCnEXMQ0WwV81d"
    "Mrqf+As3eLk7Pe62SN9ePwnmWxfJdK+6SN37fb3yfmbZxRm9ebq+bDlfdtJGTmo6WbkvXt79yXq93DyPdrX+n/vFU/tAsbwgajFi"
    "lm0a1+XHT1/ye2gtyu/LbLnr7p+976W7fynK1/cG5l7Ree16n72uX+MI9BZ6Ow/nzdv6NUIi8+H8D76XQKlfkwSxXF1hy9UVvCLn"
    "Y3S+/OgvkJuX/oIFvS/zKDdf02DPXvD5F++hw32BzVR9AJULB3xkOHzrWz/JbnjwSTz/WG5msbSULE8+jEIv3o4n+TT37b3f+HJf"
    "/N/2Pnv13377N77xl7/17//qf//BN+4ehPe2yKIfXn2qLVGOt+R7MKs9BI5fOvfuoa/u/qvvtEXrpM9ZfK/nHl7PiBZ49eZRVF2j"
    "ly/vmcf3+UKr1x8NbOn1a54punxcoA9eqQ8U7J1Dm1Z/1rPvl9l95TwD84/avD5O2NNkfX55/ZjJ8u7LP3j31T9/99W/e/fVn7/7"
    "8i+Wz6/+5f3zV9598fvvvviTdz/44t2X//e7r/7tuy//9XLyy//87qvfX2744o//5ss/+Js/+qfvvvjDd1/8wbsvf2X5/OIX3335"
    "y++++KW/+cE//6sf/Z/vvvg3f/Oj/zg38uP/9f+ZpfW7L/7fd1/88N2X/+TVW+z9PuTFe3Ef/E8BGd/61k/BGPcEpAfROkueB2ot"
    "xHt7uTu6/k7tPWOWD3xSHyi1azQr/ndf/dKdKr/88KBPuOLVuy/+yUKYx6f/tb/+vV+d9dO7L37vTphfe/fFv//rf/NHP/7jf67J"
    "d+L+zqtnnd96SxbMs7r5QEB+f3F1PWmWO1d+pEe895L+jvrn2X0/hH/zH378G3/y7ot/du//PpCnafjbP//l+/TMmvQvfvxLv/5X"
    "//RHf/vnv/LqLTLPzYsQw/PL1h+cj58vqmY2HO6q5tP8+x86Iu/3zAMKngJsP8FUforWQQ8ey/nfYvnyz8bww7cnK/gezHiIPyYf"
    "pjM9O4sWx+aDu+uzT+7VAJa88VmB/WRXxLOb1/Pyed4+epw3n7Shl7928ycP553e33+Qgt8pFsn2Pof4pe/yO8WT1XO/66338RqU"
    "yo+8P08x6Q9V3f214E+Gcf5oqd9t2IcCmc/O6u/en+KBIp/daff3P+cWR+LdWfz9bz0Q8PHcAzD4/nef6qqkz3qY2z76JN73+sIN"
    "scTv34czHjPLXs5D+knmNY0TeM/T8bSs/+cav/vV+G/XH0/u8r74hZDQe6H2sqTxIiNfxH1/QuxqgUCfvwgaQz/hnuwxvvXEEgug"
    "es8StZfeGeKBYrOpeXndPj8t6j2pxk3x0sNRPvi655PeSw0QPFeP2xRv5qsPGyweKfU08U8ewfaBi+9S+t1X88L9t++++sN3X/3g"
    "3Ze/+Te/NQuU37gv2T/5qx/+q7/+vd/SmbsoWdbw/eDX78v7dx6W8QsRO7f6HjU+Nv2Dd1/91tL0l3/y7qtZDXy1HMxt/OQu//BB"
    "Gfztn/+XBxn2t3/+X//bL/3mux/8GjeWaVF79TfAb/BL8kf9jbmRx1/94NfnFu465j/eW/jtuwiaW/s/Fon0xS/OIugxqfOLP333"
    "xZ8tRsF//Q9/86O/WPpdHugfv/tybudH7778Yu56lmk//rM/W4axNPjPHkToXWThL571cVLf/hTi/eILIfg7izfg7WpxIN+nMn9M"
    "8X+/26p8En7Pxmv6kJl/3xr1+eMP3hrefVfvC3LXS+XWZbt2vhws2+DaD1xA9SftzyEo9K1v3YMQzqVZXhVwL5d6mq+Nb36O+AmX"
    "7PnSNF963/HMWC87nk9/Xn+av138Oe2n77t7O3763Pzb6fnY/v7TyD8WVrfH8lDuUr60zl5bn3333ZczLvjthVG+/M2HfNknlf47"
    "77741b/98x/9veeE23dffjkbecu1L//hwx3zPL9Mx134dZmb372DioWz/vLf/e7MIH/9n/7zj3/1n93b/dEMHu7cPLPnrDv/4V/9"
    "8E+f+5vn/N0PvvzuvaTQ/3BYrz79nxj6w1pa8MqT3vzoAZb+3rzEZU8yYwkt3FM/HyXrY43I1/k3oseCooX/jaUM0WMpunnl5c9S"
    "5CUM+v77gMjfKQxy98S+kG2LcvpI1zlpencGfKzjvEW2eU+jeilo/37xoUv1MaL6mPWwhGKfnX33iFV///gH0Gfz56fQi1ecLKP5"
    "+Vf3MvVePY9/KcE0//rxaAi9GT38wrNvYR7Qs/L+WjDJewokfZCe+p7Zv//283KJYfXeUt/Cdcp5eN79ud+8/emtfji2Pno21r9+"
    "5x12PYezvm6KvLAZZh1/xzMvkMl7THRPYFoU5GNw4GNs4v1UMHLnjA+NquSec/siTfT7b2EPefP2qcny/va8hwa9+/0v8nKfS8jd"
    "94e+j+V92O3bDwO/n3+gsp+W7rMKWhDm4or1voYQnrfsWN23P7/XJvv01RL9/DTK5tvAMg9+dilEgiFvoyOtmQMkC0FBzX/U3SHk"
    "DsF8JC1fmfmvPf/Psnombpcz1EndmZBE1Q3iYgZFbZLVxuT4g7e5tbnhUUfVQkecwC+n3j/vki0DNUfnKCf8wJke1CqxmFbxVuTW"
    "uqwUwS6ht3Qc7U9CxSQOMW75oJADUsIYiQtzZtXbcHXRew8E831z03AF74hbc2sm6yYRaIsOuEsQKAy6IHpGbhoUH/b1BJzG5MpD"
    "Vmzn+4O8Om+5kUp3KrvnJE2zs6Y9y8CYhEcziAPy7CWrs0KH2RTA3MqyXY1hV3QUtULgtrRw2atnTBhPwWFDFxKnMryWNdd4a627"
    "QDSpTGHbMmxa7ewFfdvBWkJS62hIcIn2mRxH91tbNdDDsXAoxtOqWjV7lRd2rmTeGmY43OKuH0TbQCJ15x1jWsK2q6O66jd4JW1Q"
    "kg/ca3iDLTCruJYue2ZMaX5gT7gy2l5EayUy9c0hJaOuO2K0ejSFaxU57JoRMepY8tjGZFf76VKJkXfmwKN8qlfXdZpGpeax8FHi"
    "TIPqfYyE8LUQbAB1dRVSoD7LYzcGWk1oPMMJ8fF2MzsN5XpTS6C4wP0jmpQHv9OOAFNeWyEb9gOS4WmQiCUpOOeDmZH0Kg+zEAlJ"
    "kd26HAdPZ+O8Rzw9bcWWRNb7PjlC1To6UttYIJEs8lc7O5V6C53qzo/HmVLCOGBjw3jKBvMaggHXjbpbMQO1QYBbnyKXoDj7QmVD"
    "JXR296NoywdHlmsaqmdJ3kOADMWl7Bro3qUZjwJN1FyFRHW0rr0us9EWUgV7zXVRYeU7oGuEHa6OWHgFGIs9s9HxZsnVZJOHsbPI"
    "Ud9J0ZWPsBHm64JNyYaTHUUEmKMkF3yc5ZQaowOpHUCT8NK9upUavOcFk6FVV4NKw5U3VyFPGg4d91SPgNLmhpCb7so5OZ4HacfI"
    "w7napwhoqYpfEvCuCFhPm6LeOqlynqo7Echv2qSdXXNzhRLgRjbnMEvaASvVjPbZ6tR4LH05yS7cbSUC72/SrdymvBX0+0tHXIvj"
    "TAxmj/CEPtCbva5tSpIhRoCFhugqigZb5hVZtgQ7oJ1Gw4OMyDBJtpYvom5fX8Rgw8n5ZlKtoszJUiF7ActwVr56Ki1STQXLiqQL"
    "rsVeZTPNuUshN2BbTkxZhwTgb2mYq85NRvXxXgXP6gmdjJJ0sCMgxVfqsGM58wasmzW4rqBLWGrwKdgEGxDdnDvS47Qu3irSyYbO"
    "63OJmQ5Y47cERhiLSuGzcyLHq6m71upwFMB0bYo9t4u9lt7O7AznlL8Pjh6Vh2F5O8EJpsriOAqYvHG1Qyx3MEBIZidStUul2TTm"
    "AjHthivMEwUSkfRRuF73xk00p5rhD9gsLNYZS23w8zlvOxMRCVs+nodjxtVJKbecsW9ioxbRKgGnlaYbu2G81DEx6pNHz31qG3ed"
    "AjcC48owSJALzVKgaFldB/FKaRtSbq422fyApa/GRS0Wu4oyyYtdtqczKq3FadqSIEywKHasZR7rMx9PNn6pGgGzVVeBpx+jaMsQ"
    "N7OvQXC47JT9gdjyKobr3Pmw6ziKPpPn04q0cDxmy4bdzEPSxaKFnL23jl3rtt+78jxmd7tKQezsjkPgmn3Q28dqTdZN2mAbgQlE"
    "Al+XN+iKRN2+0bRR8ODzoTDj3uD8raE1FwiiDdBbpRCLinW3cs6pq6XiCaIYQY/R64C0KJqNI+/dEkgy3EKmUgaWg3WJBEGPYhfW"
    "TTEhTDFcS6sdnqKpmE2QvAfcuqspKqSEI07vd/z24CsFco4NKUkuzNGAyqTaOeKpbThJ2kCJ5qylgkQRfVYPGE1neRSe9CSiCMS/"
    "iH2mm+oqZZpTWCxmfUygVrrp8zgJMJSSDKI5c+as73LLOddh4u8L0WhHs4F4+bivaHy7yk4rpV8NqwS/EOMqaWoltsVAGxnOdvWy"
    "0tt49M9KmsUiZWyhXXs2DNMyx52wm6bG1A+XfqrFXWAy9tkIQkAvNuImdAQlk6AjlOi+4JDkMULBHbESrVknK5fMB0boEA5QVXja"
    "pR4CITiLrK/Rx+Ol2G8sFm7TukylmGXw0D9wo95vKc8W4423j7Neix2x0gJjdGDQa9upPBy6LlBh71IpTiSZORowO5O1Dc1k5Cyk"
    "vMSpMAvvYRtQtptdZwFC0MjriKf0Yk97BphPA4Zdj0MTu/0OQYvtSVcZdYf2BFZcSUWyJDRxrTZwlRNNZRDlmTyadDALjIZqolco"
    "gIMuoeHoQt/4Ts+sVDQOmhsFRuAG26COHTAyhd15t5dqqIBnuQbo06j0KbBDfGQNQzavnLNgaodZ/ENGQGoR5kOa7O65KxEpLHO5"
    "Em3J4Gv4htQOPfIFsFXc9VggIlZIzSgdvWy0pE6mRDAN5AKaeIdbecI6z7xBJprtKPLVNQcos9wpTiajqDGvZQPQZWM6TRQS1uc1"
    "fRA2zsWKLwjD7tEWmdTCDMhYOm5vzRoNbPF28FurlokY6sqBCfjBoWApIiJ9mEXTHlnHw3UVqN7e1FG6n5X6OjTKWtT3u2OoncXr"
    "sJMYUJJutoS7vbFX4BvUwaDiILiv2iMD+C0jDfIwlPEAZvsGPEKgHRYVvRec4GB10KT76Znng9M1bM5nYpDWmuaKwGEDnLfdMa8J"
    "LHS2UO12Ou8npbHuByS149WxwOMg1jDsfN2CcAQCJSzu1scREIjcZkzbikOfcgXL1Y3bgE+4cL2MIwDU8pbR4sinr0x1CWjU6LW+"
    "0EA92vAlcR2TcXvwyNiD9zLZKSvhyB9XR3pk6YK6qZcuF8i5H5R31ivQpfTNpGexU9YI2gnhegtsnZsrHtL0nJ8BLxDWUUTBQVoc"
    "dmiXDZRN5leg3JeSei2vW4NnNFTYVy1Ugl7Yt9dGdtDdRqMI0N3enJtalp7otvCpDC+KHvPO5hL6ekzCo7ErJSAqpJBSjllxvvYT"
    "R7mOoAEXCuOjrE28DLtBlhpMerLVb9C+9OCd6oGHS6MkBz3gKcXDnRxZy61PHgB9U0jKmKm2k7lc20fzAna7S5XkO8FiLxIVUDZC"
    "42V0MoFzYh9wY7wM0xZhqaxucQ5CeOSQcXRDswzLOGybtCfQOa6ddUYqQZ4jrp76FKIJ0xpQpXxnZwIn6SIzRgUW1Ac1NhDNHjgJ"
    "gSWJVpC4pyB6Eu1ZwF5cwIf3xdWYuQTJgE42ktMls8mzEUnsbZx44qyYmzW238JVVVYxVe32gc7dqIpVen0mRgPvD2U+45u4cWvK"
    "wVaMna7z+LLX8LZCRK8DTwXHSG1tCR1lqEdrkJzG6jKLGdVZu5FFX7AGn5piTggz6G7w+BQygxhS6EaPNXsnruhYToELUB2ckulc"
    "SKHbI6PQGoerK3KrjLeE85G2Eky60zIv9D3Syk6Ynq4LwBntC99eLzRwMGr6IsqOnCEyGI8Zs3OUPS2chIacJBArOjVl83J05xlt"
    "yqE9Wj2/DqqdYkLN7YSRZpWo65sxsEqlhQnPQzCJculOMmrXVNb2CJMrb+c3M9ebMwxWUWoGbAKqstbIMKZLJwldNSpT1FGGeRm3"
    "NevCqdmjeYlU21Mzca3049Uw5CzArHO9OtTXYzzbWG2z44UYF40t2vsiGZ+HjSTtY0KxiAutU+faXN2842GfWki0P3j5yaAhJRo2"
    "JUIj3jrgRrpVx7Syed5WNNt0JLzEjvtjuN25tgADxfGURkY16DdqSlYrS2Ujn9OGi2m1OWFcLIrpw6ShLpy57gtlx7JSm2/64mQr"
    "zGRv94F683t8vTqJFsGIFOCEIh0pQrtzA9xUqDoZSotWLYviIWao1nsIvcVUwcCAtBJX0WgPKQquuLGOM6YJ/GHLnSJAOhgSdbxx"
    "VBCKPMGsRES4gG0vjKTE91de7IYA8q5hhk7Jvr9oLZeg+ThpAVp1WggKDJYPp4kxOUmpKSNn1jQ9dtnZZBCwDU8SA9OSKfINebAz"
    "NJBWBR0eTsr5QEmKL7q0OyLloQ5V72ZQjU47Mu70wCSXBbkfCdDBeADfRcl6lzRwzHWh2OSu7s9jgZK4vzTsbbYA8zAundWMdTxn"
    "gGxzVvI2N3A4YYeClAYUvR8CWQzVPg8oE2UDsWWRoqq3Oxpv6skKR4iZ6YSleZT7qEv1GFfotru1Gfc6MHuRQNkZkKgH9zqbZZNt"
    "TirmqdcZAYQ+cN7lhiXQBxUbW56cl2NYMbmo2MJENM1u5WddFoBiRSB67YpupEtBPcTdPCbP19loT9eUjNiAp1n1IS7tgJ6Nc1qu"
    "S+swLw4lvoDSoouU1c1KGjkIqWwwhFvFUfKFbA7FGKYG1c3ChJXOEbWbQDlMVXaoRId1CxTD9q2/P4nH07wOTvLOBqIQOGdeTYiW"
    "PAs5P0rMzUq8Ivh6AFCCXw0ZQ1F8MNA2zTvyys0gUimVKJYCHUUCB2+1VSv615UjWy6bOBTUzoxk6UVbb3vKK8gjjQPIZM84mkd2"
    "A+cmJyMxmpkbqoo6BSptbG2+AEV/VbS6rrO39d6k060DTIcQyMb9AB4gl8hLfgtesiAVaji/uetjq5PKgCmeWlNmzEDKykCQabj0"
    "CGbJtrDr5e1sxQR15KoQ3zR+Ok0zMqGuuNzlGnZdEWkBntM1kLYzzsp1hSl264tcMCc5URpKdIB1f/PVSTOByr8hMjAb+hN/OdXk"
    "YSvwpzY14jq5XmO8C8xi58yUCA8Nx7EhTO83HKE1Z2e/gzqMSC/Hq5ehZ910tpEVN2RzOTu4ceGK6SYLjDzPmUNQlLi4PAwL4cdc"
    "UkC1mW4r7GqmvM0Gt6N6Wx8cHkPhSAwQwOePG2sLwPwJP3pu3NLliYlQbldBs3aizI4vaLAnQT4F1ZMZyzHRKgje4UgMh+ZqhupF"
    "fFJTfx+dpI2UUFue2NK2PAArahNQQ8yuhbCKy1m30+t+7GZCwqzZT8kArdpLFbPDzJW4E5x9xKP6HX3oef9KS+gN5m7dSMzGXkw0"
    "fHFSz55bI2SWb1S5zFUeHAWUi6b6cFtBW3AtaBzF0xYf55FRcMag7XMZkgqKDWZLhT1FcZNtSHYQ+4pilc0AnUnXgmr0eL1VBUko"
    "rZaJNk7Tg3pGt1JCImSB49Opi3bsmtUvHQJrlIdv7W7XB6Ezm8wXEwKR8XAdamCo8lFFKt86AmyTSNSl5sR8sOlQMJRA7KaDRRl1"
    "aG23EEj3LOD4q2ETbvWVwKcxyoBlEcg1eAguAnA76D5J0xBeJJVophurKdyBE/3jLLRhan2szruWhdOMBfcXTN136hjrIEOjJHMo"
    "By1oI5hWtzRotg5lNG3PVHsl2Lhodz5UMTe2ALNnoo15CvHGjSYRYbYCpWl+tWKRDOvpEIHoAlIoWAdBwraVNgGpml25e5RwK8m/"
    "5S4MalYDco0w26BDvPb50jW313BriTvkwh10NxFmQLaLaQcc7JgwYHG73Zfh5tgofTmjOGETldcbMjaHRFUOVE7b2KU03dPelLTr"
    "fj/QA3FGnSOSrtjK2FK2WYkK63ebi6AftY5QqBgTA1uavCOmY+fJDllfoojWcZRbawTF7TZSa0XCbmbNMkYAdQcyIkiaAGYBszvl"
    "41Ei8hpig52XXjOhRc4au2lLgqpUPOIYiA5HZ8cDUh4SW2UvHuSVEIYTuTHh2QTQbd9PW1GYUffqeAlyedOLTkHlAZZSAiXNtMtI"
    "Ug1FE2IHiinNlY6spWt+8DWUjNRhb9ExQG3LmaxXJ167Cs2XekzVmV/myEYYOft4VPsaJ4MCOxTyymIpREHKLitDWT9rl76/HjID"
    "rtnsjNlYZzp93Eo5hBS3TJTEFawitGXr2QreBZoLYHTTaYfQx9AVYByobVWh7aamSK4JtlzIDdSFCnihE3hly8Ea4R9dmN3wq73c"
    "AtLmBAA0YRuBDaNuiIgDfz0bJ2dnTpAA7ZGYgnMkOJv4BHIuSRwOI7heCWoZHlZCT9hgbIJk5+6TmGLXJjTCOV03usVFV9ybVY24"
    "g/NrHgNb7+ad+AnDDwN7Q5ONnSe94OdyAHFnEE4LkXLYZmKadURBXRUwnhx0IaXuHEJXNsTe1GodEse5qZqlGfU86Tdsi/KIQ2GX"
    "VRDgnRuPl9m2a3eOXwQw0kx7mPRMHbSPto4PDCcZKUOJ7uVKez58Hmf+6IgOt0W77Abg4mxhst3v01IvuJ4+w9OG8kvqtCLjPEW1"
    "nSMYFhESwUj0Dal4vTNRFEOT6Gg443A4SLa+2884Y/DHRgqyrThQscsT2CWDJJIblH5Q7f053rFXLwY784JgOmDS8VkaBzFfAyKh"
    "bor1euvfIlJsTuCFYOxow7oVHXsVMUMUlhyp2hvZBgt87AC7PjxraproDRxY8wyHB/11gNx58siRC/bABjiJdn3aNUKQBhVb0gzL"
    "Of5J0qxdtztNI4aALsqnDNJQKXMZTKzlFAYkydOuzFRLkyCeElRccIUznVV9KO68PsaOZQBD+OmWxcY6JalztlZ2pLLRJXKUWa2j"
    "HHVbZkSOrDZnseuVGHai3W1DXjkfOsKNpkB0liHsGuMsCtUAHmlk9VYHLYJ14fG6w5gD0oswi5JHlQEBiaE4V+H2Z0hJKDqiV0Qb"
    "hpyflXHCB2IEJl4AXmZ7e2sFyaz2nGy2yUipqpN1bs2s5bcjDmLU1IIpet2JEgwSckHp10hyRJXvs2tSaXm699djccos2xchMPFn"
    "GYTbV3XYzoIXycfRuclQiF66bLNVEiMGpCCht3qvqD5KC+Xoj5S3b2ZpYFsIzdUBFfhiCNaFRc8seTsgs+zvoglyE2m7QfOUxI/9"
    "3scqVr7ugJNxhtGz44XjuWjoDcMD2gXFt61j1ZKz35tViXq2oHqkJFFmf9pDEZJtImpQ+IadVlZAa1sg5BVWQi33qAGDfdoMAmnS"
    "lEPY1BoCHMxW+5ilp2nYztjo7OXJ+RQLFVAdV3Al2dbyKk3L0NiuA1OlCm49TDnIEYdvXBRlk5dKLQLnAFbPtqu2zpOOOg7ERio6"
    "kUQnDNhtG/gYcg3Fz2BlyIfNoKOueZD1Lj+nsmYmhcloWn45GYQl3cgDppYZf96bxJ4dL+eGCg/UpON8wBA1ZtMGrkhiDUzCCgLk"
    "4DTu99nWuJ72DlSWGJQpt5hHCFhy8MqSGUM26su+UmGoUEgRlnTm5p8tCKD1EywZt9O0gqg94QmQt58tV2ItRSxtXuT6xu4DDTct"
    "9lpYvUO4gdeeKJeOWG6WNiwRzjq8gKSMosOj2a05So9NJx39FW3rWDPZqJ4HG6XijG6G9yvYy8Aq8cyGbCE543GsCkWIjD2KEQEJ"
    "muH5ircocy0ENNoCvcPZnIWAR8ht/eNK7fg9gaghxBEZO6mjm864NAN0nChhFoAKYNw2gmaCTAeak4vwWEXJIwQhh43KXi4dMKLo"
    "/oyhtUqQO1XywETVzlGJbhTBo/FgCwfcse4aiBoYwCDH8ihujYijEEHgKpArVEEzrhNUVKeLEa2breLmzG5CZHg/y5MBbjELKsAi"
    "O5Zn0lIFghMo4qKaEHKbLG6CfA5C1JtHMIWV3uBz2M6woAR1C8Id+yAl7KYLdhCAr2MLOB2zlWL3Ucv2CCoe0FNgzs8oxUR0YsjB"
    "UIET0eiB3+8mvotOAzDWUo2z+6khtpELa86ehKwdKO+SE6qr4Wwa1j2OobyXjmt/g/F8tuMo7gIUuz03AxYTEAYSNHdtwLgZIPeO"
    "I5/yFTqkCuSEEQbW+0Omol3bVuqo25EzDIHBMpJ+ux7ImBqDS55cHY/V8hE5i1k9uB3IOFu6tnsvuXlMaoE1AtqYzIZHp1LYsjiw"
    "HutJtUSoYiNOzRo6yzrT0lfNo5SVeEsCyAecFDH6zU1vdAXdooMu31Yrf++Pa3zyCJUMj+quPB8ADSK3oN1JJVsqU57foMtu1eoq"
    "rlBsuIhBJRxYJEJKOhxOFOXiBX0FwUuCVOYkI4lkSFgDTaPFdCd2lqzwEQihfR2XcdEAoJqJO1q6BtJ+RscnZhvoZueFNg0BfrzG"
    "vByChrzU045Nuxm/gZim5OXNHnOC1QVUVERRCkAVRU7b/Tk8II0VhBPanQRU2J6a6xTidQMMO/2yXlNFG2jaBjIviRkUo8cIdFlR"
    "eypsmIAplbppVEaGAWc6c1Kes/RpvwPG1E1rlastWmiIPlyzktQnNDLrQXG0jGlQqIaWOsp38bEx6S15praZhMpkh+YCofswiGdx"
    "zp/nhbVe8QmuWZ6Swr2GBFdV7HMIzSERc0K0ITfK6J7MUIcwnSBt+0YQcB/hZgAAJ4lPE3GjWsWxULhAstvKQEJqY7AuTyKudioz"
    "pRWDw4aRcuVaHD3gUjq1ATeswElsjVLaYYf1nO9wDAPTiSQh6ZRB12Q0AoNU1APOMeqAhpFnSsVwdG8aODg3f+5oclkTF+e1yilc"
    "nGiYqGBHPdmL2yszOaQ2oPNqcGcUwQs8Qer7/OxJ86AGWrJWjctYSMjb1EkIZrm/8torr1ob6JK7kGDCAyVJLdSpoTZPSzt42kUn"
    "LhToi1Hs9qXI7cCYhUTOI1jyilacCBFkOHK6vqW3gC+owIxw4iunT+bexK+6eQVEn9oJpjhbS0BG5scIQjp7sa/y2UrkEEbiFNEc"
    "E2sjbowEkNngEgqNTycKIcGX+rxBdux5qBSS22JTNYodUCXWoLDRmmq3nGlYkKkpFIqEI56LFb2eFaeQd4lkFUQOK8Y4rWlhktRt"
    "RJRqXfbXoEw3gALUHtvWx6PNXE6zdcXjVEZDvtaF0VCyG4ql6IS73URiL6lN22pSrjuxaahEv9YdXjWqFtxKTgXC7gaQMlFL9IlS"
    "1gzFiiAHUPYEuCSiX5oDZ9gaAeiBN8MBysp68Oat67JNknYPQTBNODypBaLphWSnkyIzMZh4A28cQy/L1tuuDHfHGkknrRnXoJ3g"
    "SKo7QowYvVodUzpOfNo9cao4P04Gc5cQYUBE5HFtb/RBngeoCmOMB2/Osx4Fm0O/l1l4WB9ButhJNWile96uJJOUDLIHlDQjyPPM"
    "k/SOUoIbcgozjmaVK3dbr/bJyOrIpvQr6ZgLq91lc6zGrpRmo06Rh5iSauc8AkkUzArxzPkBzpx0LcL47a3zxrjoBWy/E7MevWRY"
    "MzLEbH2iuNrDRbumAprlEWMXcJQg2fzAreNgnnrzel3xN3JWQ7LuHm+9eQAYnz9HFy8qVS+QRwFsXCNx6tpdYkqmGe60QyYdvG6/"
    "O1NTx2mgAN620x60eyAhxlwCs5lNCdaQJPaA0DmVjdSMd7hAHpA8IfLM8VCwjsIYFOyjwSr+iBt6P138vamH+oYpPcog9FUjyZNx"
    "he3iNBZAePUyu0BnQ5FAtjNtNiAKzHpEu66VSynxnCZPjMEpQL6WaJcWAllAeI8VByu65ufzNUVShG59wowP3BpThP1gXWI0LYcV"
    "V5+D0Iy6c4YepM0UmMdiNdrHZLv3AaDZyGNVNOepVWgSoXxCRbhpe0SPTCGyxGwbrK61Pq91Q0gN+kYBq9nKUDZnRDjJMDVJptVS"
    "suIE03o3rbeIHJ3VEI9Nc32YDSWfodyCHeo9ot/OVa/yD31cq7wmGfwIkKcVTBysDtwNTGgMYYDoEwNRHcXamwxqD/IoU0dLpFeb"
    "MEdQgLrU4rnLqUu4NXwguhxZi72QBN93bMiyq1smVRhHed6JkHLmdkM0wFu7+QG25VwmvaPLr3qIBwDPT1IMqQa/oEQN6MALrU5K"
    "FUrB3gBJjjENJOgxSKAzLe6OFb1D7BTajGGdOsHVp27aeLlNwu6I8VnDr8JUDUM5PIWAtr/SFHVhotvVpYNspY/ZNuZvN25Yu2Ed"
    "205re6oqOwGKrcT1KeAECZq29cFfoQBvVTpGJk2o0JKywWreY/pTvJrOlrNvTxt91802nuqqG2vPdT3rHqwEakuiHw4hIqWshLR0"
    "ANQ7Ky5tBKJrypPD84wzTy6pyJoC2oRxLisFhSF+kK5kFciqfKP91JFAx1Va6QQQRaleUUpHMdsM8zFT0DastRWb11MySjsYTiQb"
    "WOWK2l1l8IirIsFO8eGKYrwo0PzxWBuMGtbG/kDCp/NOZnD0HIwWusWJmp/mZXq95WDlgnF+Y8HG3mlo2nD1GigOhcKrmQGKhz3v"
    "3cZDzvmqtNlTmZSrbTjmbT4q/akve2xjrcvGRYm8ydTr+YriG5Ave8qDOy0mjtsyuurqHpFni/EgEsw6b/ztae2gHOmztjKww6U8"
    "4bchCqg2CC68vKa0uC2KdS9uWj4RSTA/j9ph1ogIWSuRUimzNvOabsv1eS2iu14bcKsYnVV4QB2m92PWnI5yEqCbKEBaJMDLknKR"
    "uCcjHtvKBrxO2ALIGJyJK9T1XT1oA3+FXP0LQx5qU5k13LaIugvnMicaaIubwXdAm6N1W+uApxhexljxcevDEEfxDEJTdMAzDdMV"
    "ux65nQcFKzsNrAjz3IssbxQkceJCeD+1AnBMVHGlu1AggfJhe2oV8Jjt4v6UZnIVclkRnuph22hsb2sutwnAScXDlWrAdekcGCHu"
    "A5H31zxM5D7ApqZdbXVyddrrJ2Ui/Cwb4vR6rg6zZFu1jl7yN9fHQ4plqNXWYSgxuRyYsQQUYs+ESHHC6UnGOomzc2itns7nLZbf"
    "tmEXtps1p3MRBcd6Fgi+xI5wyAnrdJaQV8s+U4OjWM5AkN50luelcKp2Zj+uRRK4kFNaIDMiG40WbjqMPSeM13iW6gk+OxYpx9dm"
    "Md3A7LAHrKzjidZLxSAd7RNFnHZCFq8ooqU2VYXtA10aSo+TxIKJKOZKzerV3uFn7LpvN66UcIf+pIsAovPnmNAogqs1DDBclcMN"
    "8phs6vMMIDGkLohNdRXagixOt4G8QR1Jy1DilCChotV60LqgzhHjwAS6H/qyK0H0NjnTdYGn+RK3wKkK6GqM2W8uNxsBeMLPjSMV"
    "BL211RGLrmcgi0bRauVFuj4M04Y6EmxMXb3AFUZty0O3TZIT0GFzCurOJeHrAXJ5IiF1dIZJvTfKKTRNJh1jbkvsowPtDFtC0rnO"
    "4kIjTFgqCKkgCs+4bOElvmfNnLPwggJVcOrrer2lT9Hk7GnAmy2QdSBaompaWVaqIu0N5my+XriAVHX65nIMolARsjlTuIFipRcX"
    "2xDZR5tkZqTQLzEqvKGnlVKvb835piFUyvlbQM/gdZ81RAjqFNRwQn/aFWp28jGv1FSwAklaYanGQkyJUQvajy6tf4sn+OrB0hrb"
    "YKJ15WS5WsMQUHrpeWtuCdaXpdnsn5Ceijvf0GuKKjK1SOM91FzHsxl0bbPmmAJe0UCKRAbXUYMg28pN5s+Z3lK0a2qBsqtd3QXb"
    "mjw69Z5zTW8lzird0D0IxYdZP9j2zHZQT6PdPrNdtg25s9LhBjxJ3I4yoX3HxiFFMxO3FY2NCoH6wM7LVe1o5ELmvniN5Z1zxQVc"
    "LIC1eLt1GoEmRX8w7aILejfeDshxSuFi46wmPqAsVoyRKNrMtrtN2foOI5owTuJDFlcJHygcd7K0YSCmlMSLDbIW4Yvl9cLJFCks"
    "yOL16Cjetasy2M5ZXNuNJS7PAjsfenUihEp3BcS90rjBrDU2lYydFGiuageQvDfX7m6jiaMgRjt6F8IeW2IVBA46LzpNJJ2tfDxp"
    "JNTnFEHDDuZ0hWas5WbTgxJHpqQpY4J+rvDyMmp5cWPZwN4aFEzw4LpiGEpqqf1MZTNyLFZOOMPJTU2s50W3scaDEJ4wNDPIi5/R"
    "ok1Iqi5Ek+WJDajy8cHzNI1pCpSzajLFXO605jfCjbsQIHgoz/FphK0tYnMxK/E8Gg0EKiIstJ0JGcbhMRFK+7jHdHxcbzerkJmO"
    "BV8DBMcoI6ypa9WncTLazqr8jHg3Sr3l28qP0esIyXpYs3I+rsODmK5dMEy06OArW7yKihZfdeYetNyD6BG0dNG2I83Qoz0rRJYT"
    "B6AW3VmUNZ65X+3JY0iPmnoSZuGKKpIsoFDVZpS1hw+YthpbuM3PveCLFdw2o9Kh2JkdOIiuch3XfLeb4JBBe4E24TZ2rDyFtz55"
    "PRSeSNssNag5YZqiN4B9JSaCNJjQASsP3t6/sZMOTQVxRONe64OwvTVtoPRQClWNqWza/VpZn6ruRDVB229EztjfYFHDhsG/rlmx"
    "gyJpldJMkF3cFukxXBTzaxcRsFZPVuJGbNyIrmzMRrBsz/NF0uO01Y1ZMx/XklExXoXH632sIhpPr9SQiDsJPPYnBiPG4EIzjKYN"
    "15K5Vo4BkUmEEXSXK6TXY+VtaCr0kiC4YCC5F5dH+nbTSTQOZlPeIwiExNBbC2quBwsashVzH7+JdDCjfsJZ4bcxKa0IAITzuYfa"
    "cb1hccVXbyh6Omj8GZqfgepObHbybhydMXqKF2bT0Npl0zAlVgjIDmJODaIONHKPA5aIjoPEyOGOiqfrAxhcNSEpxrPVymDfzOJg"
    "O2gUlnQBqZu3EhaHfTpkjYUSt7gg5T3vTEmnWBcKDqzzBmar02UzMhAK+nh90MOdeDrfslCj0zhCN/BwuxbX1RZAMd1A+FO0I91U"
    "v9qHS9oKJzLfJtuTNMzK9AbvSF2Ft151E2WX2Q68ctrs/FnxTfmEVW7P7izE6MyCTC7WiollvCcTi5xhezXzKaXAqYkHbn4jSwDe"
    "JmIwcs6AaGAu4Ji/Xl1TEWL3LQRxi51o8KtN343KaNkXBDTOXnSsKh0R1BW10vFYE097k2KVVPFvcDwCq77e7pjeUD1mlcx4ZUDn"
    "LjT0pkEYSTAzw7vNFsrq6uJ4WkoGkY1w3SDRim+tonyL+0DjTdNsfIcHglZUxUJb8nASetJaZyq1nuV01JyjY13lGYsAjp32PqBB"
    "kw3JA50BpUzoI1G3LZrhLOvzRWEwW94UwtqGfdYaiyPpF+k+x42CEi4Ykmp4HJ4uI3TkoG1q5A546X1xnDV21PK5JtvUVjExqb11"
    "azHCILbApELUqVsM9CXAS/kBwb2zp/stsHeHirJNLtHo0RdZNBav7djHgzOYPnF2Z1s9zNcroVq5BJj6it1Tl8gmbd/t0aFsyZVj"
    "CblozfDYbIiD6B9lCAdIsPfPPcGUpxnTUfsZcnk4aGlr7Ygg1trbohosmesSQBwKXuGYUytABPUgXhHeBErNDJFDm1LWqmmfqgPc"
    "201aoP0t6m6RSboRPav3WSHs8cpL4divndsenI37KFdgwF6Vs8nn7vkUslOGOPXXg3lZxZu64kO5xqbNSGsaCzpUrc7zNssop9bK"
    "nkR26y0QkvxVbotkoOc+zvQZ70/SrgFrJ7yxTFU1ReefisTQ6U00S/VZTYqnziYr9brF+boHSmO99cpLeCgbaYbsRDdbNpPLCbGH"
    "ZLuzkK/SOmn2h2xzwaZbJAIhdlvPyulwK3hPXnEE0FsHj4HSMQlXzFFwdLtK1tZ0xE8g6CWixl2G1KHMKyWtz50XQxtJ9ZQVMpvI"
    "pJBEZ5ZhYUWtE9EHYCfeCuzkVGteHJsrjcJXS1KF3u/FxkBiMK0xksf2JueeJqOeUodXZa9R8zw/zrLy0ugXo3CcCHYoa6g3ZqEo"
    "XjkjRM/acruT4dxObHQ2OTAHcoyYvH5VBORVDnjXpEPIsyojTDVJZY3TBB0r/dhU61QoW1YvqCLwZitYyFZr88jvIY89XWbp6BP0"
    "Opuw9WbSDofDfcvM7nDUTBllbEn69v2NGl55L4Ty/9eWnLh9sSXnGhz5kzUSwOXM2KRkJGl4nh+KlrAZefK0cXTXUGnC/NFc8fC2"
    "azZyuxusqsJXDdJ3KO7vDgZ3lGdkstuIHrODuEOS+btzdr4pN1iHfe8m7HaSmyrn2arw2xs+5WkP1zCc6wA+/4HD2SyI3f0l3PdY"
    "OAYMENhluuXopN9gGbUL9Ry/HjebvlBL+5TyiTyjgA0V7iq1qjc0ceS7nl/ZxW5KjmtznndJqNgTT0KbQutGOcKD5EhnEgDKyT7E"
    "seZ2PBuWgO9y25QPmW/iu+KGXbdHfe0JZW3bfijnNHEJKLiBz96pueQYewFpCzjZKnkU4bmx9TBWwRaZ2ORYmru64dyYnRoXZgFh"
    "zZjmTrrVpzUjbUcKZSj5WEWykd8Ila5YPGfQxtu6x4O+KWsAFv0ivvaKfQldKidzc6zZPMjXhwDmhCsxG51glzsyucsqzNgVKwzX"
    "hFQNpOOuqwonsTZ+BhVmmDpxiCR7SzdwYnXgt3A8mwvM1tjYtZqcVkchP9H7CLmB6yJ2+ptFpCkQTFSH8/5pR0kCImGJeQUZua8C"
    "OBXIzQEok1sQXFP7qJHVxqX4yuxx0r1V+ilfn0oVJCHJS2r0eIxIb1Ny4G0W7VuateyhItXdJmlv4rmZkSC1u+3mGaBYPEZAE9iB"
    "SrXLwFl7BIe6BdJGLEuHkcZrHZA12+s+ngUrFg92BRi0FAVMLUJKhCmSbiUHkQ4AV5xShySSpD0+9N2hGtaYf8PPlyaMMq1SDsPG"
    "TvPrMJHCdNtw+Gq2hNDKKpX9kMR5IZo6QciXLSjLNyvaFxubw9dpfiH9Y99bZx4sWVUgLzTiOHVQF2IXAdHeq6mIBGsUP5zTYWXE"
    "rVFRAUnqK+8iEe3I4nuZHCzCMjmFI3G/S+GVdMWP+mUnF0eD3hID5p7QGQYoyAXUbD5a0+5ZJrYsZGiR4leqk5oUD2a4up5XFJtc"
    "rnigQqRNi55AkjG0U3u6wMUqERoZkdfK5aiPpIa1/bncWrq+O9GJC0uZLyfYhc/1/XoVtWFhuvEpc7beiolAqCv6Rh/k6nQOkI5a"
    "n/jiWnTbwTyJA4HwCi1m+xY88e1gZ1NYGGN9KgscPxuhytiN42p76KD2IzaDHsMYNkCPn1mAxHFOpZ07fVOFdQhtnR35C5yZ5GoU"
    "5daqgjwIkNG/wuPJFce5Ic51VqjDVBwA5qbu6XK/J1xFQNCjDNtMttHItlxHMHutXYA712JaOvZYpUczIipAykmwu3StPXAIxUwg"
    "CKqod/VqH8qP/EIHqAiP4VUMEgXvb0AxEGnWMN3ANVo8pUlbEwUKjbJ84ptqXrpoqdw6BStMPjgeKGUCWmyVesUeAGbFe+y3pjvT"
    "cL3JSf/sy9E+966DXKqUDKSX01ifSRGtruipZ6CLnx8IlbkB+NnF4hITVoeC2c1zeV7BQOPyNqlumW7XRSsSO2kFAIhFs6YOA95D"
    "zq0AQoajHbIVGSEkrGNPH8BtGG3PAUfkl03mSdl40fsxSabGs/JyQ135A0pFtmKIkaeuGUpUtJpckyGvAv1UewFszWOH1lHEVgdy"
    "wDcTT5zcnqNke4Yllz2MtF3PcLdsT2WlZ8VJPRUWH7pnosP7WuyJWf5quHQbjrmX6eYEExuJ0PZxhHdeQviSzYB5inndgSRlo9re"
    "DHffBCczSpxAvv5/tJ23csPIFkQ/CAG8C+G9BwiTEd5bwn79Qi97VZuuElVJojiYubf7NMEZ+qzrfMXcWIndPGjoq395HMXu0aNU"
    "xtR9t61TXrqe/XT+9v3dX0vZWpF9lQxOubMyw9CrEH1acMz2cq2d8awTi58530CAZ3rm8jKL4OfZ40xSeCmlC503ZKd+q+3DGsOv"
    "sZUTi31ud3Hls13ih+jkB9+mzJF+2seZ88QYRnBdnv266XTaIl82fOdCDP0x+K0QVM1S1Zd4ZotkA9d/QZIG7JXooPCYlx43Vdp7"
    "4eOorVIoA7FzBo5vKQBjrsjGI4aySvUCJXKBfb9cMJZiVXDxn4GrhMkKs9F9wQA+Kwef9dlwZVQk7fxSem4JkGOQUS6gy2FNcN3o"
    "kc9bCInPoorHTPR4nfubFcHAJqDK/pE0y5qYa/WGGHmjPlOgl/ciUruzVdO5eG0pUfFLJXTVENRVdaotkAvHSta1CrwZK/edT7it"
    "nvgT5Z5M/CkVM7IWMIrwZ8GKU4cZgS7K9RYnMeCHPok/2mIfBid9CrGSt/GmJ/xC+UpZg6TvcWsFHtUYujKnXlfjfJS+psrGejvq"
    "o3J1G4cs7bAEpjcoy9EMRxwhdKecgtfC0Sq9qVNIv6LD+A0jj+XNOoWVEFXaQDxHprmcAioD4FtaKog+Q3+XBAn3FZvdNh8Noaxc"
    "Vibvgu/phnf1bPqJ2zgxTOAp1M+46s8PCAfIBgbyllqeILVUYG/OdVpi0qsc9uCpL0j0RHiP1xDVt5BXrmYfpjmpCEXaJvoIauQG"
    "03B9vq8tka8AbJvgt+5RMbIYSAMAXhHYM8ZSXSJq8pj8XjxrSCsFujQUhHYryLgDMGkAGHvFJOEJHbtAucTPcyF7s1f6+CABFrLz"
    "VthzjdVQQEZuuEGNcPjhVaABN6Jef0ZdKl1d0X2Ew7JorWgjBMPXrYubMpIqEtWeLh0wBtA9zVW32Dhv0Wyq8zmCa78DMpDsAHp1"
    "9dFEJ1YcRiDNhsHZpJCBuTHcVp/50r1QLN/oQvz9PtJss+iSXQF/8aWdEkrTXennDL7ulgqu5xAW8BkIEuS88pvrG0Hyxf5GrcGV"
    "FdQ+i8QB6wV4eIl6fPxkou5DAIWH5lrYNEYlHzGzPt33irgMAOiDYH82N+5m/RoelTlKoKuq8A0/OG2R4niPZci9Ucc3ka/nEWyQ"
    "0voPfjDLoEVqfljEorFQLM9t3L4MCWxKJQy/69KUkzHngo2JrAyhHgcZMziqZcsaitkfqypUQzVR47PbJFnndkYexcm4v4yVo6ZE"
    "egw9dAmIkc7IBnRBb/XbvM+9pomGoTRYoiW0fkTnvWzK4OpSQXvMLsXXs9sxTupMUXfxSAgmywDqOMZZ5JvPBplMyy8a0OrEhbfM"
    "kwYM7eo19fbt+nXEGc0dflLTMGNPE4svexHJJJFI9Dh+0JUrZ8U8u/OMKHugWQB2S4LKhVVgit0SzQHBv8FU7fFFex7eHS9mQ55L"
    "QvZ7DrV2bRyELsyuK5pPjD6hSFAqfYZ0kySudWD9x0ycpI8H+oFwZFfSzcTPTGXwOGZF0Uu+PX8Vh2YiIvbzy4bPkGpiPZ7kTqqN"
    "MeaeZLr0a5NQ2ZhN1XlxASaL0cz+cBVMj+gQ57uAV8EYtM8bcDn2BwYq2CFkARAgF4mwKplxyk6/FiqjByzDJ/ta04eoqWQTuxft"
    "eraZcT7eQTxBetUtkI5wBUrsGLroGzxabsaurVhYM06faqMSkVQ3mx+s8K+TVzqo/7C4mBGgWZzYWM6mus3WcdYkYnviU+80BYlF"
    "lVLqwWy9oSYgYK7p6uECziNe7ZX54JWJFs4lPnAksSYkJa61HYmQBjcS6+HXb/roW4GIrB1whSrKrtRBMrivXNLqVyGTEuHo1d1p"
    "Tn3c0P0i9GKkvDg5FZCDkF5gyOiZVwMn2X0w7DcbsFT2FuzLYJTRyBi2XM1Mx3JjBtRnFsXKPN8FD8dcR1RmbI2gozT+G0ExkLhI"
    "T8TQzkXMSBxKj4BfQlIjhIE4messe3NBbshrWq8+h3B+qjQlpifx8FKngIHvrm3+YPQuKlJkWNNo2/c1drBCx9qaaB1aS7vHYtFk"
    "7+MsL7YoQcKDiPhIcvvnM+HpiXvmzAb2unImQUMMax9E57sYjmmS4PBkfSGqQQyf9gJoeLC4wrhW5tkq2BkTJz2uxwYeg6QqwkqZ"
    "5sbKMHlwZTDGnOJhbJ3aBieY7b6FCzf3uZF+AinwmAXDdbGNJwboJhBkc0E/7SyrSsV0Pm2dzMYkKnsq14O6heOYvEUbZqzmsqeQ"
    "yVjuYTlRl6tSCeMVO7qjLE1x8FnCIoJWv6pyB45S2zu8OVY7GYodatr1RmqLBQ63kJgtHBmfaz3BpEZinJfqafJkEK4/ZX43H5AU"
    "78SsNq7oLWV/F+zHVt82GC9NCrqLUbXbwnwT5JysrB70mpSC54lCJWeDbgvH3VkkboydRVksNF+umM/KvXmEZR79lOx23Z59FnUc"
    "WM3tJ7JHLPVxWrRnisg+rGmona51MTGCyEjFBQHcdj2TNQNbgyFiF7OmYsoRKhJ+OJxFi2YGCfE0gcZdf6OxLszw52XbJkaOX3UC"
    "cpNaUgYjc7k3xAnA7O9wBJTDwjO+ihw2OY/1j0o8kybHcMox8ofcheSrKAfCfm27qnVxRDqcv8TV7rQGwoAHSSAurpOh/GKnyjGM"
    "hT6PfcF4R7Fr5j610pYk4qL7RDaxfo01LSXM5pFZh7sfIENjTK6gdJHqWdzQo+TQoy8j7reavNsKpr7EXvm3NUGWnwd54W/V9idg"
    "C9Z+dQFIq+cCJCFfBSVkWLablZBGdwaUrw+ivThq/u2VdY+fANgEigja1BaS7Zwkl3TcpX0wLnLFK0c7uyrDOmYVedAU25d4j2H4"
    "FvtyTZkLvyEn999px8/n9rBjFo4lFWcScFjTX6skgRVotROq17WEr7/dMNn2qyvrWbwXOF91DLIXAW5cF/UeC7gtx8rKEbBgKyGF"
    "r58fCYBcMrP9+xtE+c/20SAjU5Z+Npt5cSCZrQtzJzjn19HMI4PZKgk5CvjNSzxZAi1SmkrsVYMeJyTThjifaga9DfepIzJHaQpa"
    "WGTESuNNhiRCVPJ6Up/GMEA2A3FhPxEO2gr9tse1h+UpE+8f5XGFdVMFhDYqxxo0IkOHWuijiDtj51Dds9ADwuiM2/gaXJS+dqch"
    "xgsMQ1jy8nfLV2D0CaR+69xrPL9sRcUeCj8pTKH7VHkA8i0ALDnLv3bloN8r5YiUlZGwUjn2iRlLDR98rAz4tK0P7wtQ6U+ozMep"
    "d2E/tXhhp6j0nkolbGQNFuSRmgXPvLrIVAsZPIFDjEXQjySnMJi2Vq6niJZvOkMH/M0qAqDVKbNcWFAZ0GVCwQB9HQs026go42jU"
    "TDtY4wrQyYbkcxQsGS2Y0XrfeXOiBub8rF4oT91LB4wG2yhk3j4BsJBsgg2gL5w6ra/9PkO0cNzYLURfzp+CZj8m+ve/pQMaExzk"
    "lYo12WPBMvEUSBkpaQiG5UAlnbY1yAdYxUMTkLQFeHJg7G4VrYWVauL3yNDXLGvDnOMungqMrwTM+Fk5LFbbr8GP4J2O0nt1Im8r"
    "0OqwbayYw5WmBbWan6AmjERhdceebD7MFFMTbBzRK1EqB4/B4ohZYHzIH3y3wKMW5VqY+dmfPdIXklp+q0TcbKXhAIZUmkjLhI65"
    "1beT0VIhmGjA3v5d4avOMZJreu1bhF5CoOGsQApTpqlhJkFql/yImlW9a4FvO1xGZT3cUqbD5sRoVNgXCG3J+cwk/sIsZunJgzJ4"
    "Ximxgxu+S7FTTIei7TJMMfGEJSJB7Oso09RjPJWsyWuE+SQBkx7x27EZ4BWgGNGLf7ZFn65B5TChY2thD6EU74ZoQHVJVKIpZNs5"
    "JTHygnw37gkZsbHevHaaUR5/MOtBsxxKIvWe2qc7IfJNv3HMwL/EZ9TL5X+r0WOCtYwsseUZhkgM6iMzq9fc039yBLoBfKZglCEI"
    "5aiIl6T45Dw1RsGS+uUb5rp+9Y9hyTap0uX5BlBpk+BtW+Us5rnjRBcYugxoUOnPyLiC/diSBNk92mUzl7mzx7eyGqcSZYG8JQKM"
    "WzEvia1Vn1b+8fg/2/uZcIe9VYbs+JezWbf7uQ/0drroMCQWi5aD1AIBYKe1ZZ/DmmmyqNB3oHsOUgaAo6ty/iqr8s/MVBRJQjZ7"
    "oopThDhH33EcsJADq8Y32kbXGI2ZKfTA0WaftZedLsTsgZSoU63U195ooYkw38GmZjcYnZjFdPjV588nEuuxKUO1q0pr1e+YRx+x"
    "VwJVpV2ZVQIRskyEPfW4ucgqRD1cY+wElDBWQhvuI+XGKAoWfSoxAJ5i/oD02e5+pZefur/eUPLl0ZZ4hNf6VIeHnfhT5R7NMTz0"
    "xnK+wWlzr91Nq+F93z2qbwkzBlEGaXpnnRbIA+MVZWCwLX/tTJAAzHPX6fTIpiPkae9aXx6lc2k4v5moRB+e/+OjVpUR2fGydznU"
    "kYriJrbcpP0yk8i1WryK5lcB2Fh0DnOaA41QjMZXTwTcvizXE4xwpGh8ghzBkeoZVBYgi+McCIGUdeHY4yL4UsjdhggJfEeJoU32"
    "67DiKesydSXMZLbWyTk0moxo4co/hL7EuxsY5hIue3044eVZJ8f28rCDW5Woj4TrUxOk372x4iLEQsS6e0B9GB3TMnysc4ZaoUAh"
    "CP7QXkjUnYX0MwVT/Y3VvWKMmF/AYmU0Pz/PVgQDt7G1fOz6wa1XHF3D9K3hqxrF8IzJ7QPJpMG+ceKUP3liy+FsU/sRozt0j9Vk"
    "Kd5f3km7YtdcfsDY5CJzPcryitImdR/ZmHtOMWBXHd/EiceeC4K5mLFvIKq71YQI1Yy3Umboiq6SS8agRHFLQuo+rXRG8/bUbgcl"
    "5TZyOhY6J6H2E479cRUPPBRnJ19mU+HK4TG+a6mWKLGQHpRIzDvGfVmWETrQb9OPJe/oWXa/ahodhj3PanMc7QJVdncJbBZ2VLUh"
    "XdUL6kadNtAYKahv/lFeArJLtt5osXs42GJIT8SENKrXtgum6mYmf15KdzAjvyhhuapPxGDwF+fqt2oI+8hl26i6tIw+7N+73XOR"
    "/n7J+CwuIR12igurTsRw4tfrjE1LlenS5wvF6Pk5QyzwH0aL4R2ymgqwqp/0AqtqWP0e+zXChbB9NAYe9F9TXEp/3r/oxBT8OVQe"
    "g9l/uptlNUDnjGKZx/IbkZaQgcYTXVMeFRzoBDWkOdMjjHHdcAycWn7WWbFhzPosjrPSzWMGjOvHOhGCiQjjWoxWGmSZe29aQAOW"
    "l/OTkynYnrP9GwnzJAa7OuXB4X+H3iodKepwPGL4HGJMLKwY+4pR5u+sgpZPsVTdL+L8rRMSW4PA5RX9a+4gWUKHoItSJV/wbLNp"
    "85dew3Xx2vmOjrm/62h+Y9iCujIIripohocQcBNzvI1Ej0u28F2/l0BJn/Y1dqzRt/hrH0s/Nu+M9X/3OpFbBPvfBuzZz8xVtBf7"
    "avgkJt+cxHbWKgO6ZQlIDRzt3TRWJlWMsY5MJAGLbmh/GJUpn4pxhLN/HeA4UDiXzcCY3hXfjpuwUP5LhbbW9efZW3RKFMXqz3WD"
    "QdzhTkfVf78pFmCaQmSxpRlbz1mCwdINwp1QlImswj2eev8OFlwuTokrfePESuZPH2CClFLsVZlqdPvIpl1Tn4ophafgqc4SkJwS"
    "B70F1icrnhumkLfFMAQSqpbE+DyoEgQnU0NqNcNyyrTBbwAAmxyu71YOmwxVTs+hDWNrz4U5HhYvQzcCRnsUUp7Ve3OBesFNxwjI"
    "w7fVix42LZBg37zoXxxyaxxttZczRO8YiiDxBthydO3F7ZHe9V9fw9Qa26epHGLCV1c5whK6P5NdKeIUFRNrlW1clSWfrGLJZ2V7"
    "n2zQOFeblM2T/Q6cQii7VHzshw5iFLyxXbMzqtIgMPots7M0Q4lKAclzPPzrMuEsGAnks4sj5Y03ubfvyxb0wShjeX57JUmwa0n7"
    "CL5Hwhdd/5RcnEwpagiAQ56eqeed0srNWbMNaxm2bjOwWSacEbxW0SaWp+lNXk36Zpk3fkdMB489+joQy1paKMR1aqEy5R3Hy+Qs"
    "WlPFGrx6ZJqryQzN8e3Cp/hheox+BASVZ+7jExbyvJR/Ct6vHCcam25YItGY9arQGN9x89sfYzzVCT72lLlNXuF7xnnZZtlYLkVC"
    "aMmO0HQsy7Hxfbc9BiJKnIq3XLEdvtsNJah8LF+Wu2WvISjYaszxj365h+/ewH7GKZiU9iIGDCphKp2MARDEX2EWhOlllQ2gnsAh"
    "oxfo3zExjmOoxHMOb84PTh2MExeWmzBmn57dYdp6EwDQaem0ZW1lOjx/7XpRVqq9PfToh0k0nwBWNiUNaA+8siwuCGdzDsnaFgQX"
    "VRK/QjEbsLq21yzAt6FPr5MR0SB0swXT9rra94DvH4Q6a/iXcZ4Bl8SNhX6m4TM7YyRUPUKbeZmAeKWM/uFGYA/6H06lFdH7GPm7"
    "guO78lK7s9tba2PWM5L1QsI7vuI0ISOU0pmJWCRrEWfVmGIUB8MO1Ib4UmqMcBvLpykZUSa9h8VUAm+CtoI4RQGF7FIl5rE8N93o"
    "pLRTqgKYNgtQ8DYCgc5wZ/Jvp+5GGIv1oBIA4KMfpZY3SqlTwfEoScJkNv6iK5YvpsLv6sZOVclgyrgGfndGDG3sLOa9NO4X9MWO"
    "jv3dglHaR8bUmaxpZMiXvZ92gp8y9g6ZASuN+V402hpczFfnzhI3w1dYc2agd5ARoKD5sLE+w9zK+tNSFcWq6dTlGMvP38TciC1n"
    "HHoC1AIGPwSKJBO1seTWC7F9aRM1cGl/2NT7GHTWWq7btBclTqAVDPc8XT/sqI3KUT5XHwhp/yq7u50cAJxZwRbGRjvuyUnZxJs9"
    "49+eab7ZkXOz6VrQKvid0Qgn4wkK5/bi7MtD0tNOt2RzznxBNLr/QqlmPi4lLYx0b/ZzfW2chau/ta07uyE1FdAzWU+ylu1C3eo4"
    "xbZrknmlPP14tcGvNpe8SRR/ki8bJyzHa5h1siUvSV2hAWORsEzESTHKhhvDEj9g5tq7eP1WxHc2m4w69b9QAaoelJAGZfScSLwp"
    "5Cq6LMzIuIWd7a0H3Kx1y7mS5yWcC2H3z4nkD9xi5OyQuTzg1LEb6qh9julriSLLUpwjDg3PuTYmd6xhnZmlpLZfE93hk6firO2F"
    "Eyd89Qizc9GnCiXld7brbfJ4sLHi0WPKziisCY4ZxGz0uLIXUP7t3SAF4xYVwZfyFgOMNbuCuhc2dLeEk45ZnY8k9z44BZQj+gHF"
    "dAZ5nlvpVikcpqmoJ/eDqLS5iXm4WuB2zabzyE1zESwq6zSSrgiGbZ0CUxDD2UZ29Fqvq/MzvzYEuQpqKCwMtWp3x7E0iDoxim35"
    "Sqxcz3XZJlPaDQQ+6Fq6iByiz8OxS+F8ZTuMPzMIRFnNSMdpRZsyYrHLSJnABmRzhlzlBZ3OtqThDu5oOEUNac0g+934DQ9E+64I"
    "e/VO33HFkIpp5uj4oFz9Fin4yDEYW6oPWtLM+L3bshUvboFdHzVsfTE9L6Z9AZNrdEp151ACp+JyuH3G8PV4kjux5guaKHNkSCQ4"
    "qDcTzCc7G+JvN15TZJgK3P5ijhUv1xC8LcxjpIusxcGHtDTR5JrLJiNC5vgXf5IKe4rEGG14BgDvkSl5HJdkKejbCB1uld58PRoQ"
    "hxlionDjPJ7G0CVAdzHxK5B2bAYfqXUreCUHqD0vjpUu0T0URRNUY+cg5Zg8Eic62irrH+Kt27owMFEMH+ZpSS7MwOq1g1OCWapx"
    "OYaFIxvbkV1Mrhlgbox3Qian3FaBck8yGwCx+AWvxUDQ+13O9gmKZHg2igryVzUWRu/Nbh8381XZID3mwcYtTGRkpqtzIBvwDsqZ"
    "QWYLQNvyTDHrGkWu5om1XUgsmphMO8l+jG2UKxLvYd4qxpk78XpuyqTr9lcP6VYI36ZZ0V6z/BlTJf1eX42XgBNyYbn3CsTR0hsK"
    "ZYtY1WHreWRHo+sBhhjuIs5y+NKUFqOPlCa0GHlX7ihc5KSBKUFG9pKhCKtplfY862V2oDL6gWDmGYy1aALqY0EGkHVxZfdcOAQH"
    "KD1bgSNwTPZXH2a6ROMUYpjRI2scxEISDqmf7yB3jkLxPUX/IPeh+EWSqoSkO5hgZY3QTD8kmhg8p++o1HazdkkRSMUneM3RqPR4"
    "Sj2rZOO2omcPNwh+MRQ4jWzxQQjqGsCyW7HG4sJ2ROd0PT8HG5ejeNnJEyb/u2/AxBRwDcEuwstzKqeZOIylm/yW8TbrcRz1gfdJ"
    "kn/dKrPymLKfD1QckVxZ9zqCJGa9hHjRspzaacKHTOyJhcUGQYLbA6paQjqa/silu6LEDeEkdFRFjhs7rJLkLuTCjnFsuzYdEUVK"
    "bFtgbAvsackXYT4B+ZB/NU1Nh7VsAHLG+oqRCCqbWMB9ma85fpRXap7EqAVDfvStGQpE8Zx2M7HTYbjMKDWBMxkfE/UzNWhS4wgI"
    "mHPpxp5+0cJCPG5gqMm9bA6RJQv548Sl+NR/5zkx2GkZvO9LQjfNj+bTRVFO2TAAIC8XXMvy/uv1MSQxa1Bnxym5VO48B4+KbBC1"
    "Vk0ZCvW2McJcd1xWgzvRUDk0Gui0xfJaBQ2bU0qEWayZHFkHR1Q2FmpH7WOBSkGSy6kcjsPrCsPNyttWD2tlYZLozus6ngciA+QD"
    "djNvG1bmVQrndQvaBC96mhJWzeH12JZ9gQzs8HD8fJRnBC2IOzc32vBK+ficqEHmOcKq78PG07fa8QnBHfpgYC0KoF6XA6YZMqZb"
    "pY2NQSDw2M54FfswcetZJzpy8Rs4GIGRLk5m8K9FlV5GdSjQOywHqfxBgrJI2x9qfQS5xUmrrCh8sGGVxzTWT+cYW8d+WM1rPc5x"
    "5atfk7oxp1vYxtiBHHViTSx7Vm6CJNGINFLm9QFsG55SvKeAHNcPo46GoQyIUodRyLL3rynIl7R8uK17ph2kt9UabPGG66N4A2Be"
    "syU3OUrHFLD3dcB8JVhQfqiNsd7seXPbhSMp2X8r/BuOP9q6QOXAtrfFVVkc+eJh2Bfatbrs/eVX2Mln/MqN+vKMwQfn1NVGxg1n"
    "VJGOQDmS++P9O8pZVk11Jo1hj7pZ+KunIMBjVjcd95PJ8qeHAPxMtbKKGVXXLjCDl/gtOP40qrVzBV0WWUb72yGHmy3njZOiPJLB"
    "IerWC/VnMku/JxJqOhLvAD4h1wJI9gZ+gOdOodP5hgRMjbfXT+vFjLs50QvJ1VZVXJn4UGIAbw98KzONUfvRtWwfWgHYJ1hjj2AT"
    "x5Bh3tS4uMGu3V/P1P10+oFv1A4CObschxM4bTL5KkOjzkHdVEfJ94GfroK+KcSQ/iX8yB8FQjSzgYlt8XwyY5XpfTGwt5iZnXr1"
    "SyRSXwxwAo422WbEq7HxpqlsxnIxK1S/E9BmY8yvWgfhEffVms7BlbZTglnVNN5HCsTm2qXqg3LyiSuNHg/mbL8TCKXO5aNWaqNz"
    "rqJP2uRco0e0UyKqiQXqGGUOFdmL/vrNraBKAwoMWvQc1J1vq94Lbl6BMWr3x9W2GdcM7SSTZsLJM7aBTuEyaWp45/AU6W6rOj5T"
    "KsImApifkM1hxgTVKNWHC5khqZPy2+1ud/W7Pm8xnwSxm8TTvBj8dIhiSFGFp5aP7t20/D6/K/Xy4rOa7afewqmq4kn/O7ICYbeG"
    "krX2nC7hOsKaQW5Hu247qxeXmQmBt15ttGAM693JLfhxGjVU9ySNg01PoZmjyMsF+GFfbTk+GVDe8l5Eog9oP8X8fiVN1QaOU9GK"
    "S9iQV3XGK2gq1YdT/r1BEDCZL9o2OAARVXi3omXNROk15RPs/YSOnZtI+4mHD9qGUqHwAUyxscNUdZ7ZGmAChUIcn68BWOrB6/D7"
    "JEWlBwO3Kz+1qx3GVUJBblw8/FxLxt4k9uaKYfs4j8x2USPLWGDvBo7nbtJ/bX1yBkGSMwSsFKa5mQo6uCa83Bu3HL9gdhLUfKXC"
    "OVC+GhT4iM5T5INReZG0/UA8gfevrTTXwLHXJve7GFj9nvcD2mTIj0Ml3ls0DtvZyquLsS/7UhSkeaw/zSuXtYwTmYNxnFvWqp5J"
    "kiEhjwEhpcHc+PnWC5aDbZMoQsTnVDDoNLyvCIImsKZn2RhM4rzJjUZRRkY5X1aEVO5RkFTdBsQ4xraS0I6Ni1gzuESnR97yBtmS"
    "opgRZyvhviDgYL+3Ruqk/JJquFOgRrj73ltuBJSg8TiOGwj3m29C/il2Y5AkDmf5mg/en8maQwY+27Dd4BmIS3eCa19IAhhJrJvL"
    "F5JA+BH7RI0DfTgcbOIIBVMWNffisHsTVaQ0rdDoSsufz0NFglUbumdAyXHgMpuG3zJsqWn6xD//M556dlzLocNWfkoZ++UgXQiD"
    "Z1vC5S4W5TY4DVZNng6gmvHMjC/RM/894mf45QeenX5Pu1GB8K537n0ANWmHZYO+L6obSznDfF9lgsbtccGoHop07OfC8asl7KHY"
    "cHTgzrZBoT9VAjH1cmcSLL64cX/Dz+RUfXDo8TOdMgsPEj3hNOTjQNJ+QmZkpFRZ2m7VL3/0TQam91+tI4QYgaBUp0n+iw4OVPr4"
    "91FNxkajZ18WPZfyvxNJms3VuZtBNEWnqt5RWeBFAoZYP8ukVuxwA1P0Rsp88EsZYRqILwf7q6b+r/uhLf4g0sffXqvgHZM02taN"
    "pAbJ9I282spNGGfZpl+mRlAYlYdz3Ju0yM4pnCaBE1hA4UkWgbfXree8RHi3phXPdxAPHkPLH1/iCjF84mIhod6vXnOCpAVVcC51"
    "D7SYEgswowX7F5+QwzekxUGmgOFNig4OMqimZwUtbZK7uvpRC3BkOQZTaW1+1mDZ/l4GdhLbT/PvWnmzGrEGxPMjiVJ2Mnq1/5Uu"
    "OKfvn7+cTCx2UuWVo0+8df32IJH1DWWKIdfbZKD711ASQyfDZkqpHcFlPHfzn+cg7+ZO9iz4aIzp0WabNFUmTaVsj8dIlWbpeGse"
    "qFw+zelnJanJTAIqFN9sFJ8lVFoeYPMJClNffjdHwCdh86uuIFb6ciR9nb/5Q0oEXvoAPFf/TeSagOQeTUQuBvEH/cySqX2VA+aO"
    "ZgnuJf28XnI03cZtPAsB+SPEPChix3k/b2YvFDFYOISFXxv6FkHk8iK2ucbr19dneiILkUcQZb04+r4wuvKMHaveCjYpFHqUTdJZ"
    "hzfqW7qg7mMHOdngNQjQegguuAkz1w1XpFHQsYK/Zx1wRHQOlNOY+3dT1Bp0fa5jKjV0EhO7PPeEvRNHk1RWKP2gtwoM31g+R1Sv"
    "DzT4u2lMf9hwckoeHW6/XZ+FxvZfqa44xK47xqeZPnELusprzc6RV5JsNzWY1g1kQBh7e98HBIWBNJb18UnSi0Ge5sIPQAJ4Mpfp"
    "Uk1SA0ZFIHTt6kTNPll5z6ZNZe6hofHIhbY+5A8iYvr6IdRVFX/H+u7y2DfQ4DmzNHUVj6PM4jvWuCLYzxCl6ZSClyDcHtxowHCm"
    "Raw07YItl2V4W/0Kqzw1fKxDfH2CQOpqalMGkWgklaC26gbPAwMl77ApP3pzU4DZJzjIJOOPyXSj279svZnmYv37rNr/aueNss//"
    "t/NGNP923lCSZ1KCUDVCrc4cf7FvqhOmJ8zxd53eC1YaW1+q3Bo9C2uUqvoIkFaUXLd8hMVFnYlxOC74OMc8dBCakyi4k9rX2ecj"
    "Vwv/lyLpfhSlQb5M/LT9MwPQYIyztIoNeX2y/Yf82hSx22QwR+Tslupr8Yc29PP388tGVfsMf3t7jHcAT3Gt8PcXLqGmfvXBrLHi"
    "UDp+iThYW3ufw+DxwywyPiSDO2i97igiE33kIgz5ikQ+vnEbveZ3dcQGzOj1Wj8GtO4pdaDh+WfuoLyst7WTeIj5LCD4XVh9TWZ6"
    "/d4/u5AFcxtV79iCOdfcsWQ6c5KKy/i0GqThhZEHZts636Hj1uT7CNQE1wZZPA2pnpmws5n4mB+k3+vjUe3UcXEDQJTSbJWUZTDO"
    "Tvk8gk/wR0oo1c2aR0C5YKexddSwxlNKo/kv0n32WHPgNLx+S2gC5tCml2IXxO8TWm2F1/fsQRkuu1CxGfZHiVWGDVezDi4yBAhU"
    "kQvwrUb7V/9KDChjmTsX67ymu15E4NDH6IAmgZJ+H7Cb7wZhqVxsYRpZ3asluSVSnZVh4x3NOSSJ7GONqeICl8IaLbXqTG7yP22q"
    "zkQBM+NBJnO6vH2NqXs93dmbHhvx28LOQv1danGEMi0DeoOhxw+NCiHeDW/iP+13mAiY4CIWjOvkLsb4EuzzRwYJ9DakwyDpDwN8"
    "j0CjlH+uBw2zUhwuOBNGFV4gnalXogqan4sLVGxE5+vmuTAzcroBR3gsmIAC16lbjK36Qtj2KD1+d9sHjTZNwedh47r/24loSEeI"
    "/ZYfsjrEDlqj7UDthDpFkt2xoBdEHrbxAdN4ZqMLHeB6v10AL4Zqz04MKd/lryWj4wfSIYAqhKivBmywmWz9/JAyywK+MDVi4CUQ"
    "nW/HbjYiR5AKAntkX7PoqnnSzpNef9YXK6PD8cBCOp5ReX396tmKCUkyyV/lPOKSdOfBBq3C2+tKjUYUvwKrRVGklSnnrZWY6Rcy"
    "sfmRigvvCwGZAey82irjjO25TrsL5ifd69zXt1GCyXgRQf/g0U58edAmkTEFY4f3n/F1YkTjIERyxekOHxs9je1lO3bjpScHfwA4"
    "oqVjeAJu1EM0FsvHIsUDaUscpAXqSxkX2zDOJJ5G8YhrAf1WjXg6EHtEpwCUodZahIa/U79hRoX3ysSYyY6MawPTlJVvOfmF6kGr"
    "dosfdQJHDhqcMSodHLvRu4BTWHW3CnRbWSy32JPhnKePYUAHq9WgHVzej8d2dyfO+p5KNVOCiHx/nFpplW83j1q97qmGRvCXzC96"
    "OlXhFjSuShlqguwSfPoWnKZhGTqeHaGW5BPoziBHlBzp5Pz5prcu+Q5cO8N4o3TGGxnWGX0pETHzbIdvoCwqtYoY2YjWz/xguyfe"
    "RRIdapCWY5RNr+f8nGMs+VOMD4wJZRuBH5QEPwwUUCOO3xv/vAhmEIHfjN1bk7I2qm6rUuR3Cpuh+1mre5f91YY6KUoBM/DQbnW0"
    "aKxBZXBVLLzz1m6AnuweapBhSe0D7uUCI9zJFrYDHG5ovzlUE3+6edXbl6aGXzjm8e/7TSIrbCoutiUU6CcOfDBUu41GSLTvHSN9"
    "0pY3CaAInm8RBXkKY88nAtJrraAgOUntUGJOBKCOHel5Uw6by1iAPbgzTR9PbzXNF3CBOoDK0qU3ZEWdD1PyEiXLy6mxqcZDx6IL"
    "VJu/BgMrLrAwoN0gKfQlfwPi3T+aSGHOmS2/w2gT5xduu7+9zuOtlvDSRyHqu+u2U18xI2xIvygsH3boTXab73MqGhwqWcBhjtYK"
    "ZcuONU+YbEBvX4XzQNlWyEQAoYndF62R3LOuICq3uRXW78SkRz3NRumep0AL1msBtEqiRAi0gAeriulgEeQaVGWWiRN74PrQsQPo"
    "bboYsHOar0AqhmDp7vZ6pCu3V4NNZ0qNmztDtVP38YGSsZj9ZYS+ux4CBB8k2kqf7dySK6GB8rpEq1apX1qBjNA0QI/DtwLZcm+C"
    "2X2+KQQ38L1+AYAZKuwR4nj+Wg1AVECduzpT8s8bdF+jxbsk7MwyFALNe/+KKf16g8sAURuhJWT+WjYZ+7b7YvBF1OMHN5MF4HV0"
    "VO7ovMe96F1HxTRSgN1o3rokzEX+Drt3Z361V5LPrhzBOK9/ki+6vd40kp8IMlvu2lRLMlzIPX+6TynSu8lKLITns/I2EtGS1rVN"
    "359i8at2Z/tDOWky3La0kj+YoLDuE72ewAYsEbbtKNLZo2JXEy4kLLnuZHSakt16/YYl0q5n5EhzvdfHWDoU3NFy7NvXYLRAhSVC"
    "GsMt1+fs9i9SC2wROfalL2uQHoRntNxlfiD/fnQJ2RZ1eNInvLEvZYfJD7PDVIbUSMmZIg3R9Ldo1wR9nV8afHqxdj8Hn7AnyH8z"
    "gsILtZVZvndKRwbiaxaIWqTuxHG4agUkliiar+i+Xtb8wjSTkUYbc5BXensB0jVRLLktyRWY0MqeudLK9HgTgIOc0fn5SvytLPl6"
    "lvMyOl8bCcLl4yRTS9ZcijKbA8gUHQG/t6WgBGgecO+7RHpDqXT5SJssHSrM9KIJlfcLW4dWjmPsVHlMz1DOFZ7yTYEYCfB+ffco"
    "VPJTw/3TA7zSYPoaeH20MuAkQAAchau7DNEzmUyZHyu/yex3QzH9yoKRO/oEIu6ZPqPkfJ3uDUkH2BngbVDGWppkvv8EksRIXl1v"
    "ipaDPZlARwkczFjhyt7Fnl2rfADdau6m/gR396r2YC52ULn+OI0r57RSDi57K5s5v1mr1PTbaJcRc9YjR0/603SwlRd5ldkrrtpC"
    "bqUwYRPMUkzV1BibUPc4EwAQow978ipQcrtEZLvEj/dohaxEPx+YVLfXq4s1g9Jwo8F1JqxWfoCUMZkY0UyXwacr/+rsKIP01cBZ"
    "LkNDa2w+9+NfZk1AWfN9u17sDIkfzdhsFpKd57NDWW4gdysLY7wUu76GdmM/JSiWM8hXM/ProFNr418mLnhp/p2q9cDMFqWDlf4I"
    "giF/DctyiBh3xaSAkypSgjmAg+tbo7TjLxnHyN8nftgv0Po4FdHFUbogMgfkEX4/QxQt1HBtqWQFCqJFV0B5uD34zbcUF9QxunPk"
    "L3hcyQyooSw9pfRu2UcDVx4MPM6Kc6mNbnkfox+nwTXHALao2Qx2FxdeEKP98xbCPXcKOICundj2vszGZ5Z2IffdqkkUYqIyu+uT"
    "KmfgAgENu+fIZcTQmHjroY+iOMwzqmxINQymzA6Lb4TP8hC8RVmZwDJmE8BLu3urjLwqNHeuMwsBJUkuk4Q6TtvPRvYyuPpQ70N4"
    "+rayqfdfSlMOg6OG9aE2y3Kb+Y7ysTqMYqVzsCXpnItayhdccyVxSCDEkfnmyYF8LKb6vSadEjnwHQk29ta40m8dRHvQsjuajq5S"
    "BisRUr5mSDl476IWd/3cu4Jk+trnW+6vpegN4S6M+Xjh4vc+z8NQ++e+sxaZoWNk+1AmI1d9Z09gygCKGemkDmVY9CXvR4qUKaBe"
    "PixuvQuph2Sy99gtuYXPAVnjSNd3JmHNYurUcjEq83uEzBW1KGn1ssgWxDj5S1FZDUsDEWR8x2SMhMFQSlHC+zCxtXAnlkRzTGQe"
    "kD7vzMXcE3jGDvA1z6TdJDFowRK+YmU/dt1SEcu3NzQSfrKEu2dD5nVajept6CA7gcDIzrVTYh68mvLqYfy15juVCIaA891xbyck"
    "5NpUbBu8lN+ahrT5PZXCHz7H49wbCTYTSM0X+YbA+TxYisMlnasIxb6ElnmJAHq1y6Vt1JKpQFdyMkRzKEfa88bKlq5PIs1Z740F"
    "2RM5f+8qayK75kewwiYx9LlZG144bE7lI+i2zCXAIXRfZvOrjk324fowRdaKaSdoEychpM2Y0+XyykrsXjBfmFMN/NjGoI7QE3e/"
    "WSAquzRiJtNRRvXOFwVezqlkGXC3v7x404nD7xPk+pzOSG0+pfm3KUrvqgKpWy6RoLNNjXb8hUrRiowvCXIg4g2AbckzlNTDg2NS"
    "GsgeROvTBAxlo9El55j16VxCta8ux3r0h7ys5QPlt21yn2AixQAmy9/PHpI+ORghfNJYclKz9Pi2Si14y6Ty0T5jgghsIpgEmJJk"
    "Wkd4F4zB6MIL+W0HiH1Tu5i6MIJ+CX0k6ssN0m0BxC21HjOAmE2WnGAGC/DwJQmkpd3nbLlFms0+UCLPaAAYc5rGhvSmji+z39/c"
    "CPfxwbX95qYLsK7qEpQfh2BouURfj3ql9k3s81JSkgse9aDT0DtgzvoYkMw7DikTvZJtbfQ7EVN6si8w6SfYogK4oxntW6YEUuV3"
    "V/PCBrDPlR3R4vwiFBrlWn7sevIFhwHkaEnevIt9iIS2WZGf+VxbBatx0r0crY+PIyRPnBZfDe1v76DpJBAqFhT2+3yqGMeXfLns"
    "9pOidaPYNXN8Dm9ow7l4vuUPtWGFeNYSY9SEGm/K/tskbaNDAloCRg1jIgzhxtDzni2Jy6X+KhUQEnwk9x04a7S6+A0YwdF+iJ1H"
    "lP9Z2zNI2GaxW4oCo04PezObHZt6cYpYc1fbS3M3/GaL1ijrpkwHFQrheQUKGFj7O7A1YE74l2phFNDTRI/5BUf6ed5bh6BSU6UJ"
    "+AxtK69wi2ihH3r8kzf9t5QBXCuGmFg/IGrFUbY7mfn6f9+lHPwrBIbi850xmMq2owVx4YiGjLohR4Oy8HKXveT1HICrvnelaDlP"
    "fOLuzFK56vAc9UZg+REObEAA7+G1sUxByH6QVYRNiiBte603mot44Ow/mCVUKET5lQWk+Y8J0S/GktehQkA+DwBKUspr2fRQJ++K"
    "5rx3M1KVZ7eQubQz0DEQmd77e2qfSP7kzIZ7YzmvyNQ39Q9Lzu8JXeYCYj2bZ3abXSCOLEZiBTI3FjPTuJaq9IU6pddgIBJrrJo+"
    "HZlIbi/KUak9jK1vqKScJ1QsJh0GI7GtYgTuFumzM8rkdO+2TJXOKlDhyTJ/x3QZrrsLbUwII78QXblpJVJrLPlxX7v8LLJ0iiUK"
    "0R4QdConaDWjQNau/+qXYWldpKhRnN0vtM+S0KMm9aNsupOTSGUSmRX4x/yhgdYHhMvZTF2zCT+gZDYbE0FNZXkRFYqSJQfZjKTW"
    "TqXHZ7iZD6NXP/IUTaTgvzrPwYd3j5QMoVewJUcd9fThcKXL+NQi8SDUHYddcb2+srpHv6IoHDqr0xXHQPWWhT9iv9UWz+HyNMWv"
    "wSggL9Bg5M8QITljFuIVCe7qN1pFoUtlpsMV13dMtEe/vMs7xD70glKbP+tnWXpUaPpw3dghxOhmFI329MGBY+RTwh07esQGHvII"
    "jBPlWhMnKCoAQ8XMsBOcfSbG47KqRU+SJsx6hWBWinJPFKavrQVSXoMcIglblTBjGBIsxoVaXZmAOTOFt2j0DuG+2GOZYknbN92+"
    "9sE5KYs8vkIBqsov1/Za7d3IUQW1w+ocEvnrryD9IpvPMlz4w2Jzrkng1Xq3DRqKmBEw07qTEajJETcIWZNFYdhFByCuLfEzPMlL"
    "/Pn9rzpo0AoO7JfRpHAVwZ06/CPU40OP7NrX6ivlC1zs0B4fR/embj0UQA+zlYqjQjRGivd7e+fk6M9w/c6ZXm1tKhiqXguIIAzu"
    "19wXKCfMSE2QekkpTHP/Ie5Nuxu3rkTRv8LCy6uQlxDnURVai5NIijMpipSUeg4IgiRIECABcJS0VkkVOx7KbSdx2+04HccZ7HLc"
    "Kac7Q7ttJ17r/ZTIquFT/sLd52AgQFGqqiR33TglYjjDPvvs+exzkFjs5+R5259NTby+acBeGxwkh+ntTCCYnvfjOyPwWZhqMyh5"
    "XGA2BplEU06P5FbB3Zej8Wm5HPPJDNv3j9u7MyHemkqTELNb2pnU/S0qXe750EcXxe1FYTqN7vkrbCzlS8f39iYNf2uUY/rJXn07"
    "GtjZLgw6DfdkvJdigm377qQ97gaSB/J2LTuJutLTnUTMGcg0GvZOoVcPTj2hkp8N7HpjVEMeB/37dbc8i5Y6B8VybE4VAiFPQ9ie"
    "FsFtALqQDgpSlJ5y0G2z3M/teYKDSsiTa1X8k2o52mULO7HdeazFh5LNudjrzKu+XHDqmqSBZ6Z2nu4XcuIsW9yfLQ4Gi2RJljtU"
    "o99u0Y1kOc4s9l17YIdFh/FM9IDbbpXKuc4w7HJmygl7jpeiQt47mvANoPRkmou6Skw/VRzbS8J8crDbTw5TYbRPMDAZFNJNsEy7"
    "Lp+LyyfSnmpqGisLKXdCmA6ivf5+qZPjFsVyghYKxQLvdQbYfR9d2t8Oo4+8cZnytFgQ+9Esa58nOrFpviqPXaPs1JMWEr5ylY/n"
    "Ap3AnlyfhahCQ6ih8XSTTHRcnlR6nVo9mxwKVXcYzLKOKwDW81waxalUbx4dJIr8Dg/zul/k6wG62E12GkM7m+qy3YNoPtPxFHKz"
    "IDX251ihRI9AOXONIqjySVUMdLqDzDDZTbaDCVcgbG80+Im8XYfxOdM98M3824FkyzetR7kD0F/RHWSyRQuJXSq6ndh1Z0KDvo9p"
    "xLzl7XHFPY/Z27vF8G7Ue+AOeSbdaM2fiI7CbYGdu5u1SsHTCO7EpUY0WM33KxlfIhHl7LXEfosa1PZmVCBcDshcesD7p9F0jCll"
    "M856wR8Ct8IdDIMrJGSSjY6n350lK0zCO95jKt7oLEhPXM4cNwrVg/VoKtNLCpWOL+rlQ8Vor15IlXx1GJGnM98vVZrZ+LAfaPWG"
    "uWQPLO9RKt3rDqvtmLMNjttwL2CP1YM5f79bz3Vbw3i1EwiJc4bxVlr96bA0s/P+HU93v9PpxMe+jH+encQrgLN4PpVI0cWJsFeK"
    "18LjEh1dcJ5YX9rNcrS8E+QSU3Ct3NlwS5i7W6F4aFbgWvP6hOtSdCfR2U4l8tFkLC5Ow3a+IXoDNd7P1pou0T1Y8N1Kdofud3oz"
    "yclxIw8lcFV0erG0W27mfNl9sGw6HjmTRKdZeBl7kJ/v85V+Y1YsCovOOOun2+VKcF+iM/FQIdgJTeL2A2eZ9bsD/fhuJcwmYsEK"
    "O6uK2WlXzogDftBLgax2byfmkv2g5mmBjRycVPbGXLA5trPRRIeaxnoxV4wvRctUj0uCMzfaY4e53v6gtz0QvCy3cOdCTWraHeQL"
    "Yr7fyyyKuW3WG+BSuV5yEE1mM1U/26dc3XK8bA/vd8fBgVxr7bf9B770sNAN780W7l6xHC1GM8NYvMpNaX96JAW6CWZSnxYSe0Je"
    "TvQPdvJSs5ep+7hwK5Sxgx8c5pmqR+bY3Zk37HSJ01w5LVftPqxbe8OxJ9+KtUHDRPf2o1DCC9LRvu/iomN2L1uv5PtcrMBngql8"
    "tDgAW7Q3DjmljNMTLLhKbJVnkoWRx5/yiv28i3aWM51AMBDv98Ca7IdTNfD5diTfQbZS2Ekx0Whtp9hk3F6wOA7y80yj266Fd3bj"
    "B82YU2LDXu/M1a3VkpVUMckL3ULdPx1xdbHbiQn74jTaiTX2t/O9mpzmFxW26+p46VC2l41vs+GDOjNq7OT6BSS3xCLjKnN9L5fo"
    "sTUvlabkYUeYl3rpLJfKJkr0tjOYkRJMGsVTeCpd4Xe3ezujaLHZDe1ldulUphOlUrv5qC8W9cTY8KI0HABzFaNyoVKri2F7xre3"
    "Xckni7PKOO5xxbLhgVvsO2t8jApxVTazyGaStUbYPmjGFmEqGl3IoWSuNkztVOKtZCMIrJ0b1ILFaTYd9nDTfXus5PaEEkVXI5ix"
    "d13lalScJROdoquTqpeSbI4RyoBWKl1NJBqJsKe7Rycb9hzF7+x3ArWp0HUVOwnKPW/seOL+Si6zW29yCSez06q1U6lmJdYHL3i+"
    "w2XkWiLBs6xf8gDjdGf787S4kPuLA280Zs+UhKjd7pQq0ZirEBfFgyQTS/YzM09s6G3uu3vtYWcnUQ0kZ6F2NSA3xHnJfhBubqdq"
    "VVfUXmrKjVSXEotNwT0N1XfparXNH+QaKW4RDtQD4/L2qNoTAaTEyNkTfCG+Nkole1R6l58H7B5WlqP9bt8bzQ7rYm00j3F+uRcL"
    "gbu+4KkwJe+M5RE3jLk7Plc52aDa3ChM9Tzj2H5/P+bOh3Z709jeQY/aFnqJkTs+Qyf7FA8qs2A3Puw0ktMQPc1U2GyZFqLt/UbF"
    "3t7uVQLueC8zHpWyi2x0mPYGkk4+1h5v2+nUlB5GE7PmKAgqY56k4qG+UErPS+ndMVUX9wW7s+8vubgdtr0bDi8mw71JtFVN1qMV"
    "nh25pHmlWaT3Jp1JZhKL5aiDUJoNpNr98jQXnRe3O9ndEL0TW+w1Svwivt/YnrWEVrGd6lUTVLjUr7tTxVAlFKNGHDXsdBLTELjT"
    "0SSbKu/n0hPKPTtIzMIpKR7IsAOfzz6fzkodXo4mJvNEqeoCs7HZCHba3O52p045x9MWSK/gaO/A2ct0QrHpjrPLNgqpeb9SbcPc"
    "7xW6zvK2MzBzSZNyO+mqb4f6sdakHRrv1UvxfY9zkigNEvvR/WiiyM39zbLgKyaGcXcoJ7LZFAv8NZVYPkTjWOEs3faCa8uPJ/xu"
    "0rs3A4HMtQ+KXMxVLvv7zq6v3/GlXBwz30mPusl8t1Dx5Ko0CNI9b4HjWd9I6NS3+xLTdmeq/WCqFto+CMRE0ZW0V1LTUCVaqlGy"
    "eyc365UHfSHpi277w+E6+GRBZuIqDlIH0TmXH/bHjeAwWXLa57EwnfCmwjs5VyIscBQI71x9v+ce7JazvYycqiXKBaoMHmYwwLQX"
    "bCtdmTPVznaGP0jv+kLxdCDYZMKj6Dhc4T1Sfn6wtxujwQ1sNeM1aiY309u0M8FlE0UpOx9X862OL97eLmXj0U4n46PtbnlXnDV3"
    "UpUc1ZkcLKqJClcO5eTQwl4dlHLdSkrcn0fzVK4leua+bN7Fb1ODRYHPjeqDYXl4sMM39kepTlzI7u1EO/F6km12aWdVFIOzeM43"
    "rJRjob7PmXCXk4kovTudlHyDSibaDjizUW4R3elW/Ml9PrHgdwPZVG/Xs52Iu+reXS4UiCXCkwFdCndcjbY/VimnduhKNO4rLHYq"
    "0Whc7jQ6KC8OpD9YL7VSPTENxA8S03Y8KmSHO05n0xWquKe7qVg+lW/UgAvzYj8R4GL7U2emVuzuMOIo6wd9eBDO9vhZMuYrUNNx"
    "U5wm6+X+frzsSc5k0ZeJN0alMPBCYpiYSUCbXJ7aF/p18WCerjdYsdpsNN275daikl/09kaubHmY9mfAgqH2uGnBGRy1wnZnOCk3"
    "ovaDWLWcioVycd/UExTc1E4xJ9D7FSkp9/zVZM2ecrZz8p6bzlRaMMRCOlz0eJrOeKCY8QYSs1mmzQdaQtydb/H7g2E1X55MnN3K"
    "dGRvlxk+lirmY/KMd0dFfpKoTkvOhgR+danGerq50NxPe9rDac4f3ssWU/mpq1UQKjQl12PyoMPM7PExGPhsrRoeuWHKp1Q2O6sV"
    "DyhfYTBbJJP2ZN6TaMbB3uR5nvMzhXSQrUS72yF7myk1yhm/q8lwPfvC1ywUqplxKkG1MtVR3MXFd6lwfq+O+GM+c4fi3ZC84860"
    "Ggmnc8anhZTHXqbnrkYgIw2SLud8yAddSTo1sMcrFfATw4HmnjNRyw6pRLApZdJjr5RO5FrlSSPjpPfyHSkX3cmnp/FozxvoZ7pO"
    "l51NjHytUI7up/d9uXTF16yw7r1hdbRXiYODGyjscVR9sC2H2jHPvMyVsglhNAD/t3VQiQfD7nTN08klwwcgdif72738qOzK1VzB"
    "UFCuT3gwOgqpfn6UKgeilL9ddFHBljPUyHDJfJhxUn33lAr3wIEqNjuTpr2b3veLdAsU8mi7OAk00pK4az/YznUTvdqiTw0FV7Ia"
    "LpZKpXa5PxBqXH46GcnCvLWzVygtWslKZzbo7zQLMrs/qvI73E6WLudaM7AofIHd7HbFVc2Gxep0vF/PNw/sA74eboaY9qiU81D9"
    "nDvRqveyMZERq5kRx3hb8UDeGe56evFZkttuT4J2716MmnhSsicWaIOMzI/rwI/g04Bvn045wcSrsK7ReD/fmu555F6F9/LzuSxS"
    "KYGNSZlisl9i0qW8d9bPdpPleY0D+EZUdhKY7W3PaD7R3RuDrMyArAzUs2Om4+JpPjuuMwvw8maCZz4fexdzNrcnTNMzZjpqTmcL"
    "V7S/06nJsVCPpqNiVPDEnPP4Pu92JTLe1qI1a+9Fa7Xt8qCe4EPevjPPZuLpYZwWO679mq+QnpbZaFdyOxchMd+ONuZ5VzIbHfRd"
    "ofzOtOgJskye3eNcrmZplA+2UPywkvCldsrZha86clOi3G/2vU0x2cmAiZobV/husRLK7jG7jUCrGI6H6QIzCZacwig77oMZ0B57"
    "k4OYO1Bpb/f5IhBZqF7fHh40ufKeZO/NapnkNDb1OMVigt8P5/2p4Vx0M6VZ375fTw3inR2v00PvF7ZjSabPyK5mOyD54rFkNL6I"
    "Ix8lvsjP8+OD/oGzlOh76J3izA7ylZkAj/V2+tMOhY5l3PG3k+PMbqA4lhvu7T4Tr0qJTq0K85nx7/Cxni8p5yrJaO9gEkgkh3sj"
    "3m8Pd9LRaj7I8ym6WfRIyWmtOgrYhaK3XUjvpcvJJp2t8IGDGtWetfIHC/B0EvuePdHbbwBuwnJ6VFsEsyGQRNNFvbe/E4tm+qlE"
    "rJtpt6VSpxj0+1rxmLNZcToXAV9KCqYW0X5pPKttp0suOhp3ZibbMgi8+aga5blwOLkXb/rq/WQ0I+QXjRgDRtw0PXYH99rjLLs/"
    "y7fTrkW7OZFy/hK36NHbgTLL57Y77fDOMOClvX3wToRtvhooOWeNeLhTLHL5ZHR0IExTznKbdTW2S42YXBOjcnLvYJRNjLNCaeaf"
    "JuKBdH13e5EZ1FhxD8bX4qvToByrSaHQJO2N94eZvfBeXOrkEzKd8yXjw64MI8lMvNIkIAcXnjIdLzqDk04xX6OLmf3FZG9IJ6ha"
    "bZSbjV2dUTrjK4YmiXI/nwgIfKtQF8vBVIVueGeNbbYzZqM5X3rQLc9LrpwnGE7lPHx7KsxGVCU4GHRGznHO7fPtzBalnnd30Z2w"
    "WSa8y8/CPP5OTcrPBNg9nydk56dMfSZ5Y+xue3c72bTHQlT5oDrvDtLdvjNXAPdImIX9THqUnXid6f2dvVgyuR93JkoeoYi+EFkK"
    "FMpCftrJt3YTs1w8019kdjJZ1lffjrX25iMx7TqQ41ydyvJiS/T19keFapiN+6epMt9pd0LcYkJ1xIyQrMcqiZiPSXPVxi7tjSV3"
    "Y7JvUd2War3EThaGOO5ux2oHVWrbG+yM+HwotzeI1/sdfjfKBnbjUy8dLRy4xV4OaLM1bwgSLXu8BxIf2Ck3uKgQKonucTk35lL7"
    "hQG3M97pNnwJKZfyDPdDpcS06zsAQKfycL+Wm3j7qWypVB4PKa46O6iFMrNFkUrsyGWq4p83iolGyl8K89lgor/dWHDOfLAx2PWP"
    "PdX9cYFN78VCu0IquNNwopMm2HICbN9MmK4sSuDPhnYW4Ual0S27+bo08Ab9/mpjWsin6Uk7PQ0GffYMWxyV9tlaNDFsDvbZ7niX"
    "8vnjbNzF0EC4QTnoLRdjXMie2fGM/Uy46mk06YPezOesoyO7t6fpQEZMBQ5GUj2dkfvcWNjb7nWd23a+NfQc7M0DrUZ0f9acO5sy"
    "M2GFWrcwBv7fnrZ3dlN1bijmF/O6Wy7Fw61i15XNV0NRsH9bY9nvs8fjkj9nH+8XKf+wn07Ye8yk0evtRft7sU45JnhDnHOPq9SA"
    "DO1pMXAwF+hCY+RtiIwUsNtzB514rRwr1+JCGuz+vn8nu9cvCaNiz19JFPYSO3Rjz7XXmxzspfw+Pz3fZ4RRLBpNxFvjScMeaAXC"
    "dl9+ke9lugOqL4VidrFZmPtcDWeJ7y0CTR/r344KUW/IFy61Crtcg2YzgXwHlR3n+L2dqtwsBpy5A1+w3T3o5oRyrFPk26K0qLkK"
    "pUo4NO+Wi0x84um1Ru50ojk4KKQr8s7udqwfTbcnLpr2V4YFuzPpFUvtuLscbyfmVHY+7W9L7iLv7Fdji2S0Wz6IJheNNO9Jzejd"
    "ZLvrXPij/X4+FBJz4t6ovy/nFs1Wkd9l50lPpst2XNGZGC5NPK6ubLfbZws7l5+UQvt1WayG/YVSLlQspnPT9n53uzbIRPMJdyC8"
    "kNpJPuvtLPoZnrUnQ0FXOOef+hgx2pulMsNCOeFjpHhxNPQEtiuL6iw2TS6mbcmZOihM6iEx2yyINaYddu6UqWhmmokOea7DJDr9"
    "0kF2WMlQ+Vltzzme9HcP5EDDXR3lnaOGn58PdqOpzrBmd3LBwE48E6KTlUY4vpM9YPsHLfdC7Dckp+yZ59NO77SxPxyU91upHa/o"
    "DU4OPEy/zfnnOyCeRkI2zI3jTnfDNyq1BHcCHDsxR3myBSCmQHQkLYR0NJZf+H0Td7A671OeIuuT2unufn130EfrkoPdjKuQniRq"
    "ottemthTwVJ1u1hkGiF7K5t2ZtuV7DTuahUn9Vl4wpSBKEpsyl5w+XIhaTdZSfUKqZ0J6OfJgs6Gp6PxNrj4ewd5xtufV/PdWlHe"
    "Hpd3ouyizNaTi8xC6lOprr0diHnAiq9ul4Wk+6Az327Eg2lPcBrwFyu1ElXNVlqNVqDe96d8obZ3Ns7tMY14JgqyDaYLeAQs/hoz"
    "ZA/c4Vl1W+A984xUs2eqqQqYOdX5Ts85GO3Pp21ndtYKMvwAPP+kr0hPpBoT5EOCMOu3A3J1b3cMvrc8Tfml/UQGTNRCyRUE6cYG"
    "6u7egV1iR/NKl56zlG9YDVDDbC3Iz1vlwryRCGcai2CXHovOeaxVaabcEs07qweDvMy1uVCvt6C8km9c7DMt2jVqic1AW6gJYIju"
    "CkKrtL9IdfZL5Xi246LRkuGB7Km7KYEtjFiYfqpbFWuCONif0pJYnLt32YK/5K9V6wdd3/5+lO7XZ6AT0pWRvKDZncp2KuGTR92q"
    "vD/Mi1SzH8wvpIA7uiPJewddZKOEG6PddD0j7DslaZJzJvoDaXrQcWZH+5ez4U/IGR2pjw9L4u3j4/rYMaVkunurPeZp9HEKS6dj"
    "tR3RAi/JFibSEujxgOFlBy0ylMwkOQbdWQmO5fuE7RbjEBkuQrBQnCAZhzwfMnCnZdejR12RaUdmNKk31GWoloMaDhm+Fe+yXMvK"
    "2E6U3iadyJHEUCLd3fz2d2hWpDnGQs8ihNtNWOi58itGiCDhfOE7Q0ruWloRYuBxWTyuDa/Dj/7Bm2+T4P1w0IBWIh+whKiAJWBx"
    "wX9ui9tjcdEuS9DitYTRv7RX8m54LN6NsLHZvNvl8Fo8bsrtCPss+I8L/+d1wBXuhu4ydN9j7Mgdgl6CFneQ2/Bv+M1Qeixu10bQ"
    "4bfAv5zba3EHlEaEjrEFGEywuwoJ9B9M4+aMOAmqOAlinHhXXqtvly9RV5wEfYkMLVumbEvuQuUQYekybKcrK9czVNYyx39FuPGY"
    "AAF0TaCUCTa/9uzbJMdKsnEsgIyu22sqHgLsr3kWWn3mhaoOl3vlGdRd8zCkPvw2KXUFRgOgzXJAlsC5IpBcXOAEkbBIsij0gTx5"
    "gWcIXGJDHHPwgJkwvNBqEcqQAo5QyOJzhFzRsMNjQf8w2cDEAeng5274Y8F/FJIKO1xeeB3yR/2OgAX9Q0/hn88RDiovVqssezkA"
    "snF4YSAuhytIuRwB6A//UZpweIDeLj3eUJ5D3aAjGEateV3PXRdD9/dW9f2dEOOZGrD8WDLSih8Thg+/BMFgYioP8Hd3hSUCwIVe"
    "R4DyONwW9E9BqtfizcGIwtyGD6F4w6f0Jk2poanFgMXL+Sw+KOUzNYu4L+1boU6PG5rbwMVNbxBXdlUupkRRmIrrB7SUAcD1SAwF"
    "NuAfrtYWuBYjrvC/x0XBiFVp49nw7IWW9xtw3wUpEtYfuQGvgfCGI5wLA9l5HeHosjKUA4ykfcb6Fs/E7TV2YPEoSAJVa8IRMHY3"
    "MAmsyEQgaUCIxcytIPbc3knAABNcpf3Ge9Mw3GhYXU3+DeeaUAKBE8LSB/5qAspnEFC+dUIJpiFAAxLcGDuOMO7LR7vQI3SH+3K7"
    "aFwCAHCE0Zg1AT4xjHkAfBRCs4P+0wvkjCUAK+7QBp5AtQjFMaIRcQOP2xFEUmkjtOE2Yh70Rsji4jYAVz7DHCF0AhUZZgTV31hB"
    "MIihiW/1EZCfJvlYvi2sqEyPqh48WAO4XZdqByYbl5oMGVpsCjMTZXoQRW8EOKQruxs++N3wps1z4Xf4/CD+3DDBUHgSMNOZeZgw"
    "LRPUGuDFvwHC0Ei4wN7BgMWXDoLIMKDQjUUdNL9QuIflmBWS9aQDq8R+CQjPCnsFD1a1rWfiW6mkCibuKqFlQqJ/ogqy2SXbIGAx"
    "688BfoSQpRguYzCHWL5jNl48QM8rvGPiJTTKkHkQqNFLfL+KCc8qE4e7npV2w2ae7m54VuVBoOu7JCJca5751jwLqXhtCVOjxAek"
    "hDVBid+PhyYeBA7yK0yqitEhu6ow3MGJf8V0AWUVDJjEJpApoigO0VXIJDhhYv1AentAPG6L26LrbEQ8hgcb7smGsVEsc9wby0Y3"
    "DK1CPb8CxF5QbwQpKYxptUnXhi9tEPdYPhjKWlTK74js0MzuYYXbAwqzr5qK/uvehs2C4oq6V7zWKoeur7x8/W1S6D+HpEIy2YMR"
    "pKjfb5Oy0HqqqFMtvY0WJXVBNVPIoAUzTjGDpRVy8SCXgAoDzSnzEXB4PBshhz+gqsUhxbeM9BdEE4n/WzHxg9AEPENvNHubo4YS"
    "Y64MGn5ZyPjCZ2gUqZ7+il2AuGLpWYD44yiToABK8UuInHzwD0ShJYSxhu/3vNIGNojgnx8Edwj++ZT7xYo29YBYDirSiOKfZ6bA"
    "mrSgf2D0evAfhbdZpNovWRa+VQHmW5U0K6YTPA8i5Kw6Vqg5kHXK1HZblzTW/0UNZRLHl/0ZNKSArm+HHDU3i30fB6oIGRGWkML1"
    "PCMbLCWwPJGphH5UWymwNJUCiqWEO9QqeJ6zfBiX9zytuFEbgknhNcs2o8TEAmxyybJxg2moOAXMQDARCpj4oInNEnhFiwA/udPB"
    "FUvTv6Itg5wfKWW3mcQWqwrC2w2sPgpqml+Ymu10NybaFaMqBE5JAJySpSxxexzBoMOlNEJzAt1/TisNLHDwVDArnSwDNAnrEb/J"
    "QIOUJBWoAbPJn9iOREYei7xFcvSkmZWQJh2CPFqWIFjCbuW3CAth5zcJwkZOWGYaAxOPwKQOffgIkqBEltrosq0WwxObhCyOGYJs"
    "UXyHEYWxxM2rjJzheUZM7+Zzm0cvvtiVB9zmpHPI3D4+JoiTEy2OM+9ErA6Hg7FFXmAcYKbJjGiNCQLHULzN0RNY3gpw2AwBJ9p6"
    "xMrMQIJBTShuDAMiBT7eRT1vyiRHNRluUzSMlzvRAlRspOQYS0yFaVv5McfZyEOBpG4rD6syJTPK41sqdvDzHDUXxnKy3QZKt1oB"
    "SLUtOsI61IjBlmM0ZkQYMAdlBNFKNMeyLPCHGEESfsq0IghBt2Eg9M2blPVotkk7hHZbYuQc05bJqX5bRwwEyCEPeZJxcAzfkbu3"
    "beRTYOGZqaXCSOyCKTYlRpwADg3vW38vrC0V1pYZ1tYKrDrG9G5u3oTxKJBY9Yc2EsFEO1qsBHDxaBBonDA6TIeSlWixEyBEkWlv"
    "soYJnHeARBkgUeHmTaJLSRss3yJImD4RqAQoj2qiaJJGkZgACEQBKF4I/W4eQj2N0kFBm0kdGlbak+Q5tHaEBdim4JiSskjxUlsQ"
    "B5vfw5ccEEjD+q0jwTE7Gc5s3ztZywInNpi2ATW00pEX1E4VFEO3KOC5qd/q0BMk24L5Z1ukzMrwjHbgX7V5bVKITT4SidCOCaJ2"
    "jgXpgLApW+GJbTlW2oHHf0Kix7bbMDk646R469EQ1KtJFkSIJiUSOofIkTwIFIB/ZnWRyiUwoNvlIpnjY5fN5oTLWyvCYxWlvDqy"
    "oSh0REaSUAfqWDC/QovEpsv0hJoRm6gTwzNemBKbGAIQJ3zLKv8vKGAYqNo7C12rM0dsbAyJTRlJFuOoORAXMLhNJkKgmB+hIplf"
    "NiWrcy+uCEadIA3kwgyG8txC8ewAqGGjTbUYoB6NeIw0p8J3qQGAhVgdRYJEIhrBTfI6qTZRPa0cyGxSvq3LzF4ncsTytDBA/t8h"
    "cfHmu998/eE3n/8W8DwQWsRtNVj0IogFeP3wnd89/ujN87v/en72yfndT8/v3kHzQdNQjmq1oMDjr/988drP0cMWqgxNoFrv/wEq"
    "6i0CFAh+6OytNy5efePiV69CAXgLz+FtC2QuvHr1tSfv/Qoewu0SCL2mEQLUirkJtbTSkqmouVUQPRzLo/Ye/suvH/3pJw/f+e3y"
    "Ha++uvjLJxef/04fES0MWQYN6vzs9+d33z6/+9XFg3vffPGyscD8RUYUjUUef3T66BdfPP7NG1rzJ+T2MHKkoAy592ptUsOfhrkh"
    "jEdBG6lh0YA/FGBUB02akamhEQc81U5JDam3kXX84prOjajSAUFl1zW2Bq+X58kE4fpJUzAGZZVg5hIYDXkIWyU+cgQOnAGlDz9/"
    "5fz0aygn9KEJ7J0Z5+QvL52ffohgZQdqDwp96yUUEhfHiF6mFCvrtK9M50oDkkg3xxKCshCtXpz+4fz042/+/PWjt+8rzUwpEbWj"
    "Frn47wfnp+8+fP/r89NX9HbUIoAfTN1vnJ8+ePTqK3/76hWYUyh9fvp9uD0//ez89C/npz//21evLuswLTBSzCT3EhT9WEHg+enZ"
    "+dlrhtIq6d0/v/sJwh4JYrmlELtO6FD5/PQN3NX752c/1sqckH2QBmCITzYRWsmOIG8S8AeMMQF4gUB/4VoUhnANfwnNzSKUX4JE"
    "MGwqkCjBQYw/MLFlSrk8Iad6FwjfX/4bTKTa0zdf/eTi53+4ePOdi7+8i58qvT5674vHH95/9MczzGVK7w+/evvJh/egKAz9m89f"
    "Pz/90RIWpZlHSB4o4Dz8/f2H339TAwi19asvAMfnpz/UIFMgOT/77/Oz/zm/+/L5XXj5AJ5cfP7Zw7svXfz8P2Gezu/+ANB5fgaz"
    "+unDf4U5gyn4DUwbmqoTstDR2PkZJeBV4g8tT14m1b/e+UirbLDHU9YjrIN10a4qJNmglsXLJvqqlt22gukANhEhbxB2hhRty2YM"
    "SmOpB/ui9aiPlIyq6flIT7HFDxlVGTxNrxN9sJMsfeiOP3TfNnRz6DLZGRMw0BUrnAG9COMbSB1Qy1rHYqTEH/KoY15l1FsrSvdy"
    "z/TQQg+hYxF1rIyTsRObFvTEddtulcFX+eudt+Fexv7KUg0jmwmxxZZB0xJ0tw8mD7anCFXKmAugsA9BGq1E9ABVAf+AZJaKOD+M"
    "MOC3oIYQy20RyjovsYkfIY6BZ9C9cq/3pbSnPMT8uUWgCI32BHHpFnC3XkRh1C3tAqxGEJ3EkqbSQytYQXh2nzaJksxqJlCLVp2x"
    "tfZIfmhlbAYcrB0BOHIma6u2HpC1kyoC/VoQ7a4aTc/XPakPw0SFc6BCygDIDTBgbzAOfgtN4aYKleTYFqkOSjQw2FqHjAPNyXeg"
    "sGaMpcB2V6WiXox4/PEvH/7sLaRLAIgb0DYIcXMFJJ/XVHjj4s3PtDoTtsVo7slV8OBySCpe2/rFr955cvf+xev/+ujtLxUvZNKG"
    "IluXqiiTr0pcEJl1YGthKllKcaSeXn7j0dsfaKoGiUoA9vHdPz+8A0/uPfn039CTP//i4qs3oabSGTxX1BlWTe+ZYMIFlPKFFGIg"
    "BBUaigksRfWocOmtK8YXtH7x9UtgiwE0a/sDKf/4k48uXn7v4b/cv/j1fayEVyGA6koZnYeXKL2hIkq9uoxnpIEuN6lq8BPkY+GZ"
    "pHAbV2H7/O5vzu/+/vwMTAWwp2AAHzz54PcXv/wdNq8+PD/7FbKwTu89/gjU4q/OT18/P3tVQf/5nVM8TpiTzxSl+vjOS2iqHsDs"
    "PXz1zvnZjx7e+wE2Rj5CxS/NgdaP2r9GeCglR7p+oAaY1bGSCmsAK2LmUO5eUCnfyjhogTVNLLJHlu3FixmE/8szbyqCh/0uFFTR"
    "OpYFM5irdR7/ABHGE8CTAiOqxQs0cpGvZRg0MDTCu3Dx6PsfXrz2P8psqqK9PI4cYVPERYLx4tYsFY9ikXgNGp2XrUcdUHbgxuLg"
    "muZKA0LaHOi52zYcELByJAse+yEHKovkkCZj4Y0kiLL2yloeH6IXt7e2fLYNdMdqd8fH3KHn9gYLf2y32Lb1hqzGhmyqnEVUfUvT"
    "sDA32vsX+C3ZIQEyGPDo+Q23bVNe0bfrhY6owHzIISj1UMZlKd7mLG0OVDOrUfqj9x9cvPG7v331E8KetHIGXYzuTkgO5lVUYfuO"
    "BqQuAK/sYCCIuuuujUdrRkEvF3kBegDc2rSwIbCOyRYg7NCCWmdDq3z7xBwlYSg8mat6Q2SGnEl1KCSFHmtgfU8xSC/+Atz96beO"
    "lDonF+//TDP5FcZfcqlW5kVZ2iKQU/HTO2Awg0psMlb9jc2uXUvjASoGeF0+QNaOnUAyD+nC7xkHCw4NeDMWlFWHSpsHCcYgzsAC"
    "C23cbrNmuh2wSPWKEQ1XJAeXamS2y9q0p2xE3DIEaDgUoHGKtk3XU+05sF1RcIggQWpwIEzELcUK2uS2CBjIghEFwmbGquVbR9yJ"
    "81tHommQKnfzJA5sscD8HEk4oV2Sv2QQZIfamGGoiINu3Og7qlsAvSBLwIYDxsoCC7KODoxnKCl8ix8LkRcEx6D/Ilh4x8f4CkFr"
    "s61hveuR15hpyHsWFEF39BJFN28qOLKZ9bfueCFn5849/fb8DnZWMS8q4tusGJHjjIoCfagoMyGr2gE7juVpZukxHJK8KVTuMsfJ"
    "L0el5cgUWxYOCa0EwPgnFIff81Yx8oJod9tIN+PVWsGhYY6hRL2obAwOr5dS/aE1AbCAuJ9abU5ozQ5Tmk3WNxiTVbrHWY9EoPWO"
    "icyhKMxTl7HakCZjW4Bl2SEMMUEg+QmXFNSfMKYblMLqkGRKlKU6K3etvKPPzO2AQduWoRQ2MtSR3eAdqn8IJob4DPbnDWONKyOR"
    "4kw3LgrR6vnp5zDfD9+Hv288/stX56dfg2EKNHHx0v1v/vxjeHV+9kdkZZyBE/0ZLv/gm8/vPP7oY83W+OzilZdNdgdYHGenIEKV"
    "AIsSuTE0cv/JnQ8uvvgIzA/FN18hryv1hdikRAsOuK8L5eIY6HUuwwoJ63FPHWMvuJV1K+3eTnzz5Z+QdERFmnOZkfD7kVW7taF3"
    "3xKsiARI3gZv////xgWWz0DEOiWtDTz3W9dOoNKESrjVDqmyklYZa5xNLJ6Q8YhMJwPbcBHRIQsyxSnCtc0JggiqDjG/ImGVtyBn"
    "QQJbMc21GElWBZYqaUBkoTrL5wAAN4Z7qwBDsikaE8s17KnrGvPul4Tt1tNi4OLMgsJICvEloR9gCdtaqbwy7wSJxDT3HFPMkgSi"
    "bC2ookir/1dBr9qzQxpyrGxFHOgYCkMrXvVAwsxmNWv2+hBHXpauKbN1NRjgJg8YIyRDGahBQhYwcyOCeHiL+OudHxN2/JyB6Ty/"
    "81M0o5jzl52WVYdYSXjmVdXDrFUdvDZ7Y1pXsiJY2pKMfF8OxApxfGzV7nlmJsO9/hrkoEhgUTbmZZb7TsTrQrrn5k3xumFON8ZL"
    "1+vJO69ffPw6inPe/fLJnf96/OE94C0sDh6g+NlPf6OG3EDQfPU2uCHYE7vschwSelGYJllDikZXGsRK4ONaRro6ioFWNXFgc2nP"
    "q8FGZATcxp6mAW/P0I10VT+4AePodNQottVAowdElg8fvI7cEHudw2bbQOVzM0h46v5OkMAwQEDhJkjDXIN9IAkCbzZ4H/7Hhwgo"
    "ZACc3idIAMqwvKdWxvyiwMeprk+8A74LyL3IC8VmD7S6A4ATWRAe4OFRSKKAnNZo1XooI//gBryjeApUJRpgqbRL2DTfRiZFKIBC"
    "dxsy/LEtvRHDqn5qqPhQl5IT1qIn3sHwqS4KdKC7KOvDh112aKHBSTEER1EtVVeIeI5I2WY2GgAitmWKmIpgK5CIT6uKC3Z8jKyH"
    "tR7Y4e1bbZDbqki3CG2LrFiaWABwIJqH4P94bFBAZvkxc+vQ4XCgVfwqg9xBkxG6lOkCMjZ04T0Fp4dUHtlWMydstxXsZ2V4JYhJ"
    "iu6iKqJjOJa64NWBFrATx4RdIK0qYJq/6N4CN0pVC3bC4rQQ2MlIWgUbuFYn2mAde8lCLYksGsVIBvcLOV8w++orEEVab+oTUv1V"
    "CUC7A2OAmRXbVgDHBkYhcmdeefTmXy5+el8JBSDL4vbSaVxKM7wwDjONZkmPs5wiY0eLbaHlAnXpAEm0nzz64NeEljSiwqSnjsAA"
    "DmYwctDQHUZ24FKXtRohDBF1QK9KM4QponD63vnp/2AXTwUBSSNRc0/Xt4DDAXobyP0HJxm7sZe1SY/WaRLR4i2NMBMSJsycaOV1"
    "9c0/E760hZX3zs9ef/jur5EX+u6vz0/fBnmBpL5h8U8Lu72OX72B7T1lBPISiWDYV4egl/9JSARYEAZ5jEFxyeIr9Y3r7mAV2Mip"
    "BH+xT/3Nl6/hYWEHGTAr2gBRQLX80iKSbUsre6Vh2dSwbCPX0ubJmplKGrfFYbnBgyavXvL7GFrtECaF4Ji2bFp2AEnGWNSnT80s"
    "GHZXbep1xpuyZY5YH3TX3moWGhjl/HCs0gwxAmWOM1hkrHyGHEUzXWVXCqEaBHe/PD/7EofU/vv87sc4evijh7/66aM//IIgUSQv"
    "LgyGHCNDG0K7rdEP4xgZMrjAEIYH4IoZaQiZXQMW5Quptp2eKLFujDIIQenSEKGkkhu0xsLQhqmMDy/iNIUZTswhBJ6b1whlBx8D"
    "rOPAD0wQfwuRjlJMh1stj2BF9pAWzX6AFsBvG0zgvxumwipMhbUwFa6GSTfnTDDpGlTNq2lzzGzTfWK02g2ShEBqZjmT6O4SGEoR"
    "+XmlAkpHMEoGVapforEnP3/ZQLGrrYgMDcaDsR198f76imNeZMwR4+U0nv3om89fA5tYiRgbUHeZ32hR4Dhl1hSlbmhRX2mIdhTf"
    "1+SwRK+QIcj24E1K22YWKykOqEaLxv7y8UfvrJPjrxkyCQwm49+++vLx/d9ePPjJ3776sxIPuPjtRwjzb71hagX8frxmrq08vIm1"
    "7b/iFYszzfclmiJ26skrDfmBwAt67l0bjKEqu2A23W6HH6XEo09wTSjRurHRYgc24sRIDH95fdPyXfifO+xxuAMhh8vhdn33uyiH"
    "n/nud3WYlQnSXawkmKkjG3jQOZSkG6ckwKoDbNuBFcXsbtywysijwqysXRTAOAZzDpztGQulBKRlbQbjjkLGHW8w7tibN1ndxmVN"
    "5o3tRiRCIQdcN/tAGFroiJVaZ/B1Iy+UeSsqT3axlXfzphVfIBMbXL+eaKWUN6Rgs9lugV6z0hHaUD2plF8dsEH12ZBHi8d7qXLX"
    "oXCAXqSwpgi0fgNBc/PmmLZ2UXO0avZ3ybFNLYHh3XJvjpc3G25VWKjr5IhFt6xjsDsl+UXkYrhsGwC84fb4WOKV4ZC4HZuhAZVV"
    "USBlrEIN3SlNGG7Be76uh8tdaITTunqGjChYnS3zBJHtSGsdejVXfxhZDgiLvps3KcVPeCHiuYW9BmxOXx2X6Zrl1eHVJd3PFKtr"
    "CTK4RzAmJa8OALsBHhPS3JvaM7hF6/AoiYqwXcfoIkcYl4Io1cOAKsPrVn/k5hpI9YRaQ8FOV0AZ3vhoAd0XUC3JJ++A0fomYUqc"
    "TY1hbm64bWtzHwhlJw9xYhjS83aKl2w/OD+7s65f1xX9atuACFUZGA2Fy7PouYwbRiSVVY6WtrJDWBQ1v9R02aFWBh61X3Bdh3+a"
    "l1cjO4oKtBBk26z6LlfWg4SUA+1TuBTxbbZYo+GDqAKVsymDJ4GgCTsWlzbyBq2puiMjG1yVoaurlCHVwplZ7pBBeawQ9Pr0uk1x"
    "i3j8yX9doOg5XpHeJJ6iRgFiRgP4libhT5C2HoIe191w4H3TEA5Y8kjcpMjOZpfssmBM33CfkJTmoCuyxNigIpIGOOc/Tw3JDtJO"
    "88jRCTnVnxW0K4Oi6iJF1dIsinGkwmjSyXZr6uhSEgjHCQM9gBzEizbaPam2pUnDXmTq6Cxf22711NoSI2WhNdBManXlAV7F6alV"
    "1DIKAro2srBat2Cuu1LPRs4PtZvbIM8Nd5GjFjUHHQN/SXi0iV8ge8qMARor6aVesh11NGBWcWzG0WAFR4PrcTT45+HoHxwyCi0N"
    "0BgkqyEstCQEFXSrUg6B0LXpIT+thnVGTkB8DVnof3boun0bdzo/nGjXivbUXgIc+ku4RoaBRjZd2xbqSbtR3AHcUZujwMXbRG/H"
    "lx6T8ciSKZA67GojmEVuiDdvTnlr3EZOIj09FBZ5IbaqY6PwGoer8Et1ichG7kZmoK31Nyhvg5K6gGEJz5reb0y1Cp6ujLetxERR"
    "x9AygTKsCXIXXaGGuwT4X+jTshv4xWaclKlmBtmJmy5184SmbZQdEYo6QntAbszI5XaHCU1sNkXV5rCdmPSMKFnj5A2MFDBaeRhL"
    "Au2chtEdWWMa8SfRWitYkvoDC1pBgPdDER1zIieYNjXmEPKNzdlOnsV4mLD0+sRCQtu5blKvaxrgTRYDUgtk9JqdPMMWSnrW1LAx"
    "ZVzvRdeOPXg00TXfutaaVKtj9D4n14GKzn64YrBovzqhKbQJYUfTMbOtCJpqpNSxagxxfDwm5wYP4xA47zYIrrFG79EIcBlIAsz8"
    "BIE5nwDtsxuJYr6LRQq4qRk0NUG0unt8HMUsqjZQW3LSjOQYjX1qNnLMRGIa/2QiL2RW+Wciw3vMJvitzkAJJsIxN29O9HdXslBG"
    "YSEyx0fasnUXhJscqargPhtfSQpfof5UxkowS86C9tBSCMqKnssOSTZzWu05OI1jVhmqhjmgZmKoDGKozCpDZcwMlVnLUHpzz8ZQ"
    "z0Jk1yysSkZ2OsT0cPNmR7ZSNkeLeyFyHS+00AKKiRkVcoL+EG2BDjUuwuJFmQyZXy7JlNYuceWv5T+JMfaI0ru/sCBGTloziJXy"
    "yrLVRP4nCYTYCSL+55IIwL2IjK/1XrjLFnp9iDLHcrwOQ3mIQm2bc5nUILmtSAuJsCNa45iluJjoVmTtSiuyplqRLoMVWVOtyJOT"
    "zj9oh548fXWOM+2/G+OlOj3rRl3jumVlzA61CpQIJgat5F2ISuhCe8NFXpAdYM1bOWRMlDlsrsi3oe1lZ6WOuTO8LiKiiI2MojgU"
    "jRcjkZhZZh7e4PQFPNVk1jYLG9fwDgUkghmtaSrCwxMciaOOj5eNUYgvbkQi3DLCo23RBWlHYVMI7QBmFcQfwQg3BVLepE90xLKq"
    "vSWQlA2t+IEQ26DQX3AZaStrGO0Bq6c1KRNm3GTRh/Hi3CQDa5Ks8kgJwTBqcMGtJB+qAXxjiO8VvFHnNW0hSE1TVhZT0ELI+3/A"
    "23guv+UOOS3P0n2bFCLccnGR00NjG24t7QRAQ3qMirTVqcdQwngjN26Ijmoyh5YS4QcH2XDyMdvSHmEiwquOKMzSWtnhfetSbhqa"
    "Mvr4+EZL35Ws4F2dp04ElWott0sr8dsMLwt7LDO1HjXxxnyCZyiRkWSQJLc6+kLcPAIm/S47YISxbO2QPrRhdWp+5va7XMaUtyOc"
    "86a9R2M23k+BYclD+rbWQds4fwSxWZKsvI0cqklsvIMebtVBuWAR3Im8gB4cdgBZt9Ws7AlNqltzOkr8BW/Q0UudkOhHWcpS8+QH"
    "kfZyS4ppMwTeSmaIjV/e3HVi22yvJHpolVdTN4y7xbRq/OVq5g0Y+goGsZJhcnk7eYs0p1aKKDSBdpMD2xBkW7MY2kB5isWDNMFy"
    "BQC9R4s04opVw2jSkVcjfooVopv3IrGJ6Vm56xCbCpVqZgVMUQUmijTR/NOjdyZF3tY0VlpRI+1rjQDeiMDDG4AC4Tr9NRRNmS/U"
    "NdpxgpXtJd8ED41Cy3Zkm7UKgBhFk9/GqpzFStyI82fWvlql68xyqiOYaqix3i2Btuo3NryJ6LoVHLTb0NDMDZymxUh4EVk1gK/P"
    "5RmQ1ra+Hez4uK3tFlMvlbRexL7LSPI1VG/Y0qhulFAhR53iDFdSHRzar3fzZvuGxktas30wevqbhkJ6E3scuUyUva3t1bh6XEPN"
    "jKK0rldBWaWt5cY8BYvqBmNVeaxZhNRroIxNdMDF0mecgzSjYBwUT+nPUkPcM8lvelcR8byDX1mNm4O2RYwrSIx5++aUbaFMAbZl"
    "3LZ5RU40F2GRDtLdBYmmhmhiQH6faNJLP/sWjJ0kchpyYBYyPHhkBFTDpj46/ALrKa2oyAyECXN1adAizO1rSFxoUZxFQBvXlc2U"
    "aEw47wcPC0x8XAJFsvMCDAx7PmCQHWnpMjAYTtOZu/iJMibzZlQFB2l0dkFbUPQLOroKX+Bt2DfcZE9oKg9QAqYIXho+gUMpKzKt"
    "zaMTw86b/aFhhTTtQM3eMuZXHoGQRo2u+gAXL+F8+btvKbt/zs9+gS7uvov2VQFTfQJGjJpQrYSGz36kLd+/i/ZjGSj24qX/fPjT"
    "V6EADgPfRynTpx8pC6h4ZRSnRp7oiTooJ5AWxBYpo8VGHqdzomGpVrBiJeGneH+W8almNeAxydpWmK3vKRlPCPJPURa3As/pA20R"
    "95VvHfFItgDKtvBfO87yRVJPPT8B75XGq+rKevpX53fB8PsUY+QVjIl7KKvx9JfGvSvnd84wAt5DOR5Q/vQeaO/zszdxsQ9QFjna"
    "t/Zj/H+0iPy3r768eOkuyiJ95Uu8ae/PKDPkta8uLx9/7//iPJ3UQUwszTXMuApZHR8vwE6lhqxTGDp5RgY/V+4yvJUxlLAqFxGG"
    "7KvZKiBDUMYkeC+4KXSsjw9teaCkOU9bdDJuIDKWxbnaUoRCZxtYVjsklbdgMzdB96SVXyv+jSxfoWL4Df5BOxVkZS/ymOdRzO3m"
    "zX0OGFOBCvwZtcsjRhQFkH6OASNJVIc5OdHGcLICbI+1KknMaQfiWdQC+o3ccOnDvqWMBXh77VCcOA1FyfY3wIGKXwZDa92tt36y"
    "lMloKGYLOu3AcgNhAV8Y9qBoRfB48HwgMDXpsRZQwCBhu6WgmEF/FXiP0KLO9Wi2HWngkghIlXdPlF7QfF8xTS1VUS/B7bFkCHyG"
    "E7xZZjn0Ari20AeWyyijGIyvNPKVBzgZmVTQiS91QFC3CtWi0aN51EQyT2G3R2/PVM8gb/fG1iPJlBLLOIQ+WkZzqdvc1VvwKQEJ"
    "KIWHeOp2AtQQWNDPEgLj2fUBMH2XP97ar9zibeIzQt3WagqOqSBcZWkbNoJjJ+kp27PXndej1kR5Vud37mCzBmha6qi70tBJ9ywv"
    "X5PCxptS9Ii/vvwjvJMP1VLqi9QU5frDzw3kEEPbuvF8uTHRouTZGOCDitoKs4GfxlbdgkEJRwo5YAMSCMywdck6Z0ndGuIpxQYC"
    "CYCynKCosCZQqWY4LTtLdKymNFZNg6P0cpzp1FKCpTjfHBSmrjvFCGYakkM6VESBgMvsRx6ypGDar6ZwB7ygSHplI5sxbOC6ImbA"
    "IlZF4Gm/OniGhTSyFznCGUgvyl0WL8fpNzcQV2iHeI8dygU+fAGX0criJ9A9KoN+8P0QZnIKI4dn2qXynGFE1Av+xU94QeIYZgjP"
    "1CulWxAnL+qN3LiBlgmXD2Dy2ix+ii5IFNYQWVrGT7QbkuqIDIMigrdUKdMjBWsP+3VXmLrjSA+ue5dMXWsPpksYZgYDpsUC/kui"
    "MKQ6FCIJlOFGIan0PKbwGGdTPIc1jCvgrYV6VIUFEjPM2w2XNlH69PCr02OcFn0qDDMAbZix7lbx7DZg2L3EKzmMjHXcARk5HI42"
    "iRZCVzFODtQ8tecwHclOpH2JFudogzqrBmBREvo0grUGWYisU5Hj9SoSBjkeomTRJfqMXWmIbKsUr6JTLaKgso0pfYnOtk7lKlrb"
    "CoXruG1r1G1GcXsNWbdXiLqtk/SJptjHWJgMrUf6XNhIk/JWjZSx7ahpHWuWCRlE6viE7BqQBXKC+s5yQyoIBsP2VLsfKpjDe8sY"
    "JKlfrjFY8NZYJKb87mXw8AQ9ufXU6RlDY9jSMg32mYf3VOXd4joW6Ad+ninxDMptdK8uac44vmwRdD1GJQuOzBuKl3J+9zMcE1Hd"
    "H+wzKIb/78FVANdmnQeBPJ6vcSEo/WkpbtF9CkNS8HAFfkaizWdIPI+n8ik+2+M3KHUIbaN4HSXR/uZrnC6m+VTLAvo+3Ps4Lemz"
    "9Q7N6af66SiqN7Pi4nx4Dx96pbZPmFPKrsxpU/KVeQkr+GUCG2j69fsGZghlxJN3AKB/g7FpW1vxySCCfirOKjbhpckmwYWvy3jj"
    "JfOmzGsNurVHWJl3mmie8wPlVC/DvDfXpSkbQKWFwXAsY/2Mjvlam6n3nOBkSphqXj2/+x/nZ/9DPD1rWq9qkOP60Rd3CBuG7W0V"
    "NrylHQUB/nk4wxT4zDjDvZ8oW2jQZgCcEYiPrnjmZPE+cW1w2xwoPQRYv0RMpoJrPofvU3xqH94Yf/eHgG7EvGhL/G9Xdj0hvsUn"
    "7JgCBeT8KT4BTMCZQlPnpx+vOdRHY2ptl7j0DLN8SKB0d+ibJNCPrKjQ25oVbwjX/h+Y26dhm1COQDREVPRYkZIbuZrN2vWaICT+"
    "+sOfW8xTtIzrEE/PwZUGmsiqoNMOWYlqckxrU4ke6PILfGm9S+XVFqFEjNTj+pBEByH88jef37n44iP1+E8F8OnWVBFQW88izKaa"
    "MIMrvA1f242n3eIsiTHZWxrMcVDOYKwOJUcbTABrNPJCVPOmbWQ1Er95M+7gGaaFD0IDww/l3DvQ4MlZ5EYc3Si1cQoOrt1XUskl"
    "dII3su2g0qFSBWUPYduL17wMTEwGm5Y3uhrKy6daA9tWwH+LIONb+KylzRk+zqUjCC3i2Ra2pFZ3Xbq3kVLGumf9rNJxjEXNdRXw"
    "QYrLzcVbhEENG/J70XiW8cXlY6KYVWlEmwI8uVFyVz84aW8Mxs1m9AQewVxq+jAHPjGajU11HlmelTcnpDQeDgURnR6KjrLS73BS"
    "CDgASzZfoUAUHNCX4AaU2GH5XWG46ToxCUUTj90zs+3KCUVoeCAYjVuC/vryj87v3DNICm2r7X1Tw3fQ/tB1G4EMQuYeQa6bYGKd"
    "EYXEs9a+CubZ6xenf1CNNQLNFo45KwkJlr/+8EMw5z4GyPX+wNZSR4n2uhoC0O8p+4SheDGLk8CxoaSL0yvQfIUcWTmIDWQK1iyr"
    "Vh06uectdHKsGx+7AlB+glXV69gw/DHWDyun3KGkC0Wda2gzi1ACj3mNhbhcCsBmMmDxp8jwvft7FXlGGrvWUruWstSJffjJB4/v"
    "/hlpNu1YQR273/z56xVTdMVgUuT3Nvi6xk2wHSxEwOFTBNQziBEcXpYstMCtwKx8v8A3nBEnf//mUJFqsSBeeFVi5YUWo21/JNzL"
    "LZmd5S5I5L+hY0CMAYa1yXrXCj6jel7ZiafNNCJsQjWxnsEBwo4JcisucRa8RL7Iv2Nx8DP892P3xfs/W253Jv+JWHMtsXbjerS5"
    "/yG06Ytj7ypMqKPK5AYu0WIwH89+pOwhUon5ztmjBx8+eutlfAaKflDlZxc/+MIgNzVUXbuHpyOyLc8a1nJ7jCTaebYQ9CpCCCNh"
    "mM5/vz5JRBKF6Ro9bJ5RZRO4xrMotmPauq4oYWWG9eCPmhXDUK05WivQIqhocx4pDRmOiyM6QHExnQrGmAj0uKlxC/Ez7c7SQCyx"
    "aMlJMwSfJcA1xDWOkLmGGfaWYkjcvGmERzEt1odQ/EqEyDAdb549eulj3V+8JtkBhJ4yd2gLK9rF+/nDV1/X7XJlX+s/dQarinTV"
    "5kuJzulUOcNf+tj0eEDiXztPWiz70jR1rkszWnXc0GqHyXlTjyizENe6mspIarwpQoN9JrvV5LFrIgGdnYjfqgNWdwJDiSWebaqQ"
    "0J9gx/ETFbCPwV24eOseinogl/LdpbK+fn7VDh69fR8J5LNPz88+UhbS/9nzWpMQX2rTiuOsq7Pq9j9tVtX1iKt479LgFJdaDcrd"
    "fXXNcRKXAS3BIJeA6kHc5wfWsFjyNICvcWavmGBVw143s4qi0DkWqOy6jldn9Ol4QpHwayStEik3nc2Bt8rno5nCRilOWmLReLZW"
    "2sA2tRaieN0cewL99vhXP8Dn5X+GM0GAMn92ce+Li1d+oB0kef0UqOtSq/i/hIhriX2NO7Piy1y89GvlLGVsFJnSWVAUVM+LefTe"
    "l0/u/ZeSFHKl0/EDNHB0JPArioGE5ntdRozib9y5B+grxQGBgA4QVg8Isq0vES2lByqJT4v48091Ux6nzugWl+YuYKPr9N7jt8B4"
    "/hDvHb6vHcH9CQLlzimmp48xeX0fVVq2oW9cxXY1krXEo0++ePgf31fp1+wIYAFmrqIKq+uOm7zSqL5srfxDJ5uAKkIrO0uTcLnY"
    "s0Jly7VO8+kmmM6IJ+9/+fCLtwwxd4wMjOgn7/xYjacvfUMsr36Dp/pdnIf0vvahiFeMr3CA8DMDcyu6SXNtlgdnqiqA/Edxwcil"
    "qREXphWuVeVrXAxbjxVFlGls/2BF+WCf8z2Mp0+NZz1pqw8mqa6dgfLg4uWXLh78D1qJ+NWrCAvIuX5laR8j5+O352e/U7wRNcK6"
    "2u9nBufQYD3/o+irqGt9RgzqS9or2NOXCNdjziBOVLFzhrc+AOmgqAPeJHHn3iXhj8/hVcwXxQ3+9Ml7bykoWpG5p/cQ/s7e1LC+"
    "EjJ4E4c4jCLkCqflx2aPBV2CBLiPvg2giktTut0/CdN1ts0asYxXXVcwjBdk12O3zm5ssxazuFLCNEATr2GifA8vaC3jbthD/SPG"
    "08tAQMia+u+f5KIF3UUzfOAAGl8rCb754gt1ds7OcJT+FYwdpZOXTZxslI/PEnnbJELDGfqApOnUmlUeQkec/UIJzmDlgZcJEbOp"
    "S2mnH6DTxn7+BxjXxVs/VOIo2kqhah+jMZzpC4dvXV4TxVUUcbc8WU352MMrv9YXQAwwfbr+TB+jG8vIFIuO2DKbMnQXfaRviJLk"
    "XWvSucYDQM38Cudc/zASmnZFpKAe9dR6YsytzdniWPM6ghp2WgbCkKj5CHu+X+FvLHx6tRFgoKEH6ORjxe67vMj88ksmvwR/lEiL"
    "Jdy5d0k7aBT5Bur87un52cdqLAah+QOTiD3990v1cCB1zdIvdFbNx9Dbu19iQwQREz5qDR4MWb5jwSHP/7x48zMFqY8/evPi1R8Y"
    "Dm7SGAxkM4oKIP2Gmrlzr1q3FKJVS7GUrER3ixUEORDcGsJ68Oj+gycf/gxFhIGI7r6jf0/hb1+9iRTp3U+0JGFsQt3BQRJFS6yV"
    "9KvTSayNZ6JTqFGDP1bW7ar4e5cw6Log9lEmGEouW666w3jxByLQQtwf/xtf4HDI2SuYxZdG/RUgXOWpaVadWdspvIalzMP3Hjy5"
    "85M12u7OmdeFT1n82GA3mOQ7npXlOpQWpr5/8eWfzk9/j/t8FcsAo7IGYv2dQkC4kb/gxl/GM7fUv4/e/vLJv/8C27Zn2tmPStRf"
    "c1yvRIRhJ+Ay9IhQgDPDl7E1jYwvKflPH/8GlP/XyiHlyPvAHI9F3oOH9z/BivFH+EC6H147I9fZalex150zxSBUnYT3znTmurqf"
    "y8r8spNh0Lj6l3SQpf37Hzz8+VdqMbMD8uyehpHCFORrBvw9gyh/GU/dm1it/dI4YOWUd41Z3sKewqf4KzIaMEYeNC8gj9eaAP/H"
    "8aNKpOeF/ErhsQ7Td07NEKuEazra53Pc/XVTck2vq6vo2AK+QhuhHKQVLlEcvlUxuZJh8iz2R+Cy/YGP91vdh3H6Mb5+Xxc9Gk9/"
    "sB4Fd780zMMH5gk/e/inV/QwGBY9RrTeN+xd+8xQUjPnwBBGJ4Z+rZq0nz3++m1oBrsqn67dK6ItMiKPV5Em6kcaX/vTw5deV7CI"
    "jYoHmDF+j2TQ/X8z0BCCEbSoG8/Rihn0G1zowTKl7Oy/cAFlT4zisXzfCP+jP957cvoviiZftz7wQDmHG/kAymICooRf4nl/FV1f"
    "IZQNDvolI31JAlyTs/ASTmF8aoBw1XiParU06x03s2q+K+mR6+13syf4sZnt9cQ0o4lH3L4+0asp89IzHv02FFnd4UOn2evZH8aV"
    "zeNj7vj4hmFoeB2gYDh5GSWSUzg1HaVNKHmtW8TFgw+Uw95xekhni7hyQfmVdXN+T1sTUldwTeyCFs2fJmQGyw8CX5n8onx1fRkA"
    "RymfVyFBH3r3yqHjnFG0AKHLidU1bWKTemGZ2bpFrDdWTPVx3tSmsVH0MTY1LW3YopaLz8+0RIC+wfn+z3Ti2rQQZBXcd75j1Zuz"
    "4e8eUTRjJXYJEp3EslyPE6/beiGhbT+k6VNY0lWun2HvAU74IY6PDY9oiqcZmATAJlpBf6YUDdwbOllFVJJJDB8QU9KFjBklY5QR"
    "go4Yv7SB6DpFYRya0N8i1K17qvWJrSaQOcjiu/Pk7n2zibE8IQ+bnqgwkP5ffwri+MGTn7/06P0Hpl146+X1ZUZDFAiYmsAotsyJ"
    "e4YIvGayG3TB60raB84eO32A8j0u5W8pOm4l9RZe4cqnaxxd/dMspr0xuY5VSdZhlDwd3pCnox+8cSiSnGlzCb9mJwrK56IitJ74"
    "1cLZ/iLK9qdRtj/O02JuR1okZ23ZTp5hAxVOB1NXV9E1XvjcZMirvydhzFS8R5CMEqi+ZLQbXbN1axLGAPFYW4QQ1Xx+4xrE+d2P"
    "sOb/E0oQQoHxKxYQACuUuuBEX7l+8zRIhp4lKMutBGZwzCtU14OjB1Xp51p/xnppOSloQpZSWT4+ZtcsRwvWG6a0fvqKHZR4wjV6"
    "xOgSV3ZRLId+YrvVtFo12PVMRGLFVjdb14ix0Qd2l9UMnwjCX4SAFrHIWzZ4fueO1sjHayWF0qBaa017Up8dDpEi0C+NbaO62mND"
    "ZTthwT63IjM+vtI4XX6/AIX1NPt6NdntCh/l7s9w/AMo+PPzu79UVl2ukXLK3vkwSgBQUgNolBpA66kBAfRGwJJgucEV7cg8WZuP"
    "a3AgT01Zqer+zaZybA06BgafKN2WIoTh88BFfCwSPusS3vDoOGd02LAwPD4+YniVIN0kOl0HbWHCJ1aiC5ypunl4G33Z8sVBcygh"
    "RcXoX5wy7jnSnkUO1QNmlovsJMqRQM3pXblObtvItoS/uKo3htNW0fcjFDUu4tQK5XAxZVnehj8xqpU/dN3GJSJt/FEmePxiC++M"
    "UopQc9MOKP0AcEY9Nx3rUxDW6GA3B4tyXP8fws7ZblkVkFAhMBfl5VHZ+uMlHPg0IhkAwVAuNUVMP7f9kFn5aB4+WYfEX6wxPkbE"
    "gr+0ufpQwPNqYP4hxYra3nN+ZXM5Ovrg0mY8wbrc5rbme3yCsiH9qm/wtdVv8K39YhWlbn1qR6BztP0J1As1YQij/Bpell94CKRO"
    "eIxDvcKbveAW/ZC0gA7VOD6eCGzL4kKqsQ0D5K1DMHYwZprWoVZxi3hy55cP3/oC2c1f//vFb//NKMOAE/W3D3/7C6zxtVcacw4R"
    "cw7NW59Y1Atwo3F7l5VoT9XR8da143JCAbSsjeAjro5BP1DjsqZD9FehaiOo2jpUIQNUrQijHGAizm7eNH8BcUN/8x23/5m+9Lo+"
    "m3R9xuB95aQmtIqHVtj//fzsDWXJ7+otU2tjEygPM2TOwySMGYsoVLCu/wfffP7hw3eQi2n0vVBxcLlf/YHyCqzAh//xobo0cvo5"
    "TvX9PgrM67BrUV9lcd4cKDxVLEi1Nc32xE19urIGh785jFcBkc9/T8kaUQ9SQ/pU6w5FTNC1+hFFdYHlA6SvkNH1c31dR4l9WZRo"
    "1+OPPzKmnyu2s+fizd9hv1GDS/smhray+8rj+3ce//DZVnGuSEZEbiQi5iojX3NMvEFNrSWD1XLXxy6eM2aBwCvyhrzRG0sxohtv"
    "bfSpUWRaM7rqaT9lbVeJyL9M3L42v2ldcs81+ahXJfOgQaB0nuXXU7DoMxmqeraORf8KuMXwxQsPsXa4WJK2LxurxLX7jVadQ2Pq"
    "rOIlgDDCjsJTs9s0MnwaPVyPnLghS1g24QWl87WYF0GT4cMLFWGgstedMz0RQVtbQxymr9or5lng4Ts/uPjtu998+WsUu9IY62PN"
    "0zzDKT1G3IpWM0KfLZ9JlXtg9wP4c/Q1awZIuEMNN0Mkuq6LcElM4S9x8pzRLsyiSN8avIobnOnMWspqM34J3qwlCbzPubrlECTk"
    "h4NxQFyONWkdbU+v6IZefvf70rLng0cf/BpfvI+Cf2+COPqhvryjOvN3TvV9Alev2C615Z9+b0iyfErADSbVjWNE2kIPuW5d8Wmq"
    "eWV35zppgIPNawSBPkkm97SF9zOsxLN06bWlWzPK93vxx75nL7ZFYYD9HPxBnv98TU0B00JyCklfmoFLBfFKAkqGBRdM/5Y4XKvH"
    "eRqqo6jLcjMfynBR9e5zGjWXHCPw9bCM/eUqWCBd2lP9HBdw99CHK6/oTOlJ4fcrwjWZpxjha41lgzWHzpCQGSc+POYKe/sa01iO"
    "EF1ZHm46nW5PEAQ1iOpNhGsUL7IrfagdEKQYOTxUPglKEma75RUNQUqSx49WrAi8dE4eolMaQZETbiikBlbRU6mLEksJg9GjtoID"
    "H8rC/KvL+LOaWfgmrouO5ltTF7gMPzGuyuuJRkpFdSPAmqorC8eGSih2OZZQrqQ2XIWlEE0abCgDbtT92sDhO9ViAePh9j9g64LL"
    "yVADSwJMAugHfaOO4pUkAsRFD3/8xjd//inxnKtvayzcQ8LYNEoXS6GjSVjakt7dLYFaVTbXpZK7aq6Itp2tVsnhXT5a+pa2gQvl"
    "or36X2Ak4o+UfGRIAX3aBiI8MWhw6u45JCKN+7MA9UZYPzPm6aAMiteviu2mortJNDg1z0Cd5+/rSa6aRv4UN2NOQb3yeEKDXapw"
    "TU00fd9PVD8Eizzo5X5aISLbOTuxhQ6gQbwHvys0UnqezTTs8yj3AElxbIfPyMxAAtuVwcfCkwOWV7LYXWt0PY2NnWf8NpowYcQ2"
    "J0wR8bVaDPr8EAiQov6U4Th2KLGApGmXlZnqEEwntIlu1dAQnuUwCLy52mhW9CWrYDhJDFxdhULNac26P0uqhdZlLJvCg4TNdsX5"
    "ErQwnCukqrWhy3x0uuXqWZ27Hav5M8LrvB1hqJ5d89QNZJ9hk/BUY8nXFNZ58nO0FmH56w9/fn7np3/94S8sRh4FH1SxsvDqw/M6"
    "YhQnPx2sNQ6yys1oHdlSiiYSxXjWonCkUXzomW3aespyDHhPwNKvVPOnTJv6TaMw7xFUtvVC+ziBA+EIpV6hDa4P1uViIAn4+D/e"
    "Rw7z78HZfg9Lvc8vEdF7ONMeO9cvK0vy67LCPvvm8zfwOSiKH/3qctVcjZE2xtpHrY+WwUA9vIf2AdmOj53/32F044DaWNzedDpk"
    "RpKtjG0LvdsknMTyA+bawqLz8Lvfdd62f8tJogC2bOdPyBdZJWJkYSIvrMSIcFxV2sJhw5s4dknYkwz0YLMpXwmSyJ3IkRaFbbGi"
    "pJx7Ko2bm0cnJLbTCMNpfDus9YhG4f/hJk8OKVE2HQCPQpS31LuCOe6pfZpPi3uObbcKS1SISpjz+Fi9ihTUECcpKmCiQPKJdp6t"
    "1jA6swB/WMNqLZBdaN5a0NuH20hEbZZkI+hrE1tqvUPutjJIIcJusQ4tVHzpkDY1cEq2Vo9uaysHtlsLkRcKdvcVh7cJx8cyOsUO"
    "g09oJ76jSHkhcsOlzeu6ecIzxG4pQ0FrDYaJE2yqEOxCN4WbN2mr8i2JrjabyowpcXXhZHkY6Er5w9u4ZFcP9S0rYNF5BEC60UHw"
    "wu01p62h8Yko+H18/GzjtJoOrNrB8wCVhJs31ZuIQO44EPkp50DuOIAA0efFdpCrgCafvKG8t6FIqFpUIfUX0RnfavyyaztSaiwH"
    "BoNuLw/DRJADja3G6jUS7kaUprXv0YwjL8x569gG9XGdCPp6o7I61N1Ui2rfFvDZlCVzqGNVFyTG6rrGGOxvkJM29SzOEnhWrMQ4"
    "KI6zmoBB1RVO7hrOtFPn1vBRBWAO5EuMb968gTF1OL6t4kW5WWKmMbYKwHkafnq2ZRl07ulmb3nqKYogo2kFcGBaTXDhdRL8/Ug8"
    "LsxZ6GMsaFkCX0WMxQG6LaUgpl80A9Y2OmcPH05rXSEwTEekoJ+MN4wU0Ft0XpxCY7gPtNBSQC3hL50qX7L3bVnVy4j6a3eTrOPF"
    "5ngwREfDgvrHKa+rnxR3P3zwx4tfvKuFa9DKHM7Qu/zVWry94if/cvGfv1KithbCrvVEWAy7L7EhgRfYbJs3NCAxHAD8CowbbrLF"
    "oO9RW9QiCM6/p3NDlovSP9r7+7+pe/PuNo4rb/j/+RRgj4YPOmxBpOxkMmAgHG12FoV2TClKwnAkEGiALQJouNEEwZB4D0nZjmzJ"
    "I8ex5fEycZzYpmLFlDNJHMfycs7zUSKTtP7KV3jvUlVd1d1YKGsy73uOLQKN7upabt266++KWXYahWhBnJpwKDCTVHTVmJuZdy4V"
    "lhPkJUhar5VB5CZWH1i5YMqLSNfOoiLDRZ0MF+NkuKjIcNaO7iEynI3IUALTyBumL42PHw+C0mrOa9Pf7EkbYWnU2XEJqdDo0cQl"
    "moYewg2mjHla3ryctrGogUUcVEPVgbmkAeZcSnvImRX9PQn9BdKFnXkSZiXl3qn5+HBmof+z0XAWbcKr5B6e5N5Q8XEc0EqhhAVf"
    "RE0Sv1jiGhRpdgUsOBPxZdjRKxgmRDxbnKl02iY4oVGaZKawksPzQqshC/wQFhIOb1l/Rn762tFj8m75U7aFoQVI4FwcOUbgpGne"
    "Su5RskHNKMb6EDPG07bhgc/K9x57qGgxjhKelQweLr3uOyIwcOMaveUlDoUk8fBqhDvDTpn4dkaXHNpbVuAEpAK5pUrHsr+CdysS"
    "Mnfubby5+/G7ozhGhvtCuC2azufuvfrCwb0DzeXGggzl81vfX8By4Q1MfEUffH7KfcjBoLD8lIpvka759fXJyFyNXDv6qfB9EFnw"
    "G6wfLKVuxMayx0TN5Bz4/okj+9svwopPZgqZ3SsfYkQ+hcGm4H60hvkOtBne+wOZZDF1+MruzrO7T98UEbmcXZXECMKw6ARaG6he"
    "7OwSdYk4d8WoBP/3T64n6xixEsNqzd721b0rL5Cfx0jITe1DHzMKKTe3SOPY2L3yc05n+PKzT8goF4VrUzoQZjxsbWiJPFtYsebz"
    "t9gwllJzCROu1cS9fnfzNdamSOlkC525V3RLHMcPo9fwmh6WPML8bvcZ6uAXGva5COUS5uU5nhQDJovTprckRuSzslUysd34gO59"
    "av9ZXO3dvwB1vLL3uokXlDYM8843917ZphZum8PD0/uCfivZDs169sD7dq7qYeH9jGixlk1TKAW1vyoRnG4nKgQzVcCC7m7+CQPv"
    "8XYKQtra0l/fFzwrsXD7f7l57/VnhD/ZIIbbTDn0omt7r/+J5pijyjFZhrJtnktdKtMcd6KmgTJ+h77Mc6wJMWIKxrFspWgGKjzn"
    "IAbZUS2qU5OxoAHejGIjsZlBJBhcI4PHc/3LUnyUtv3wVFL5YklTBG7gK/+198abuxtvx3LIR7dxGC8Ubv/9p94ivxgmcan360xK"
    "ZHylRkWYqYO3FCxCzAa0eU2aY/SRvWoczmJuohxnCS8bp2XdhKUDeFVQ6DBssxreIRse+qMDExYGR0x6FmhsI7nS+f4lkDlEaAEf"
    "jUI/Mt3p7DfAHBfExFARJ3QKqdMTJUypXV0yjkt5VI7UGzQUGHGpoC1kdLCORcZA1Tu4DFtqspiSufTTn+pUBK2fypuXMpkjmQyC"
    "3XBS7+Mn4ROZxmJPxodJ5oyBoxwArTQITunSMDilSwJOKas6QdNBOpPSkBeyl0bDU7r/BPZoxYQPNgorWUwGlfCsicvRxIknlCyF"
    "+B/P/VX3agxP39BN7Gty36C6ApL3sjMl1A5t+M+CjPk2eafJrHAQB1UCGDIwYjq/9XCUQjAEWmvh1PFKpU/nucilCAhNDQSND8qw"
    "+rfqy23T6o+HnvQvwy4+N3siAu3Gucag0hlUg/BVoHHh99EQwhZOnXKrsWHMyAjT+MwP259Gisuo8zjjhierNbMLWOWlz+RgRQ6C"
    "9BD73TSdv6p8bVjbk6sjgbgkctmexT0TOc2Hl3SVVl5hbxtdUTIfPDZ1v0B2CZV1eGRR2627CP2xxrrUEz4WKJRqE/Yqri+RfatF"
    "QdnS8m3yxcj+7QgT5Ny8YSo1ycSwubPtQ3TNb6EBH7rG3dEs5dHTM9Jsx1TYI5ONPTgUJabT01n/i70bfx2MKqZD+zwYWEy/daqR"
    "Cu8oDIwmxCNMOBEyrXEGwd9Y0aOPMQ2PrrHgZn1VGEqjl1N6MGF6Nyfj3dx75R3YXaeO/xjzR+HPUYJ7fTY+BAaBHWz00DRsennx"
    "vraJ9g4BzDuKBSIS3mBGgKo1KiADfrEvellM66e7e7YwxisuESK3j/te4WKKQSXk2u7JqNEwSOs5Cljx4e/04RKxe1le5ieUlzI2"
    "Z+IhUQ1SXVvwKwaKSUPf4cq6OZNqm7yUcj3FxOtIm+symjOzPKHC/k8329PocNBMlctkuaQDd1ma77uFuLG2eFI+n59TCtolaKlr"
    "2nC73NKliHhoAZRovpiydKnrpphwJGVV5Z5bjnZYp3CsBtpBx4ywTL4kxjgtPaYP9tg9zNz/UIACzNKydPox3Y5ez74DfLtjx9Z5"
    "1AF15IAuGQNafdAD6hoDag8a0RwOyUma6sc0W33HpthZBBh646ZWo8AIOefoOpwbB43oyRbj44iCRDUIoJPMGIZN74GF5IYUjxcH"
    "icckIC/KwzM/KjezGK6ELXsiAbxnPwAQhpEF69JqqmhNgkcul2s4kWgtc7Z68yMJ1Mj3pBxN5ygGXE4RBewIaBpha32RSZBTLFRi"
    "Lt1zS2UhKEA5ibl1TSHSKGMGm2NSAr7a9w2n9dWQBumwO+UF0cFPc3sBWC0XyIqJh+K3SCiM63wxm3WqLwWFBQOcKALQIWFNIiNY"
    "MeSzESBlVfQkvHiUYz8mH8NkROIx+Z0tK2UK4jKxSW0N6ZzCcAwWYNlhNNNf9mUzTVzu7Tny+YHArfE9C2SsrDoS62hn9y/vMkBF"
    "BqY/Q7GTNxTuG4OaChOyMEtzNdhYVZWDiWL9ZYrR1JUfkqtQLQjt7/hysDYycEFWRhIkRziFRJieGcyNZVHYyzh4jfWjdga6N0OY"
    "BdR9OFREE1oAEv1iRyaIWHtyOvTjTj7kjHCmUTkXPJJGPL5W1PGVTx9gokPKq9vvEDGJayQOaFRbYBaTYdyD7RSP7qAo/Cs6Apzk"
    "7Gz4jfH9v+rGZ1PRoRBmhcgwULkR3dvaghdpvXpT4uGIVxueYQqzMPtwJTWCJHnS0FN/NDwpNOUsFD8WFLQqla5Mir1w4ezxc098"
    "58IFFeWH5VXLfgB/8fTwqxn+CnTa8ZfcQsGSgXhW0fiFwgB68RrPT9S0UuWPBVnyoLgUomEGIgUYWDjnAkOoexX3AsIpckXTprsi"
    "b8o2YatFBQKbzkOTkyC9Srtpk9/k193cSiloxptymnBexbr3s2HdMzp0oVry0FBqy3rI8eYeSWsulimBbfP3sTH1jhpi2HrNpta4"
    "9kziPd+vYe1oWYxYvag55EU4JdGLsJItFjVOe1+8GrgxJiQRs8vxBJFJVdzWLSA+bwjz385HSfeTlGNP4Z4LIMdx3kVjuR56aOBb"
    "gd9A3qFbmKjUwMNSFOGsZa3g4hyR79FrlLtuTl4uRB8d1yVLbYH/RCWf4wOJTfuTLobSOqETcClwSiOr++VSXU78QtaSFTN2dEcZ"
    "+a1eQfi+rRfNTAIJgb1NT3yuQ1RblKTujE1NR/SI+2laBqEmcrFxHmBdKZDSdWqBTzGyAcjKIck1i/5KHjj6tOpttp5bWSyRR1Pk"
    "sBSttIyVWNrVFWuiTlNHwS5WPmqF0m+K1sBkG6MxxMao59AyNWElG7YO+IA9ASNqtGvFi/90cYI+ESIFX/tX96H8QzSjk4Jj1CNi"
    "gnl1FvBhLe/cwfDA8+PjWSQ7p1XLykhq2tURPUm/CPptLJw1hAS9RXby9yQo47akC+GjTlaXiry5xuTJEiycs731HifAJM83jhaS"
    "QaaCVNHroPUTdhsQuSSgb9cKsEdSxoFHgN/if3OtwG0X1accb8+8jrNxrpZde4TKo2tlrZsFrWEsY817TfRvrCnftb4+5uaIUukT"
    "gnOMhVrJ7fQUhgUvtfBqmmoJt2ZqvqlO4uywLVy8GyeKaddWiZ1pOV8D6fr5CMVU845HzgmUvM2EzJiWWlq1Dl7nJ61HRjONUt1U"
    "EkOhe1jJ7qXU7ukzp6NMKPH1wRMam7jH/RU3eNwHMVArS9tnvqj1A8/XoFQ+TVmJT1ozR8cTVRbkA6poHQUxWyRSUx223c+uiQRU"
    "0PkFKOkdTKvPJ26NGWtTEjm/pzbVA99PQ0CbfB+tlSKjUaydqHIWxZsYR0QsHkSSFHFnQWwiKhJnJ3O626qD3BhkYhtnJJLifvXz"
    "DoqfOWgoJfFSFGEV9C+UIiEhn68V5qxcqxWicxz+tsXfsCG+i7+h+GrNO08uF9a+7ZYqKUulLU5mAIttRu6CRROgTOtwM9Zhloqc"
    "k269Tm92EJdNvT6ijT7HlEYYhsAItzdz8CvQ+pIRZCqslj3J24NCM1fGzsO/wE28ynwx+jg3OY+CXb0QiKzm9XX65Fa8EGRF8Q3W"
    "yXK8ArywBUo0nsVHfpqb+/ccpRXZ6+tzlkVR/LnQP4M84WQJxH8EBjpfizRmDwHl6pRYTrSWfbw5F8zjw5FN6jOg17e4rQnLrEFy"
    "TQIAojJI0/2LKK88Dj9HMyA008HJhXNDjbqww4y9RuJvpILXzV0XO0YUt5ooRWgEKKLn2qHfAk2pVaoRGDhMV3IPwXxLvqzr1RED"
    "9IeV+M0MKkv7SFYfojhQtaFydnbaUAdnZ9//WLkPRhRDnxNTcOAeJQ41A3JtR0LOD2qUdaYQD0ENMHKykGXBQwREEm059GsWPC03"
    "F39vIq6T15uG230nxMwh2C0axhc7vIRFER72YFuNjwuAMC8JEJaOlMj2tMdAI0gHtImFhg+WPmM4R/0tNA8U7sb3dbCbZjIqyUN8"
    "EqVWeqkoNwqYKF0wv3yHb1BWUwLTTKEQkNPhJ8mVP+XAwf7SxC9SwPbnDT/K6EUR0/Km+xTgihKFh0MSmaZX/xRKNcLy2mTFODbR"
    "pJF7MXydgzn32FoVE5FjOUeaP0FYW+tkaPX6ugBxh2j98KLzEk5PT6u5Pt9z8N6YyzMloCRVh4vwsv7hkSX+qQUV4ikOjGhfgFpH"
    "GjxdNsI3cNGUhYX3wwABuJ8A/pUjToze8xmQ6D1fTu09/TSg94MPj/iodmSA2IMemJSZkwsjfkhfGimyasyqj+gqBecRvGIp87R5"
    "TddCojJX/3ha/j6qUmrahD6lTRupWmMDJi5mKuQApT7alz6BejIEZUxci54SoEFig2PhE8zz/x2WpUMsp6uYzbO1KV1lXE9JlrAx"
    "024eAFmZM5QkLKWMDpkhg7j6kRWOEoPeXxSlUzavIpy1cCh8mF7Rd1geVMwKOhyaJZ75lBTTeU01ihawD6IylEwX2onlg2gapsC6"
    "ZV8PZYjsfPHpG3vvvE9AiZuYo4Q4XdvkO9UzbG7tfvqHe29+jsbbn1ORArPkna5WMGhPTP9QTEf25yqmOG3eioDCBqT7pAUBY1Cr"
    "qCoQL6aUBsEhfL4KIVyuzk1Vuy2ab0pD1NHEJJ5EzBj+KPo6yOsQ2GsxfwHZS785OanMkdJ/kGqxjiz3DrQ1PZrNXgjoTr83i1ee"
    "Kawtuasog4RBaZUxFy75C/yh5dfr+UkCkqCmQJ5uoXPC7ZbrefQ7geTsLAqsgsAVuBSIM/pdaMKiFEUXMSqUi4NuQHWH4r7dZmXW"
    "rfPFar0kf8ePJ5bbqwg+3F0M+OJyeyG/JiPFWyXYHuz8AN0ewXSgA2036lQl8DouXu31nB83CwoR4QzC/aQAc7kF+gVU54rbfaya"
    "tdYtuTbsLeCfZbqrawvngX7ZnZjCPISlMr1ubCx7JodGpjM5mM/xcfoT4fEHy03Q/H7GXZP+lUib+qHuKFvKzZ4+4zQL5Hqk9wqY"
    "jAno5oS4hBbnJpwJ1KPx8Sz9LTSdMzlcWKaFMzlcuYKcpDNY9FD+gsuIccvUTxG2DM2sBEAvK2XQohIEjj+pPv64GXPmKTM3dSSC"
    "/mWQ4yTIwtzPshcZAK17BHvMOBuH1k5LtdXujdNA5TX6YvcuwixGT+Io/OAAD89Tr6mPMHnSQTgtZi2UExPkiMxQ8xSukdBe4ymG"
    "p2i66YE1FCSJGtHDmp9bq3fy1gLGrqKrJVQp9PNO6Icl2FzAN36GoRnxuS3j3CLmsty8Z3K4G5XfcOiEo5IeFpSjMywo1Bk1WbDQ"
    "o08URqEuSL9u2pRJ01d/eueZRvIKucCHuRvWcCIcHqeGSS0nYKXsPKxxTEw0NNoQFS7QxkbbQLCh8fEAV0p8K+DPTphbguapEoff"
    "gJ1Hj8FeAJmAlhK3hbwAHUIuNtecL0SIyvGdVMbsJGiWIeyxNQMCf3x8IasuaSnzHNebOZIBVoDOKYeXCDeWHGYwPp5GH+0Sudq0"
    "vCptgfEXWq5pOdvR+IF50jQjgUWUjN0zYK4Tnt1Wll92JkeMOnZQATHRZQVS7drqzrWKR3A3sH9adZjBtgC28RGuVUFK0CB5JD9m"
    "t5s08DQ1ZKYmXnTJuSkN+0f+PfvTXKV9Afe9ux4uLjcW2nBhYR1OwaXQb/0UeLpnHzriMW5TiNGuRDVB2D7vhYtZK3fBSl78fw5h"
    "ifeIIf+oFrm25fGhBV5k4RzSIebwtx99/8y3w7D1hPvkMhqbz+TgLCv4jp/DMz1rPf7Y7FnLUZtxGVSXUmXU/chwQ3QtJB7o41YR"
    "r0KLO0yc9aPDs+cPn/WX0Od9qYX38EtyfrMV+DWgb1hHlIZLObzsVvAWv4mf+cREHlIqrPXYv15AUMUcHL0wXh93RwsG6551u6GK"
    "9/BzDNoIW+vo5GSxni3ZeS+Lk3EaFxxeRAu/vm4htGHGmpAPIIoDvpt+ppfrj1mEqH0tHRkOHyst+EGYfAxkTcR2N1DneKqalWzT"
    "Tspshzyk3EhQQH+1iNqUVrLUoDdLZ0tLeFrSkwRtu3v9BgaaXb5jIgLs3Nt4iRLkUTy3YoJgs/BjjGDhoBWFf2Q2GUvyvxZPKo81"
    "GdKJ4aBrInAry8CCsmWngsj+ExXeVW3vZy5GpqDYUljzQPBDtx6/3EHuClf41Aqc8jLt6ZVFn0Ugh0sagcTW08UK3NV0EtULk+KA"
    "8EDImK7C6rA0AH2Y96sZtF2CdOm2ceromFhu5bhNeyFwS0vUq5xXKE9MOfzjclCowJvES6IIENipIP/RkBy+oQqkTM/gIAr1iSo9"
    "0tMA9VPf6HGyA7Uxwai4Cnbf7tUnCvq8ae33JBOgazBFTqmgtc7zy6KrTJxbyF48tCa/9b6486ECRqalvpZWXOk1fCL9MOlFjSHy"
    "SobjszFmv3eRqo/kS3gkpe0PhwJApGTjF6MTKZ92Dj1pBFph9LnLktK8YZ+Xxy07VqSx0sutuAtLXvioGx5vn4b1Xy0mL2XZm4f4"
    "Ltw8SVjzCI87b+wP9MsRCBa0PObZUsgPFUIQ2mhF6im2kfco8Mej0wSBtYJ4bF496zk+EYeX89qPwDNyqCVx/hlHAG8njzpIXxCR"
    "THtfid7nT8g39tx6282I1k95gVtG0TV6hYcVn+DAfILZOW+k8nTFXyunvb7iVBHaG6i1VDktNhNes6PdlqlkYK+VbX66Dj/L3iCG"
    "kd1bWaSuS4bT60VPevhkUz3pIbKh9KsEvRqoJllNGEgLNTuTqrWeyaE2iEor/ME4+niMmYOihxPWqA3lP06oP9NKTNMrXxxWV781"
    "9U334fHxKCIN5CrR37arBYWxh4w1KtF0TwyinAB6RqD09vJCuxx4C64ZCAhiLGu36TL6o+p8n0btoclv0qHcQtDVxS6Upz7JpqLZ"
    "VOX+B3EXnw38HLs5Z1WCUg3RYdGxGvgta15tC5hXIWyXKpXTHeDDZ0DjQQRiqg50rIlxTXj5lFstgUCMqiDT4ukw5gP8SX9wbewe"
    "3L8GXfCqq2hEWHLd1gVaCvzWKl9g255F6v8FITSWlkP/AuyMDt4D2z8iovX1NcyuANVMzXqdvYt4X9Cbhrdh5m29X6U0gg3ujuT7"
    "Y8PXQCioB2IGNr17QfeHNFmRXdPN8fRF1kwYfJiVkxqk+vcICuWjSPjAQ+TXIsR6Y5Pj0PeFoexdUapz68X9p7d3X7gSFQNP5pw4"
    "X3Fw34P114cW0UN8eBqlpA8xOiqFDVShveAQDVPl1lVRCvbZK1TiRZXSklA7r8ZGS7bL91DW0myUcdAg2R618LKwXX4K9zy/d/11"
    "DT07AZf1gH2cTKhcZJhyr6zBqCS8Eo+XtVIjvA9NeBRCReG2p6z46sidGyTqihzEHs6t7/7hnb33/6SV4zXK3bLZFuTxfBRjkXTI"
    "MJSKapoPGJE6BZzE9Tpu5e+f/FdfmtnYXCiVl5ZbeE/aMsfJ/wEv4f7rO7vPf7D/0p3dy9f7ZS2PBjU+EFa8PzU8AuyX0t8kSUh+"
    "nEITCCyjlZ2Z/OlP24ulwP3pT3kUEUo5dCs/ZfQoRkWK6QcHqqUo8iJ5FPKGQfAzQdJygQg0FY/dCdOBQJ8xu0RIC1JfCFATC/rD"
    "z7BbSBUImR9SAktb+uufUZbktlEJY+sqTybVnL7MhIFYfJMXeM/sfXQld6lVy9zdeCMz9c0L7Njc//PWFx8/w9e1rEIFARVzde1d"
    "+3msapbw9Vz+BdU3vMUuEtGRrRdFuRb07zy3+/YN4WRB7XNbR++XVHybs+rp+mepQN5R/P/mNfGUrHbcDzVNpfD0rQ+gn8mJ3fiN"
    "QUE5BzvJjoOQop9kSmiJ5YsypUciTd/DjKbXLD62cU2tNldkNfgErGAKaNlHWm2jK+ZPoraYWaoSaU0UNNvail63SahpIntLi9lB"
    "9++rtOK3opsv3xHew+s3dj97RZU4Y3pU3dbzsyRNmol4qS61C9Kldjo0BWo3uasjnxkKhadDJWGeDuUhJ+LDIoETfpKfxW8RpPu/"
    "g7Jx6EgN9Z4e2kjSlBkhEJPK0kMJ+UdCTm+Ivz9pYQHO2KhOhNlEugzaeiS+/m1GHtaSYKRrU0uFUdaeiNXFJwWuVr0a3Am90kx5"
    "9LFNwXMgRGYxZw3vA4W4USdnIkn9bex7pKVRtsz58fHHatkf1Z3oLvRQyc85v3UBXZGMML2Ua/iVUr1glRHMSGUUKXPxQtaNsVQ1"
    "Qd06TJB8nuYxepxG+t0a1srBPWXJ/UOEq+LKQAGqIcyPpRNn4hbyIMgQGkmxxg2oOeEbbjDS6N1NREXde/kDDV3vPZEDS/eTUq9e"
    "C1I23v7Ge3KLc5aK/gR6jbDezx9v7j2FXP7enae+fPa/SQ7YZEQpeSf1hCTT13B73v5s9/M3FPImsYKnRAUmiuDbvf4Bef9f1KKW"
    "oBWqY4SRD5sSmXAbx/72x/IsQEZhzc87h2iKvWbZb1CuoMWApfduXN3dZsRVzb/Pk7b5glbn66p8I0dcXGi6COmnAD6T7ItuLiHO"
    "gaUbOiU2AfwI9BD7keEsY3Es8sXAz2HPx55AKZk2E68Xcn/zdwaL0DpuNiM6azYj7tRak7dFrfnVat0jcgP9TNQjvvE+/9SMftn9"
    "7He7H32AZYwiJXsZFL48Jn1TTLsZh65CFoXwFh0+IZYBnAhjwCMiujjt9NhhYHMdCI+QzXWxfco56jzkPOx83fnGPFn1wr4hiKER"
    "/UJNgxQfzveckACsIia/HKUwYr4U73uMdkLOsb4+9qO6lq6RXfUwT/Nk3W+7+W7dWfEqrpGkzXe5HYcMNtFr3I6yVThuvHpEswBc"
    "jR0Kriwh4SSKuK+1KJCf0jTzD/VSSro3c16tiSnAZJy9+E8XgasmaljAXWXfu7DkrmJVbmED0h+oONVkWeCW00hUj5+rOavmnQul"
    "NmYYrRSM4g4g0MrYaPZwvLP73OuMPSwqoG/exvw7gaf3KcoXz32iB8toBXVjSXYPf9100sopKHgC2ggHJXEBZmQ3pLX4hO/X3VIT"
    "VsCYk0LpgA+DnLfUxuwJ+hBVbpjBwg8r+Zncijz8A3gGvuOfXtQUNb9iyzIA3A5JbbFLcKzA63xVdLhwHtM+zOrV1JjKaxFx6jPJ"
    "OHVHPnuh0oiQc7NNs3J1VPZiWULBLUuQg8XCjPb72HIatj17lWaUV6maTcEHgxWfUsGQw11ei3prBlSAeO4pPuboRbqnirJVF2VN"
    "DjUgKzWrH05OaHLvuV9RJqtEmt/YtFSIfw/dATxbwChmePqjhjFWQ/xMdTHkFyplI2BFeg3Cw6/iLiOvEiwKy1EY0OWgpVuUTIgy"
    "jWcGyFNN6BymyM6IhS3OyOUsZGeGrOz4ePoKJmqYiHhuUcmEnwFqzkfvmpuXhCs7YjszlGGl6FHVN0eS1H3h/4z+8egGLPUyLWux"
    "pIqYzow9jUKbs0hAAygbj49HnyOvl3YtHguRR/9Usmy3rdu8y4xwIITIGaS+mchD1yAEwelh9b4q9VomUhaSttu0Bw4vDrgzYUw+"
    "aiLAkFjfvzA2MI6y1vr5ooWAJVtXyY5r5gLItEIW+riCn0BaummERW5sfrn9271fvYA2hKsvk16tl++SgYz5mluUljiCMcd3mi+U"
    "oqtsR7UMmp60DqS1LMunkFiZOpS9t9+gqModNMKh8PUmZnJvfQA/3dt4DUXJzZsjjWJ4em4Mprhb75Mt2aUIWglNf1Uab3VPz0xh"
    "ADxqAkgxiKFgN0381KaODDrrdAeBYgcmKHb3K4Fiz6aBYrMiAKKtxMVmvBa6oONid2AyRAMFE9jOCR8kLvYs56nE3kuBMINe+5Nl"
    "EEHhYRJeUWrm57jgT8e49wHDRM8mE7L43VJW6MQhw8KDw0SrFOQv7jynSqSiqe/Nj/c+viF0TNhdb7y3/5uPaavsgKqye+0GCnXP"
    "36QiA6jAyT2mKaQmwhxKDbOYG7SmODMlB9zSC4RGUoEyxbgog7JGwz5WbKRn1onkGq7SGrU9aCjiNdIV28HnO4rpm0h//ByCihBY"
    "7OUr1n3jbtPJFjSyF+9uXDskyX19nemvx+ATzOJAFf/yD2+JpAlhGyXWtAnT/CaXeUgLxKfSIZ++TGHor+jmsIssqjBrEMCGXQQ2"
    "DLN2X+Dvrm3n+9lFRy1Ma1Evfp2sVkGGysXCcAix1CKWFcbzH9kl0Xw8zhl0rgC6TLS9ZgvH6lTrPnBaQGexRDyDu6Hrgs+h7zwu"
    "MfGBtcFHyeUIOv8n+fiVIz/068tAb0fUM0fUDWn0RZiNjxPK/SDHxGw6Ln7Pnp4VLgl9ZIZDYha35OxoePgDPVe8NEcPsjZn9GMk"
    "yNVT16I+ZC2Mk+bOHTJ9PWvFOHiQQz6qNwsc1kgY7YvbQEuQxMyUEx+pw6nmXtKXZgV2DWnH5EgBlTlF/1X8T25YDgCixIVZh8V1"
    "mCapfdIpREMzwO/rSdtCOAJ8ZwTcKSSV5cF7dMZZxLsuDZVhRinspFXCK2TSiuVR4VfE3ns3zdx0DXjf3s6fKbPqlky/u5qW8ZNe"
    "koje/RBNgyapmJln12X52uvJAlF9MrAmJ6cucHfF9gbV9Dojd6e+hMqx37l37b/TKlgN6PnDQ3rep3uIvSd7dfDBCcB04RwfCawP"
    "1wNUkr/94q1Mf2i+D/VqOZmHuQzje0rnt9IgudHiAOuPobZoT5fyBKclJ5K+eNKO5gWeemyy7mcCECF0Y4PbncrH8eVHW42ouXh/"
    "VWknrPtDITfsRNj9YAszKXEq3qX4gw9Fipnwfj6nSvgYN2xui9oNggE9J7PVNr98720uTE/VfLa0sJ9NmZS3w46/3Z03VW6gyLw/"
    "WbiPmnmstz2YOnlSAkQl8d6NX9577aWvVioPU0m4UN4UFcr7xqRZJ69JySYX2m7ZOLfWouuFidlU3cLK7G+/aA3MMCZxm/Mb917d"
    "guF8tbGgjYJgAFXZv4cmE8Phm9IGFP1y0CENx9kdAEiq56nubl+lXY3xNjAj+2hn3haeba59xxhu5DuK9BGM/f8zSslbH1MUPfp4"
    "gH9AC2RLJAPI9ovANUCvIbiaZ4nSr9O/qr7XNZUYKoqecR5noqQcwqCSlWH/zy/s/eoNQop9nsWR+UEgHxbWIIsjUT9QtI9gpa2n"
    "OIOo4gfhBYrZxeyXVktXNHnR0+4pzPbTOnUQRowLR5bBuIJvAvWy4oh+ZwZs/fNfgL/TItySaxUH8UjwCg1ngCf5fwc3pdQs6TMJ"
    "X+urP3Pjkycu958vGP/+S3cwmxlDMN6mYJlPCA7jj4yccvKx78C/fBJSCstzlPocQWbsP/UW6PloxhKGreQMDokZUhYxTrbOED4X"
    "qCmEzyVif6ju6PtffkxQEOb5Q7tAwuga+Sm3Y1oonBLfc1ebfujiFnple/fT3+x+cj2L77MxIpK0XtJ3t5UdzhkZxTgRH2fh3KEo"
    "8jmN4dW9Gz/fff8V6OXUl29dI0R6zPDe5su7H1znD6CT3fxy+8Xd55+Df7FX1z6mOkjCqIEhKxvXToIqD0pA2MaQ9u80Qzdw2yEH"
    "1Xz59s+Rj3z6GxzjS3+FV2mr+zKtq4C21/oWFWfUK4SAilQK3JJQAMs+qCHtlluvn0QiwsxmZtklg+rKWZM1j0wHo9dkQ82nnM02"
    "6kX0sCWcjZrWGBU0jKpW9d3ZKkYtVgk0HqYG8zn1rxf0MAwzSM06IPx/itliLt2drSLnaLneJFiKZ+5uvU/gKBglYJpjdmTxAnHE"
    "MIEhqHZ0irFojEFMeEhFUcfbtH3wDOojKIrwSMZnuMlS3N6zf1AYrlhPUqfkNFpHi/vvPt5/9VMCZ7h2gUpI3tm7+vvdT7ZxlBsv"
    "3N34RRT8d/kOc6Av7uDI0L0vUb/3rgGff4v3PVbKvbYJnzN65Va5jUTh2d2nr9z7NTqL919+b/f6X3iV9QfIw8cThNYsnq+n9BqR"
    "OtLKrd1Pf0lzeZuiA69GSBAv/wV9hmLidxRcCRkcn0opGZFaU6ixJGwV9CG+YxJVe5I+45glvk/JobSyJWlWE6NnK5FtewVFujPk"
    "B8g/PBnjFYa1JBa/ImOPrioWycZ6Opy4rFvCWL+SbjGPVWGRaH4Usnv04cRxrIWbGKMKolGhWz3+cryW9n6tYFSNJ36u4xyft0eo"
    "1HOcStF8hTIy3YxXxl8MYEFk/1svCquqaToSRBI3xyZmKPIjiXozXb2bw80qB/BiGf1iq9MKmo8owIEDvUY1I9G49SowAzENB3Vk"
    "gGMcT6Bop8V7ln78YGfOF+9DSWUJ9YCHixE3b8WByrGadBqsFiowUTxt5JrdluhBb1JWST/IHyFLb23de5OkDXSJvpIoFa3Q+GS0"
    "HsbpyWrOZrXoA1QrSZ00FkrZZzQ82loj3kNyFwP/nNcY6IFdbJGkDuInkM7c7HwssrpDFKd+7etY68IOnLX7SzFyxMK//I/O+Go3"
    "K/pol71c219uJrQ6eb2/ZsLjIAp68d4f/0QqsRFmv3/196CWoBQA92xsPTZLCenyITh6xUMva+GpXzXlqx0uxUcXAr9YTRse/TBs"
    "fMikpJWRSqar3l4xcQk5lPUzvE2keD2A4fjtx6iagDEiv02FMFKGJH5Jjkn/dX09S1/LyEgLVqnVsuxIPd+4ppChj2QeQaiiCCL6"
    "ujQaiiy3GLQmO3h3P/qI2Bams+39x83dd272mwnBCFulSgXY9Rm3GuaPPjQ0jcgAaSvX48tNo8JAzgUfHXoGJNtafNyJtY4WVBQA"
    "FaS8+8zTKHGbwr7Sd5k/stcVfdUfbexe+fmX2++asdr/0BkoqBmIcH7TiScxMfzYAWaGh5/5+ydXM6m0g+cMA9geEL/ubxt3Ulu8"
    "nTgmd/Z33tp/4RndNMC9kqE7t4hWfytUgK0/3738a0w6IvkW4eeuROYNvNmEtmRjBmYMgtAirH1oND9LQDC5ygIs/XlKb25TCtRT"
    "mdyp2QuzCBYDv3y/VObEKEEdougapzK9qiUfGTGLmIoYQeR9hMeFgr/buQaKm/B3oAnyVXXex/ZflA+VVqwiFekO51zGd+3s//lX"
    "0CFprUGgOuaFQiBAc8ZtlhIwgvPyTdQhRb2zbaO2WbImAycH7cjyG5oUQeGPwilb0y3DcWvAU2+pYK+YuqJMOOhK/ZwMZnACbX4N"
    "aOdmppghR+DnRspsX6MKRhqm2VQ8g/36/WwqI0rfI8u8PltVONz5oIYVckDJHbFzX5muP2lJv6+MeRxJVK6VTbGmWgMlGuQ4UUNS"
    "9UknGqng1aKZXpVAfGuEeNZ2+ZQMT9BH0RjWJUuNULR66OK3uD4PPceHq3iuD+Y2PVOqdMQjx/GT7Pbv/rj/pw+s3sB4BxgoTCp0"
    "b9GrVGBGanQ4UYejWRpbqGVVQdOzGtUTQnRZqKRaq+iSKZeCSppYaO6Tub5Li200dTsve3k5YCWl6vn8QYytbDVDf4UR7aPikiIf"
    "dMJFq0K6jfQAAhflCCbTiBxhiiKf3hKJh1HmZjO1fny/YAW1jm5Y8urt+GYI3DQX43IDBr1qZslfeSd1FiOlF8ObhN60/MBeq0dI"
    "0GS9zZWb8G2XYsfvP46wjgorpAKaFYUpI4r6rgct5JsIAxoi8maYtyjA3Prf6jJHeRjsY2BvKRUjkYw9GjfwhYxvWHV+UKN3DEar"
    "T22OmFV8zCldxvvQIX//ynsyAgcbXHYuUaM9O9t/ItxAuJzL9Em1WRk03Krvp1quDu4znqt4jpXpYJIoKAI/dIM2kJVzfn295hYv"
    "Ilj58VOnHjv5vczsycfOnc10Dq090e1l7l5+lYwvf8WASTR7WZn/+5fM//1dZvb0D0/PnP32+dNnzhhy/lAAhW8OKllCEWUnCc8r"
    "PY7cQs/C5d+Sy+iOwGIeIE5EYWqzpY5e7KSlWl/RGmf5IL0wUlDSIblcGWyMJcoosbCAppMiZSBiBqaII9nWMaCt+bx2Nybbwf0L"
    "y+1VzI6lEA1RshTvQ0Ai0JCiO1R4sbo1gzBN4r75PGY4YkNEoPCrhZfwuc039t7/DV3A+k2iA8WLh9YoKXm5Ga6vT9pU8KZcqrsi"
    "b8VGuDRc60Nrbq5dLjUvNNpj3OesunBkyn0In3zE67qV7JQ9YbUJDQ2fQWTMC3hfkUjGmjgVZLWrNqGmIbqugAPGootOIx9qCcrN"
    "joaEizmLCNabm4VRUC7eE241yxhmQXRh0nbm6o6XzOHznVLiYrnQNJIDGoVjjZxXmWjIWsqcPbNuYW8xXpGeP12tAk/mbAWP2gkQ"
    "Ng+hkwuw4ebK87ZDN54prfrLoX47D6ZRCOUD02ON9fX6+noDpjTw63XC8YBOgGIKv9K3ianx8Wz0BuNOx8OsKuSXiZ4lX4XxlvA2"
    "UV71CRcB9h5baLtBxw2OWcuWmftfI7BN8y5uuT4+rrozPm709VhB/VKkqcmP1fGWrzY4KXfXcj53JNuwHexKLQcbGrrbxFHbMPX1"
    "+ZSZwHH75uAahRr8UFM2I0xzbYdZi2ih5becXABcoZUr1WqWvb5eMlKeKn55GQ+LJLAXiC3wblCKYSOKLqqbA7fhd9xB90P/feh/"
    "VE6130FCBGs5gVuF7SJzxioFU+o7NuVUCw1JCLi9arC9VnsFYGQNTF09nZVkjgWqNqyJ2tzU/ER2lWpYInS5PYGfGhQUPQE3E4ho"
    "ka8x0CzeAz80L2C6WRt+InFURsRpZ2QGnxG3TVjAWZBNJAoIJc60R7IWrQMw7vFxBBVuldAt1tBZLvyALFfmXK84I4g+FT/M4Hgn"
    "5wfWoEhVWnVpIJpCaGcM+5jhaRzcbkNvt1I0hlPsc3Tk5V1FeGd/ri0mF/sAqmO0NMSDGf4AuqiuwyrQOecg27O5BFVLwD/qxGS3"
    "Cv2HI5ZotHknGTMpRO298Z5I4EM9WyI4jgFnHKvAy3UmXeXfFYOTv4k0z5XCsZUoK3hFn1tboq7WBj+UXTFP6fX1FXnM2qqNVdWG"
    "xH1dcWZgw69MZGeiBULg1wFzJwk8g4zGaShaZueilGhA5P0OAujnJw3DSAnZWlTIzKj6mhYovvPFRxtfvrttjb5Dso0idShfK7IU"
    "kkcZwz7gpmnHds1cyvpnrJjSijuoQXLpobVGD5S61G0hpNIDbLfVxJZxaMtEGgx7bYkpswg4LNOVur0yUo6rzrm1+1vOGOHDNKU9"
    "JK0gDvysa2u7zzzPU6LK3M9zGb26aiT19S2/lZIpKaSf9MNiWK4vUnGrH1u+X3bcJ+u3P/8doOhqA0bOOEjfMoklzkH7nm8JntpX"
    "C9RnH/uPpyt2X5yp/RdPt4eIm4WWIri3AHdCHv5oWDg8FWGbXGilCtKgu8zmCIOUwOMRB15mzM7Jj4en5qHx/OT0o+G3JhGGaBb4"
    "IzQf2g5I834N7YnyiqpVoH5ZX8fHipP5puS09cKxOjR47NFQctI4dQ0wC5Mmd8ZHnJxS4JUOu11Y7IpbsfLqjZIfipjay7BeH+jJ"
    "gUKLQjP8f8p0EiPCQrVUGIsaxeHBeAU6Up9AD0pCHkSIC0aIKfcNHwiOTQ7Y+AulSs2VI2Y3Wj6gc57C5wTSj8DJidoPjv3bvxWt"
    "f/u3Cbi75wSmMhumaFYxnSo0dao4SAucpnLhBuo6HtZs1RQQzxTEfVFDJkcDRsEY+WBY8ppACVLgs4ueqWSEkfpRJy3DMzQML6Fh"
    "qAcKxp1OnTWMaV9hTpTS1B5fjbWkVBCP5fuSqYJEnGWR4KUxOReYfdMxuOViBX4INJHWHuXwAGL00yKyG7UYCysFS5bTDsr5btkp"
    "1UNClKdgs4cedhZdr7YYwqeBR2bdOMUr3oCq3pZmCSJF3/lZN8qUOz8+vgjkVRyoyuhn54M4CKVlL9skeCKHmNZYVvTFVpVmU1J4"
    "225K0PsPW2yZkuZZscMvlflyvUIF1COmj64f6S8RcUSpbh431/HcFaPa5YUuEpbm8mFkA3r7GU9PSxcJWncSGVV3VElVlvc4gSnV"
    "kS/dOiPYQUdkcfUFk8W9x2HAQpIix9KCT4ZrGtIJ/ix59tM3FcjN3s33KK7g3bubf0UAZQp2xtT1P25iPIaQZA/Y/bJfbx+g+3KO"
    "3yB3qkhVGez6WlwImwbcyRhQ3Zhy76ZnWrRXvLC8qKZBxpupcN84rKiKzlFRGJybxlBTU1/f336REktumw5phT9wsPCilUeAXeql"
    "M93cI4+dOfPYeYNwvwuEGwvBGSiUhUGpvJSMG065ESMOrJ49+sGqO+yNfXmhRewgsSTDJI6zrrbxMB4dc5VB3brC4H4yuu0aBhVS"
    "ei1baCPBolLrIzIAKdQPJDI8w/tJxV2OCMnCmdrIuVUk7qu8sfZe+Q3Fekg8RtXnRr8+0+oePUivzXdZ6mQQ6dEdw/cb8wUgqqXo"
    "szAQGOIagnz26yfIiQcgGgkfNM8HhipnMDTGmSOcqbc/WPYUoZwvGolfjHtJIXTv3t0iBwb63N8ltzsB4XBUPyYTqNS+21/+9joq"
    "86j3ajXiCU/oPhrn1oh1PCVT0FSbfRoUYUeDmpWQnlrCjlqjn7XSQ7dbmLFmCZXFEE3bumj641bWHkE/kOXfLVi5xVIbBCv4F4Qq"
    "WpQZV62Jm6O/BgXNtPtSUNM9mDz/PKOh3L18m3xmtxnJwoo7kqIBNkn2zs2yxW19fYzkk2QZxZDw1YZCbvktKiUp4ihbCyXdyzin"
    "S+WBZgBrVmSxd1DcQ66e4dQLQRF0/4CrxIxiqPVbIcm0wQDjLLFmTIFXeFoUEyUhXjgrldNWkZ3uXJN09WZqgWKzdutHqQjYwyIo"
    "nrUmsmzUPp0NTHt4PdcOySRezzXoDvirzOKBMIsHmlk8iMzi+L829/XiEOMHvWtS+aQFAS5WBtLfUlJYsfrAIZwGFYjE1/V1GK4Y"
    "aJo3G2WwT39pkU+pHh2RQ6xqwUgmbDGhjrxbegbRATTMom3JcrDoYYfBRPB+wt0xOaizfgtldCVgjYDI8PdPXpP8cQfv1yAYFHYA"
    "oy0koRIigtYq8kYgS6OYxJbMAzTqiE4QMkuIt/up0uosSpZ69CvX/RBIsThnkczGaNl6lRezREBUWhR0+Hj9XJrNNfg3X+/Z04jg"
    "Ys7V3Y1rQNO4j57X8KW4wNYVa8JjWpywMoOnio6Sr0cVHGuegrb2EDjGU+A834iB8zCBkFkz6JfoFGjGErSQiNIaYynUNT5+Co6J"
    "OKkNoLTYoRdTFVH8CbO27J62AmIfrPUcrwB8x1/CPYEcyK2AUlghl4KPvwCnkT8Bh6XrJbyOZnr5Qzsoy69OuWDs0fV1X5j2S+vr"
    "dXhtaxV2G34M/YqPf3HCpdU/2rAwfYSdUxhtx19Ua8qI95lDa17vyKE1IDWseAc96x1aKzEfMKqCELwDsIYShxP4fMvdrZsYr3j5"
    "EyxxSAEEI51MoGEOOpWGsPLRLdjlgaqlbptj/jvo9kZagFDaja2UdOWKZ/L+QFqZyVocsLXYCXMlkEg6WGPMEA3kdV6j4vfh0Vy1"
    "7vtBVv2CkO5fm5qcPGLea+cnhy6IRS7cdIGr3fKaRionXTCi0ijsxTkddSVw6xqMa67ltxDyl1t9tOmstcohbG/bCRzrXyw8OZ5c"
    "dvEYnLSPTQm36A7w/+fwHNJ/PTxl86GDJ44hwNX7CXCG5MaFgrGAN9YmkDs85nf0C8f8yO/oG85K4ADEJPRb9d/xneftuKdWCpFY"
    "LJeyFfsio2jBidsMhRqFEBtp1zumnMU1JX4tA5hfjs5OLRHZGhqV1V+Lk7HRUUDy/aRKmnL9YOncsZpYwdRT3B4IYbnZXvSqYf/5"
    "84h9w7JcNDFhrwG7Evubj78+nssrFKn6Hk2ogFNRhp3Uo/BihM28YQ2dksQkxyZk9z/e3H3915Tq8Tmq56D781RUcCqAaKlmAgiB"
    "fSclOSd1NSWH1k5nfemby2dwSthjZQ4CXueL12E178jzX3PtOF0PpecBCLv9YMVkWv0/nKAVzf3jp5fKD/vAQaZjYeLWDCZ6eiBf"
    "oZTkNTNcv7CoX8613KDhtTF0lIqDc00Sqzic2fQ3m8np/8Pu9dtfffpPtJxk1u+L3Lo28fmBo2p6bsUqZvVRpUBRDRrT5Rvo3xPh"
    "GLExYabTycXAb7iZI5nTlZqbISZLYEyXr0g63M5MHf3X3CQWAKPfN66J1ikjUU5XPMMJMxIx1fQmuxel/+G2QHY2UFUECQItTNp5"
    "oSyAfjhk1Pdu/PeX725LhDVhg4ZjGffYlXf2b93ee+MWpyII2+LlO3JIAjVHIqmpCjyM4SZTzRIZW2ZHh64Km6xwAX5HxqoPCZOk"
    "31Ld4hovUXK5RnXxReKc0KeGdnHobhiC2v2/y5LQ1nQBgxUrox2EuiCBU71xTXpxqIrO5d8LQQKdKL9hVwrQsCqqg899pEsZnDpo"
    "FGuT2iNVjYzMo5k+yf4ylP3R42dPs/RgavpvquzBRFoljSB++ooJ10AH8OX6WzJmj439mHjHTcY6ginaexYW+9ZPvvM45jj+4WVa"
    "i1cj6BtM+/xPxgtjXDCjfNnmLc0JqEtoO2pxdz+BR57f//DVu5v/EUMvcEDFkAQ7QPJJrjfLPaU0uaf0D5B7pITCHY+OzxFPz5I4"
    "PUv66VkacnrW1RGJx2getFESjlADVeWwxR3ZsEDVzsLvI0aD75QwRqA4Z+ScOvh3ogRjmM9TyG+ygu5CqdnE6AFDkZUXgz4G66Bo"
    "lepuEFoRLslotuuQLB9s6430HO8+wu/pQmqkvEQFXspVyZ/4PXdVIACLgBDth4Jm++4WZnOYBd19rEqR+E6n0EI8L1mivWs78kt3"
    "Ysq2xWdQ3+Ym553jhU4R65urMGzQ7wK0k1FV8OP1etb6Z3JIZ3Jttz1HoPNYZ2resufZNn62cOws1Wdru1jzvI5W8o4wix8fH6+X"
    "sscp+jcetR3lbdF64js4b0ln0nAhw/5wFcddL5zOurmFJ9kSuuIGJ+HNWVnMBpTCsbEsnNKUx7F6Tn6YwQ2BNiqnVDiDAStOuVAq"
    "E/05lULXE2XOq1jdnd/Two9KHRVFqwUmE4bMA/OvqEmuGEtgjxUKBFlvhPJ0CrUwO2vDlMPq6HW3ZRkhOIOw8jbma1nj4z9oZrEN"
    "h66BunopgJfTF+izPV0tVDEQBOQzmF/xhrMUmwMbSyu9fgLR5o5LOj1XeMKVzdhsZJw+iy6h7Dl7ff0sonVmzznQKedsroafbT6p"
    "T9hYbmcMbvB+5tprML8tgfXjNloh1dUO8rNO4OW7Kh2hZ3YCqewsvhcWYT7X9oMw+73QjjrGLzzB61B3C+em68Bt4UPdVRVq3MKx"
    "0/Av995cfq9Zri9X3Ha2btvooKTVT2sAHl9uYrF6ddtM4rayjWZOeP8YXBQR3uPjcsjwdiomQHXgT9DAO/kTTofQFzq5Tv1YYbJ4"
    "QhW36JTVxYVArKmdPxTMdf/lUCCjeZ328oK8DasxmZkKxVnpkLCcKtYgO+fU2nmsHNVT+6JRaHjZqu3UCg05jkVPi8ZuyI8rhVW2"
    "WQUI5pKtkZ1q1c5POjPRo7OFY7Mqpls+uRj7Xcyj/Hm50NJ+HstaRBuoKM3aiPYN+wnX9iSqVkBNvjqaxsr2mpuPyGUWaVbMgR1d"
    "7uJlY+tAK10khvFxONaIsrtMG8CrgLTgTZPTC9DHpYzbi4cpH5D/jBKAthDzKPa38UWhE36sHjW5l6TclowMZx0efq851hHLWR0Y"
    "2Q1HYivAaFCYoBqw5dUi15rEcHU4A3/mBn6K+VYaBVeg6RU0CsZzhFNGk2mXhVt14WTLxGc3DZNp4ujMKO0vyxiCc02jfS4w8uV7"
    "z/dpfHFI7YFqfVD6aDxN0yP74uEoW/No7yCoaZnqghgFRs2mxpuQJGxGrCkdxNBXflDPXnIoSS/VVMyhv6KQkERacQ7QQypteJAu"
    "impFGG3Fzmi4+Nqvhd6IVPBHwt4gDXPzViKwmMcz2T9apV4vtdpuemmkvsvbdktBebGvPZ1/TZYKohl4Uhb4ZgRFAwxR+tvvJGdi"
    "7+039v/0G8vBgssn/UYLq5/lOe1VhjUuPGkiNeGVQgwdW0VT6xFa0k+2wH4y52Tc0yZ/FJAimgcmjuD7t2deyHxx5zn20cY8uPc2"
    "/vvLt66JaEKO22LXrOqIDPlcMGM+7xfUauExPK71EDo6v41ZOoTFPfm22ZRIuogTcLHir460RZ2aiXdqJrVTM/07pUqXiU4NI9mF"
    "ulsbdIokhhAPlsxQReKopje7FlOTgIa3VRMpabEKxvfZmvCjJlxW99lcE08zY5rvsyFRMTka6P7rfxqQtu+3SmUPxN7cN9KQuZKt"
    "y27qJZ5TEO/jrf+rg5znlFv2AzLDYnwxnD7hIkhAtUXLrLUT1Ya27msKWJizjJ2EvPzGB/v/tWGglaU6eD3dIWupEyANEO+mQEmT"
    "dfUE4r0ETTNCUssdeI1fb+eXHZLDnqDMsGapgx+CAWlEdDfFMztKvksklsUM/K3oA5pCYHtrImxxIOAIwTFyTTb8iBC0QkOQiBPW"
    "4cOdsoVyP/zmaaJ/CgklRtNZtJKY9Im7mv3OuYVluCr2Xd8l7DSNzCscgcwdM5Dhk3kXZnHBvvlZNJXRffiCUWIk9PsIX8HEgkiv"
    "In0trXoYGvVca4LXRkaS+UhhoMKx5gKTlPecU8d/PJv3nbOn8mUHVInvgdIKklD+Ug+YPOoX8tlH63AKlv1IklBxfL/7b0KXRph2"
    "Y1+QbBDBem89ZeCpbb2ItSQwFj1pQNffKd6SlsSaGLj2dgRPEuBqn4pCcX1qCYmiFan4cDKPTtnB/E4WZtDVZrDJMxjiDAb6DNZ7"
    "toqZWnL8gpsLnBLaRcggAwo4rK/UIbuFY924illJuyeuplZTzCCkO/KzsgcdtIX4QmOcrpIVpJPjztrr61UyhsgLzloJuj8373Q8"
    "ygXE0K4OBYzB73m6C3ZIlWwYqpEcPMM2g67dS/SlBrot3a91Qz0Jr5FPRvaoXC5XNS0o2a7TiYyHxwvcYNd2zoqPHRUe3PKyx6nD"
    "Z6kO8fp6uwkX4H3OWVKXMcUSVfRYP1vRdMnGUXkPI4P4WLC+TlMxVigEto3paR7alVSfxIzYaA5saDaUrhPmjwMhNYyxdHNhrn24"
    "g//aCmqjXEZMhlVa2FnoBDNoWH3ZJ66tTOapY1POirQ1zOiW0sXRh9ehBZDFpdUF7udx5yzCCuP0oTXuLLMEVLLlNKBFaabA9LFo"
    "+rpScoMrbRd0ZrpbNAEMEbPfQh/FfF0jOp3tcJFpUclq79rPpePwFTT9Jtro5wRkyV9FNEx00WpGyyQW01Y05UtTV3d6hceiGRzH"
    "muPjKzATtnMCxluKduYpt3DslBvfv+cKZ7F7eB/VyMa7PHQHtBeRRdAeVO875YqZrbsRETnLbqEmqbwTFvQ+T1NJ8GHTDfdbDnTD"
    "QmO15ZzDT9gB4N7LLnxph4etCax9HdriRKcb88d1nAETgCCebTt2VhwEp7NZsSZj8H8pVyEzIF2aoKLTFC/dCe2Jiwn04O1Da2eL"
    "UnnPazpvD30+hu4ctIEox2gdbPgBpvKUv9LM4+yuZXka0W9/GouOWOvr0ZUMldiG762A8pxPcbwC1qfXmkzJ6E3LO1x0O1Z6NoMA"
    "CxiYhK5LH51QD1kjNO9TrnOmGaF5P56ay3amOTD2lPZZtAcyf9v4OIMi0WloHTcCvAD7GKPPUwpDyh7QdguxOyKwCU21gRZPjJLA"
    "LIOvNTVWFHaL+nxCTaEbOGsoeOWptxiM7g4K8A5T0jbPgw4fkhVZtPmDFuog+WXX0Vumgo7QOG0JJJq613Et+t4qh4x5JUeHtkP9"
    "rWQQRWMi38zspk3sBpioPCp6zF2lk+V44Zi+i7MlkNACEMdqWG9BcYfjzBzsXk+csXA6rkjGtEyW6mYFjwjBLcT5Go0ATdID72qi"
    "2Qer03XR7VA1bnDbKUGVs4UVLQR6BaEDgtXsSjMJ5DOKCkGbNKY9uLlOuTeKKbqzOJLF+qtrDJLPQc/Q/2HrKoS8Bm2UH9QOwBhi"
    "fZbHmiOkoJWrRp2NixxxoDCNkza8Q2uzxcjgqXiwdkUx44txK+aKMzZrp/JBaFOYZQ17psypay8vDIAmqVvm1MLdA3Eg26MUPhRG"
    "kyRXYVFZXf9eK369MjihpNyqfeUg5oqsJlvUPeRdcfwvs9w+LOer6a/UM7Tfh2BViRSNgQRvJNafzC7jAnQRuczggqkT0gxMtwXF"
    "VFvO+XqWGrCj7J38pdTxXhp9vEOHuvf7tw4yzkuDEY3MobWQSbYJWPoNCmbZurt5kwZKTsdGqYtBCSAYhl7dtrnOqjb4hgHK229B"
    "yaKWjOs3B/nG70W519j23rwtLHCEhIALNz+6dQP1NtnFxZFtHZ50NI/xp3NF9PTt/vItw0Irbjunbpsp6szwdly1j9kZEop5CRTz"
    "ABTzGmLGrslUyaVEPIqDcfdAXYkjDfQMy/EKj7ezTYyfCHOVoLTigloxNhbmZk+fwagi+ENWNDgxXTib5SXy0iI+GEcsFDDoHh3b"
    "5VZRpfa0CsfwwlwLnpsXC95R2BAt4T9H4Et1V89pke2G+k3/OuWCR6c1ksQowOOPotSTMFgqA7IiBXwWTRlU8pTxcOlFlcBvHeRF"
    "gQEolW6p7f+yA47K3BemwTni8iV62aCXD3zjGKEVuW08faVsPD7uYeCKMKQreTBtrrXUCUG3iX6V0nsmrq4CjZS4gKa69miL72zm"
    "j/KpUQFynXWqhdPZOmekZivlOW8eSdqeyIoRFC8yhKv42tOLBvAvT8KtFPRCYKz0JLpXLoTiWeGQP7S24EY/GTe36uJOLX+LXok/"
    "9XZf/5W6l8BfZcN7b2zAujFskWxe3KA1z/q1fEK6wrF1/iW6s1rH7VdVoXoX/4mrAeYzFyfoutiRp7Otucl5O4r02+RsXZg/rVgI"
    "Bj+JeGjCr7n4T2g4xJjiWzEtloWnizqeZSL2zTcQU+ulCPFUgn4mHgm1aDjmPKQVNDkcRGstG8bi5hyj/aQMhT6CIBZYCDuY7QKe"
    "I2cW5R9LOE0QVs4iaJwwZswwO2ZLW4MlTQsByvReRXyrWXnml30tDSzAVpXMCQv2BCybQ43wOzQDQAv1/1Zc/W+Z2n8rqfz/wM1q"
    "Daao/99mTdEbKEQ0DImVMOj0yRumDWheGkHLg+BSajEdQbip6050AppJagRX7Qq0q+80Q/+HnruSXVsAql5CaINSQKgmHPERXVDx"
    "Vs2CipkE8ex03cWPJ1a/U8kKZ5NtJL0ppAJXQ9NFPQ8OWddBvAFo5QRGZAEzPUnwXE8QZBYczn1fVHZpSTHqcUmdzfWih2GwBOB1"
    "mLJf2y5DfR2eOpoPcgECXMFHOtD7vHTa59uOecWmmCIsRTRRIBmu7Hr1rLjjsGfnMZKrGn4roD8TU0eBqPSnDmtPqXsO80O2tiRl"
    "9COgr8+NfH1N6esLlQQTFNLh02g8BpTa+noc17hUGISE9jDi98mYOw5Ri2DXQr9Wq7tZAhEv2c5YyWwZpJC+K1gZYQWr2gpWOD6v"
    "Afy3zLPsaEta0ZfUzss7WtI4Pu2lBPEyqSkTi4KyzGC4YD8iqAkiKPOiPQybtsZLXT2MX1qI8JxtqOhfeAcdr4izmdaHDgHhGr1o"
    "pMxwxwPdtUXsM2q75oc+NW4nGscQ5ceBhUHLMrdfLTPS37cKR9MemSHzTvojEzFAPYNqDh/tTScx/YK+GON9If440WxS0Safhevr"
    "Wb8QuNDfdni86TXI9Q9iWMMVh2UBDgWE0kO+XKjClWquHAZ1YProtUpAdpMCA1yGaKq00M5WcxW3HpZ+bB+LX/oRnAcDNgjsa2OS"
    "CrIlp5o4Q6BzlWTnSvVQfGq4YUl8FDHPx4PAX8F2QXo0Lz6BVGilDY7CdxxZn8lhxAfnn+WuWl9fyjX8CmVtJbvo1LNVeRRGLy8e"
    "nspP2RGauZcCY85zAHzAWWsB9XodNz822cM0keS9K4suYeZpt06hDYtyB1PuDwhakZIYBgCpQ7cZFr3CMItrXjqAuuopdi71Dtk/"
    "1aXUu9J6lXqj1rGeFrPvqd3gaxy7VPCL8Y3JnGoafuC+n1jNriHPyXtfy5aKpX7MKrfCYJZH8w9NTtrOgrtY6ngIUNBu+Fi9rhet"
    "aP/IKzhrRLgIfYrDEA+1MzY7OtoV8SSF3Yc1vZXJ8aO/f3Llb8+8QMU6PkmEQtYxOyPdk4JOljPWwHAMZLIy6kV81qwX8njDow4l"
    "fn1hGh7sb3KR48qkRJGXC37kifcMT3wVfbGmt28U4Fo+EqT4CzwejSBJu7dHdm9pa/aEXRnxUTY/2t++s3v15RhKLQ+pqtFaq1Ad"
    "H2cXer/jUWS00LGknWnAHzwRJABnHjInpsyzvqBMzbDVEoczyT1V/cvUN9KpMj2AjLxScpwDI7zLsLzj4yXoJPxhA4DuMS5RnHh5"
    "3jDZjiJ1V8hZwwPX6W1U6qfjVZn0f/9Wgvpf7Ev9g4g/aeVaxjQsSr/6YU3B1LpxE1cCv3cudAIDsZdTs/qc4a3hIhyd7S39bG+o"
    "s73GZ/sZ1k6zjYkJoJRI8kExygLpr1ZDlwuenav8QKOg0VYDuUID9bfoSebB+sM9Z6UwwylKM8kjD7rkDH7eGaNeInyQRdmSt3b/"
    "8q4GlrodRXfLomx6hJDlPOw+pFKAnqxBJ3ArnQ1KzXbVDexcuOg2s4eApzBO0WLhGLyIy2liFBQmc8qMUmwZ8znzGWti0YAyiph5"
    "K+VwxMHwojg12+l3R92lkker/e5As92KOF1b6Ydd/EV9b9Lf1ecmfl2vR9lXCSqkNVlflwhTQfdIGJRW25aYT1D0A1Dk6Zotp5Ye"
    "RA4zR0/PR6fxKHW9ZGQ0HoKuCIRHI5nlNICUvFYdZR7a6kH3ERXlqDIlODQ3ipVuaSV3kAu3pCxHhjfM5pmn86hWOJZdw2v5Gpy/"
    "9XwthywQhN3plhEfX7As55CXbVBJ2pQuN40uczdP9e3miruw5IVsvPQDLO7yIHrOrT7h1kuIxPN4CVE6RhkPlvhAZsIbMVVq4QGJ"
    "hKUIRq+/OzDoxn0ShlPOa2LY+wHLC1gytB3jeoewBQpH1xgJuYY+o2Tt2zEcYQIdMdlMhCv3S/pvO7Ihb70Ivbi7+Quyq19T+BHp"
    "6S5G3dRSX2DLVn25zZHQabCKolij8E6G6PFIYuylLMAieZKMAnRn/VZ+6mhvuGsS0Q4ICOGj3aff0dAOuNCCmAucU4Rv+D0asDdv"
    "UdHx3yrcPkRP3dwxK9suG0kRIYfatJxGFGhj1b1UOugPMiQGKIDUj37DqfrNcBa0Bxhp7us9013uAtdC7xHwRfIYGfED4prulmKj"
    "NEfukO2WUtHh6SZ8ihnvLedJaIKM985YK+d2Yf7bAySgUmPBDQxHxcZGamwxokFhjv7VWIQxVpqwFWTrtNT+f9zMovfMS46GnGwg"
    "ay+VkRQLj7og8jG+aAWluWw5licMwilwI2m/9eSUVQvl4hNutuzIK6mgpPfNOCghZpTiLd3FkbAbg25oOsRMv1vqE2Zsup8MJeNx"
    "Ga7aitqNgw66c2zKfryd1QC52e9UiUW+p3VMx+avFueqFPNZ5dRqB2OI2/Mqwdv3QQ5o2pqnxY5RNCIm9MkKwZzD/FRvNDzr/wE+"
    "J6D7TTDqtEo3XZZlSqiNeBJlWF4dJYvWqw09pSx5EJh12S/fiSPgXn5WwAxdfmVg1Zn2soFsf272RAJzhgBRtfZkZuPWY99D2BXk"
    "xgzX8csI7+VWdDYRJxaZL7JGpQywx1B8ON2YwSeAeF8VVYv7z1gMU38QgRDujYJALSlK6XT6zDlj7NKM4PQ+Kwti3xAZBOTOJsl9"
    "I/3MTXkZkqWrCiGiibG81JdISYKjNdeXWsoFB3pnc+R3Uppn9FazEjW/Na2sr+CulHQdU2ErtHPUAy386rCEJy41tL2V7dKXOPj3"
    "d5d18G84V6bP5JZbxSz+C1I/1oUtgFR+JtddDMbH6U+utIBR67add8fHNf2hLKrIruGBk3f5FKbjA2Nc8G8vrkioblRQ5QYJFV8b"
    "JXTgNzrnEriYXgSI6fVFwkw5T2ITOaD0y9SBo81GrNCmgTd9pAmaz3GImpfzyL7iofzx909es8hqA0Smk8YIfPq7yzpS9Ufv773/"
    "GyMNTubk+45hsQky5K4cyBzqR/XhPCnWAjGfjpCEJBcE+38FeuRY/0ImGS+3suiPFQpEogKBVgIIokKOA4U7kmGwERS1JNQzcMgt"
    "kEbjIh5LG80taNwPlptWCpo7ougkSEjDVI3AVKle7xKIRWjCL/uNhhdaRVGtPk1yM3grxmbnB/A1Y60tJyicgm7nmv5K1sa6voeh"
    "G5OIA39sqvik6N4RZa2ZQrzkCesI1fv9/welh4SY6QqKdjWKdv8HKbr51SnajVG0a1J0U1J0XeKp1yMSVSyt2gHlPQ+KOfI1GHzJ"
    "hCtKC2TCu7RwAAzJbcilxrrJbhAU9acRG0tHmKPk1y8+ep6BF/N6bBOs55SDo4I/0AxQeseruH6+maO/TgfxtfAbtLm+Dr9W4QN+"
    "r6oL8g76gJdKeAtQrNdcaiOaIf51yr6H0XW+V5yC3xCyAOOq4I/T9Mt8bjZz4iPDZjdhw/ntJbwfbRUxTKyWjol1hgxSTpM1oITB"
    "1RI2U3doPd8utjNCimm4OErFnK6xCsrySBxBFsgSFhiXjTwyE0z0083hnKIHBf/GAlaX6wkVAbHQdLKhp/qq2urRVq6uC2X4Fbkm"
    "QZdJNZa3PqOa9dC62GjXpBqa13hqHWGxcGO0UCygMhgUNVLGIM8xGCcCmSNmHHwkpM9mDfRSOXyhwIDOMnYG9OhynZzzaMrEEN5y"
    "oaRqvPKAWhMN0rudSdRkS9rz9aJUxC9QJ/Lyq5a9+ShF0qEaPALjjFFGf8YZLg4NizaF9TcNu4qSAnaUiUU3pbSHEdqcSUrp1grJ"
    "ueYfiBKohGBPcWUqasDxc8Hqmlm1AGRCNk1LmbCpy4RNlgkdTIMlXzcTggw6ga+B2+b4Om52JVC1CFroTGgpA/7XY7UIjFNMqHfK"
    "jAWq0u8+jsovmUJ3iOPTl1BeX/Arq/p1OflC81b23AQ1O7VCXxJ1VgpZ/DGGqM4YcFNSk4dLeW5Lu8mZKayweBQn6TAw1k4WFLZS"
    "iDWsRIQg6hVO9hL8rh+iiUQxGWvECIOt3IswK4sxBJOimJ6Kixg2Yoby4iL6rMScLUVQNRplUnf7xQPOrYxUl8SwGJzOrkRzbKOU"
    "Mk9u0hmDJCop9JCWrOi1MuXD1gSoTdEr4Itu70mMYFkfgjIuDhhzmGLKqIJmV82DduXUzDBpjAdWHlOuyyOAUF94nsMHDA3YSPVH"
    "GwHfs//sFTR8RCaILz7/r933/1M3Nex/ugNS8N711wlqQBQCEq965undnb+iXXnr2b4VgXTjnRbUbPUSC2FS68NJau3vTQ4aRs6W"
    "xhJYPn/7BtWK+R9hckDVbTxw4e+8YnXmNkhyuUXkcot9uVycyQlACm6NvzqpgoXmtb9f2WKIaEFSgxAaHL844LRNKbDajhXaCbrf"
    "h+k962ueji5Fj+UfPgrsStTaMdxr5LrUfGEpJUVipWksI8lh+w6QAiP7xrxGLM452SpGbaRgbkprOsYycsSZIAFb5PqLSWxyFLXT"
    "4IBoeY6kd45vNfwYseSamBfDaXGzaRrWQPpGETUkT33fOUh64pRzPnV3DN0boCGE0E/5zqhykeU8hJWIfiClNyfsc/7HaxFZu1fe"
    "ibpNAT2MNaYlooxOjH2MnhkyK0ezCVJvScpiRuSQJsi0S5q5jK0Lg2aGpIULIGLnU2Rt5CDLFTePHmTmJ/O9vpWyoxKSlaLBYlWl"
    "VyEOmS5YizTeAeYPEDJLAwXQcpSQ54gRxCHUFDuOWcLfjFXQFYfW1ovUvV/c3XwNpbiNTQn+JCrbpfZT+jj7lAMbJuKISU+Vc1q0"
    "xPR7oRWTd3RBBh2L19j4AdNAX59PrRHMIxE9Zgl1WHJs0w9dE/Wz/zGPebAOlnjLYJECgxTkwa2OfcwQjB37UXZlZJBb7BTW/CWs"
    "oxud7yID0UEZpFSGKTPITv7apu7rkoLloOKYt7749PP9l26SoQztFZaqRAUPLYEMrUxA08pU0DBNBbDrTGtAzCJIlb8crPSIb5wg"
    "8wr8i61T+oS/NMEpVdh9/AH6Okx/JHdVgHggYdFq1mA7+Uuj1RpfrPQxw4URxni0i8PixUNrQY9K0t8WZRs3Ng+theJStBJp4U9p"
    "bn0W5iLxDyFB8hclM9DLyb0m37z14gDOoO04fOyi7lUxgwTmdF0qW3e8obECKUAcmfZhrukYTeJiZw4vzGNttXY4yOlaNfOKQC5r"
    "h1SOEcWYAf59XXineznCkXCgq/VSTeN1BxiHb5Qi5Jw6a/Tu86vtUUudIVeKcoY3aOfTKzEOxlxDVasXX3AB98n9DZBK3N3/EK2/"
    "bbxkjTw8cye8h7J+VOE7pvlcjapU9JsU2G1GuIweq5FwrnV1hpQ9k8N4HUNabJIHEfmQUuNdw/o3KO5naIjPLzUZaEe4Wv7wzt77"
    "f+obr+Mq/PlvCpScJghdRhHbqF5ivZANVL3EQHFK/B5nkzHqoNTTsC1jbZq5VpkSw/lrnU4nrCAomywilpF+fGA9Q/kjgReh/B6I"
    "UoxBZCdvjxKVM0dhOW+8x2wUjsdsoBV1DGThx3lh/3Sa5t5ODwXBNgXJ8KnPT/GxzwcoirMc2xMzedfMcwyfa0ubd1hYyj2Scqyx"
    "bbniBfZwCyc1yFCno0TX1BcOuFkZGNgIS8vrdiUDNhDDtuVmo522zW/Yf+nO7uXrsZgJIIPJyQtqZ+YutWoZVeRo9+nL/BCXs5FI"
    "ZgIiVIv1I4uF5HFCmNx6NpIPVbyky1VK/j8wpXGaFT3Tw8KCAgUOCuQE1ifwQoSbQJ+KYc4L3UbbSLNoLI2Pj1VzFfq3FZU+ILsY"
    "U31dYSBmA8HDRNJdVYtph6YoY29amEBtOnwRX4+ikOsEPNISNSDgVbYW1caUfoL3cIGhOR2/wGVzqyRlyxswJEGK1lrZ3FYhoX3i"
    "EwN1LKqxUKWauhS1jdxGbVysWyOu2j0uAxaXa0BGIulVng/XCNJnmwzMujR1hdtiwy8nNRLq2kNfn5wcpNbqg55yysADek5JmxQ5"
    "cp7aqo1rg7TbUniKcEfVCxpZc1hVNaC3b6jaP3c3tv6pv0yH+yZzaI2hEk8b+fw9LMe0++xz9159W68FrgEz3N778Ipe3YnLIl20"
    "7eHL2kgu63JzpIVto1UUVvZiJNJEoxWS8KG1hoigr6QNLLFIDVykxtBFwlRKCS4JGp/bgNMqdM1t5y/xKUtfGBrXJkTStNvH6P7p"
    "EXnRV2JDI/RXozvc6LL7I2RogYqEJQFaWBMYkQ4DENyrOQQlsNNsr2hCaRVL6g15Hz5yEhMbDlrFi4NJVhB8VuwQ0Q7zMG2l5X7Q"
    "6HQ4CcP2l/uJOyUbGWaEuKj7YU3fa3lxiTEEZVdBVJCt2w6ae+oKs1UjjzIvhK2WaJD9qrqQwUt95ruEZV8EstmB5na0Wb3Y10gl"
    "B05Dxr0wkk+nj7zBA6hEO4ymUO+cLgNidTzBwm+yNvzle89/iW4OrgWIcfEsXqABRdm8QFL9O9aujws0si3Tw8JV2gRSs8JEliDm"
    "n+pWGIVhJVi9qhFWAuEQeeOZ3HJ7IVcJvI7bLmQTHJJ/gAUQtwju5drmg3PzzgLwJ9PHEHvl+TY+FvHjZpIfLwT+StstYtHrgjVx"
    "2oUHKJIQXkTXmvTHkVcwYpKuUSIlXyWpBC7SX3Gt7Sp/sOh/E7lv0+yvMrLF+t0RQYWJ/LNR7dmJThhdhanTRggKCM8KLpCjz7Gg"
    "FZBopsbH+R6YUf2Oucl5rhfuiOzyggU/WpH1UA1pNV4hjsVUeghDOfCxVHMXvQ60BwrxZCt/8jYBhCHaYwFMVQ0xWHt21ePcF7/t"
    "5gNnxatQ8tZwRPlKvZYJuvBvygG1eNRQYEcKENasSq3Ym9x22bSJymBDCkJL05mxyHl6SoVMDKHAjbS47B3doKaH+inBimOxyaSK"
    "uTd9faEDS3lUAh0Rd65pklhRfUeeV4+OgLQ03wop3iWUEPkvhlEGYfu8Fy4CPyd65DPaPkhFIjNVAAhdNDUwGLxOvHlIzSYjvSSH"
    "pnqHwu8onON58jbUc9XAdclKVc+5l9xyOBzLM0qo33l29+mbtHy4cNIfnO4ElkpLghPSWy3EZggX8zx2EkE9tA+C3C8axwI4uqcL"
    "GZnjgYQ1cDWyTcVsmhEXauosSoqpHvI7zxRTNQaltnUCSI66xkqwI15s9w97ADlRHb0tUJQQrN96uNXNTBrVRGgvv0XVaN9LbOr0"
    "9Cdl8qGd/ktkz1vPwkG79/qf9m58AAetmXg2MKxpJHqNFnjIPHEPrPtsPKKeepJ6WnBvxaOapfZ0XWxPdWaI5RArXMcVrvcND4jn"
    "GbA9hP3X84Scxa335TXl5cDkNXxcj7KjYixAPmob1aJ+kfniI1juj1IMHxFDbooh2wMRNQ1zKD9SFBskFkw5coCXfDzGSTm66n8m"
    "kIr2MUnxkmcqJ6NHgCyxYCq+H8OmxP2iBRFWIhtxk8FUQ2Kp6mhILA5i9fA7hvsekNlHSTDoZSFxHK2f6ku/oKsx6tAAR4wKvqrr"
    "wVf1gwRf8ZgtK4+niBGFNezJBZzqhm0wTAKCHYDlaujdeH7FUsO2mQWP2gRtpB2Dq/ZPmx5YvND3w5FMB8NsvEyJOI/oqYy+Ccch"
    "9G3vuV998dH7F+Wxw/LcoOQ7TM3bvLu1zUCQVt9aWioVPyqq+M3eANAdScKBNqEaHHeMU2oPqjKG6AfSCtVTbnQsbXBjM5n7Fw1c"
    "5uXFMGcC0iRSo0e8RssPVPRIqBvAhAzrYKfbzLexKJRxhIkK6YkuDTnUzFy/sWhZ07By6gRuQPfMTz+IodTNMUj6/jXnoVNypiaD"
    "q/gJ3TUnIxZW3cJagMFlFpXbASEKTjvMlZ2O6ZA+oTpKLWopN8sYjOvrY2apL027NIsibSu1Y0AVpEjllKCO5OwJCnhUYG0fUO0w"
    "wqRZs4puPizyJOWXGDJ5SUEmr6+LXqFG6VXIhrrqYs5wioUArrZhiO0iuQxIaw9sm0oR0PX+YobsLDQNk1gInFVK6DEcEEExRZeS"
    "3sXDRnCzZUV6L5xmrTTF91KiNPpc0wnj2R/OXODUjYvcs/QC6XX5qxPiwz1nTmi+Dg9sHs9OpVpTz1KUZo9KtPuYZMCPYf79AD0a"
    "sxuUMMhNVApNUW2cqKtCxKRvTqynFbke3u0ffSdRqpJReEKsJLrhfjoslOWZQJS7gL8CAVHZ8GKwvq6u4EqRv6QC0ilKx9DNLz59"
    "Y+/KC7oyg7l8FQLtgR2PYM6zoJ0YL+bNLeIne2wvZ2Kr4tCrscC+/paH0sEsDoaEZiEa5jeOTra6ztTk5L/YVm+oRWJQUnvEOAfb"
    "IUQyYRxCPhEIxrFtyn0feynMuu5b6pfnzU6WgblvNViQo2kgIkYlSi9WP3wkIIR+1SGAF+oyv4z15VhXQSJK8q0Q3kClXziv7BiK"
    "6ZV+8bMVhB7WlIqKrEPo4C+2qV0kOh1bKuz64C0THxgHMZdmMSyMO6RvKmOo9f4jFe8cPFBzlAMChGnU+fsW7/zxcR/0jBbVkrcS"
    "9RB2hpQQTK80uLP/+p8Ixv6WTt7WoKUxeWRK3WW93rJYBxwhF1N+xC8vt9FuybPXNCsyf/HZ1Xxmcurohb1ffQgyuiwck1KFWV/B"
    "MLGCEXo2/LxWMcGzx8fLsYrMcf4RK7P8f37608yRTD7ztUwxY2W+lTmWWcdATs15QKF+G1v/5/7l/AcuWpd00RNB+n5LVXGAam6N"
    "InGKhXvUj+Tjsq790BEUk/OU5LCUkBziyH19UeSrNVFiQkG/q88KsbFVmDSKmahCTNhpgeSnZyQjUE5GXddiIDueu4J0wVjfcbsM"
    "tlZZdEuVkbSz0OpnB5JBxtZoGX8EvHiKDltlJ9ULs59ulw24xbOtgVl4ByizLmBmsQNcVo8x2KLWa7I8WXZZh7nQ5gufY7PO0Dzf"
    "anul1Erct8IIGyC7gYBddJWYTfj7blSVJG8dtuxk+N+KTnlLTpMERQQYeIS9NmwOOR1g+ZNwWMpyHGxNe1ylFkOHUDGRTdXcItK3"
    "FI2wzqtpqcVz/t+UpzRdvGFN3XSkGPCNV+9tvLb/5jv9SjOjo1VtcDZsItjOf/VxKu+kl3LGI0Tg83BNZ+mWlWg28Vekf+1TZloa"
    "jU1YMUNkkxYWPWhURFlraW/Cbi2m5vKd3T/8am9jm6Ivscw5T8fj/oobPA7ncchDpELuFHe6ucPJ49JzhAXe2cotAfwOTCbp6ehR"
    "yFhCR3PqqMmEAjXMK0QBZCDZ1MfH69Gxj8W8U0jmCgFcxKcLx5FnLzsf8slfgzlZwvrw1DyB7xuRat3CsbEuxah1c40lRhSWWeKi"
    "0usE1vTEYE3MEy8nfldgGvA115D3VVJe1BUV+0QtGku+NMopX+tN+yoErouHxVw3h2GsX9y5Yc0XssZXCiWd6kWVd5s5v43tr3hN"
    "q2id7rbqfgAHQl5eb5TKcP0Rr4n20ryeWcMpEI1CtSwWyQklalutAOuDoRhxiDcaEIsd6ubVQqVolf3WKg4vXys+3s7WuPACmcst"
    "LDxjCThLZwWe8zF00G9RcLw5VW6T7EE2mlFm4M6G2/Dx7c5i6syWbKM8b7uZ7eZasCAt23aW1ROiHG92bSn//S7dAWsPBJnv9myz"
    "gW/jz0vQwJKIfaG3eFiNMe312iqejCGwOLOF88Vv17KhncRYGaDopApYo5VLLAfLjYUR6uqhZ1rWTncCTQ0LDJsKhWzzrAApdGC9"
    "a2G2buc68K0xICS63Hb7QqQJjOQBntmOQHo2EbYXAkmgjb5paXpRyNPZLp+g0P38A+hqwrfftUXrurC9OGXe5A02j5fKoeGHFtuJ"
    "9L6DgAOu6snahA1oykPx9Z9TMOlWRueb1gDF9clsySyUmdauxVWh2KWZsZwFN1tmFFKEWikvoUWPPlAlqkENibpV1IT+THprTUmN"
    "eqa6IWNota0sRz3mWLuv/woPHuq2+TYsZhWlG3LY8rCqkoIB6q/+2yvXM3rhyCP7v/l4d+e13c+evrv5lqgi6cCGUuvHNYHqjljD"
    "8/L6uZqz9kg+HERQcXpSz35PPdvkslioh+jVssbOR+NSAjyJ64/B75YWvqedxZFYd2it1YtqaRnm+0byZEnfbqhUI0QMynOipXTw"
    "POrWSZhq07+x1IYXkb+MMafxGhk+f3F3668kT4pFMEIlGEAb74t+BhHr+WSaG2I69GEU2BeGBYm/i0bw2AJGccDBFgaei0GVxoHT"
    "mZuaP9yFfwTDnYPL8/aAaJvIP9nVOtQleKwOsKSuPdC9jVOENaOMNK9Qd4yPhQqMNpUjpZj9YqkKqR6h2/vXP9t946akoVt94zQ4"
    "8BvkXUo45RJzUkJ/c/f67S8vfwpysLBGOiRLRMvHOeZx0VrEixpZVvg0I205M6MgJIMynnYKLz6U4sNnwkDRRRAGRqsotaLdKNXr"
    "w2zBwm4LQ3kGjRxAV5evwOzkwm6opHjouHZIgzQCcl//VC/szmG8JbZUd2ANgHb4cWCJGyhPZ/hFV4SCtPXi/hub+y+/w+xQP1RT"
    "XzOSuNIYCnl0GkU1u/+hBF0uAsuGPwxNO08Fb4WY3bdEa2MhEyv5iKfN52/BfCP5GeF21+BcuLt1nbVPqSy+EoXVwsnQ5ewZrrE7"
    "YPbjb50jbSo9o/Y1XA5qdmi1S2nnC9z4+7R3dXNotFxfH6y56jlVV7RAAk2t6nFN4TBYbpb7V4NOzvC9l/9Cew8103sbLxFpw7C3"
    "tSlVm/NVaXyT0tXKg9ueBqMYsCGZImD9RTo0QwhsPfvlz9/bvfoyrlT8OFGek1tGxnQsHnNw6JHbiZXzXZEqiLD8dApdxqcsPt6c"
    "Ex/nB8BpG22XMxV3eKpnl1UD6GVHhwfEYwp1SX8JVEn4R11A2MAi/asu4doX6d+8JRBgVD/kPQiuqamMOmJKZ25SUX0qsmGkVzJO"
    "MUNlmjzfLN36oMCqQcjopgkZ8dPnf13mONDp341Of9jbXkVmkjqLD3DjRYaqDFuqBu2+qy/vv3SHQnbeI9v+bfh88rHvwL+8Ae9t"
    "bCJ7hhs0K+H+U2/tPvdXS3Zd7Bx+yXdBU/JCUPfxfLCFFkHFZ9r3O8b4EFH5+fLzX6B9jkQW6yAbXXUmljKtb31YJzJAsC1G3vjQ"
    "pD0CjgTsfjxSlrEo7GgQEmEKHnp2KXDWloBFIKitKC7fqg8wBeB9maXDwxQyboe0sf3XdyJ9a0RoWBIBKAM8k4X9WpbfbIsFghW4"
    "073QhhG13MqAwL+VtiEUbL6x9/5vWAhLrGiMn0S23p5+6LaXG41SsMoUme0oSltfhy42L4jVnLSPwSJG1BcDtOiwjHfcORvFeJwo"
    "PNKaOw6S7zwQA+a643/zzrkCXiOTn49eH/hWr1zAkCohnVzEitHRVbuX+dszL2b4oiwjzZ/EA+qHFJzgUVEa/FbGB23lBHB+oUie"
    "mDs671ilwCsdZtwevqLaOgEngJHGdoKOhIGYDjrOmJwF+Izu2fV1eYG9HBfE9cGFy0/D0Dn+FDWr0eBaYTaJK2cwSf94LvRFSOpx"
    "yWFHa+ccseKzeH+CUA6OkgEbeXQc0EgfMN98+KFJGBZCKcxHrlHztPjKopluior6Gz8dNOsVITtcIkAH7jZIX5wrBzR9SWI5CO/g"
    "cix4O8nxyugrTQYBqShvjdoQYiYNA5OdqmvJNtIjvRfNY48UXo3LxH7fv7lz761fxX8XPAgF/ON1rwb3UVlcI2Pi7tafCa304/6N"
    "s9Fu75V39l7dGtCF5z7ce5riWFeS+H+xeyOJRLdjPbmc+zZMkjBIGbs6ETa/nCL+GiGA0sHjHI//wrVrzpK8XJypkbDMkrJzAi5i"
    "Ls/Jw/j3W1PfnJwcAnv6SJZcRRZFvXUJ4MBqLAX+Cn4zfTtF+mTlz46Pnyhai3U008AtWF8+ZQukBc6bXlUszpj/5kTna2YIFfSn"
    "aP3txkcZEp2BwdiiX4NxRDJqX5FcvYTz0liCQ4QlbGHm0zciBgtyotyVt/duvM9yKe8xSndfiZqwemyT0ZKcb0rN7vbeyx/ofk09"
    "a9eSzRGae1eAPsgCFrMwu7C2o45MKAyEQi1d0fuvfgx6Zgyj5+jdzbe/uPMO2aIMnFK0XaGp6Rrpo6ADfgD93f3sGk+DAD59+h2Z"
    "tkfRwhxirwsP8n51pxUvyWFmJdCCWmjRWCoOzExITbIfAUm2qyczdA+SzCC69iQsTXvAQ6H5jGmZSR/02QHWdBBa2yEwfgtlh7Mo"
    "OyTdqEp/1PfWWQyDw51dBKKYOBVk8bMo+9CHb+kJN4tw5M22SmUCwlsJSi2dkbLLmLXyc2hxKwNh4r9z5+AknBcr1yk7ayTX5M+x"
    "Mg17Oh/dhf1rtGv6lSk4S/ETy712jF+edIFrIb90SIXhg7clz90BiR2pJ1p/P38s8+6oHo01KLEkxahhVll76GgvFs1yaDm71qF6"
    "BhGEXrXBBcibKXHRYWEO0aKaYQmU18CRhQawGEDF84ES7r35x93ffgALLi45iLaXUtxKhC4ioKRNwHydyIjhH66gLCqukeUCL6Is"
    "LS8uN9H+gUh8h2GWLASy0VvYfeb5/ZfelOo8Zvkre/Xu29vxpr98d/PL3727+8yrseZ3P/3N7ifXv/jo+b3//A/E0KRGH/se8Ntv"
    "545+4+H997EGYUIcT3Glwoyaahc1TIw2BB6L0GcCJku3BKkGtByWOvmOVhZXR4vVHRYpE+i5PdBqDAJyplMA0glchT0ZT90hjk28"
    "AVcBthPXBECbamrxO0es7bxTWmjjiUMnwpcbT4tsa7ShYKgNVXrEa9uIzTZwMSlSTTULdE0S7PMEOXrl7uXbdATelu4yfAHdjsSE"
    "UbpohNGf2PuPd/Y/fA0Njp8/DXQR3atBUtbqctNQxJesLOM2FtyKZQ8lB7OI2NyJJrQhYNN234T52mR7JVVZQf0I/lDKlShLgvj/"
    "UhUUC3to2eEOzWuFRmY6c1hEB89w0k53375x7/JNZcmJRjb9VXrch2SbeFBoYW1yjnjCraKbK9FGIx5hod+IuiUS3f7IXASNieZ1"
    "NkhZ+cTjclTRg/KKeERpg64I5MUSQ4w4gwHULw1QLc2xNEkFTpl4WceoUnALxwjaF7Y9gnTDnxyV5PCXLHyrSS/j42N0i/xlTPsF"
    "1w+/4x607IgAZztZ10EQPwXh5zIjpgCdOnxrXqDvwnqgvudllAkx+Lqg1Tlh6MMC6yh+WsJs6+DD8yojZqZwLFDV3gvHFnl8izw+"
    "GNCMCsHxC16WODHGc8FH4rMYuwWfkbVieJZqCpqdiY1ci8gadNv4eHZGyCKC8cD8yivAYBAnRTTUKszB6XQxhZUQKwY11e9dxGKE"
    "F9VhANdKcK2Mj2kHAVwuw+UqXI5o7MrPQVSFX6q9i/2OuruX71hYWBvWqCrs9KX19fL6Ogh1ND9SWK5FY3YrGNKlT8GYW8n+v+y9"
    "a5sjV3Uo/D2/Ql1j5pGYkkZSX6an2hplPB4Tg90YZhJC2n3saqkklVuqkkvVUsuafp+xDX5sGIc7vA5OCIEAMcQmgeT4YBP+C2bG"
    "9qf8hXdd9t61d13U6rHJ4cPL4BlV1b7vtdde97VbAeqpJXfywVaj3o5YNrVrD1Qs9/4QQXP3xFae/kV3RX95ZXueJ5n1gAIYTlL3"
    "HAY5RUMGB13p+knc7Jthvw9kyC4a0u9KQ3osmBPCXcjqdPJUttR++u53vvbhD+8QpU+bR2AL6y6HeHLv9V+g7lDd1BgzkHVbGNQJ"
    "g7j9HwyOndzk6bqvPI2eIMtXRCRuTR+ekf00X4gwoOHJA4sxGVNaF8YXLLaTtABulu7EzB5eiZQDysr4OJEVDauREsrwUuTqjXkG"
    "fK6vTRFfKfJPxgNUgUulNWSZEjOh6DMgb/aogn6JGAUwoiiAAQWLikQUwFhGtQr2hTmFqP30Awu4PiIMwfZ3GNn4/Z9+8+kkfNNt"
    "q6Lds58el1FZoKjTjHPgWgNpR7gMbJGsfCnn5emcl4ecl+238EIYkxlulMnmlWPZE7jWCt5pZtjn4YrSUj/JepajbIsojdi+zDkV"
    "SfX6n+CQE/Ky5gewWUSoZ42yopp4p5uNkJqXuPafC/VU0kqiupKmSV9NgvbKOL9ci+26AP6Fc4KpNOYyfChlfrV/VUE0hFU2hsE9"
    "NUioubp7f+TlzU0Nl1JanqLaBobX2AIybiChkUY8hq09IDEiIjH2GdoEfyd+KP9o4Xjdku/FTTVrXZllL+tZ5rKe5V3WOyHjkD3B"
    "TFr2XFyY4oZM0CwciqeoY0HoqGfHHChg4zmLpzNX9lyKpwE5y0pSp7dRF8ZgM3s3dRPMTuBVZV9SfS7ex5gqjyiwTgsHQs/awDil"
    "nsqsgCRQGANpR8E9xZyRHpC3HXIlXyO69xuU8T4h3NPL0DntYnEzIaDn9mypcVuW5J8nJP+8dhQN90+gCbRE3b6vq6pT3U4UGXZX"
    "DXDz4xigMidIaWCI4TE4cZMpKuPcOAgVKy2RZ5gLigUmbIXWhRkTAE7x9uQQ0fJkIUHbCX19y3vJfl/77KPIlh1SbWate/e7Gnuw"
    "HPu8HiJY9ZyMj1Swatw9nAV3yvYhatDFod7NDNhsDHD35X95//tfef/7b9/92qtkLQBn60dkDvEWZf8ADvxtcg989/1/fQV9hDhY"
    "YnGMKBkn+qcf/Pu7MoqzwPJ3//HXd7+OSSzu/fh1implYD9h25P4ZESUppLWWwbPhcMI18lTsT8CJDRpK2yjmzSoFUkO2VjRif/w"
    "d0+vukDXpmUUEO6jE0Z+NwQsT3Nsidy+cDnIooKC1q66MbDnKPlH8PwBASaFxab0GxSw8g5x1t9J3JRwPP9HMtqvSLdfNol5S92c"
    "H97+d92Uyjp9avnnYIQYUuYL3RN3DGUMrajWcmxKbL4CLQzppo3WOsuyiLm8+D2KKvIuiRdeIhgVns54TaCl5xsMwaRMeVVukL5c"
    "umMcrYxmRMhQ6A0nXgnmNspcmDKKsAmLHIUZWd29+j663iCnN9L5vzkR33D17Cxdp5kyzeKLMw3Moywwr4hXRonovn1mEWQeSkbB"
    "ndnFjJwJ3zJMjFC/84YyXcwuP0dpSW8CszpkR2m0ZgCyistaOaH9Wg6AS4C638L8LXiTdb0Jriw+DfxuF0375S/FyyJx+vf/wPxZ"
    "ibkiUaSSkCQ7fyoE6Cn2Cv37S7gZErzPV4rEppszaT3PNXlcjiZ3mrUOIFp6bgj15ntNbGS+t77PBhXYakVpdhJ1yTjrds7+v5TJ"
    "mU3HxGkdtq58LigP2elC+O9VpL1YpRZB6WgCv9DBLmqtrQXoDGIG5MhIZg0/9GHYR7/zrCP6cMUk4eNBaTg4PWSrsPyHi/yFX57F"
    "w/yxsC98zI04Ul4NxofuLBhVPScS48oe5qc4mJurEMtzF8vgfyraZ6+T3qWVDPksKC7t+KyuG7tVHzDtsMZxTpL5DqXvBuIK4II+"
    "56W7sw/1JZFhkrJrsrJ54CmGehTbLtZ0yGxOOJTmhMOPYE547/u/s0QDpvlg7qD8VI4mMhTgJE1nMRaUMdte+Ce61t/QTAZ//sF/"
    "/G8iEH8gbAfzLAsFz4ydepG3xP50ZhwXf8mwpt0wznGeFDvvU+64nl8WXS4HajOioTJmtNFrG8WwxQ4A3TiTBAsrkEHbsAZ3B9uw"
    "EosR2q7GYuSAPE4xFKlHrZkZaJ1MYIDHIAkA6lScEhZmb4ewhh1ZumQG+Q8XuMeoeOzRMDV2XLmnpL8shWUko7dimVbabX6vqCu/"
    "E1r5KVj9AIN56jYa6XxMGPZZ+ka9lQ6Jg8gr31nv+Z9Dpbt3vqtlqfqZioZAfI0MgrAvbyERgC9ooa8ppmoK3S4G7Guc7Ay9uBR0"
    "W09E4cifeKhxD4dTvJ6uxq267bqtejoEXsflMOpXZfCBHXmtue5OcVT4cHxxErt91EZR5Vu3XHet1ZJpi3aGAUp0AtI74hDRzxFH"
    "qScB4ahgi5PkWr0aZPRZFI0jsIetBaZGwAZPsEeSFgUhQF8vjMoCg5fCXkk491EKhWGlMtzz94VsCUufP+/DKCN0pIcPtIBWl5zl"
    "4oljuoufVHbi9nAv4lJxTgGHQ7GWsJDNEx6qycGKX7gAKw5/wYYEXfZPWCXMtFpaEc/Nk6lP0GolhmFdjTnavA894kyoZ3zQrgwt"
    "TLQ0t3r+TTYWRP5P5HjO93JAe4QLZnBpmE21KkLgI8TQ7E56fuAOh/MFfjxRgPmo1xK72LpCY9sTm7jfJnAol+N2u/wpzCLQzkYz"
    "iFC5yNEMggoUGB0+hRvU5m1Csz0C8vEEYzTgIsKvT9/47C4GIQYqirxpb8Qh8CEeKiIejb1R2erjxoURhluoAAJanOA/AHgMgNRW"
    "AoTeoAAIcVgAE+MJAkUsd58eaSRG35Ocvm0aKId69Hvz8nhSUYcgGxTxyOVx2FFFxdyEY+RPmHIJW1dCynxg+y3AgEHXO/4snAs4"
    "jw+iPTvnnAcK07cbeEOIJxUko27zTx9JUyGJjAAR12HitlgCOD/JcK4b8W5EqMyi7JvhGEjhT8nUvmQ+mJOXADcywnDnQwx07sOv"
    "HajRdecCIASlBjCBNtNk24MfJekMNejFrVtD4pKBmHt4UsbJSs0Z1kRDbyAEW4/BpUsJqwjMZpOKqJbIumV+ADPnc791pc85n4GK"
    "j5Gqo0eM1x6hVJvav3Xrmagc8xdMEYn6bqlBSxBUHxFUmPD+n/dkHWTv5xgB7jMAYi6x9jMYoEt6tRkQZd7cmXF0RipGEvOUcS2s"
    "MkksUtHakD8l2xhYKagMf9ux04vL1A4sFsATcB5wQbmkuJtVGMSI9e3D/pujj2uTrh/xCql50BQuWBefsmiT5TrNK5zqi5fo/Pk1"
    "WiNaH7Qc84MjT6z9jJcClmG3NZPLAE3tYowLTu+BDbtS5kFPVDBpiddql9dql9eKitDEZ8nEZ6mJn/ThbgL2JIEaXgk0Y8D3LfEd"
    "SDUebYdC37ocAQ4T9djdVkcDl7UY/gEODxm7OcMPnKkelGE/8z5MtHVl7Jf7NCjaE1iqcrcNb+J23WlUqiikpV/wHl6eP4/P8KM2"
    "qc7xb6degf/fujUJ4DMZB83ZiqWy01OqWuh60eft5J6F+iKANUBA3eU84jtyHwGV4cYRtqNlJ3ncHDs3xVYzCdxloSEf2EfQ8B78"
    "AwcKNlF+7if4SpWhrrHcjjE2/jyjLR6IE8ZPR/TUntGu8KcqP/AXZ1f/sqt9qcDp6hwB7zACuuNEi9BDYAk4pa2jA99xO5Sh1obi"
    "EonAayg7bnc65Z6BEmIml/sUxQZAjs9+DP/GSQwb3mpt3zDhnqFZX0RAWyBWc4YEqD7+/XjYRZs8GavX6dnx0BlJ+Ls6bV18cvLJ"
    "ctt5srto2M0Tpw0/mifwbq/6/7x3+/X3Xnz39y9/8/e3v/X729/evwCvzXK3xOO9115I2rj78kvtSvvUJnLqVODrRfumZ5gPoDod"
    "4TGbayWxKIhJ0MGJPstXp6hjqajni3vv3f76k3tlRGm377x3+2/fu/3tB//73df3cYjv3f7Gk/sVFsi+d/tr793+zpX/fvcf9i/2"
    "U208OVk07ZPM6/+19+TkqSer+xduyR8PYBkkCgLN7OCJqR4dGmaECTov/q/y3tXq37jV5/ZhTfaenFX3P1nBZmrv3X5+/0K5dqHy"
    "wMWad+x1yoGaa9xeBKETo6iJ8FKMYiYH38mYu4Hc3EGA64hdIzzlIXndAOxhY4gecnIwRkEDC/zk1TpjpHbkaNbWygEFO5z2Dtwu"
    "Gm+44l8liKds2RXoLNayRcIrXCFKQSxcHsORRwSb8CFm8y4xkWCg7N+AhsNYMWjZBj/7YSx+IUknf/pQIobmHwcWQJvgbgcnqEAG"
    "S0YYXwL/thyaftsi3TUaA2Zab1vwLL5wF3ANURdkbicGhr7R+M1yggE1CA+eP/W6lnNjQi8O5iHQntLQXcbxphl6erpfTGF16xZU"
    "ChKTs8emrYVsUAbJvff2y5YNQ6P4+Hf/63v0zINwLLZ6fR9lFNCvY927g5agli26R8fWN7gZyp4eRg5aLrPrNbQCK0PNUhy2b1on"
    "9kH+AChFO42BO1Qj4SOnHs0MycjXMjmRHm0qnR6/5xDpMoDDV6kmTeqJazwtivbziz/85jci1dJPBbdiuK28QYzJT1H4/wKmaKJm"
    "1HII3jtJZm4mb86sEcXw4xh1wIW/xskI7n4NI9ve+9XP7n3pa2grhgpJIxQ3T5oW99673/7wh3c4JIVc5QRkr3oY1gyNlRhsyx6e"
    "DYRDAEx2xydgE08IWkhMeq0E7IACZ3dJ8ZyI4Kb9lHDEt2yMLfpQeOxY9VK91NiA/1vCmZPVCAC5cXSUl7u240cdFtBD7UtQYE7/"
    "wGJtWTaA9VCGiAOeJTxEaZYblavVflWOrCI/fYGjbjdqm3qsbCK9FwB0j2/UNkqXao3SVq1Z2q5dLl2ubZU2a+v334t485gfeB0X"
    "9gQI96Crv0VTMvmatT+0powr/uQWlFMRr7qal0ob0/Xa1srNbBUsV9J43sAv1y7T0PEfHnuqG21ZiTv/n1/VS+mR4TgqRSC4LkCw"
    "IUDwEoBgM39fzvUw9PPHBnVDAOMkdPjHszqnLs5G4bbJYY2jsB8Bkfmndx7kyM5wJNZrzavrte0S/kcDLV0qNeq17b9JL0PStg7A"
    "SFD8yS0Dys2r66suwmi91ADYrm6fraF9zV/xfwg0T9t9YdJafAIfdicDN4owWnkTrpSmpaV/+axHGTo8j6KZtoGjvXXrC3G5slff"
    "5wfL0lwoOqkUMKjDxUioLnyfeiRrpsQnmAsnSdrnCZEHXd1rMcdNRXqZA6gqqvmzHrA8lYoS9ca1OIzdYZuEb71hGGIcTURan2zU"
    "6xfFV2DtJXd46FBkHuArLT1qYcm64F+wPgFEEJBg/skJ+R/JVVOdkQAOpqJkcOiQ0X4gLPsonvFyuylf6xDF+/BjSPoBXaRFBsEs"
    "JTIylyVyXfw8eVO5gIM4mMfehFw9n1WPFXK3jv1xttLyOhfKYeLuFFZgwScWv4ditB38+f3/uPPh838LpQ7HZVNKfwG29DPXv1CV"
    "5alZWjDmAyrJCjAsxpLm1yjUFClKBsNE9+OoMx9fFskQkXL8BhsXp8oAuZg47HTG7doewolywIrakQzthONCO0A1KtoX6uPrwuYF"
    "lZ0vvvcij4q/WycOteB1/RjJx6SVpL5KbvpTqbWSpP0JGsWP1ahoKMOuJYR5+LOtw+XdV4g/eOVlofR68Z173/0l0eFfopciJaoc"
    "k7T/bhfBtho88JuyT7iMqTxZfcXOE8FehG67wEMfok2TH6u3MOr6PlQzP2mBqSSjfei39tjEUqySTVPbt691DEkG8c9j5Ck740p6"
    "pyQriUYbh35y7IPKif14oNhDb4I+M7pqClpzEWEAW85sNHKPKE7GiNIV+7NTFDS0nSeu3fqCH9x63O1U2gyN8JJskVjD/YtK+4GL"
    "vn1jgl2lOXNo8rPTGhyluHy9jO5qunTlycl7t2/vs9ijojHcD03Li77hCIyoU/K4cesKSghhoITYpEQhUMKyNXksktj0uSFQuqER"
    "GjUgWVqslh1jl7OLIGz/WqNNEOCIs4IjQO+2qE07zrYFfmvYHqZjog2N4Gb4t3qlhUljKBH/mOmILD9lKdNBzCvsDETQZvTq+TvA"
    "Y9g/ZlFKQK1ixtQ5vfyJHcsALoniZTLQb6i9fUoy4AZuoligvFiYSEzuf8Di+2Hi27yInevlqGLLMzR26ifOUEpBta+oaBk7DTg+"
    "yTs2Mx876yeJRAuuvZglSG3RGzomiEBhz7/JnnKW0V/FoSo4ILwpp/iDMnCkqpcSP2z7UJoswphqmxQlDKVVRi32DkhZ9Ke6hnpC"
    "umVUzbPsS9fzMIWDVsf0tkBbxGwdcrLMmZqVWk4o2gl9oyCZYWdKofGyOQrDxNYsr0LcpiWAaWleai1k9LsXfiYj0Zvz8gh/mNMi"
    "S58SOlVRyLBDGe157DTJRZ1E/wCfFZST12q1yPbReV0KyPlLVBtXhzUYY1Tz4YevQf+jjI/skXvsBK2m3QPKfYBqcIUp6HwgOlCu"
    "AwGqBuVjUFkp1vtQKlWLcNYjZauPd0mbdBJhLcb82W418GbK7gswTlg71OMiHrIYBxYEnXh1a6qCsClyPYttpdiwTfNfw1ZPxN4Q"
    "LQ9jO0GbmwrmnM66bGabxHmpGVgckZZRnJ+ommPTgVUb8wVL9WNEDXgYLVS8Ccq4EXydtfqJZlHitZbo6qGaVdnxAMk8HFCCQ89+"
    "OKBDALeB0pkrIAnIbkSCRCzV5OLSilpX1iIpOk4wmLY0sdDVQclHPTguEdLHZIZgRxUl3pDziiOSbHvcidQa4jOqCdvSeykB4dgc"
    "naeSMCq1faCpRdRHht/4QiMxjVijmUZIcsRRmUT0ePtpWnpTXq7aogaQxpAqN6APYmWfQRMmtR+RJ2SooQxsKkj7ZBryavGQNG0B"
    "a+dEDRJ0wOjEjmTGd3PKa5GolSNUK/OwKsk2nT+f3Yg1uRHnz6OhkP5RbJAKTiKWfGdNQM358wKOWq2AlflwgfUBmC0bfUcx9uft"
    "O9aFm4guLqBfDDrK/scLFGn250aw0AtlYDneu/3CvV/8EElbUSsWtTgCC3E7mCIxmffnM/OOtXkXbIM+z5jnCXOEYfOa5w0bCHEe"
    "NrJqKJ+Wobb/S9r2vHz3yz+7+60fYs7w19+QpkE/v/fyO2axV6zUDPq0o621emWRPZMBHeygvcQEBo808pxGkcgbhVMvffCLbWKi"
    "ganvkmDJcWqkljovXE0CCQHDcK91pScMjXg+ZKGiDFRixaHp5ZPDM845POOcw0MeLbLRaCcx5JGNqoPUKz5IPXHge3SgzliVhiBD"
    "PJTY6sZvVRs7QeLT3bPH5NEtOyv7LXRXUqYx/pVWHTOSs0WRwkg9iZG0ATrT0O+W6thpKDsNd6R35KmDDzDvQGrwyh3b3ZEWGIFE"
    "7j22t4CSZIUhTIY6TiARKg79/PmuwPBQXLaMaC3mBMfG9zV6jZc8j0yUS4YqRsoo5/x5NAahEsoehCGEAEYv2u7udZMUSE4XGVgF"
    "2c/lJLJDk6udTN46tL9ThgwzWM1wRkcNk87BEMod115P0vhilc7QcyP1fYy5cPcTXBm0I1RbMhuVSbHLOfRysutyYCx7DwgixExB"
    "m4xZvNqzqmkfmr7eIY1ozK0DIMH5az8yLQe2X3EWmJaZwcUOjsWvE9vVMvixrUTF3uvY3VXGlfBEY3sEPNHeXohJ/WxhBIlc1r4N"
    "74Jj2wIUbu3vszHROG2S1G+NiaK6datuz1uuygyIYEDnvLIzl6b8/StwoXTZDIS+2bNB6AwCWGq2zQGazXNGNrnH2ElbE9mW3a8k"
    "1im9ZPqLx9HqE0io2MZD7fj22PUjJ0z4sJ5srFVY1s5uHhpQAgZAO5eG3Ue7O2kClBio4qqMKpqd6ixrp4roO/baE2ArvJZ1QTMu"
    "HMPJHT8IBw8QJYLnsxXNDu4aXn2zWmfUZUOya1jgwRbQ/1CaHuzHp+VrWMBWE5R2SjDPXZ7hgGd4dNJShexnWikbywWgYecIv7dh"
    "Q+gHbwqZXgCygY/BMX8LjpNP4mZxBm24XQcUY2nqAXg4u+3r5cPajTYKVukNSVYpqN7OM0Ci9GHO/dYzdmaZ0Ko3PpoIK1A2V30G"
    "GCE21aU1x604SWxCR7duJef7pj/ywqO4PLe36nUtb/K8zPHLF2zjRDE4sjhDoIsRb6xIyH3r1kgGYemgg84kFqlVbVQXuJHn2iLN"
    "rRST7pAPo8xxOum4Y8Bri6hdFvjAHtXGEbk/Pez13KMhGkKPaui88eho5HV9OLlPAHXnwl0Pi1uG2+Kw9iwsGPzdspLM4GduRmbJ"
    "puHBsfXcGHMlwn8xTrITR8PPeHP8OfJiV/x0hzH9ikzL934rk3mdyEa85tux5CyC7qNIu6PP2lwsyGGSM7LiwP2qr1VgYY/iYdeq"
    "5EzQByxsx7qvaCqXbJ9usjUewl5/P6GV1zDJJK3kWnZH2T3LdgG3AxpqAct5tC9+x+7BPuxtzmAAIpN+iNi8imSnIEW1DzbTOWrU"
    "ybCvRlE4w8y4+tTp5V+O8d4UA44qi2z/Ch/ltNZu4OIiDpu1+hfmhFd2xJhm+8jMiZ9yfXYqswutuV7kc15qLjOeZHKqumHnCJnz"
    "mtvtXsehPQbFvAAIDgsKdnEc9tgGYpjOnirN9OzSCksCMz/CRDDGexN+YOfPW5NBOEMXtmyIpL+Y2hrSD4PHYWedMtx7cJ1gsunF"
    "sTO253Dv9Amh4eWjtIaf0+tqQxq5flo4wK+SzjtwhUtvnQdEMy6m7KWk7bQcZRk1EwrGq3gHfyo1HCAjaoDCR+WKUJp/URRYNkst"
    "9OZfrbw0wqmm2HmoX+A9xH5BsDteUVK6oC3yLt373j8XJEQVupFsBm1pPXVH+pt/J4l9oHsVFSTiga5Z0ZbX6R0hu5QZXJW7EdNI"
    "H/4jML0//cPb0NevEu8j9J1+hwfz3+/+FgqUoIMSSnr/9ScwWLMH1SopmN4Uk6F0s9LRJDGs4hz2hkNnMCdXce0YFHls9U3vTgGV"
    "Y8rsS15lqu5TElRjjHapYFUSsqZ/7yPTZQKlEJiEUAmUbFRWEFcT6uIjcs6ww4piBUljESuRT4R3BKotkLWK94YXgCVY1o6SfsjL"
    "jqjnCAlnX/NeeVwfOUxYUIPRSStgDwy4EyPtNvcU01VZDAcAwbv02w7xAojsCG+k5HIVViPe1Eq0zJGxNl1Ym26yNkDxa5dllyYW"
    "88QoV7rd1RbIbYVX6m1/L0T2KHyw3kbWyt9PXKR5eQpb4eXRGNA117zaO9BBi3rYl6WuBrIlV7vOMNpf8qUjZS/25zyjtFqahK1H"
    "khSJTOTT6XdwLGIsoisW59ETh1JEtNainUgeBc8MWkSmCrxi6ZzdybNqMEMxQDYbRAWc1eZ/2LiF0yzgO/5BeAumeYK3aNxt1W0v"
    "bNUTieXQELOo2w3IiutDD38+NH+0i3a6bEhM5xHvO3H/wZU3JrMiVACEvR5Qr2TBYetF4WJNymlHzx8wAMOiJZr8atx9cAPIXrGb"
    "MOTkm62BrWJqSQ6qjDdgddaU5E/KJlESlMhzTCHx+fNa3154BUVhC1gjrVcUvtHupFNmvUCmpc+/9eHtf//gh3dE0ri0V85Ps06i"
    "GAdCViENoZAriiDunMEv046IdIGdvoERclAhBIVf+sPbt+/+5if3vvKuHFiCcFmyJ6EIdx5PO6AbO7A9bSfCjCPcMjQoYqWZjiJh"
    "K24/GpdjW8gXdsJ2uR+UQyW/JDFqZlpCqBlKoaYpgqVDUHFoA3IXhTJ+5V985j1rHCd5hiMNYUlMnIvPBe6OGHdHJu7Ox9woiWMq"
    "3tdlwS4yxFFFVmRM5GYE3gmSMsTdmUUGmA+hi0LZtyH4vvf6bQqzJ+kT6QVaCHPFkvGQs4YbknG5h9BaGi5fA0IBe3/57wW+g5YT"
    "DPhzI68fidQ3td1CaPP/74LZW3IdjGR5yrYGgQ19uXMqZk5+CrPL3fb1K+lznvZSO6Z/MUU5kUe0riKQdQXpISlHb5CfaDiGK/l6"
    "uexrsgvdySQds1a71edBuVtRbihlr40ECofVRxsSuL2/iCk+OixDKnVZ1OCJ4NjCq0m5A1YWN8bQnq1gUdvYISfFrSSyp15G9gTt"
    "odGjO3e6J6QTSalyunl7SmFYr5d7PHnY9hLC3Pd/9MFPvku5y7IpBIUaRLg+933ptV7u4X3eM5ykTxL2UXIT7sTvplLV9PnVCiE9"
    "+rO8lDb+CE00J1HHOe7Y7hAzmdgzso9s1m0R379ZL4pT8MTVhx/+7LXPlD519eb15VmIKOITa4H/Et1stJF4ih7PM48hwtUw3iEr"
    "m+Qt2+aQOQ4S6eH+KemK+hPPjTqDQhaMvyYzJhGWiI3zLMxhPsYQI0gfmPY4KsvrO1kUd+/Hr7//638Clh3NpQZENa1UHhHutXA0"
    "Rtdwh6yWbFILwPXwLIaDGbhB33PwbMCLVlcKa6iMHakgOGHwGW+O0g4q2k1J3ND1mAVmsoatWjoYHkUYAIAyyT+rNiovRs+xCpjC"
    "o6ekhV9iagJOCnRG8G8EsUn1e5IfLeNYJaHw0O6BnLYzWT6y+4zlMsxcXyXvsJiPJvuer7BFqlxd6iNZ345tgg+cGEqc5YixoFFD"
    "Fw1Spk6XYgRh11VAGmJBZhNATW3rD+98Bbq0oAwP4JT0ZIQg27U4PLx1CzAbNVJ0UuKQEJgJj6I/EXy2crI0W31/YMbTNEESWAFp"
    "OKsp73kPRJJlMbDAzR63CUdO4l+JqQkFopdtiTVUCFopybp8644BunVqEYPW7SaM4agVD8rwb79F5DgFOF/royIuocl3c3Ssu1kd"
    "qz1r9WV8iDlGVdf1oG3+x1Fv2VNFFO8Zasd24hCROPulUbo6Sbx3QvFgOUFbnFKaf5tN4qV2y5TxwaKapc+ft7BJmD5wbYGyJ8Ll"
    "d5jB1Q8hXHZijRlar8Mj+X5fePrP0I1Ns2kDPmIp+fYaHfWvaaYCr1G6+DBAfEmUBGzCYjcrIMYA7p2hD+/+2pa/vsjceE4Qr6se"
    "BpaaLYsiF+jRjYAq61aWXk9GBruRDcSLPU6MkJZlqjRyPgPebI8RZtE3+wL9K1MtWr+//S3rgviIWTbeu/06KXrsfnFGKMw1pifp"
    "oaW2TssZXc6AbWWZvRaV0A+/4hstu5eyAughTy5nVLr3JkZYtS7Q2wvW3ZdfkinX1wAIeyklfPEIgmMzkQ3Q14hsmOS1bE0R2Ksd"
    "BbE/BJDGzjI9CfamQIxp3XvthQ+/+y21iirPoYCz5QiyF4ZxHqGVG6/uQASru9brm1feQ6wOyU/626fITiwWtfaXx8TDkw+9UBAL"
    "OOjwN/KQ2OeuF8ur2OXQZ8YIdieFIwigJo7g7pf/7d7rFLzSFsTz0pu/f1DyO/iSuv/ckR9nY6cpREFBRX6CgXwxQuor9PubMpz6"
    "T5CrQ5mDIp3f+uBHGLCXkud8QyOj5YyeG+fTDGMM6i7pBkMYS+TnQg83oxTWaAMUkceOF2CsSTRGNkhPmcbHDI3uaKX4ZCgjbIz+"
    "Dp9lznpLROeCxZAlKKeVcj5m7oEdYpI4cvLSIFWxqSkGJP008CABs07Eet62LsQXynJM7af/7IEFStVCODmY6hMoisdwS70bpNUG"
    "qusP7/znAwu4GTtu8NRook43Xfdl9R7dX7DyI/6x1y03oCtynjnBqgAL8VNYTlZ7OCprb0mf/bQjhxtQulRsmlwI2/xO+FWjN05Q"
    "C55CO+0JfPrgjX+l2KsUpVWTv5Swjih2gVKFkisOb+Sk21qgBTOx75oz9WfQLIbMYQp02jH5emnKdhS6WiIdOEZ3nHRr2LAWmuvE"
    "0LljnC+lcIzyDGpiXfCQtaeJDHsaryU65PhI5BEhYLMgVhItenSsixxx56rqy4ONzUIixEQvlOLiIIYPaxSbD5a6g7L8NDrjs15G"
    "BVXGjQg1Nj9L5DAvvsO/OWAAsgjP//17L7xKuSMToYeFB+Hte698Vah8MNPi+z/4ZxRIwol7/s7df/sKlTX1V+TGBVBE8ES/BMRx"
    "W04J3449L8rhgvMYzyDFWQanGFt/ePtH977+G7o285hlQC3HT/WicKS7SOY2JVqi2MOUZPJ3r7//r99WSe8Tk+hZ3AKeIwXjX5hy"
    "CL5lYB4QmD8Ch58hG11lZphuKdbAWkIJAKkt4DirvsZsgmHnsDpGrW7A+mtROFd7nSrPBibUNaGdHKD2NCsiM3rg4/3yGlat7AQq"
    "DCo1FSSmHwe4jXfffhuVl6/fvvvKqx/+/T9h+M5Eyi6lbEaY8m+yakXoHvVPAH3ooZYEU2R5YroLxfxqAsDNeh3YsDMfPpwSk/Ti"
    "gn8C106eQk9dtUKsmL5biyfP5PrLfIjYiwj7kmnTZJ607+Ahgln+mbEOGI9fy7iqrZjW1Vt/ePs2EF3v/92XKDLld1HrfPt5Kokh"
    "t99/41vZ9Xzv9gsoTioJM2JSK+ujp5dJPtenC2gZBLATBq22peqjmCbZI5qcQRx8Tpd+niQaW/TkjSgas86E+sCE+ooJdShJGvq3"
    "nRpeu3/gRjotGawW8zwlUourscnkBISmMBLSEkEc1DJ4ljEa3SO/gjWz7Eog2BUZ9HylsXjt62Ulz61k5YRrh5jtM1gS6FbAv5mZ"
    "JqEmAV5eepWpMZVjh6VDhrBwqZtK0oNkfLE2ZXJnqWNCnainvETPgh0VsUCKRKXCgCKXgGRnKI2KSo9aY41evw10NFOPJcsGOsuo"
    "WdESntjoWyPP+lt3v/ZjPcWlJcMoC7Eaql41FOsLlae0esbwoJras72U+ZGoq8QUQ1raIETrAm3pOSAKFZwy2xrjLIra85LpZvBa"
    "Pge7orI0/8bWm3mbcZGIb0BXbqW8RP4wGVvEPaFcy2fdha9DZuX0WyCBUL4HpA8VE8++Bp6+Rjw//WfpFAZ/+4O73/9HXMI3fkd5"
    "6pRa6cdEUtyRqa6TRFa5qounT+ci0wfBl/mR8xa38CgUrukwODTibKcmJnbHxnAEiTIzst0k1eGodeVxzDUBwD5i718sLL18ybbT"
    "eCl8uZPoWx2jrTVqrJKkXvIlm7U4sXutcrd2cDSZI9OFsqBJ1JGPJM6EZYLfp6ZJlcQA8Poo7nZhXDL/VLWDIr4j9OAbwy9OjWmA"
    "CUBDnrYRLnvy3KdklBcfWKiEVn/4zW+evlDuiKRWRpQBSggF30USCYQ0Eenryz/7w2+/RbJBATZM3UMFmDWKr3n+vJj4hF36HJwC"
    "Hk+gxx7AsR4bgsN5U+pLos1kHjckiQtztBFpkeRlM2JNKChmDnPcxnMiHFMxMw6zp6twBgAoadCepGB7zyUJYqhJEEUkBZl3LbAX"
    "GGtDlmi7FLBDPjp1Q+MQR26HOu0td7ycHB0004Hz0ytq2T0czlhvKXWXeylNgFwlALL95IBhrHfjwog0Q44bnXJYEe6qyD1JJ0bl"
    "RFM/9Wa2VtkLbBwX1wj4kItufKEGKS8b9i4OOwnrdT/DJnQ9zsuekEaOepS9whHb1sy64PO44ySOTPqy1j6RjVwmKoyfRIXxVVQY"
    "woykGum0rvjpmDQdFZOmcnoqZ547jCAhpqjBIknjhPg/475ker24CyODzJ5L2R857VsWv5EQyhZjyAYN3U8nDlLNhrb1CZJ7lmlJ"
    "nz3yUM5Wr1xpnOngsWAchpBqptrYT+CQ1+MzUy2V+hf0h6fI7tRgT6IuBQPUIl2oJKaYCFX3aEK+eqj5/mC1wEaOnGL7s/GQ8h06"
    "pGj7Cp7Uh51h4hFktFA/sWlWj/udCMBpckgASacIzSxVyka3dcXl1uHqoh9ASFbwJMC/NkB5LTjBlDhk8J+MJ2gpj7uMCIPsTk3n"
    "TOUipnm28HhwGZpb9Yy8TZbyyelsf4ngfzJzjdOsc3++WDhJ5hXm2piNS+FRfFqgK1wMSgaIa1SYuQMIAmgP06HI1aI9AQKAlH0a"
    "bNieCT6fKuBug8QNBVFBYi3MpqodzUotbbUHxdc6iR522IrbkRY+XjNKNg3bcrtJTNsAiwm7SjTjbQsHbLbGOj2LTh/HaodK/7mC"
    "dQws5SopPYZG2rfEC1Ad2qiLsB23yUrUsap6rqD2kgQw4UrpdvRSsJrQ6yCAVWa3wGJdqF5NVAiZkQmLxxTHpZ7pqmHcY7RPdPee"
    "bs4mRWDYY2Rkecvt12D5hUeDYdmcUku/d/uOaelHTCKaa3219N/vvsPWemQB/fZ/v/tbzuXorNr9RzMJlYYry+CuFBwfnB320N00"
    "BXV+m5h0B+7GiWNdcLMg6C8FwVLXHzXPDIfJcfcrEiT9s4Kkn4Ckuwwk02riXNbGsm96ZVeXVp2yy7+//e3MThUoOg/8viXVrKi1"
    "7voT0sY4a0mG9TWBrtB6MoTL6y/HDqC7jkTXN3XTKoOpFsbqgoQK2wWGpok0RBdfY0LU0q4IECfOi2EHK3QuwobxJ8AtJSej0FbW"
    "aFhb/BAdP+RRFvMtGu/zb1s4GaF3d4pKZYQygDF92SYfX4tsIIS2yKyftF5sAywJbaFvH3hTTd5weNA1BXanpLzGwGsGEL30jd+/"
    "9K0SOiU9/5/vvfgO+VmWchATR4fW8FeJIvzBh3/GKEkpku+vVrHHTTzcyW3W1+k+wAEBJxLpHju5wWIw+DZ7HJOUStGEibxP9tZv"
    "pWK3ZLxWufiOr5GNxgD61Fn/SivpB163LVSMVdGVhH4MVVy9MDUVy7JHMufBifDYf8ydA3GV1XL1NToWica+SS3OKfFGH6nzaH6D"
    "PJPD6OpwWLbQ63Y2KV0p0Q+rsm/PWqFyCsekItpk7UFObpYjNMFXy/ZM66iGJlhAndb6qLa3r8EbdmW5GY5xcANy33/Gvlax13bh"
    "bM1qI4olkQ4kcKOFX9Aw7hnarhtCb7Y4yvGbkfGkjgy3maO024wotiO7OrkB+34NeMyjGmWaq8WRG0x8BMeWCGtpfIFpj1pP088h"
    "sB5fLD+wuFG9djI+rjyd6TrbYF5j9DI1yt7QH6NrT5gHWiNnoEIe7Ll2Jxvcwe4aZG5fpz/7ImqCInPJnI4iu54CYN22ArG2CUjl"
    "pwl49sj0rt+yHlhcu3Gj5pHJLVqjWftPiyAZ81a/vcCMHwog7IF6+gsywT5hyrdTnrWuzM6fn2MuEwTAeY1+DugnxkuEj2vz9syZ"
    "V7QAECbFjill+gnFPkbLyR5aUC4iZ2yPHZk4vDq2PUdPUrLbKfdzpCMnp2u7sPuSnkSTEyNZduT1nOFKxutmollL+ZYypy/HbFuA"
    "9C10DKM0LUutliJPpNEy04gOJFAENsONSnmGnqwvfPPul1/MC3D0sk4I3v06hk6C8nhpYhhGoaFFtem/EM7/JQdKpZvsB3rzUmuM"
    "13Nuk8VqDwu+vv8dtLTiEKxoXASrow34teUSlqHXNw0O9wr1UAYroBILkO2YTAgB2zKqRXnWk/mtqHQY0IhKSUGNoNgR/vHyxG8r"
    "C9moJW9fuQYHHF+N3Pa0fE2JRTlgBDgRaBAm2GV7LTBjtJ3i5F3CDJsI7VD/+v16fS/jQMgtGtmjFVmRQvfu/KVoW5le08km3//+"
    "r+/97T/f/fI/kw5JCuN1uwAaJSWqREsWktx/Q3cDJ7Xom6d29LE5ni9nx1B2gFc/hiCU5AnQK7oEwV2itIa7w+cA/pSfVd1njnk5"
    "urU5X47Cv8atDU5yJUMMpirlFad/4t7dgYTOvg14zFEYvV0HpC1puz5wZLbvzDHwirMGBDtFIon0SCSM7eRLQswyTZqiNu1u5Pad"
    "BQmHGU3uEnnIxU5sIDYiZ8av47A1a8+dObCCnN9Eyuy4ipbzKx37ZNC6MhCElShLYTl2W9TqzuzB3fPnd6tVGzMZShTNBe3diviF"
    "EW/gfyINHgrQmSA1SOovCpJaTM+w87Cj1vVyXHuWzSRnXnTNJVdxDh8BpLZOAMOGPs6CPz/tynqd3QV12TNr5qtNGfkSJeupXlRA"
    "1ahy6xYwsf6SAhUZTBPDT/h2H+M4VSof4TK+j2tYePrcvmPZsYqxYaOrHN/LQ/NeLtbspm+eIgvu65NOCU61UsbLDMunyJTEodbS"
    "HdOBUgun5yh+It+mHvWudUzy6FYb+7VjFGRXljgfAZAM0vPRpQoG0RGzG1Q/KPsZjweCAkBHFCfyNpnk+GSuQ1FYsuzsvhaWRUMS"
    "Tkhowl8ivFVYI2Ss4QqsETPWiPOwRmxgjVDHGgHpr9hptrJEFKNdlqduP+VR+jHdJVkhm+AYdwVjAMsTh05ds4x0B2VcDliMgBYj"
    "hklGNMmhHLTPqC5UapU0L4FK4m5LulYz8xFgOsZdDE0H1PQN+nfUGgT4bz9hX8eo99ib2zOjPXRVzdNw9OX9A4AGNc+fH7M6NTzE"
    "0E2KBZIK1sWsvFaXFP9xWg0yw27sS3WlBiklLUC7dkYrcoxpLLUSJ/Ye/K2skndTAoecgH6AqhPGiLHNo0Ec/pXvzcqLg2HYwQwJ"
    "0KM3QZcDaH+oWh9orcugeXmBC8VcVRlkh4/hChHdaiOQ+H3aUq92pjn8cgQYHY5txZ4aXOs0zYrKcieqs9YxTIFHouZxhLGkE6fn"
    "49aVY95DstMgDETvVCjkW9DzM2a0whuYfLJ9JK8RKOHsYU7MvWv2DZPH5cKVQq2ZWq7CVu2p+oiCkeN9OfKrgCaeUfQQhrK8WuFQ"
    "ms8k84dVInnF4kZ5KlfgahoQb6hx2o1mvVgrd7WCoeeOMmo55Bd37Qy9VupHqA/D8FYeXGpdzRXIGruTWLzilN30D4YSl+HOOFmP"
    "fVijXf2MN5/QHD3pIxiI9KGWhA52p6MUgYAD+KlvCUmEoP2satW3HJUUOYL5kiMuY33Y97+elo/tBIlUUn5yUGJxnPWT+5yOeOBa"
    "KB8rt7lj5TYXiEsEUVkfpdOAxAH9Bw/D8w2i4bh1HPhNolG9qOYRrFwdDoHa6LYsPBAWheFNlYMdfRiey+QCfXE8pHBeokcRaDBs"
    "sx0Bux5jr59FAvFY6G5lHNed46JAbdPWcUpYDv89hFmwgEG8RrP8PAJ2xb7aUtN+cAq00vjCtMZU9cXmTqd8tW3FmNnROggpClEN"
    "KVWELjGuxzx3yoGbOoTZ8S2QrAWLL8q0awgwyeSuB12tCQaH7nOW4966Jf01E7H5MpPXCK1eVkmFxBc+lddu+zw9TaQTVZS1RxVn"
    "Vrm3rHrUmZasCz0hvziY7vX2k9Yew0dizINwKU+kjWBEWp4VvTZHpENaVjx2+1kP70en9gJveA7tf235AvXd8VKTQwyyqa+/wiPF"
    "PptjfzgsEY7JVxQ73UyGu2VW32l1q67LsfZPcwXNtZwCrDnuoIProY2+wmitlF0k3vNxLfY1D7sxZiOGiuNOLD0uTIM2+pQ1XkPq"
    "TvXwEG+QIFXxL2TzgpAaTKi1v55m4gWFmLSdI5pTIGzkWvuwmkMjwFJUix/c2KyfP0/Y1z2gjBWMJOHbceXB7ZxPX4RPc/hUWYiB"
    "2M9OOYCmCCQCr2HUQzt2tKhNqFCR+Heufn/xBPE0Vk54zk5+DKzVRcYei4z/GDGynp2qGFkdpFjsNY/CrceAbSfK3QwDjqHc5cXv"
    "kr+HYWMsfT+EvEeP7ff7l74J/KGMBvRmvpsNRchnr5NEP2nEmLpkRipDyMAAZdo4uwdDyQJc7bQuPlkrj8fxcfvWeDyhv+MR/hxV"
    "MMPR30yLC9xC0f+428OCCTQ+JWQGbgyoheP96Uq4lAJub2j7BnkGnGZQO7ZRXTHHICUtEmEw5805lkgrYSjS+mj7kigp8MVydcS8"
    "FRn6rrmp75q15gZo7KpnVjLYgxaFEX5kGLpxGW5cjDxyFHvdG0jSlOdJDNgaxRWt3Lo1r9SeC8MR3CsNfGzYR9Lj0Q8CL6J+Lg6A"
    "qNXfcm8XBzs+Loty7t62FbUESwW1jqqz6jbQuvOCMnNsubqLZWBJ56mzJFntSrvWg9M2wft6D/cAKhbHNJ63BhSWRLEuqBMDEgeT"
    "yHNIFAw/jm3NyIUOyYLdVeusEA12hPYCHN51vsTrDm0HLHu2pAQccqDGqcyS7qQYaFfFnl0sDz6bO77ckukh5hbKG2VuQWOgJ7qH"
    "LAbvn7TTKUWMgzTRgzhmNn4Ng5t1zp+nXd0Lgd8HBEjvcpwRu601/BYmadhyUKXd41LX0JzYHrcO7VGrDIw/QMriJBE05Wql0Hfe"
    "7zq7FIxS2pbs1uCnYh4Q2gYp+jiF5Ac+krsp5muBwDrDWV6uGyIm6Kxjz+1dFDPkG0PAJ5a09VtzdVZmpD+PCvSfpEjnGTpBGJcd"
    "OZsKYoq9/X3So0uRUwKjZMQs4kJWdsrzvPjP85z4z1AyQ7DPKci3Edvbnu2Vdy/kNdtuODOVT6FS+YR82FcIBBvMhE5asdsYoygh"
    "/HUqCtWQhWMHA850VgpTs4JwF8Nxs1o14jQBFr8RXOnQ68XOEJAgjA/+neuhofosDObyp1ujGZLgmx7MSwTjGJWtFYLEJHljUsZJ"
    "ZGeE4Eq5fWB1Fn7HySWFcbijG97kOqeenmHXc2lmZGaseW1pohrpwltcgEf0+cyIEsnrY/qIPu+FY4/M2UdF4f6kDRe33A/Y3D6/"
    "bSXglPlP2v/jADA5DQL2BgG6fACJbpUsWzxAMUQa7poSvozKVtYiitcgSU4U6nEKccc5ZL2dBgSKSSOXfRdKy76E7Ed1plm+LelP"
    "WB4vh7eHxUPmiIYix9IIY2Dmw0+mR+s0WPq8N+GQLGtjSmxgEnuUqQ6ouvY8rUoDHLIrUBUL4DHGvczwcP78DO2xl/KNM7zaYCqN"
    "957/MWlv31YBhYVZA80oUcXNxZxmgDszkzoScorZg3Ndg15taH189Qx9XMjpg4gSGX497Z+ZNcj3xnw8b0wAUvMCVyjmJBMbgI/w"
    "u8LSMu+T4oh4Bs966X23RcRkewG3orPWvXVrrWenJjQeuvMEqQwYvBVI5zrfF3dH0ZuXdkclaJcQZ+mK9hVa5zjQqv1M2/xdF8UU"
    "74g0CXjxG7i2yBYK3y7u/3BSThy19Qy0T17cv/DARVukcxbfkwyVTz4JrAD+fSGjmGXpOxZw4PmCUFmJ0BjYJ3G+6eEYlu1MPGO5"
    "5LPh2KoC4WJs08yhD8dzE3YV3/lp4DsfMRLoejUKPiiF88PWlbVhrSszYALjiRRmUB7WxrZfG0NvMTKb4bgts4oztykrDxWDb0et"
    "HGJWRQFJ6Vhj/JoOkRVndXjxQdidm9YmqPkYat5rQy1pNSVcBv4YU5AMa6NDzIbsm9mQ/QwdFEcp+dZQxAOTNkUo5UIFc54rSNzN"
    "+plJHzZYRL2KeMHjKpYpGvkvOZGqrnkmHRAmjrEwJuT/e/ftt+69+OW7//hvFPXmzbuv/pI9xyfx+fP495oxjxV75aypWq+8HsAc"
    "QKcf/O63d7/yj5Z6Owrx7b3v//red3+JdNDXX737yqtsQyaH0rqfQXCqXc1hW6VpNyyr0xsQHI1SC4a+fs/iplaKa8WpSu0DD2qM"
    "OJVSUaWOYfcgAI6tbVwFoB0JoC5liu62OpgpugNwKpJF91rddjedLLqbTRbd/ejJonsqsJuR/Bn7TyV/vlAGnrYDPbat0u9vfxvq"
    "4gPFyLJdmRa6aF0M/9U1Dd6L6IWrHc4MjudDwsejAbY5UfHhSMUP95hIF2ADWgNCdeggpkrcKMIkdNzymzU/7BtfmmpmxWOg++60"
    "MSztS92YQo5t4+Qp2XaxsUPXHylaHEMhUdC3jfFxqV7aHh9bJ7rO4F9+k7GD+ynbcCbXwwNSLJkrlcwXMrJLpmGtj7H2c6QdGOg7"
    "Qc223ypHnL0+0rPXA7am1N8Y3ADg+gk0V3oCrtS4RIED/kXu2ZeUhSBF/Hnz/VdeTkL/SSM+QEF0T34Jvz7/czQtfOEOerC/8DUV"
    "9cdyfBWxwdfCNAAOM2q/lSSN+XkqNgEv5Xu3X0iNjNMe0MtX3//+r3Mk0Y7ZSZog0IKYnc6tu0MvAozJfJp4WCm4TNJaNhyllc4A"
    "rQVB4Mhpr2p2y3+HylscADryvVnCp9kAmDiMbQ6/A9u6+/1/gGsJqd39YhNS9t2yy/kbo4UfLYqWadhDPZtK1qsRzGaU6L08gtnS"
    "tu81fdBLY1eqEy/AMRlSfEpUai27eFDGMOGejSgnIDwTA4qJGMWgiZfCMb508koad23kNJ2Osj3q2r2M7dE4UTXkGMVkDCnGygRG"
    "E5mOzLyMXWVFJNQFvTI/qgx2HG4NdiUi+y9bIBV7iPqxXrkvAuUFlFasoHv1s5VNQogj6dH0+u3GRr3uUE7C1HWodk+scELtAZCG"
    "AELkAT3BuNuVvHWW2zkSKnZCV46afFZZX6xVP6gajrGqjVX0uafEP+i0LQMlESrhKKIcrIl7QzJj5c46A4oe0uHs2eRjSdeUgltv"
    "zoZxab/wBe42W7nQhrOJywkwCoj4VzA1RWtyYWQqfq8gVxoWxuZXfKT9MZimLzFHpVs6uYkxC0mO/fmbd3/8XXYm1vwJ2LAU9X+2"
    "He4n4hr0Yq/tRft2J4/JQi7HPX+ehFcU5R/1DK7J9rhoZegi6ekyl3TrlqtTfKdux7AnifOelfW6KQq5oVghjRHCp6VmHAYF/ywG"
    "WSgujeEM0EJLIBGihLW+4D2HziFTFUVnnoHKjBn9avRd53+YxlwyglUpTDuTVC6YaymeD20UDDyCsYvbn6J0lHByhX9Z1KK8ieU4"
    "SwoS/6/0zZxqVIuxQClPIwo6e+P6Y5iDTFr6WoAv1z4XiI5sWVkKB/ISlXS9OMcgeiVz4GXeMtkg33xUOT3g8/+Z8g0p2HHAHq9j"
    "pCvEJD+796uf3fvS196HkkAwaWEppXW1c7ZZlidze/EI0AMRAELfidDclddNmBfy2iU7G891W5G9fc2vNEa/UiEBSuj8uOYyDU9O"
    "2eFhZUGmMUQzolfP+GgyKO9ZH/z0R/f+4evpiGs2+juMK4KVFLX2NW9QyQtQuWwwHW10PiWeqk1hWUKCMr92CGCGWM0bHQAhiKng"
    "pdDBn0xQmgCUohROHEysSluOFgq6U3p91PVDoO0//MGv7v6I5BNf/c77337HwljXuG9kNPLCW5TH445lM0+sb3MJ46lMhJTPtmSM"
    "bIwOxOp5HAJlPNivOH6tN4ox2iH8U5tKbl1bxLsvvfr+t38gF/ENPaaiyNIE/A2PcJWxlLmn2WAu7PvVM7Lq+zmrS+txn6urzYOX"
    "8+NfwR0g2f1wcqg20krbCnGKuQT+uD8RfBDDe/7ivRfepQi2L1H8ORXYgWIRvPAGyWHfgptXBsqvOECYBmEHyTtGbtJDL3cM73/p"
    "h3e/8n9StkgF01btJpPfh5OaPo+mdDVOrnU4MmRCKNxmYT+0F3jTV4xBpmTHZnxrzC6sCX2AEBBt7aMoKgnXrEKAbmk4ZTInOTLg"
    "oABwkBIS7EX20OAx2FAgmi9EaxT9/0YcAonpoRXuo4B5OK9wbRRGnkUxe+qWMP0V10Yd8wX5rSk6AqA1OLZnNDTJNmRP21YDTnfd"
    "UnbEJ3bYonA1ttv6PBnUkbgCTT2AjHoUrznKuYwsYoxuGYQ4MfAitOmNQkPUDYNZm1JX5PNc6w3xsz1qjbUSUynFGyMvkvm0Jj/N"
    "W7znaEtnz1oaAPC9iuVhbNAUEsqVW7e0Eijf3kU3ERjyII8YtI9aAzIeidEd4MYE/72WFvtTD0AS3sj5APNEinJKYru/mTLFNEVd"
    "gFASTO2rrCSAl/ZVUhIct+bnz89rgTfzUPCsD2t0NIz9NS3vpyzm3BAHDebZaN+AidXGgLVShOgS/iTv/u8OuitxCYZd8V6ImudO"
    "YuR/39a53Eh+HhGzlWwLwijXEG4PmiJ1WL+LVbVKYcq8OTPDg7lpYbHA8o5rx04vBm7glHQlYc4q6pTqOPJFIBvSLaYFsySKEJIU"
    "LYZ5QsEeCQp20D5qP9O2nrh2787zH/zXu2bmR6Sa7r3+CwreQnK4O3/4LUuiKJ0D5jOkpHq3n88waiL2KHnWp3WzmMMUBW9LiPdX"
    "k0wCefrSVeqq1IuUdVpDzujJTNrfmM3AZGJuLPe2WfQOhqtB0SWKN3XvZ1QdJ/FV72RTdt+PDS20QzHNhaD4FDnZM+fPP47Ydan2"
    "u0jFrcnVNKgSEIVJth/JyNmzsLNMlw2rn5EkmzGI8rXXRWN6BJCXHBLjsdSgMHyG2FAzpH6y7nla8QIoWTLURBkuQhGsHaHSSVkU"
    "FjpKAlGoR80SkqJvaJHRUBfEe7pbi9XyPv9zOnUvmY75d7IJgykO0T+RrPsbFLrCyeniYwBMmPMR0UakTIh1ZQLdvsOutXwZShnV"
    "oqFRMM5wRifAAeUSzUA2eyofjiXR++d54fpSqTEFQlzCqorTZyDIn8o9+55iO4tQI04me3BphXHap6Nd2Mmldi+/5VzRFFNr+RDz"
    "xvGmPlBjDsomQsVjwKw2xz4QR8tWnff87MqSjK5kqQolJ25/iaDkWxkZ450id+RC2cTdV77y4Ws/xghgmo4dFUsYy/oHGiOpH87X"
    "VO5kU5MlEiub0TbI3PF7RQvNq91Nxzr54y53l2Wigug8w9pPgaIsXkwkyEkydrUi5tXLzmupV1SODVLHCP5I6JACby+ZgmF8OcqN"
    "4zlykVxcaPLTKamK7anKDLaqLFq3oXCmLKwRKTtWbUJm1MpYJiWSrXHkGUtdQ2fPW7dQEq6ppQXUSRk4bgQpAcdqHxC5s3d2XHMD"
    "t/Lx7AuHnadxv3n3rf+6+7vXraWk8MiNDo34FqOVDsCpKJ7utL8jqzWCj6kKAHyaZYxhXwHQAIBeObHpH17CftES0rUJ/0ohGz90"
    "Ql/+xJTBlcpHm5euJTnBwOM4gPaS6N/LbI9IB33v+78rWaIhaeRm98+2apI5J8Qk7WdS5lWptbRpTdq8WKdMQB8wye9owGqp1ahF"
    "k7Dk7aXjTtbz2mcftVK1cZdWrc6SsQ8xD9VXrCRry/7y8JRpXCYuEOOkDNPC6+FKrHdupOTYAKEsYa/fDylro1GIzDzT3MdJ08ft"
    "6+XjrLzZYUHFlUb76QcW8OPk7u2vpuKviWBTJP+nnA+KUcNIrwbnleRUswutJEnWIq0kJcwuZIgDTdDT3nV0E+2b8I0EdKi0Ez/3"
    "df0KXJ432zfTlmM3s5ZjN0+xHLNjaqi+n8w0UQyaB1pOGc2jT1UZnr7T+uwTASYcVpZV6tDWtU71TGYjt6vobWRfrcW21vqy+Pvm"
    "BbfHOShtMYTVDEBKk1GpM55LMHzaTDmSY41MaTennC7KsF4hA2XxIWVDfFqbH8GkOJfV1O2K4X6eirwda1lIPzWk3QpnPtn9+9p1"
    "8jGzgW+1Z+2zbvVMbbWGHW0pntSTN2QnVqIDs8L0liGzlM3IURqzpvu4kYNG0kbQN1EMvLZ21TQDuJo5tUNcTb4lx3jwxksCOObr"
    "9qdpM+dpnqLP1iTEcCihzP0aQVt3/+uOSG0p+MIfCBws9fvT+7AjnRo2nDf/r9iRFoxhZS3/VJmQ7mcJr/s5lLr935JzyT2RsZ8k"
    "056KJ5QGijPOlR5YHHhl9aVyInIp7SdOC1SvM8V6H2nEFPiz8IQ9HJVVP5rHxArZslnNFGEqTfTOE8k0H6e3bBLmHQMcdz24XSMz"
    "Ljuax64SFtW695vv3n3htfe//TPA7x/8y6/e//UvJWmirI6uJeE1X3xHE3Gydh6zGNtejTxKJ3pJYY+Pny3TGDMd/g2nuMTmNHCH"
    "84lvILxrH5lxPjJyE2RnBaO6ZlL7nx7bCz92pgzzy5MkmM3vWSb3+TIu2BIdmMrPllq3T09tdq1Jr/fHtQxwcj743TfIUEz6UhQH"
    "wZvq6TPleKQmd7tiLF7eGq1mWxevlN6BCXJVEA7+tBZPKkuDB6cvZtqXsMM100t/GKHgaEr2CyQG+ZgYzGmCxt7//ptWBjnk7Zk+"
    "bCDSj0YjN8IYHTByAiomkORONJq8FeWr9s2E0n+o9ch47yoQVftQGk8o/n//VPLaX207wlJYtS48BDyAuE8e2mtqgZgeAmJB3pWE"
    "Cx4iudkyAz0jlxaOm/gNDxWM1q1b8gVrKp4S74Ebuyqyo1ql37/0zRIagACRHlYc9YXusJuVhNo8Lf0J1rofkEQXQNHjasS9MvAu"
    "9i5MEfGigz+eF+AKJHsKbIXjiAgb3Nw4ScInDbuttUYSribSjQMjzVg3E/7iC+ho18XMuTforxoZasDLATFda2ie0cUXZeyibj9E"
    "kQyWZBaPRZi3sswgIYMl3Lp1yG1VKNTQIfTUR01hZaF+whxU6m4Z7ecmhlpbJXYK9MaRSUQa8uURRbTSnIT8C2INcN6r2FY/Z+Rq"
    "O9IevsgPXu3ZIz8uVmTh13BabBO5XEiXk15Jz8aUzgIuE2MaziyoWHjhhfeef+kPb9+++5ufCC2hUA9ReHGZcBmwuXfssd79g//4"
    "35Qm9nvZ1qz9rI8vUllxSFEYDXpMvPNq9OPxSV/mONeuQfnpRBa74T1b0YKe5QXwdscYRW8KGNOrTX1vBlUFdGF8SKDZ4Qm77UYu"
    "UCkU/hF/WAgA1mEVRbN9j35GxzkZQWN92yP9Yag9wNBGFBmRps8/dWzmmpm1eKSIc9E9XgaXu97HBgV68Ln1cqoomhbxBBS/dKgP"
    "6gGZRNAE1C/IwgJWccb8Yj5NvXhm+v9D8x8Xmk8UppI/RPwblTQG7qCR13oiYts0L3LjMLLaQBFFSA8N8Tqwdk5tBaktaGSn3wfs"
    "ugSRdjgOKQcC8TAphjDzTCKA+cH4KLaxlBt5rkUWbuk4OCcYq2lnFYTtadcHALjIvZKKfb7DX3AJHmk0CfA7cTT8jDdHxD0Z+L2Y"
    "fu+hdMl6Bv7rwH+H1n4iOwkqRq096wgdy7Il0DlbtOsO81o9Mutg+KHs/GGXM3GAxKLMx0nEI1hXsVEPzR/F4MIhxiqtwK0FrGhU"
    "FohmjoewsnOMW/fgxUkn8sfxlT8rlR4kmqAUecOWRT8nA8+LrVInCieTMPL7fnDFwSY5qiCBgISg/UW12q8e9J1z9e365frVHXwE"
    "yssbwptHGvVGg95Erj/xnHONrcalBpcZUMD/qH/glpubm7b8r1bfqNB3DuKUV2CbCxD45H1v8vcDSs2ypAEuUJ3EURj0c8o1REMI"
    "oc65Ry49sv3ItnpRbTrntq9uP3JZe7XunNtqbm1tPSwm0IH9cM5tXt+6+nBTe1UFNoe7u7xhN+pbdrNRh962KnoZTPKeLbS5yYWE"
    "xtcYgsyg4pzbuH710iPXuGAU9jFWI4y/ee3yBr8kuzx9XJz5/dz1hzYvbV5K3miDaK5v2tuX8P+1DTmGcOyQx3Gpic7HVKxu45/a"
    "Bq0wAMXUjcoMH/yiqd4QiODLjht189/CCjfWGxuNLXhmaJHF6AmLYdx1+TJZXOqLd18NgB6TD83UFwEFWKCXDBt3lV/BWK5dvnbt"
    "YYTmEcYzNMpUCVJwW7NvBRiYo0w+YHfner0evIhwR7PlBt0otT4nFDsR46SgiNHpR353B/+CXkdjTBBS7YTDo1EwcZpbuDUjP8DA"
    "h8B49qJKCa6c0bi8vlEfH9vNrenM3tiCn5VUC5jswNnYTtfeEXxDo16fDnYO3M4hOp4EXWOnofcwSi1iD+4DZ6NeLzXWx8cXGwBF"
    "JS4wcYMJf65OUYAG/waA1CK/48TuwdHQjfB5sjMOOdmXA2jKRdSwg0DQG4YzhwMd86qUHGdC0eOg6EIb37lNb8vtNi+ti9Hhmosa"
    "zPQtaAg9d+QP544fDGAEsShQi/zFDMNQOg1YTrUE+Ls39I4dTGcmih4edBfJVBuwfDxLZD3zFgZhZAT3oh9UKaxWc3wsO+0fqB32"
    "AzyJVexsx4WbOqiSVMFBEPGinWeOJrHfm1fpzoW+xeu+O3a2kvGuwy7vyHgBMDh8FMAfuV3/aEKFafCbYp+MLcrbVXHKcJ6TcOh3"
    "S+nzpu0Apa8ZuxRZdDaACVThqePB6s0id5zM2uGzbsb7W+SAmsACYg7m8MxTnTQOF6yf15Y8brmNyY8ZyBENnjric1sHly51u2br"
    "4qXWFIoZBKCZm6WVOfD7knffSG3ohti+KsbDJPDU6g3cySJ3cgmm15ZJTWMBdEfHj+dObQO+oq/agvAEoAencbHaUBDER6IQDiQk"
    "EwjjX4AtIz6lDiOrHcAzVTGzegFmgSHMJgujrZzjgHC/ncA9IrH0MolRH4Rw8kdLhq0f79mkdMBIYsYNb9XrOYCM+YZiBD1cOOix"
    "Wqs3vBHXr02ODhb6cUcTjgKsoO0kIIW8jlL4b4dqqpfecOiPJ/6E1pWBCuGo684nKmoItlyiv3S8M/H65hoL3FevfyJvX4gOWwUV"
    "GLjmkrYpqc4VQsbFb8htbG6rfUP4MBrbhE/Fq8jorFnbTCG0ArSZgAriQwQmbD4fkeUMe4+0QHwHed0Wxt7fX+TgTqNqDf6Chewu"
    "MKRikyZKkNnM4OjUWBIUhVciLvJxdTJwgSXSbyXRSRzC7gsEs5kckM1sJ/k7LSnM5DiLi4lysUBfg0Wy3o1Trw/cHwWJSKc0YMFx"
    "0RHTeKlzno8zcHeaxvFGigUhRZ0DOmIGbmG4SpZmFUKqkaWj5NmF71WJcgAt0m+YfB5mkrnasKYc8iUx4OxVnAB7/iWav6L0L/Xt"
    "IIrhE5CiZ/oTvrKKb9WkZM2ko9IAlw/ZgOqC0eL+cZaOZgGauMXOIoUTcxeAy8Yjvqd4f5zmxQ2NAm2uRJYZ4Cc3WAck2VOphkFE"
    "FznXqsDigqjUTkNSNTiOUzUly7ascg+YcXmRIMogiBIQhM/FWFgduLpA/dl5bqXoWuyMiIKeH03iKgmjFuoQTTw36gzEYJJmS/Wd"
    "M97TKfpUQ/er3ilb+bhRXFCF0EITcCg+M1yU8cAPFmehKbl+iXqRd5Z25xbcX/lHWk3/dB7KQK7hUUy8ej13VI5DAS4HpIpbFK2D"
    "Ua92rDRERH3QXJoGqj11MgX3a1H/kj5aBWzUJTFYmACNN8hZCLxCOlOuxmQgyRF9PVZfhNPIkvQ1ibPbMOghNQKBs/Mx7oEbZTDe"
    "qgdQI463zrB2JmEJA4D9i6sx0wBbOLk0xZVLGn9spK0awWixZNVzb4BcfpTbGyeoDjDfeCXwvJRgteb2Klz3qYhOv/lqxeRuzlLq"
    "mBwnAExMEW4xb1wsXDtwu6eyjQU0gKyf6ZCvRlmi648KURIV6B0Nh/mDljNCtNEsukXVtGte0Tj4pPF4Y4PaMU7yUTSB2mM0SYJ9"
    "1umqzPZkGl2B3uKpDIPDxRLCrut1woj0AM4RivZxA/iLeqxyPhZnnYZBAwBibaFfSQQTAIxEw2qFSrVesDj72dsBqrgqr4g6dUtn"
    "hw8MUe6TQeQHhxrVTSmd1GEiBkLcMtuajG0jc1ouX768nANKDz8jNzSHUJuMBEe0oaNdzjjlpwaYCD8/seqwUNZe0TnoJKHzpOMO"
    "vb8uc8mxXa9Uko9VVrsQCV8SmIU+8lxUOYEoukdRdb0iHjx3AkBwpFjMcwePhUpo1Ny+PwR0GsHCmK3gHNAISogM+t4ZmQm15luC"
    "+hZLuWX2ViekmEVitJvjjthiTRq6lcv05vG1CQbN219W/FSSrmrh4aIIDrRS0VEuW6WjLVmUcHC2qIm+oBwOsQh5aXIBPwDsUKrT"
    "n4T60GeClgWLFSV2CgWYjBFcPquw1SZHncNfE4O/kc9NK8pvS1J+Z5Ht8SAB4R6cWWghGC/Rw0aah1pKs1KfcJUsDNplMnPHZ16v"
    "rAIEm4HbcDZmUhDV6k7jYmMn0xcVqsEuu4E/4utkMgNGaSk6KcGEB3p9eGk2AC9KtebGJL/mnx96817kjrxJiTpb1D+hxMt1DS9q"
    "ee636p+onKQqYq9xeFrNKlcVCz4bhKVauMhTbqygmWHh9nayf9RcEC7OKlLQRb+NutEe0kHNQkJIltJmsP3Hpa1lp3FcQI7IGlVs"
    "1HGD+QxIIU9WC44XK4m1NRnGxkeRckO/aMqk899K3meIAlFK2T2rCmG9mcMl5SBv1l6vrFw4q6xUUjLAVncO5zu4aPWd56qU/8pp"
    "0swAn3l9L0jNkESSBVg0rY4wmimhEe1Kq8WXPWqNF1lNbYIkem7Xqx6NV8Ez1FitF4WjaqShGX5xxgaG6QaGKzSgoR0xitMQVhmp"
    "KxNhie5PrVkVVSUBCmOv9QC2F/dL9XETbjXwZtrkUUC9EprXpsB1VsDW1ewUOMu5c+BBWeS/WBJkWQkwuwdwOo5ib4foElOQcq7X"
    "7Fze6DQv7wiuq8o+DUyNaVuKnVTDUqO2lX/3qFNSBQ4EswAucim9+7gN+3FmjWMXZY5wETaNwUzGaOCRrue4vZiEOqusjEGvSt5T"
    "I+2yRJ0QQ2sAAGMo1S5nl6nWgOHSWuWsNY43e651IOFJFwEJsTrl2vameThwMHqV2qVMnUblpOCyF99rlwjkiIUdh+Mz70OGP8lp"
    "YGtJA3BNoeIuu2uEUes7kbiFGFsXmh6w3VIemEvQrZ+NAfQD3Fabb7BTShlHth+tJuQihk/y6c37FyMKuUqXTR5z7HzkAjSKmNCj"
    "CRI+pHE1tZ5iOisru0T5GrS1hE3NFA8oEv1wsXxz+UICMjTqCnYUZSW6vo5ARVdZr0RU6gI+6iDqTJewNELYUU8peWTNmlTypug3"
    "pfvVywozxEKyVRUkNFQkflOluhGc35y21lWp+6C5E+494YLWdVEPNzxapIQHH0EsbYjXUkJq6g1zzi+K9W55VTN9JzK3jeYnZMPQ"
    "TCKupjcUMGIlxakuXSHIPA0JpPU7JCQAiMgqEZfZe+EhGruTGPfAznkZnqKwwqIIOLSHaRkp3e3xAM5kf7BTBFk6wYXECt/IWTKk"
    "4Z6gmMW8ZMYdNIQt1S4VXxHahcel8crLuefWN7Ovm7UmXYA5xU9qYTeMJ7lGgrgD6wl7RVfRhqTQ+bD1w9jWzx4Jd/Q3B/NwCQ6Q"
    "tuAtjKSzv0T4Hq9qxSgFlEVq4JUlwGdVueUCp5ofEAX7RZhLFQrHuTY+O/cvjcsom1VfFP5o2YLLguirvl/AhheZM2FQ2j/1DeNR"
    "4q27zJLTMNakfACriDTPbl0rJA5yAehiPdUyh9uQA1tNJZe17RRZDqb9haaf19XUuRgvJb7cSppCXYiu4siR5ne9WOoDWYpVSNYt"
    "McBKiQMMRqtZxGh1B92FLvFdXc7bRXnGfVAOqwqJtLmx9gs7HDQ1PfgWmbyvb64gsBN2NJzOjUwvYBrVg8hzDx36u4ovxKQO5kWX"
    "I33uhyuZtvUiojYSgfu2KZhjaBMtkl26boCchkqtHFlEo4F0ZaFRnbpVM14eynRImQDWc6yUChVUuiLaxDvbecZNxLXom8nqydiN"
    "4vsUU+EcyEVAWzLWveKXK11/uqolo6nikutTOkhpIbNaLipGorrVbInTIOUOh9jKYG6acfFerGh0B7VrtJ3FNxNJhoEYmhiWKmRG"
    "rnXSKCZQkwWubuWwTlIMgMPomGYLgoRT7h+5xgpUL4OMM5YExQuNim+gmj4aQKcckk6B6aV2sTyelNk6gwy+XxliGPGjlXLn/i18"
    "t0wLX4xzKleqrj6cfaHyVqhQNi/6LVE01ZxjdR9uO4mltmx8HHlqYhm/p81C0hOqkS4lH+MTv6fu9nrawpm0ttHh5CyoxpTXyBYA"
    "cRezpqzsoVFmL0SthdLZlarCLD1tfNodJmuZGXB3CIh3lTvu8lbGkS1PFZJc5OvNM0iwxJ3JA+rGZ526qNdNJrqiOnmpfKBANpHL"
    "7FD3NQT2YiJJLjfHhlzoo+LbU+4OITyzNC6K+EzYW9s9WaCbshaP4ISi7TF1hqq9KgcuYUlOBiJWRYobY92dRXZQGvoriTyZ7OYq"
    "aCqVY+1bTGTe9wblW2jnnj/p7ZUQ8s0tww0MXcwSkyfjI7KLi7PKfGic1QMvnnkwJW614w47ZVzeUrWE50iiSuNClOdso8g88kxW"
    "32dhcvM9InD2K8uJsTDxXadI5JvFyjlsooYx5JJ2SLwThZRC6XK967Edsgi1lmPnXF9KsBYyUjwAaHeRuTi1/tgW+74v+zrxL+qc"
    "d4En6IznWd+3RPNjFBQ7Ib+iNLMXL3Q/NEXcDd3xxHPkjyzh0otLccI5bp7RPhxGEfsA0ILMHMHRHXqyVUIBGR8NYVGcT2PLemhi"
    "aKzGVjLYWnCEklD+XWjMnIMncuhhbqQznixyEb/6TEZyhrnLujagcLxYvbuI1AK46MV0tLcyT8RQ6U1LNW9xH5Sg3He0lhEWN9hW"
    "vKqXQZr7MYkg0dpktCg2a2mqTv14sSIm12lRzW1xCTWquijVQk0i1NAkQo1kJGEVlmWJcJfLjMLlW4hlut6wSDjKBQDjFnk/KkyD"
    "MdJW3hBdMJGSPxRzjgWnEaPTJJrbnn/sdaWriyGq2MjnKSioSeUjcHKaHFgtcTiuKI3nVj1rEQwTL5FjX4L8cRqrSdE0VYSodIrG"
    "/vJWpaRbeGwICw+sXaoNuvd9Q2yx22Ppo1p9iduUhuPHKxt2aVfJae5ny+mMyqkeQMVeW7kKNCKmMxPLDTFgZ0qxE9vUn/hQYJml"
    "ddZhTLZB2KMIx6hCGOcix3KMv0+8sZIj558c5UKkSTvRhC/s5xhSRAp9kRHF5lbiH91InNOACC9vIGNsX25OZ8kZ2jR5AzXfIVp8"
    "YIcrXEQ5dP7/JDrQzJKgPY9W/HTRZEF8FJ45Wbxcw0hcedoeGUrFBCcJM83MzKTORZSQHigNxV04TnXmHRz6gKk7aH514EbVeHA0"
    "OjDVrPS/hnvy5yOv67ulsqaR3q5jkJoFR755LsS9r9W35eGVLMd0ULpYwg9oZyQbUYryxvqW1khBxBzkWFKW6OvCqYU9dFKuK0JO"
    "gdooki8jIaf6Hkdez4smcAt2jzpeF65U2sYSP8NIdGNsVr5ObMPy0Xga2hnbPpvM2WxlT2YnplB21rjJJkGezRJjO7mDbT66duZw"
    "ZFU1tcYG8suB50YEZmv+aBxGsYvaQ7aFslNONHaabbKXGDkiRHOHjdGk2NgcRwNvqs/CeAqHk7KxS2rznmV0+fTaMN6UvRgG54mF"
    "44GaycTOuJHl8oa1XFs0OzkFLK9ma7zUqbZ1iXZuCS2AiwifVnBhKLc0LrbI3vublZ28TdmqjyY7K5hGcVyc3EEYR36jt+l2NK/l"
    "4gFtLxlRxuBLtLLkAtR2J7P41KQGBoeYondSZLWR8xqXr8hqI9MuxtLBtgtU8s3NTyyzRYNeCipqeyEmkEA6vwBo3J4sNR8uqFgl"
    "I5GNJQAoCYUakHan2sWFB8ApHFQ1p6OPFPAKG6z5MMgjYD2E06ZgXOSn8FD0SNROMr3wkIx51pcZfMoWNO1mASeVive04bmXep1L"
    "6zoIUId5kFXbqOwkGCcXlnYS8YgcVaBPBg1917MG0Xr3ZH5rG60nJun1yknTGJlmrU58wMZm/lf6eKmoapNN5Fe9IVfEaBJzrIDi"
    "DBNReTjsPMiwc5eVbgmoj/kMV7OUTUQCIuTSykpBDr640bSb9YZ9acuubeYRjvenuKYJkObaiGKHb0lrnUP1nk4rq3YzSsedYlkC"
    "1ziLOpKtHSMgHTRBR765S8LdJvaIAi30I/dgJ5/+VR0sl6bk2BmLcemyS1WKTbO6z7VitBjLMQOjyClpujq3BdjE3BaqRU2gXUbk"
    "Eewszmi6lQuVRlzSyurxL5Y6Phk+9uagV5DOY/KOgAxBl4YGKtXQQ8oswn7aBRF3ckwuhHMcdriy6CpfDjYMkQtTmnChBEkLLvVN"
    "6LqTgXcWvrKIV5W9A60/OJNENG2ffiZvWa3X3tmdhJWpkma0tEJsk3UlYqCee8HiI/kacivB0eisVmVJ5Um8ajwrVQF9y3PA9uTc"
    "xJtcJxNHFVJvW1wpJ8lNSJG8To9vacLnxU+ulWLXHyJj1wGScbpRW6+tl26VHn/0ZukxHyrC0G6VBnE8njgXL2pFa51wVPrkxT+H"
    "3QWkCOh+jLoUb7L488nRGHm0SalcLku5wGA+HkBbhJ4rsMtBt1SGqx7Zd5b3Rv5IoOgKfAcqHeqOwudQLOqRPo8+aRV5NoCqysg7"
    "I0FRikr90gFUryw+aQufNJuZQ9shNoA8EKrVeFZlPVz1GBoGLsEd7uhv57lvnzPfTg69Wbo+vUvVVscX1duEX/n90HNpK43COiIy"
    "W048wM7V4X/6W7HdOeWr7nA8cFkOSq/pFiloTP+W16TxPd0wUtB5lej9sv6KKmpf86vTJ3ady/bIEipJ18DZy3xK7Iez3/I7PBge"
    "pcZ4QKLLAONvG++Rb4ncSWpgQI3MibY3Xw+OPAFh6QVA5aT5ThId5la7MTLLqeoTb+y75iuE/oScyP+QtxX65/S+698I04maJ8AC"
    "MGagvAQLii9vwx0PaLGqjGJrzc3IG2EE7gTu4cAMu84lWnVxRqox02RQfEc5tjmGm1tlJ6GAnRRBjLG72fusmidhqDU2J/lFYn+E"
    "vcuMOU7n6MDvVA+853wvAg7OLtVt4LHtUqOyo/vbORkHvB2D03SyvKdaraPYH/qERmtS570gAS2+nis9+EmNtFkp5dZJjV3HFylX"
    "8pPaqFpXJAg8AeGsm7OSeFXc9LwzldInS+g8MzqoNhbmDW+WoyIbqSL57W1w4e2VCm+LzusrlW7UsfiwitRCjt6CDABNc0BYQKCD"
    "FinVAdAnBsVyUmNKISUN5ssoJc2Qr6tGwwbXMahuLnSJdmYemzgNtFKrYlSshWawJsyZUJZEfFmfIjSf1BTbqzHA3Kx2ydmSR9Su"
    "uJx3z+nv+HrLvIF6JzXmR2FWLDNe3JfBv9HI0XhxX0yubCTltBUWW8qYwh5ZP1G8LO5PG3MCbAzivwX/4/A7ZU6wSBsWEDFbZWJ2"
    "kW/rNYYzi2RunR8a9JA+ffilSV/yIaopyqwvKbMuymwsKbMhymwtKbOFsj4ZNkQcnIySivgUr0sZIFIWStwgcnqyEJ0Cs9B6baPe"
    "3G5662Q5Igui+W9+a7gA/GFhUGIKrPW3irsSAgHsQrrD+EkPOiGt3FAOgFNzu9WD/iItcJYl6asoWVxKlOD1yS+D35JSzWXFmlyu"
    "H8ZL+uSvXBLT8C4pKj5zWSMUllEsPJQllrRFH7nc1F/WKX/lkqjZWlJUfEYnMoB5yS4Vw/0YUPLyUptUauuUUgj742M4itIOlhH/"
    "klMJpddXK73OpeEuXKk4XYbjuTYWuvGWDWUOt/IqhfFWJr5VIK4clzei5JSpcY7pnCiCIoVFYQRkavjJPRQgPbm/MG2Akq/NJ9F6"
    "yiwgPNlUkcx3/et6+uu6/nUj/XVD/5rp2ej3cvrrZe1rMz2qpj4qtFQxvq6TelrSwhQGzuAgGztEY0hKISlKZLNZllfZKFAxqucV"
    "EFuGhPkiw6ZyhTQBb8rUCsqc1EhIw0bGLKPJtWOkhUH02TNNV/iVBJfUx+QDorfUR34lCxBSS5UQ72QRSgpkFKA38jOgslR9eiM/"
    "IwJLfedXsgChrVQJ8Q6K6G7uaR94TuKklwAugPkxb+hNgWzQ5QeCdKEPlaxBSorLr9ip1xo7rn3Lss7pj5m34gWS5kfRImGv8a8y"
    "hhna4TTN2jUNX3RqNOG99beS89bfKb5bf5lw3fpb5rkNolcw18Y7ZK31FxoTjORxwkHqhg9CQkY8XBhlTAIM7b8tLW34Kb3l/BZW"
    "aGijVPjQs+VEuz7lnIrCUerVFEZsvolDW4gT7AQObMVF2EqlZ/PiidXifbGlXE9K1ariffpZ8EG2UOVWE17WRtIQP5lBcXaW8N9q"
    "wZH2FsB0OtteyTcsSHZPvCluUJaoIJ8u97FksFiLyTyI3WPH+qS1I3wPJsDIDIFVz68xP3ON51avwczbGcufYUQ6zVxca0fIgqpT"
    "d3gkZJ/plsRFs3rX2iVyhvkRcK88UiX4y2+Hz99Ze2fRmar1IBRAmsnte1dOGQ7x/qk2dTT90eeVFf2uPrusWPjjmmMiGj7DWUmu"
    "m49rWe5nGJnr8qMPJpF3n3E1dFl4sjVDL+jHg9O2pb6sxVPWJNUUhepY0trHtU5EUayOyRQZsXodSWSsXkORIKtXSQiUs0Adki+r"
    "lxf3/xkwmaCGzlADaaXVi2uU1H1VOus5zag2Pi7cldaLLBkSqUYWzPo61qNIC1m2dcPrh17pLx8t/RUmHDsYeqWbQAVqH+DnbhiH"
    "pRtQrfTpJ4zHa5/+DL/6Cz9y+37Ar+H5i0elT4XxwO9wA497fjQPLXsyn8TeqHrk2zgI2LTIR7UY8uuO9WkvfihyAfOUHodnqHXN"
    "BVhG6y75HAZwt7vY/sPeM+5fHfEg+OuRT80QQ2erX5gOlZXiKKJjq2otBTHnsqac1SLCUXXSwXcOvePks+d66/CnIRLPnvMO4M+2"
    "zDgrjM2TVLO9S/BnU6WaPddr9ppeT+SYPed58NxL8sqe8zbgT13LJ3uuuwV/GpxA9lxjG/4cyNSxOI6NLZU69tzWJfjTEyljz13a"
    "gD+dJFVsUtlMEatliT23tb61RVMLDzGrsru+4e4IgRmMpNPreJd2BI8J3ze36+uoVQau1jlXb25vdC7tSKkeTKUOc/N2JNMLJda3"
    "LrvYOHKY0NzlS5fqWztKdgaD8Xrr1IRgQZ1zbmOrWcc3wHLjAJpbza0dKdLECl7Ta+5Ijtw5d3C50WngnIHNhRXorLted0cK8mBI"
    "Xe8yDYm5YJhvt7ndvbzDbDfmmr7cOGjuKHGjc67T67lUQ/DlUMa7tHEZdyigdMduA/644pEHtQF/cMcxagO/6fUASNQbhJKut7Xt"
    "yjfGTJUSuMH5E40MyPWNik3+ryW0sUp/Ell9k00FHoKoX/MV7q0GpnF1PIb981zYzo54c+jNtR2lMt2etgH4Zup3PX2R8Z171MWF"
    "r29e3tq6LN75I8BlsJLutlvfEO/Qcc4519zcWqd1wVfecQdPBANd9lBiPvnUmcRX4kjWD+peoymPZH277ta76kg2Go2tRkfL/rwJ"
    "m9xMjmRju1lvuvJIwret9XXtSDa85qX1hn4km+765kZTHElvHWCqLo9kZ6PT6x4kR3K759YJouhIbte3e5d72pFUlbUjqebCR3J9"
    "+6Db2xZHsnlwsL21rY4k7f/Gut3YRqO5DbvWoCTa4nxu9rrbl7fk+VTtiPNJdTe3oO5lu7mxDXU5Q7o4rJe63fVeRx3W3uZlr36g"
    "HVZhQbppAxawGw1ZXZ3c3sFBr7khT67X24D/JSdXJP++bG9t4//FuOUp7m1falxqyFPsXto+6LnJKaa6ja1LdgPqNzfrsrY8052N"
    "A5i5OtPNZnfd87QzTfXXN+wmjLq5vi0TsqsDvnXJg11SB1wNXR7w9Ng577s67I1uw6339MO+2dlwaUPVYVfHf+lhTw60guDiA13f"
    "aDbqxoEGOHQvbegHWu2pOtC9jrvpbpoHWq2fdqC3PO/SwSXzQKtJJAf68nonqSoO9PaW13M7itpAXWbDQS+THaEmdWrq97pTW1cP"
    "G06ztjHR7StMO4hm0wawWwcI1swgUmU2N2EhGzK5vGYqYRbbwmK19U2tKWEyYZYDqGnU4JhtbXBJQEUjysqFP0dd5zL/TFEY9PV4"
    "6GBuBfqN6kVhAyuFolINwfJJ+brpCPu/jTS2b2yrQutQCEX1pe10ofVKER49tf3NzRXa30IdVaf6xBM3F6b+jyCQvn3m+hcz3wAW"
    "ud7Dj2TrdXv07e5Xv/P+t9/JfCYQpQIf/uBXd3/0y0wBglcqANXvvvi1TAECXirwBYyYnP6McExfryP0Zj4TTFdOPskW0v5zCCIq"
    "5sPxySAeDe2DsDu3zxG461EPlRkMfs+aG6cT3Pf6wqAZtT+ZAE9SDMrKmlGItDUMxQ2QPfABfrsZN01O9mdT5kabo1qTgBezuSyM"
    "rGPSFEtEMlmuVEvnWWPXG3d0kEopiBdD5WQy7ddU0nstbRLnXfLhWJAdPUuX4fBFaOx9DZsR72Q+MPmI0uqOO3ZoKfWXz4R+IN5q"
    "bgiTsZmcBh5LDc3VDy4B5LGMEPRUx/BlEcFU1rc4mspJjhuqCiqizRHVaSt5rOoa/mba8lq32k5cZo0wsJqIf+iPHaVhDQv6J8fT"
    "AncvkaVyRQ8qacxdkOAkm3f6cnFgnmT+6ZUhO4S8xHmJNnVnhbDbub565ACZdYk80XNlLvE85AEKzwFRJyfp/aYcPbSEQSP+v96u"
    "bblxHMm+z1dwp6MjStESW5IlWWV31yfs82501AMlUZexJGpIWnatwv++yARAJIAECcrVExs7XRZxI4hLXk6eLN7yjSoOoV9+ixyW"
    "upEZnYgwqwZplR+8cngZg9SXCUpEoSHoBneIqQwyEZPx+MtJVr5nMtNNdt45R4sQG5vHQER1M/Rdipcdtgwf3Kfr2cxWLj2LWcLg"
    "Tlef1Ypil+eq85vKHWD/+FedrZBC4HtkHDzixrgYeOzyr/rHJf8TDvLvQ/LD+RVO4O/eQe/z0PXed/4Gdoi2KNeo27HL2juB+HtK"
    "m+EFqMhLEOEV5BqUoRAK9KbZlOiMCBVx/SJOPGtWYMzF95vaOMxu0SMhaezx383lfcxW+bHPaQjSoRt+lF0uRDS47qPi34QiEBcV"
    "OPPoLtlgHdFeV06pJqMUk+tg/AGB/EV8Sg9yC0PFJAVSx5tJnGBRtzkUmm7VY21FAT46LNaYtNHhQU7H0/xkA1aE3qgaDPF2yga/"
    "ekkgF6JDt/3JUrTvSkLPLnkviIXVGxcDySQUxcItCR0mLFPj6F1xoOm/f+i4I+bzGClANoNfuYn2kcFNOAxOxrHRyaWVxzhia9A4"
    "KmCjQqKlKI53iTBsP8CY5MZtaYytxBcIfColL4ed4jY2lAsrQ6jSBZPkmkS2Dw4BlKIPs8pjp4ZeZEZKZLvdzT1Omic0ppTsKPw3"
    "ByGCDwsIZp8bp0HnI9/ibwlCY1TmIcIiRVKfLPDkbwYNtDnzBdLmjIE2p/UuabmCbNF3ZrPZjKUVdA7/gz658Xi2oVRQzSsmqZt9"
    "qIu0W7fy1Q6UtKRwF8BHOvsNOlRVkFOMX6NWnSTdFDWNj7DfoLKZ/ZbsR/VCmpvqKqSwg/nNWRpJetHVWirhScdzoTXt5ByCzh+t"
    "3HN9xkpvB7kThIjEIqazjV2/gfEJkfDcFjSJuqt7AXzg11K5pc1mW7IJgL3lj1NGRi7awjhKt1zxMvAzsRnCLw1lhuqr14qxK8ix"
    "tzRhkMs4Bpg7TxPNNq1NNAjzKnd4rxgzB6/QknhaS1/Pd4nSQP1E02FuND9WmVvjpvG/wNepUn3lmz/r8jX/fgupnY6RxpoXbcZV"
    "p9FkFjDAJb0710eiEARX9bmK5RW2JvPtUK/3HmiZ21MWZSceQ7JygsK0c/GrR6m0IxCVS98/HAEAd603x76frI3o6hA3RzpF4wl/"
    "g01RDBRnpaFz8+7FiL2qje4DdxSt3362sSftCTWSfPNb6tlbSOxCSw39rhz7yQTZT35Z/Xdep/uMyZVqnsVkhkQ+PDE5zfdXs/do"
    "Ju8xbu6k2S8tLlVdHi7RPIqWFrjsJNZlssmT48bIeK6I7OP31UC/WQlqf44su+xSuYNSEodNVwNN0pdbuxQw4XShRX4iTRSXhldF"
    "STPWZMgCPQUIWrf1RuZuG3mb6Cbk0ejbZ+hdbLqDJMOudug8v/dNNj3EISLy22kVOhQH0tsnpy0FzYMD9nPWQnufAq1fOUzLd2DT"
    "wT/4xLbqTKVW7gVv4uWPeibXPB0BcPyRMSQHR0Wn7pXQybPKzue87Cf7W9lqlgynkn9x6BjCO3e4u/fotS3fQCbBCX05/vVV8Jqs"
    "L9bHHYtJVhbTXzcJINVPjFjmEI+HWM5P2eHMZlS3SVs8W9ZMfw70FjH2kuxySa8jyOqQyE5aiV8eQEYZzpAA1Gbm1C2tCvFxYprS"
    "1WQ46B2q7uA5EETqx8poFzE7cy1ks95Ok3acm51QjfksHxadrVyTMD/Vvnjj2W6DXLtLxbWrNpC8yxedXLsPY0brX1Ctf/zBMM/6"
    "Q+2gp2WoXWeKH7bn0oJaw4cls7SctaUCGj8zY4/QzXC+pDM2tWZsNFV5E8iUTfOgasINsK21r9Y7pZsye8MjA/4SE9PkmFDqBNqV"
    "nIEnvyVahCUps+l5QjnSHi0nA/5JDtAxHqDGJwGizC+bfZ5tPpmGxHVNJD2l0xYLg2/KuOxNao6pIl1CJjWrTAzBVtxLyU5msS8D"
    "nUMyQishFQ1XrfKsXO+jBX5t/F/E+KXC5gOd6iVgMOatADBQpdh2GRasNJZ2hs5xQ34uqQC9kNACtoJ/UJvUV8q2n3iiiZor25Fu"
    "WSV7rDxP5d/u7GzfOFBH6H5wzJ2yFXJOIk1IiZvMW1F9Rhr4cqrtJC0nsUvKVDn6zqKw9+SOPFeqn3rlS5lj8tSVmMwpLvMl6eFO"
    "I4RVnVnMshX71lTZ4oXLSBejwTSNfyqbwrMRRcr6SNO7wMH+ka7PNRcj7et416gz3NXGjcTuAEbiFqRDaYSXsfGBTFsFeqqAXuW3"
    "uB7Wdjj2euDkEdAF2TRgn1il2K6EXAyFQNT8EQRcpOu9m0/HWyM8GTka6LbFcfMN2xjivxPZnoeiGumcVJX/eTtzAzZnpmc0msnE"
    "jxJzFIYK8cehGkySVueb6/f9uV9F95NfxEeB9G+Q5MLH06li9TE61Y8PqVByFJ4M2F5a1UKi5fjMG/Vvw/l0Xf+4krjcQ7bZgCoF"
    "p2MtZAlEJSHMM3cc+CbpXXm5WW46+OZftX74ud3OGZ4tkFiF/af7A0jvdIIfZmpsXdsLqotb1i9QyYyi4BA8x992svwplDyQLuHP"
    "5HSEXiATacjo+KZzOI9V4WxX3FqSKbmOMKxzyuusU1RSO7zjXpw7uZxCHg97k+hvCFsEQupwZh06BIv84tnfs7o68KY0yL+F/P31"
    "XOKGPp98c3yLpa2//V3snoFll3kM22XEDceavKkLqQYaeshNVoNtrs52Kfx98ziYKqQ/oeXEn+41L8uti8uPA5DKm7LqJwZADBVg"
    "KLQ0MtMwZ2atjCC0rPzFZURRpZ12N267jcqgFwUpCwyv3hiCzj/yEj6UUWm/n0taQPTjr0R1tuF6i0jHHK4i6xs3LjFna7OSttJW"
    "P+Mvl1ZOQrX3eqzyZAJ5TzRmm/RF0NtY8DYn6cjS6fxDiEMwmp+61UCUsy6peXirbY9ZtR/K/+wpBSH8kAihpEp01IuVOAYeO0k9"
    "HHNvW+KO3OJyxpgP9E14dFodwBJw0ttIuqVq3Esqz4U0WDA9hsZbtgRQXgJomhLH7dQpporMCPJ85i9tYtwI3v+WBVr8a51zF4vY"
    "OUgSHgBWhZVYcGX0hdKjtrboztkoiZ/YS9t4cVQ2bGJMm3/SX3Ond0biWpxuZWvp/+VlwZ67+FSe0rJD3ocuTiuVTz5i2gwjV9br"
    "09DlaFugHtkUfy3n5IIPT/CWKt3MaW2zIFrUhs8sIRi86q2PyA11pNcpdNo887xhSJoW1Cp4DJZkQ/MraeLH5wBJGly0t3h733Mb"
    "lSYINxdGIFc8kM88j5qU8PqYHKX4EFVFatktgqecAhRqeo6byFn+vToz9+pH+nI4b9i9QaWKVoMlr/91qZCiZ8wo22eZv2B+2b4r"
    "9gUzzvZbsS+YhLbvgn2BUIOe2/DlnnW57oXFfughI8Z8uk4jPrcv1u1ZcdYXPPP8DQyXCbcWRAVI1hV0mvNrQdRq97XzmIqwA140"
    "2OZ853CxYYvM9vgf34lwP90FwZ8OGMva9th1qfT8XqLBrgOQaRG0Pn7jiPYgoyQrgYhn9sEdDHojvhXPFRQMlPibz9N7AylYgPj7"
    "PUmRWwxB5oOW76mjTDcnYWmE2CUBHc0+JcQyVj+KKe8h29KAZVkzFVdnoiOeH+a/MtgIc/lCWVRpW6KR4SoWCiDackaiQVD48A90"
    "waER55RT6bdF9sXVeeea8Fef7XFPKzsR0aTFQhxYz9hGixVGPAyarwPmClnrLOQpfn3pp2lVFP3l3upt9Hrueuk+x33rLC8kS7zN"
    "184cSE8WFkRhyiikr4erRTrTFmQcU4V6ZgNioBsMXLkTSbuwExjaIfD3wKyaIQlRYxVgPVYlXs9OiWaRyALbY91pol62mqebTCEM"
    "DlkNQoIoaNAuwZR+pJv94WzvMs+8Td7rmO/i8Aezfjbzp3GzAmQvSV/0tIowaAWZOuKgsyQeZAvSGh2C1qchDVg+1dpQCEoqiqCp"
    "WS8xtCtYSfMwyxgWbJFIVAFWaVSW6zflIAjnRi/8tOgjFJJX5+xqIeDabEvmA4715xPV0+LsJKiBXxMUWwLhqB6wXmFFryjqUIyo"
    "A4LSDcRYoZVn3VzN2Hpzu/Y3Kl/XA91Iuo68M/Xto6v595PWPrBEej1UnOSPXRuEXDcaFuCGMLUjFFwUptP8ygMQwcQ7MLliuyOE"
    "DVWIMceKpm8R+FJr7P8hDKxnjRRjSdLr/lMYpKaVHu7X55Zw9LmaRNUkqrjeUmie/3TcR9PyehuEHjVlNFaq/eAnFap4AoBWsFLA"
    "HtDbJMvq5h6SSDRMLQ3U+IEXiZi7Y/SnJ+/lyi5f+SCggMTtwrdgFHZczqT5OT3/3HXiz5HqpuwOL5Jl75DFm2peP8a/2HjtlnNV"
    "IagQ4KIEiLaeGXK+ubwjYztMfAOwmx6CuyMANWjgGRdsNYNgK+ghrYtN9oMXKuG5lJvcKIo+3lh7sc0YrSyv7pH7NdaCQqyWLK5n"
    "2Q634rCnNtAQx9iFnZFQqfPfDOzEXkKYqw6AVV5FwKtqqoZZ0i40q8V+TtiNN25YIHqZ76e3t07BEi73Lp0ll3la+VIxgzKn4LkA"
    "rvvsFK2ILoJZHC+roQvwWnViuFbRmCvHff6JVQl91rsYeFR4jeI+kw09SVSAHTSzuigET9BTocu0Kk20IFGdVCo8qToFoPa0mpxj"
    "h9CNuwFWDOJqPm9+B6eb+Z3+3InvwsL3K2US6ReqqMmnuLq/AHb25sjlUlfbGjl3imaYRa94FHFhlhBPft+efo6gEVA9CNGTEkPE"
    "SXK6blhMYyB3ssrq5oc3eFjyXhgr/c4U0rpk3fzUGIxc1afD+5eDEPrL3WrYyPvJZPHrkCx2nvqTGTCvPGz3yV6ny8Xzdeya4zB+"
    "wyW/ciWVUTqe5KcAkcs2W9dVvPmImcSoBYPdJEEAID83ZU/sBmF3m9pmkEDYfot2J1/lvsvpgyAoQz7uIJOiQVUGnckddTuP7q4G"
    "ernd/OqhGyEIm+TRno0RnfevfqRRK3fZiSSWcW2XrN5jTtYYCoEgMZLVLuzN1womQfJF4n7bwWvqQPSFPt3HTrxeW7hcthmEgtR7"
    "+SB8XogqX5ubZ9yMDR8k+4eemnNjfWRiCKE5xc7naBEO2Jw9TIBv/RaYHsXOHpwibzoUwfvAG7VnhIKSSXraR8RxrTLxzQ+Ecm8Z"
    "F4XZjL7NiiLZ5gdmQNqYQE4y/rBXFVYmvNMPE5XrX7JyLmx2aiq1Xsocd5rfE/yAIYRNjKE1m6ixe65zOTKxr4b4z5CnnvGo5Fcw"
    "DQzTmmSA7meJDLI3eCsgv5oNgtZk+klb6eBEzaftoQTBen84biiF3Bifppu8qu+R2ZZyEmQDiTnHiI5ADqWpKi00hOLyme6Ay7AP"
    "2wqM8LVF64AmX483+Jbq0lDsjUT4IZ5ldiGsk+PB35xLx6uJrDF6epYsTNqnmUG8GucNKBBhxgLJCoSs8U67AkFmPJQMZ3fL2gH5"
    "bY0V3ofp+y2COPCtuvXHk7Q6yLu92dk5+7k7k57VU+6sFj0m6f4zUaXtol+nDoYD4D9i3FmNDbzfIszpWPJU7W5MaGwHN6PcOdBA"
    "DTTd9NAwYtcxu1T5k/5HqL4JEF/GH4xuHIUoqpor6XEJrdsnpuwy1bR0kqqoI3aNx2M3bV0TxIozFHmvbvSDE0LNq6Xmo/Ef+Lo9"
    "1S1RFYxJngZWNIf5tXhJqteT+PmHwyDbTSPq+G4+cBGk28Mxr+5bCqSBpN7fnJhw72vEvK9P2PqpjWmN0Fmz8XQGfPiP1Xb5dMyY"
    "9asaHjsDATsVq1A45jGv2uuJzjKu2udAUg/OPeThOJ3261MoRQj38ZjdZc8JqJai2aHz6+mlLN5gkpjjzSl6yc9yOsORUnaF/RHu"
    "braKYln1K4h7u28f4jpnq2jYOCD4GCesK2nQhlUKg6KITmHQBdvlm0capT746+KyOhjDjMExeLRJk/RhWyaTLe8tRi3XcI0sJPYJ"
    "G09S6IHmFrDZwpgosCmTC4JwvzVgCfdMuitbwnRAB0rD2QicSXplSLFVkIp+MneKtjPXh6Fb7elRStEq7SbdFbe2EK7WxXCW8Cur"
    "NTVuv5zx9z7OvTpi9jBHkA2ztQrF5zgZPw6eeaBYfg0rbx3nvUvNnl+7PEj5tUPduVsDW0hlp78CJmocYjyrISUjSd/2MTASLzkC"
    "VK1ON4ZnyC+3qft2EZawoL3sHId8kWXTt4C+Bo8dEA3rqRA3R3Y0tG/bw3u+ecYs2zZ66pdxJv5v/fjwHNRQyOEViAVvIn6ve3kk"
    "avqaCSWDgOPzI90c9RGFFG1I4Q/C3eCnYLqUd4pw+ZnMcj6Df+PVUvOVioHliTPEr+NmiDj6EWd3mwbJPlWdb5vDtWG4FL+EuM0w"
    "ShWegxllrYvMlNmhM2xatf1ws02dWk+VdtSEUprJG3AZpyXFYrE+Uhc43MEELg0rjgdpIZZ7WXbx+j+Y10N9c8yaB4EW47CZRgkL"
    "mO/BYlUk2PRu59OD5PYQvSHL89O53kvp+0uxEXdFt+8QabmjPArSG+v2LesjrpKHUnL+CLpijyvrhMFGt0XhmAXbef8ikXrTqbsU"
    "F5GWzFKI6kPgxXi786PKGHv7f9oYj2wmAQnrgt4DHT50dSgU/k3s8P12mpG6+Txko9P7Wm1v+vRSx6jjWJAqtQ8SuYYZHcbyqUwT"
    "if9UTICU6K+4CAXhFlT3vaJdOv68U8efOsbZhZSDsW37RcgTduTiin29WJ41ajBuVRsCVx3iPoJOWHejqhEkYverQViOPQXQGdOi"
    "aXas3WQyVtwBjoDuUh+XypDb4uU+uOFODe0SqZbJ3ZykF/EdsaB8/jT5fTQxKzrYRPtG1F1sWrqQl0O4g4/0XJ3ym0cgvWA0ySDj"
    "qfWpP51ySgKJxaiAor+TPZ0TNc9VTz8VMdW1uCdFs0JRKjYBTV4WaAlYxgL7eNy3S9EWg39Wk7fZJyr9rK99dJ8XsZT7ekKkXbcP"
    "2YCaqUDFVvaAs+vF8+brsYd53Le1n8HJd3bcXPSImKpSafGCBZllUKdAy3XmKKrwYeY9lMqN7HvPo3dcu7QsXN58Ujhbh4rS5M7V"
    "usw3MTCltvhqj+S/berDPjDuo8DwFNewld3tXFFJo+e4rayM2JLqwts2k6nqbb3f3RxsS2eOg590MJq52O9CHgk/GgFLvx5vvKPX"
    "3JqOjvIIVbNdmefe6zJ9+JmV7kMKqYX9r2J1a719xgb53CZL/1K+Y2aBpu5CMXdhdsZ3oU/f7o2s4nV6q6MJ8dPxcVgwiH2/TKBk"
    "Tm25Xd5hdEGX762B5EsuF+fMycVJIiS6majc8GZJJv1ODURTLkAkkAHv/S0OoFK+b4/Zrrr7EHBc3cEOEqE/3hHrYvk7Z1Z721Uw"
    "xDOds8GdVuVA4rsQc0fI22C3mJajeGxkIK7G0E68S8Imk3XdEr/b0lVSWxaDIAnznb9LXDr1oPSkgDQbznyQBceyRPpqdVHocuDo"
    "jljSz1S/SSZWE9EnbSBtt2ooFU1YkH75GHJQ7HZIKmp9Om8dhVx9Ku3QzTnU79QdWiQCnd7o2IfXvqmDtv2/NQqQpoDykGLqFp5Z"
    "g5oGlwbjG3ZN7njal9kP77Lurwd5eo9sGbLo/Q26S+88DA/mZWFISRwoS1X4DAhHN2GsJoue4dG6hRISlEFDzQaczUn7IaiCXQTS"
    "E/D8Qk2Zz0EXaFO1ONsYRyctQME9Tyqlo/lQ5SmcvuEdaa0CwMSxj/DlPg00AeBEC4f43Mn5To3DTSN4lLvaVvMUNXxWMzVF8IVC"
    "HE1u7nfm/O5KZEJO0fA1uCs0AoG4+mdTDy5OozjYKOt4f7WOT8bO03NR523wuoY4rHwv8ypwcllHEw+mdteCaCwNc3zqEu2hd1im"
    "F8CxJdTlgYysDwZXV4kE3aoxV10yqmL9cJLc6tpimobmD+BPFDueh+Y2parslAcOI1UCciyTZvOyJH9VL4dLaEthkW08VFfVOAWG"
    "sz9UNa/QOosIChK1ecGpzZMlmwKjfLcjQ1svS0vUNXdJtKxsVNIIH6oa2TciqxLyl+mSlqF+XfVbb5JqlDbR51teP2cekP6FsWmw"
    "Lxu04+noKReN6bug2uWfhyoY1ZRzt2IQGqEqrF/LXqeNPAY7EIO2kWBJ3uOIO6GJIpmPr3sniKS37Ejb/qSsZZox8ta8t7xFWukn"
    "DsVhL3UPYndYcV1cdU+F/QCspli7L7HJ0yyY3vg5KvXTv18PdXGNwMvotM80eeS4k9a9LwH+jCPAl2PscbhMxx7/PUqSdZGJNe28"
    "K57UyGIlS6L8yaUCH80BrGO8fAjjIUk1bWjbMlKF3bp+DCYw0EmHDrt6ZgN7THpKHgXybLMQ4ERQNjI5o4Ywsz6ck3Sy5JMliIc3"
    "kvZhHJyt4RIyTwajTvebMpDTNVhlFST3bqnikiT4WXp7hMo65Ane7R6qp5LW9K+ombd6zpQMXSeB6nD8hgpL0JyFjsPso+vtTpzS"
    "1c26YxODBKry45bC5Ljcr7oRnaWPaBOss0CUBZv8X9K68N3hz6jq/IJxhiEfi53LuN8NxSpMK5m2TPULEDMaCGOLH5SPRQfKQE2P"
    "szF0XvIpOWIo9zTVhS9xcLixcDaZcGYdeA1W92NAyZu8zg7HKsUoUgcvQZ/dGTgjhQCZFNphYPXGf4SX/I7gxmHwIfx+ca2ZNLA+"
    "NC1sqzqqvmnUGeKTxM8cOPM8x1cPqo7EDcF9KgaU3cRazGtWvAyMRtYPPGxpFj3WIPMMMUvIUPIgDyG5pNDQJFfjaSjBzTKqBCQy"
    "/FiigUMm/isEq7w8rJ/E09djVsLf1Ue6B+IW1gDTLEZGwJX1WGodeKCQScO0uGyyHz1zrSruV5ogeKwTBCv5QVNKStVE2XZddXts"
    "cgp7tlKZA/aYrcTLcwKjlSPWilmESREtKwQd3J0EdGpe/UZyxz7Kh5tSXCIn0U0t7lzwD2DWeWfy/ELeef2VBTtNpjOJdhJNALHu"
    "Dt1gwU9Dxwcf5MNKw5RtxIFoSxd+gddLp/jxv1+k6EHzVRXBatU6O+Zf0q8zu0YlLowcNflucWfq9Sdri01/jhjtaOENF66QqpB9"
    "u0OdkHCO+fxjKUStuvBKTdOFKWfPY7U/nMSmtNsmwptEfVttmqfyoZc+a1TQF51Abb5zIaqO6vu6nn51u0ZRdhQtkcI9PUj0B38U"
    "ballzqajlCehEho2r+VoMlB/aLl4MKRXRntJQ4rWWky9hVVIjfJJbM/DNXejcPyV/IhUfrskslqTIRIO8iFI2XdPR9xLIgWcHBUz"
    "+uW8CeQgGdzk2UCanXrNJkKH26uqMpzB1IdoBKv6Q6A6WVyyTsT+hQPfLCsY/0eaXS7pdYRUxIlynw7xR4j2O6JLr6ADNMdNxCAb"
    "4cKtDwdO9xyZtxgV5QEEWCGdJTJtdKMcEnVQbbJgw9WlFOeVHtu2essu7qd7vcR8OiX941LVKsDgvlWQX0kEwuj828OgdUjBmQ6l"
    "FEQJxWNBVOVl9lFdy89F6merCNpcXNIopQUcznshVdXPSmQe5VfRdKXkJjvv4agg7zkLvSfmsbYGrNJZ2y+hTQ1CtYFMj8wEiJ9T"
    "eLMe79yt34CiQbJp6dsxmUJGLfeFTIYtGAv4Fn7yaLysmc14Ju3jQYbQoWIKHWImE1zrkM5k0DCuwx34X4fTpShrIUC7ksr/fJHt"
    "X4bjwcDfyXiCaPsbR8nZtuat5CpoGhuTgVgZVUa1zKlCWjic3de1qCw9adh6/LTKt5J0qN8ukTldhEotvpeo9wXTnlMSwGG5W2Vf"
    "pvP5UP9/OlkObJpAcoxK0Ui829LLF8Nttg5LkfNynxz3eGGP+4Pkfg9/5inzmau3Q73eC6WtFCMamj/3wFzZqz119g9b5AR2APmO"
    "OzxQgRD/A6fMzf/+KlRVG2sxYSqu0lg68IFjTFVZVpQpdTLrt2XkgmfPYHNOBk0q9FUDtMNTOVPpPqugWKOUeeS7TeRpwElAdrFj"
    "jzBPuK7+AiVeEejlmz/r8jX/fnONE1orvJT5Ni/BK7x5Xeeb0anAQSbyb6EjGslsGCcfDbWgM5RSxZC51oeNyCLq4z7OR+p+Nz9g"
    "E/oPotn5okU6mTUbH25GOj+NbBR0ELRK6kNW7FWWTbIahl33xBD3/TB2F8PKlS85AdMLvaCHzhU55M8tW58nd4QjD+FmfJj+Sict"
    "LBA1lckA00VlTuNRfTjB1bp9PctATjBDVl+mw3+9ni4qK8zHH7+j5f7bP/74HcQV8d9Vsfkh/rM5XJPD5s9/whL657c/fhd/QyH1"
    "9Pd9fTp++8f/A+8smYw="
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
