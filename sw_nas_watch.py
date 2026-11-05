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
    """きちんと終わったしるし：鍵のファイルを消す（窓は、鍵が残ったまま止まったら「異常終了」とみなして起動し直す）"""
    path = os.environ.get("SW_NAS_SHELL_KEYFILE", "")
    if path and SHELL_KEY[0]:
        try:
            os.remove(path)
        except OSError:
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
        remove_shell_key()


# ---------------------------------------------------------------- UI
# 画面（React でビルドした1つのHTMLを圧縮して埋め込む。dev/embed_ui.py が書き込む）。
# 旧画面（下の HTML）は --legacy-ui（または環境変数 SW_NAS_LEGACY_UI=1）で使える
LEGACY_UI = os.environ.get("SW_NAS_LEGACY_UI") == "1"
UI_PACK = (
    "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"
    "ihlOwvsZ2Xd0E21rikbiOqOKl1jjQnQ1Csl/AzPXcBcFJXUnxi5J5W9g3fQYn8s0J7+1caIxWEf80433fg5HXdnou/TuosGWcrBW"
    "wnAfmdnCV0mE1kS2ZI1LrbWmGSCNpD7AgnIMyQESL8wCRU+4ERLw8zy8uY2xrjUcq0B8TDBY9ckI83qVyoaW20csqOMV1DyGpdWR"
    "49AIz4aRS8bPJkUsbb/0p72lfkELMJvhLzSTCrgJ1TeVwOdLHVizQUkKWRbpvqKnSbjDthaO9JIwzbwEBRThwxgYgt5eGbBw4YXb"
    "5FhgDOWwUELcHgXbT/1gQKcFA7VlMqlQjdCQq8piCepnzezIgsAxqwKSFGg5J/prVj1BQAf/psHx0+8UHB9mx2NbTywkNNMUNqmP"
    "3tNXSZoCMI8BoapIvm7IxIUVPSnA0w2+eLL7xf17h1du91P1ZfN2O+B4lslqA+jxMl1LVDxU7+R1vxeeCIz85UP07hpL7FtVj1P8"
    "RzSbJp/Ers6lxY/ypWc41VX1WU4az7KtRsc28f2FQ8Luge+4GxewTrLsfpGf0IoJNhau91Q4MUGos6Bdto+LWueNGm/zlOuAZf64"
    "OghitZs2nfBlY8TRdPXyirOZl+ncbuKSb9z1aKrh+eLTY6w2s7CiJ4G+GtnCc5vq3VDcHblplRJpfGqf2CTuJoOG4VlXFiUnYvfi"
    "XHmNW019C7PnkVNFuRJ+PAZ+UNik7zolgA7EWqosAAkaFv3onxEbfe0IE/AAWZ4dXYORAyF/7UcrCQx+PI6O4pUf/TN8oheKaFNc"
    "dCzGkgLNhPwsFYPkKB7XHEy/SSq5A6vfSx01+Qn2etL8TTUkH1lbX+V2/nDzxnkar8YkDMh03lI5w/LybFrlXAlzJ8Zj6VUcvX8c"
    "jRwMrMoCDBVq1XoGVZZIVVzv4O2UjtLrwjg/hhcqyolSUmiJs7S0MO7VhvRgQ/yIyfQ+ojxcfIN2bULNei5KFkz2klGY9DNEDjSA"
    "Bdp4FpipcD3EtDe8sgoxU6rzVUBJ4LAap6FHPdeaGAvA1ddJNfJv4tyNHRLauXfj0q5MJhYXJnm5USPAL6QogEb39svjZHzgB3m5"
    "Gg0GHj6pgMW5xLn9910srA9JnzVxYV7t0vHNNfbIg1ZrjvGC2Iad1hKgjODK7UT9Y9fL+sJ5RcOdTNX9VWPvFhSQlsyjlKEfmXFh"
    "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"
    "N5tdlPn7OMM8iu/hTdA6wxG1BHo9QOFcpP2QaILwNrBpSwT6oeNXSXnstQ4PW34PiGLxbhSmfa/or1JjlCfpdaKKsFlCli+eP9qN"
    "o6J//CwqopOxl+Z9utGrYyr10c/Ua2H1lj+bqYH44osifI060BbmGouAHYUtkgVAX8YjiexeJ2bkz6eqY5wCDeVV+EXhNADkqiqy"
    "TYhJEr7qtZ59cffu052H1778Yu9eKziKbcku/H0EZbZg5+mLvZb4OMXv/v5n/+qX//1fyy9++S//4u//7r+BmnAO7l57+uTRm1Y3"
    "GgN2vGYO5kdJZ8ldKUOL2HsXUgfbyvLrFNK1NQ8uTuLyOIe9efZ0Fzo8jiO4puPgokWKo6y8jkQEdIdBZhO5pp+/G+OcWq+v7766"
    "voeb0grejebibT44DyrcOwBNoOSisygprw1jOo/ILwNHBRz4xVxlp5Pvi1Vs2DO+08jBEzUwwVu90V5HL7dYKjvCFp2GlrrlZruL"
    "GPVanqSg5N1vybKW5PWL1fy9+shWUc3CwXiwt/fsWmtF92tARjqXy3kP6JWsD+D5xfOvDMAW94CIuX3BpC+7tABe3OvBGQFarDiJ"
    "0uRj7LWe3N/RyXCrdeFaiigOL/Ck0gZie3oTcYLpLuwZ4Cs8y1+V8YnXGp9lZ6utlZjpBhU2lPsAROU4NtG5jCIJOhrzTpzGx9XG"
    "RW1LzQ5x2f+HRoq01VLQIQv3W3fg0DzEfx7jP1/iP3t3Wgd0GihPRajy1BW3ww4AXNKhKZLheqfrF59TsShXVtSEvbJXAFy4n0zj"
    "gVfc6rTRitMP1JIC2bLSgt1ElYbevwy3yiw5rBCKPovSWxOtdsu303lWaMiJYycjCkzdFP+gE6+b5b6HiZ9gNx4ALTH2sLegtaIL"
    "HyfZBBBhtXgXGVcMmMLVfPElnWGuAlWiZ53BnPFZzYM8witFmKRQDgPu8bHnr3RWWp/DUpDDPTZOS+OvXHEKTGHd52OlhCcn0dRr"
    "C2wVjvqZ538Ow75uD2V2a6vdo4rDNMd4oNDJr//HP/3lv/ivYIi31rfa7tvPt9pQ4Zc//hNVYXtro1oDv4E6v/rLP/qHP/8JVXNe"
    "0xf4/i/+B3zJYpyRKUbMR80+RAd/Z16qWHYH28ALfxcLcah4an93q222ppfpJSzNQSztugK9Ifv4OAk92Lnbainh4s+Bxvak3gGK"
    "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"
    "ytffXKoWLYSx/4r94d43V7y0KvazVbH/aVbFAruPHvPzv/0LT/n5g1svUaE3bxcz5hErmHIh/Da8e5SY8pGUX1ZuacIPtM/7/uCH"
    "7S3P6zFDMfukmRWYZYf1EySXoypnjL6/v51VAT+fhdUrv5+h8YK7v8gkvseP3GVdH5fi2X/4dOe+J2lmJkvO42dLMaSvtz8PosgW"
    "N9fSSx2+/nr7b37yDx9Ssv+Hg5tpZ3rEs/b+/zcX1Fsu3nz6tTzxF2epTncnwR3nHr0F93X/OgN5VD2emMSMYvUy6UXDfqQvt2ni"
    "MH+9VGz4rF1w/D6ER0/BJ6+fL799f/h2QZ7FDnsUHj959udp1vseLdLF+L8P9MELsBww66VF479E2Q/t2CUz6REZH999zuJ+Syz7"
    "au79FvlDgv1jRw+AWL196Gkh3A/7eRE0rpeM6k9nmb2bRdtiRN4h9fYxeP/mgc5nNtTGwfTRExbMkPnmLKO25R0x7tohtyjSb6n7"
    "5x00L+pJhl81TB7ERf4kLvKH+oGLKyvzFylVP5rgy/rM/T8/f6Sit883HqUlAi1FcJ5bieJgKVwxT6FtfuGD/ObVen7167NcNt6F"
    "9zqsy5QWWvpgRo8vPu/ze84Vi+71LWfQvb/jNvx8veRf3znXe8cRALztFj735i1TvpTK9yTmO9CeMkXCh3jufadMsyzg/eIp/P74"
    "9eNffLiY1eI75Nq7P+NxqR7SCWe+957l3Ofz6TeflPzFRX2f1JN1/x5UPzt9xQX28yvUh7/3vUcb5dmVeZ/deyeY/95b8djw228+"
    "mShvll/fmfF7vn5f4fpO8Q83HwfzlAf1ve8Z/gfr9PYrZ41T5XMFjxfzeMKq56j914Y1M8JnX+KTP+3r/qP3r7w/4uu9H2mNvWf2"
    "+p3Z/0y9ZHwtMqYqvg29TZuXUdPivqCvmuFnl1G89Oq8GPknr/6XV09JM2/eso8x/Y/c3H2wfe6LfPdQLSLnxcJuP8j7KJZcj597"
    "yL+d2cwS53oqe73g9kIrC948Bi9i//Lqzd1Jmz4d1PqNn/729J2Z1dzff2z4w/ffJyj/TD0j4be+9QKt7nd+HvbR+yEPD7rK/d5S"
    "LPnJXmLLe2TnF19dFgn/6sGT/52HL0UQpHHuv/qll1b9MrrlbKJiHlDxeAbDvdVvv+/65/RHIfzpfU+b/3b8OH/buuHHs+qx+C+W"
    "qnn3oOrbqlhOXS5+ggrghW8RFHrJ2NyvMLbZCHh2OgyRX/sL6O6dXuLXj7fe3Ov43fnYR02XZW49vbkfNN66cfr8Pvf66dabpd7c"
    "exR4ofU9v9reA15LwPcbM0a1Hy35s4uFsvzm1d/8wb/+q3/5j/77X/zJf/v+779aOM/rZz/Ws63xASN48zyMV7/4CuAeSfA7qXv2"
    "07mXX1qykB5MkO/+g+++AIa3aDQL7v/ck1ozw/yxAhn0YD09eZy+973FN/i979kfEus8uLcPR4K/MMGX9XnMV3rKFT+Xy1HOCz08"
    "eAIe8fOOrq9nBIo/Gu8o9IQvb38SMj1j8wtsmn/4gE9v7kWRXqkLM33cQTeLum88YMXc9ssHsylSZ3GzONSXRIewdmfGeXn11cm9"
    "D3a/N1rjRdY9hJSX8vHx81aW9O4Dqd9nFt69W08rBr+nsaXNl0N5fgl49d//y//17vM//fG/+bW/+sGfv3r76X2fX/psRyIPXoxi"
    "ZjHFPOc7cn4y4+nzl2Wn0X0rwJIFMKPB8qCN2zumfWPBtOIZ7IsK8LDH8S9/b4k5fry8+4Tdb97jCvB+Csgn3/0HM0p+9+N7lG2m"
    "w4U3nh+2a9b+rLbU/pP0WaqEfPOb+Ufd4o2Jvev0tpnxfSmq83hzwY+7T/ppv4T/IAI//ia0uAVn7chLl7DMPNdPi4/K+q4nsA81"
    "J2ed6JHQgweZ/VbuXt9rhT5qW0+qZvpy0T59n6A5vnW/vggzbO5lVL/TtEVZ+pdPXv3ijz//3/7qT/7VDJ3nNfmlR9C+jn8aID9+"
    "eqO4Z69+8urd9//Rj//zn777/Hf+6gd/+e7zX30FPDwAXv34B//yr3/wp+++/4/fr9bDWj2u+8yoigc4P2Da3xPEj1fvIbwc5fLZ"
    "UgvtCcbeApz/IYyLl9rUJ69nOV88yPniSfrdu31o8q5vtNFdEM03i+Y7RbkcjBR5H/7qzcf3xXOfF++zF+wpXAzfe6L/bPi/fgi2"
    "vX4cF9Vd4uJxU8P3vvd4c/DP17h9+WjxtzyeE7KM6rnG9HKK5BJCnFH+pYL+Psz1XEv4Hm96D9BHLjiPZxnd22+mzZsPOWLa3DNr"
    "HqszLKII+AhaLznejyVx37v0vOW9+14KrfHix31Pb95enm8L7kyIM4t5qAj2qrlzRu+jYMEGP/emx90W6dvLR+H86sKZ7lUXqXu/"
    "r1f+zy67OOM3T8+XLefLTtrYTU03K63i5dsfrdfLy/NoV+v/uV88tQ8UywFRixGzbNO4LD9++pLfQ2txfiez5a27f/a+l+7+pShf"
    "3xuYe0Vn2vU/eV2/xhHoLfR2Hs6bt/VrhETmy/kffC+BUr8mCWJ5usKWpyt4Rc7X6Pz40V8gNy/9BYv2vqyj3HxNgj17wedfvFcd"
    "7gQ2Q/VBqVww4APD4Vvf+kl2w4NP4vnHcjOzpaVk+fTVKPTi7XjiT3Pf/vuNL3fi/7b/yav/9ju/9Y2/+u1//9f/+/e/cfcgvLdF"
    "Fvnw6mNtiXK8Jd8rs9pD4Pilc+8e+uruv/pOW7Ru+pzF93ru4fWs0QKv3jyyqi5+4eNYxvfpAqvXHwxs6fVrnim6fCTQB6/UVwTs"
    "HUObVn+Ws+/J7E45z4r5B21eHhfsabE+Pb9+zGR598UfvfvyX7z78t+9+/JH7774y+Xzy391//y1d5//wbvP/+zd9z9/98X//e7L"
    "f/vui3+z3PziP7/78g+WFz7/07/94o/+9k/+2bvP//jd53/07otfWz4//+V3X/zqu89/5W+//y/++of/57vP//Bvf/gf50Z+/L/+"
    "PzO3fvf5//vu8x+8++KfvnqLvd+HvHgv7oP/KUrGt771U3SMewLSA2udOc8DtBbgvT3fHV1/r/aedZav+KS+ItS6eBb87778lTtU"
    "fvVhok96xat3n//TBTCPs/+Nv/n9X5/l07vPf/8OmN949/m//5s//JMf/+m/0OQ7cH/31bPMb/0lC+ZZ3HyFQX62uLqeJMsdKz+Q"
    "I/57Tn/X+ufVfT+EP/wPP/6tP3v3+T+/938fyNMy/N2PfvW+PLMk/csf/8pv/vU/++Hf/ejXXr1F5rV5EU9/Pmz9wfn46SJqZsPh"
    "Lmo+zj/7qiPy/s48oPApwPYTTOWnaB304LGc/y2WL/9sDD98e7KC78GMh/jj9NV0pmdn0eLYfHB3ffLRvRrAkjc+C7Cf7Ip4dvP6"
    "fj6v2wfTefNRG/n562Vn2oOH8w7vzx644Km4xxOewyMvfZen4snqub/11v+QBqXyA+/PU0z6q6Lufiz4k2GcP1rqdxv2oUDms7P6"
    "u/dZPEDkkzvsfuZTbnEk3p3Fn33rAYCP9x4Ug8+++1RXJX2Ww9z20SfxvtcXboglfv8+nPGYWfZyHdKPMr9p3NB/Xo4nsv6fa/zu"
    "V+O/XX+4uMt58QsgofdM7WVJ44VHvoj7/oTY1aICffoiaAz9hHeix/jWE0osCtV7lKj99I4QDxCbTc3z6/Z5tqj/JBq/U7z0cJQP"
    "vu75pv/y+LbwuXrcd4o389OHDRaPkHrONnj0CLYPWHzn0u++nAn337778o/fffn9d1/8k7/97Zmh/NadZP/sr3/wr//m939bZ+6s"
    "ZKHh+8Vv3sn7dx/I+AWLnVt9rzU+Nv39d1/+9tL0F3/27stZDHy5XMxt/OQu//hBGPzdj/7LAw/7ux/91//2K//k3fd/gxvLtKj9"
    "+hvgN/gl+aP+xtzI46++/5tzC3cZ8x/vLfzOnQXNrf0fC0f6/JdnFvSY1Pn5n7/7/C8Wo+C//oe//eFfLv0uE/rH776Y2/nhuy8+"
    "n7ueedqP/+IvlmEsDf7zBxZ6Z1n4i7k+LurbnwK8X37BBH938Qa8XS0O5PtS+o8p/u93W5VPzO/JePXTh8z8+9aoTx9/8Nbw77t6"
    "X4C7Xiq3Ltu18+Vi2QbXfsUFVH/U/jyCQt/61j0I4Z6b5aiAe7nU4/xsfPPzxE945MyPpvnR+45nxHrZ8Xz70/rj/O3iz2k/ft/d"
    "2/Hj5+bfTs/XzmdPI/+QWd0ey0N5S/nSOnttf/Ldd1/MesHvLIjyxT95yJd9Eum/++7zX/+7H/3wHzwn3L774ovZyFueffEPH96Y"
    "1/llOu6Cr8va/N5dqVgw66/+3e/NCPI3/+k///jX//m93R/OysMdm2f0nGXnP/zrH/z5c3/zmr/7/hffvZcU+h8O69XH/xNDf6Cl"
    "RV95kpsfTGDp781LveyJZyyhhXvq5yNnfawR+Tr/RvxYULQIvrGUIXosRTdTXv7MRV6qQZ+9D4j8vcIgd0/si4NbFuH0gaxz0/Tu"
    "DPhQxvkLb/OfRvWS0W6Kr7pUHyOqj1kPSyj22dl3j1j1949fgD6ZPz+GXhxxsozmF1/dy9T79Tz+pQTT/OvHqyHyZ+3hl559C/OA"
    "noX314JJ/lMg6Svpqe+R/bO3n5ZLDKv3l/oWnlvOw/Pv837z9qe3+tWxhfGzsf71N+9q13M46+umyAubYZbxd33mhWbyXie6JzAt"
    "AvIxOPChbuL/VGXkjhlfNaqme87tizTRz97CPvLm7VOT5f30vIcG/fv7L/Jyn0vI3feHvo/lfbXbt18N/H76FZH9RLrPImjRMBdX"
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
