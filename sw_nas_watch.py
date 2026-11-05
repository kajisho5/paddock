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
                    sdirs = [{"key": x["key"], "loose": list(x["loose"])} for x in w.sdirs]
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
            if not key or not secrets.compare_digest(self.headers.get("X-SW-Shell") or "", key):
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


# ---------------------------------------------------------------- UI
# 画面（React でビルドした1つのHTMLを圧縮して埋め込む。dev/embed_ui.py が書き込む）。
# 旧画面（下の HTML）は --legacy-ui（または環境変数 SW_NAS_LEGACY_UI=1）で使える
LEGACY_UI = os.environ.get("SW_NAS_LEGACY_UI") == "1"
UI_PACK = (
    "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"
    "rApxsSrEn2VV3GD3yWN+/nf/7lN+/ug1t6jQm7c3M+YRK7bVjfBvJSSX7dlWj6T8QeWW6CPt834++OF4y/N+LFDMP2sXBeZ2wvoJ"
    "krdXVS4YfW+vLKpAUCzC6lUwLNB4wd1fZBLf40febV8ft+LZf/h0534maWE/t5zHL27FkL7Z/zKJMr+5uW6jtNHrb/b/5qf/8CEl"
    "+2+d3EI78yOedff/v31DvdvFm8+/kSf+4l2q891JcMe5R2/Bfd+/yUAeVY8nJrGgWHNb9E3DfqQvr22TqHh9q9jwRXfD8fsUHj0F"
    "n71+vvzu/eHbG/Lc7LBH4fHTV3+aF73v0SK9Gf/3iT54AW4vmPWzsg1eouzHduwtM+kRGR/bPmdxvyVu52ru45bFQ4L940APgFi9"
    "fRjpRrgfj/MiaNzeMqo/X2T2dhFtNyPyDqm3j8H7Nw90vrChLgnnT56wYIHMtxcZxVZ3xLhrh8xNkX7L3T/voHlRTzL60DB5EBfF"
    "k7goHuoH3lxZeXCTUs2jCX7bn2X85+ePVPT2+cajtESgWxGc517iJLwVrliW0LV/96P85tV6afrNVd7iK9G9DuttSTda+mhFjw2f"
    "z/k954rF9/qWC+je3/Fafrm+5V/fOdd7xxEAvPVvfO7N2231Uirfk5jvQHtkH1n0EM+9n5Rpbxt4v3gKvz9+/fQXHy4WtfgOue7u"
    "z3jcqod0woXvvWc59/V8/u0nJf/mor4v6sm6fw+qvzN/4AL7hRUawD/4waON8uzKvK/uvRMseO+teOz47befTJQ3t1/fmfF7vn7f"
    "4eZO8Q83HyfzlAf1gx84wUf79PaDd41z1XMFjxfreMKq56j9N6a1MMJnX+KTP+2b/qP3Td6/4uu9H2mNvWf21J3Zf6+5ZXzdZExd"
    "3k5FtB9ETe8b+qod/85tFi+9Oi9m/tmr/+nVU9LMm7fGY0z/E6/wHmyf+ybfPVQ3kfNiY9mP8j6SW67Hzz/k3y5s5hbneip7fcPt"
    "G63c8OYxeJEE51dv7k7a7OlFrd/62a3n7y2s5t7+seOP279PUP5esyDhQlHv0ep+5xfgAL2/5OFBV7nfuxVLfrKXjOoe2fnFV+eb"
    "hH/14Mn/3sOXMgyzpAhe/dJLq/42u9u7icplQuXjOxjuvX73/dA/Tz0K4c/vZ9qCt9OnxdvOiz7t3rY3/8Wtat49qPq2LheWs2zh"
    "N1UAL3qLoNBLxlZ+wNgWI+DZ6TDGQRPcQHcftE9eP956c6/jd+djn7R9nnvN/Ob+ovHOS7Ln9tzrp1tvbvXm3qPAC63vuWl3D3jd"
    "Ar7fWjCq++SWP3uzUG6/efVXv/8v/+Kf/aP/9id/+Oc//L1XN87z+tmP9WxrfMQI3jxP49UvvgK4RxL8XuadgmwZ5ZduWUgPJsj3"
    "f+77L4Dh3TSaG+7//JNas8D8sQIZ9GA9PXmcfvCDm29wIfCPiXWZ3NuHV4K/MMFv+/OYr/SUK65Ut1c53+jhwRPwiJ93dH29IFDy"
    "yXRHoSd8efvTkOkZm19g0/LDB3x6cy+K9Eq7MdPHE3SLqPvWA1Ysfb98sJgiTZ60N4f6LdEharyFcZ5ffbi498Hu90ZrcpN1DyHl"
    "W/n45PkoS3b3gTTvMwvv3q2nHYPf09itz5dTeW4EvPpv/+X/evflH/3kX/3qX/zoP716+/n9nF/2bEciD16McmEx5bLmO3J+tuDp"
    "85fbSaP7UYBbFsCCBrcHXdLdMe1bN0wrn8F+UwEezjj+2T+/xRw/vbV9wu4373EFeL8E5LPv/9yCkt//9B5lW+jwxhtPD8c1m2BR"
    "W5rgSfrcqoR8+9vFJ/3NG5P4l/ltu+D7rajO480bftx90k/nJYIHEfjpt6GbW3DRjvzsFpZZ1vp5+UnV3PUE9qHm5KITPRJ6+CCz"
    "3+761/daoY/a1pOqmb3ctM/fJ2hOb71vbsICm3sZ1e+1XVlVwfmzV7/4ky//17/4w3+xQOd5T37pEbSvk58FyE+fWpT37NXPXr37"
    "4T/6yX/+o3df/vZf/OjP3n35K6+AhwfAq5/86J/95Y/+6N0P//H73XrYq8d9XxhV+QDnB0z7HwTx49V7CN9e5fLFrRbaE4z9G3D+"
    "VhiXL7Wpz14vcr58kPPlk/S7D/vQ5V3f6OK7IFpulu33yur2YqTY//hXbz69b573vHlfvGBP083wvR/2XAz/18092Pb6cV5Uf07K"
    "x0MNP/jB480xOF2S7uWjhSU0j+8Juc3qucb0MrXmFkJcUP6lgv6+HuhzLeF7vOk9QB+54DKf2+zefrtp33zMEZv2nlnzWJ3hJoqA"
    "T6D1Lcf7sSTue5eef2t3P0uht37yeO7pzdvz823BWwhxYTEPFcFetXfO6H8S3rAhKPz58bRF9vb8SbQ0vXGme9VF6j7u61Xwd26n"
    "OJM3T89vR85vJ2kTL7O8vLLLl60/Wa9vjZfZrtb/fb946h8oby+Iuhkxt2Ma59uPn74U99BaUtzJ7Nbq7p+9n6W7fymr1/cOllHR"
    "hXaDz143r3EEegu9Xaaz7N5rhESWy+UffC+B0rwmCeL2dIXdnq7gFblco8vjR3/Brn3pL7hp77d93LXfkGDPXvDlF+9VhzuBLVB9"
    "UCpvGPCR4fCd7/w0u+HBJ/H84127sKVbyfL5wyj0zdvxxJ+WsYP3B1/uxP/d4LNXf/7b//Bbf/Fb//4v/7cffuvuQXhvi9zkw6tP"
    "T7cox1vyvTJ7eggcv3Tu3UNf/f1X3+vKzsues/heLyO8XjRa4NWbR1blJy9f3rPM7/MbrF5/NLHbqN/wTOnVI4E+eKU+ELB3DG07"
    "41nOviezO+U8K+Yf9dk/btjTZn1+ev2YyfLuq3/z7uvffff1v3v39Z++++rPbp9f/4v756+++/L33335x+9++OW7r/7vd1//63df"
    "/avbza/+87uvf//W4Ms/+uuv/s1f/+E/ffflv3335b9599Wv3j6//HvvvvqVd1/+8l//8Hf/8sf/x7sv/+Cvf/wfl05+8r/8Pwu3"
    "fvfl//vuyx+9++qfvHqLvT+HfPNe3Cf/M5SM73znZ+gY9wSkB9a6cJ4HaN2A91a5O7r+h/p71lk+8El9INT8ZBH8777+5TtUfuVh"
    "oU96xat3X/6TG2AeV//rf/V7v7bIp3df/t4dML/+7st//1d/8Ic/+aPf1eU7cH/n1bPM74JbFsyzuPmAQX5xc3U9SZY7Vn4kR4L3"
    "nP6u9S+7+34Kf/AffvIP//jdl795H/8+kadt+Js//ZX79iyS9M9+8sv/4C//6Y//5k9/9dVbZNmb90zbeX7Z+oPz8fObqFkMh7uo"
    "+bT44kNH5L3Nm7ePPvi3P9VUforWQQ8ey+XfzfLln43hh29PVvA9mPEQf5w/TGd6dhbdHJsP7q7PPrlXA7jljS8C7Ke7Ip7dvEFQ"
    "LPv20XLefNLFQfH6djLtwcN5h/cXD1zwWN7jCc+vHH/puzyWT1bPvdXb4GMapKuPvD9PMekPRd39teBPhnHxaKnfbdiHApnPzurv"
    "31fxAJHP7rD7nz/nbo7Eu7P4i+88APDx3oNi8MX3n+qqZM9ymFMefRLvR33hhrjF79+HMx4zy17uQ/ZJHrStFwXP2/FE1v99nd/9"
    "avx3m4839/a++BsgofdM7WVJ4xuPfBH3/Wmhsf7e5DloDP2UNvFjfOsJJW4K1XuUaILsjhAPEFtMzdPr7nm1aPAkGr9XvvRwhA++"
    "7uVm8FICRM/V475XvlmePhyweITU08Y/eQS7Byy+c+l3Xy+E+6/fff1v3339w3df/cZf/9bCUP7hnWT/+C9/9C//6vd+y2DurORG"
    "w/eLf3An7995IOMXLHbp9b3W+Nj1D999/Vu3rr/643dfL2Lg69vF0sdPH/LfPgiDv/nT//LAw/7mT//rn//yb7z74a9zU5WVTdB8"
    "C/wWf0v+aL61dPL4qx/+g6WHu4z5j/cefvvOgpbe/vcbR/ry7y0s6DGp88v/9O7LP7kZBf/1P/z1j//sNu5tQf/43VdLPz9+99WX"
    "y9ALT/vJn/zJbRq3Dn/zgYXeWRb+Yq2Pm/r2ZwDv771ggr9z8wa8Xd0cyPet3Dy+o+j9aavqifk9Ga+b5iEz/3406vPHH7x1gvup"
    "3hfgbm6VW2/HtYvbxe0YXPeBC6j5pPsFBIW+8517EMI7tbdXBdzLpR6WZ9ObXyB+yiN3eTQvj94PvCDWy4GX2583nxZvb/6c7tP3"
    "w72dPn3u/u38fO1+8TTzj5mV9Vgeyr+VL23y185n33/31aIX/PYNUb76jYd82SeR/jvvvvy1v/nTH//cc8Ltu6++Woy827Ov/v5D"
    "i2WfX6bj3vD1tjf//K5U3DDrL/7dP18Q5K/+z//8k1/7zXu/P16Uhzs2L+i5yM6//5c/+k/P4y17/u6HX33/XlLob53Wq0//O6b+"
    "QEs3feVJbn60gNt4b17qZU884xZauKd+PnLWxxqRr4tvJY8FRcvwW7cyRI+l6BbKK565yEs16Iv3AZH/oTDI3RP7grfdhNNHss7L"
    "srsz4GMZF9x4W/A0q5eMdlN+6FJ9jKg+Zj3cQrHPzr57xGq4f/xd6LPl81PoxStObrP5xVf3MvVBs8z/VoJp+fXj1RgHi/bwS8++"
    "hWVCz8L7G8Gk4CmQ9EF66ntk/+Lt59UthjUEt/oWvlct0wvu637z9mf3+uHcpuTZWP9my7va9RzO+qYp8sJmWGT8XZ95oZm814nu"
    "CUw3AfkYHPhYNwl+pjJyx4wPjar5nnP7Ik30i7dwgLx5+9RldX973kOHwb39i7zc5xJy9/Oh72N5Hw779sPA7+cfiOwn0n0WQTcN"
    "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"
    "/glL6J/ff/9N/A2F1NPf9vXp+P0f/w8M7YyM"
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
