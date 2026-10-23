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
from urllib.request import urlopen

APP_NAME = "PADDOCK SCOUT"
VERSION = "1.16.9"
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


_MK_NUM = re.compile(r"^\s*[(\[（【]?(?:[A-Za-z]{1,3}\d{0,4}[-‐]?)?\d{1,4}(?:[-‐]\d{1,4})?[)\]）】]?[\s_\-.・]+|^\s*[(\[（【]?\d{1,4}[)\]）】]?[\s_\-.・]*")      # 先頭の番号（00_ / 17- / (3) / A01_ / S1-01_ など）
_MK_TAIL = re.compile(r"^(?:み|済|済み|有)?(?:の?コピー|copy|\d)*$")            # 後ろに付いてよいもの（受付済み・「- コピー (2)」など）


def mark_stem(name):
    """目印の照合に使う名前：拡張子と先頭の番号を除き、mark_norm でそろえたもの。"""
    stem = name.rsplit(".", 1)[0] if "." in name else name
    return mark_norm(_MK_NUM.sub("", unicodedata.normalize("NFKC", stem), count=1))


META_DIRS_N = None   # mark_norm を定義した後で作る


def mark_match(marks, name):
    """目印の文字で「始まる」ものだけを目印にする。後ろに別の言葉が続くもの（受付済の資料.png・Backup_図1.png など）は
    データとして扱う（データの画像を目印と取り違えて数えない・消さないため）。"""
    st = mark_stem(name)
    for k, role, label, i in marks:          # 長いキーワードから順に
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
            uh = lambda x: (x.replace("/", "\\").lstrip("\\").split("\\")[0].lower() if x.replace("/", "\\").startswith("\\\\") else "")
            if uh(p) and uh(p) == uh(r["path"]):   # 同じNASの別の共有（\\NAS\backup など）にも書かない
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
            if self._dest_is_nas(p, roots):   # NAS（監視フォルダ）の中には、フォルダも作らない
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


def claim_port(host, port, url, app_name, open_fn=None):
    """ポートが使えるか。同じアプリが動いていれば画面を開いて False（このまま終わる）。
    終了したばかりで後片付け中（ポートはまだ使用中・応答なし）のときは、空くまで少し待つ"""
    for i in range(20):
        if port_free(host, port):
            return True
        try:
            with urlopen(url + "api/ping", timeout=2) as r:
                if json.loads(r.read().decode("utf-8")).get("app") == app_name:
                    print("%s はすでに起動しています。画面を開きます: %s" % (app_name, url))
                    if open_fn:
                        open_fn()
                    return False
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
    if not claim_port(host, a.port, url, APP_NAME, None if a.no_browser else (lambda: open_ui(url, data_dir, a.browser))):
        return
    store.roots = [r["path"] for r in cfg["roots"]]
    store.write_json("config.json", cfg)      # 2つ目の起動（すでに起動中）では設定ファイルに触れない

    mgr = Manager(store, cfg)
    srv = Server((host, a.port), Handler)
    srv.mgr = mgr
    srv.token = secrets.token_urlsafe(24)
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
    "8v/Kspsyfvf8fNn6vexojd3UdLNyX7x++5P1enl5bu1q/T/2i+fygWI5qGlxYpbtEpflx89f8vsUV5zfxWx56x4nve9pu38pyrf3"
    "AuZa0Vl2/c/e1m9xBHqAHubmzBD7LUIi8+X8D76nIqnfkgSxPF1hy9MVvCLna3R+/OS3S81rv31B78s4Ss23LNhLNHr+xQfocBew"
    "maqPoHLhgG84Dt/73s/zGx5jAy8/lpp3D0tDHqaPZ4OXqMOzfprr9j9sQLkL//f9z9780W/+ne/88W/8+z/533/8nbsn/8EXWezD"
    "m0+TZbbhgfwAZpPHCdzXQbb7FFR3/9UP2qJ105fVdG/nGt7OiBZ48+5JVdXxq1jD0r7PF1q9/UbDllq/FSG6lk8C+hgd+sjA3jm0"
    "afUXO/tBzO6S8wLMv1Fm9TRgz4P1ufb2aUXJ+6/+zfuv//H7r//d+6//4P1Xf7h8fv3P7p+//v7Lf/n+y997/+Mv33/1f7//+l+/"
    "/+pfLDe/+i/vv/6Xywtf/u6fffVv/ux3/uH7L//t+y//zfuvfn35/PKvv//q195/+at/9uN//Cc//T/ff/mv/uyn/3Eu5Gf/6/8z"
    "a+v3X/6/77/8yfuv/sGbB+zDfuAlinBv/C8AGd/73i/AGPeFQI+qddY8j9RaiPcw3QNO/1PlvWCWj2JDHxm1Op4N//uvf/VOlV97"
    "7Ogzrnjz/st/sBDmqfd/609/+2/O9un9l799J8zfev/lv//Tf/U7P/vdf6zJd+L+1psXm9/6y2qUF3PzkYL8Ygk5PVuWO1d+w474"
    "HzT9HfXPo/uhCf/qP/zs7/ze+y//0b3+e0Oeh+HP/+DX7sMzW9I//Nmv/u0/+Yc//fM/+PU3D8g8Nq+w/cuh549BwM8XUzM7DndT"
    "82n+xccBwfs77x6eYuEPP9dVfp41gx4jh/O/xfPlX5zhx2/PXvB9UuFxHnD6eFnRS5xxCTA+hp0+++S+K39Zvz0bsJ8fingJt/p+"
    "Po/bN7rz7pM28udBzp8jjXd6f/GoBeVi0WwfNnW/jiHKxbPXc3/rwf+mDA7lN6I/z3PDH5u6+/Hcz45x/uSp333Yx0SVL0HjH957"
    "8UiRz+60+8ufc0tA7x60/eJ7jwR8uvcIDL744XN+k/TFDnPbp5jEh1pfhSGWefQP0wpPK7xej0P6SeY3jRv6L8PxLNb/Y4Xf42r8"
    "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"
    "rMTB2jgTrQPA0iYzdk+x+em1b3cUCrRdiizTlp+YYHUhiZoqLiIrrS3XKj/FOVGp7IY06/wiMXIKlq0oM0ZhFxcJHhm0ovgKwuf8"
    "U1huuCY/+rP97Bp0LVZGRMEoiOKkQcKotdxEse9FgwlvTFpspXm05T1t0KfKcV/2Tunaz0Z+QeWuFupAjzDH4KJMJsF8vQ1NyfJX"
    "qBZxZyl3bs79Zd/SsvubeSjtcA2XCfHqTWurej1CS5qQKm6dNw5aPvdCaoiI+qC+tLWjdmNncu7XvPoFfVRm2chLYrLWFzTeINsQ"
    "eLl0phiNeCLIEXU8yg/CJrLEvCaxdx2NHpIt4Ge2/cTte1HmxCu7ARXiuLvF2OmEJTQA5i9pJIwG6GLnTIrLSho/M9JWtmC2Lhh1"
    "6w1g5UdZeYv0qMOYoKWW5356qrUPynDdGw869eZz88ldy1CqJzkL6LrOO1v0GxcTu31vuJFtzKEBRP5MhexqFCmGwSz3SKIEGA/a"
    "3mjRIzw22nm3qOy26+e1g+001t5Eo3a0nbyMYsi9QJMkmGeVrspMT6bQEvQW68p0frYuIOyG/iCMSA/QW6JoHyeAfZGPDYbt29ul"
    "ZlADgFhbq1cSrQlYjETDKokq7mi+3n7vHQFV3BBXRJOqpb3DNgxR7vEkCuZnCtVN+NtyMxEDwW+ZA0XG1snslsPDw2IOyGx+Rm6o"
    "N8GNZ5wj6qjHLoMHD4wGpsLPj5RtFsra6yoHnYYvigfe1P98jaVcOM16Pf3YYGoXIuEr/GRJg5j1ZDp+UAyXUWO3zh98L4ZFsJQs"
    "5o3+y6EUGrUPrncAbSJY2MmWsw+oBRU8DMb+lsyEHPMup775UHb12pp0KGYPMZrNxYBPsSIN7VqZXhtfm56gtvllip96WpUbnq3z"
    "1oGSKlpa2Sr12BJJ6QzOJtWPL0iHTcw7vBS5QDCH06HSpD8p9aH2BC0L1iUldvII0BkjuHzKsNU6R23hr4nB79i5aUn5dQXlt41s"
    "jzUSDtz+1kILznjxGjomD1VIs1KdcJWsNdoFozVvPV5ZBQgWA7fhOaMEUavea91uHWWqwjQuzLE3D2bsMonPgU0qPEwq0N2Jkh3e"
    "6fnhRcVtd2J7xt888y9HkTfz4wrVtW5+RMqWm8qhqIR06zY/Ur8yMmKtSbgpZ4Nl5aON0XPdcG3TbJRQyzDJ9kE6eVTcPFxvK09Q"
    "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"
    "Y0XVEDDtcXZ6N4bLkGdmRmjUYbFQmM1RvqmQ/Tjkjam48Xxt6n2f7ayIevwFTApGREDc16w9HU+WTEujX2dNKjgdRScDlefGCVC0"
    "K3+dz/4NbTpdUz/OKS7zkJUbkEelMaSFVlBbBghzZDsOsiJpDLKrqelwzg8Ff/h0u90meNaMxGKq350ESL2rA8zjouZHzJVxEPKC"
    "5MYsyA4qBOflbzuWfpYXT0Ndwk8T5gRrWUR+rtDxXIQ1a/LE3jhcF+CLm4owyjPzE28jqcR3+IZ7cc+AN8/TeOibRMwhbpHtA6OK"
    "SMUsO+KmSMu/Lnu/nEe0oeezrDi+QNK2vfwddk9dk8vs58tl4IazirxVFVKCGPcI15+gbC7xxhjreLXOYDDFBH+ipoNH85pn6Qbh"
    "4pICqqdp+SuLATFmwKaoqQmZxnJmJlwIoqZlb0xEFJ7aKHdolitZBrEolLRm2GVqQ67yT+lE1pSRc78ltQ85oTUV/vhQYZ11c71u"
    "ScUcrSJtjqVKzNjaVkqbc6tPoy9nUk4Fam85jf1Ky23H0mZbqUuNFowJ13sKQr/b3rsCcghb80y3GpJy2iW1l7/VKEiyw/6ZqBCE"
    "+KICRElcEV4vGpoyfsZoA/ni3iTMs+S+clkEVzXKasUMn85XT7FKCZX0uiXdAS88E2fR5tKgmenpMJt07rKS0JRXjcuqKG7bRjIR"
    "GVOxPO9kl7Yi3Mi9/zUJNPwa+LaLBXYOBfvMMazKZ2JRlbGtKX0aAbVYXcWAn6yXdqrF4QHiFGHa3lPqa66pnWF2LUa1rDT3LT8K"
    "recufWWnNKvQrkOH02qwLjtsKSKXt9XUqMtRl0DtW6NeFJyTXbt7QmapakGmEx0FUYM2PLICgmFX19uQ3JiHaZ3yTpsjO24Ygabl"
    "chV2GyyGhpbNJIAfj3JA0vCiXZeX9x0VQWkicbOwEOQcB/LIjqPGKLxtRI6MfCiVhXHZBYQnGwIiarZst0JnZe/VTnqvXrlnwXxo"
    "3RsqVVEosLTzf5tYSKiZgixts8zPKOTStiv2jIIwbbdizygu07YL9gxdDbbchmfXWZeDrWyxd7egEctM3UYhvm1fDBaFYbcGCzrz"
    "shsYLxPbWoAM0bJAaW5fC5CrWNdut6nIV8BDgUXKd5tdbL5EZjT9D9+JeD9dywS/XbdI1kbTTZfKlvMFBW46AC0lItdn3zhQHoXx"
    "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"
    "Rn/bixm1"
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
