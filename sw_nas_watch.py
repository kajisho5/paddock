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
    "leJ2Pw10mE7meOiMMioMZ90kHBX1jfaL50LhXebEpaFLCW097s+Nw/NwRDuZdGVupIeRfmhEZOmsG1kVaiDD0SciyVTPsvuW26ce"
    "AOOWLLVaEC9OViqEERaNUqBZrgDxTu2eBDsSzVeA/vy5fet77igS6Y7JK15hs05VMTWGZfVpB/HYoFB7hk1SHQcCulXs9cwlvwQ3"
    "KnmqWoVPG+H3MXE7EgeWRDan10uxOAoSZTzsFT3lz2ouFCzp6VBicKF0LEJCrxXrHwgphvAwGJO4XA7hHb6qxHS7uRsPfYbKivgc"
    "fXXNl0EWqafsIHQvV1hWBgkAITYSI/XeFAt1d0LRnVBI75HiMVVMjymkPonEHO3kdWIYhLpjOHuZGG2oBr+8+hhrua/6GNu/t/rq"
    "6F8gU0DD17OHEKjme9FWUIKFs4JiogcQqjTMhPL/i91HDXlLUBw5vC2htF5Z/R1MrazenerqfYKMsAg+NTqbglvjEn7cuKUU64Vq"
    "kW96uMu0R4diCS17nWLBd1Hw5wM+q9jrgZPuundjR2O3tPGExLbcJNuFFwu5k5YCk7/nZr/HDRobhk62Be937LU7nmUO69g0cfK4"
    "rvDYR7cnlgc99tat3PbKxz7L7ewyrRwhDtQrUJepZmQu8XGc7Wwyicvd+JznqLrnaCARj7IkU+NzwjiTF00N499d7Cedted4ssQf"
    "rbFJLhfTgPzODZKf62t9E+zujtnPsUhLshH7IMNvD9dM/3edh2JfvnyJrz6Ru2OoYL3TbPzEDI8/jO/a/l2b2nubB0832HkebHRe"
    "bKy3N0xlR4V9x1Fvcu2TTDbQUc7I5PdaxYHIRkVv8XlVubHzVKpF6irWZR1PlSLg2nOpIPjkqfT41lG6gu01mWmtvSFzwSYtsz3v"
    "vFD5nq4/lxnX1549lTmfPnmyLrN21jvtZzLz2tO1zobyLbe2sfb8uWps4/mTZ09Vey+edZ7oPvM6gm5toy2HL+Aou7H+/PnTtqrk"
    "6bNnz9Y6spb19SdPNjbWZcNPn3XakHXDVNpZb7fX1qFepYu5sdaB4hqaOkLOwtPnG+tPNp5o4OoIqaC6/vT5s/YLrQFqIpSirvQc"
    "p7tgYiqyAsfB9jhxz3BT4cP3bZjyQh3jtBfttjzAtemtI2GUFfGIMtOzR1Moqr6zoKyrQTzpSTuOtmgpDLL6v5JeSE6k8wBQNfS7"
    "jbgeZCxeIZ2ZBsXGaHBHHCTW9q+EZaZE5neredWZ0uqwpNJtcSWY1+srjbQu3zfM680c/e7XmylLXgaxMBHsPEXP+gopfOq0IfDY"
    "Qn0D27yDHnWeIn/EW2htj69syaFTi77aRVSiOCOkdeBZ2pvAtZYBLOkZiooBnJ3NTWC77wIUZWIegI5WHtST9Ua+MFqxKXA9LBoH"
    "QKvoYlCuYbV01YL9/90yTVef8PX/4BJtdqoLs7IOK8tu+SprVgVxTdsL1Kexcb2mhSTuqskrqwYXluuRUa4se122N2PJjGQSh2J8"
    "vRJwKGODAA2fegMSe/YbK42wXvp3d2FdPu2QnQaARiHKvrqDTbT1a8gWZRfugtBnsBT/FVojGWQVMaLdn3pTw+UJ8V9t4NOAAmpg"
    "9S24ta0zSNRQ0rO32qLjbb65GXTYSuNtrtcg9JH2OeDuLHFd7DoVPDllqLWz3nlZCneASoKnDynW/b9+ndIdyV2Q0uLV007QcaeM"
    "XmK0pixAwyOcNRQ3iAlLzcomY/vStLw/vp/e1v8FDKQTg676ftk8c+evToUms1J4AQrtWJdOYVxaJVCSxNvj0fxwBTEBD0t9uBMj"
    "LtFKEPAw6aUnySm+8oo/TfQCJX5LQKzYQqxp6MLD7SHMR28pGe2phnPTMBHRvJfU0zt+kp/WCbUhcIdKddiuvCH6ClhiuCTnDFEP"
    "mpx1Nnl/A/5xs331gaQYUrDRFe61tyI2DtlexD5G7CBiMzrWHdG7pl+kxtY3+ftD/v5RCNfZ4ZQ9MsF9wt7P48BDe0KObodqFJpN"
    "a2U2G4zFWUCE0e8KBYSrlXB2PUDRZi06T0RAulCRZeQX1SnDUCt628KK8FfUE+XZtIaPnEknI5hqfYpMF/yGKoJf8miGAaiNZJHk"
    "t4TeAYBy05vaAALTsCh5TXRrMCZnJNKICO/naqRYWZPKlpZvDcvQebBsxxOeueJU35vAVzYrva4Eu/0YsxhpqU0+8DvhIcpxvy3m"
    "Jqijrxp1+0LfWPWPxcwSnFZ2FYMF/ihaQlUfzXZF/F7k2+VHWannyhYNJ1mxkPBoaW3WQjoubNndEjt1VIAh/XZc12gv24dldXuO"
    "JzYeHaXdlEXZhBLp3cGSEQE4voEZnOzimaebM6uGbszEVRLqc8BRk+dFF9b4nNlqgniTk/pW1DhEGzcGB/OGpDBWA3dBTvSoWi9L"
    "VowCsbraS3z5Rq5+WxpqNeB4P7afB69cJWj0UU8PpwGA70vKTBGmvEla+CNzf6Pc35bmtvBH5v5BuX8sze0gkBKB6dlV+xYgEiyT"
    "RsygHgiPMOxL60NTqal1CVopN4929UCATL2PHqx3iUfIn5ad003ZUJPmikUkVT8v0QjOdmQp5IskCSL5IgpRKWo7InVXnY+3NILC"
    "ZnWAqk7Kl7X99O4eFpv7RtNIKsqTJ0pUT1qQJrki11ZcGAtFt9XSiILtWhRy7qXDTLhsUW3PnT474qcfuRY/6SyuCAnv9DRHs7gS"
    "8OCg7g8VdId4tWkvXba4shg6h2EOBfCdS7pboWOuUyUXgBtUaRuISd+jeKmYZOjIU3aRzPlQDEKlGznsxpkl/9eqK0APygV6wBx4"
    "M4BB2iKHcA0lkF+xuUat/E/gxNlVlNFa//8Y47MWtCN/Mc1BiS/k3EZuFD5s0HbiN0r8phJ/OIk/KPGHSoSlqLR+zgc+ribr07ow"
    "kJek9hgDyXa7eAIMxN1dY0Yy2IcEhY0HJGr/GPu2lJ/nlbe8Er0xQL/widc5Pc11lCvd5FuIP8oJW8xbvMLpts5E7LXkviBviY/x"
    "2oMjw6/K4HCryhD6GqLbguI6U7At6KoD+W1BPR2Apw68kb0jff391O5hHuwLjaJfd66n3jBTFdBV0T6tmtKdOMru/yQ6tZhUr+8b"
    "3EUIPSqDn2nrnqfS2SQhgwM1P3+Oq36ivgI7/ai0X451vgJtxPYVH6oybqb0vf7XIGFuEZv7/vp/0uDGv9GgVQLp4CRR7Q4zneBc"
    "D70lMyzYia4TWPKM+MHcWELBNq83K99H9yTZFG+Ww1EotgadU5ZkKUpvmp3Nz2PNSqCuCSFA4kr6YyRXCfUn1ui4FeFhO7Y7zGI9"
    "+5XuYoK64koAEIaRWdJVQSp1DUQSSnlPfJ1URN1W8+QHSIrEeRCFSH05bcrmNsRfdqHHRZ361Z+Arj3JsZbckDluyKlVjb4i4RZ1"
    "lxuJ3MP/2l67cOGaPrzL2u3SrSNdrYpVqV5rSQLhAdCg3Ydl+v7igKTUuyyVkQEw4Fyrfenjio6Z3qjgTKluqVOYOmTIs5h15oDz"
    "lPUlnLaq72xqn2SWnGvoU2h8qPAluuqVX/JYZr7ocGY+Z1P7OGNllYdMdXrB05oOzzQM0E7fPeA4oLNOmG6MrhinWhz/VARZ1Okw"
    "+sSVBvmck/26+BAHQ/FhnYPtGANWcyaWEZeo3+y263wIpRlADydWn2L1dLtn4MVo0wUrcjZFP8oy/pyjecV5MlPnxHAI4LG+RQZ7"
    "gq1EfDdCuIFwOkrYIcPjsBg7idNsSsvIGarzIQfj3AURajo4656b+XVcLh6j9Xf13Dwx2lLmHL30mC0Rxipgn6TvOWwX6MDTIMNo"
    "pPUyCRWsyq7GXGMNNW0PjCLsociW7DwySuZy7sc8+RSIp/TV9oDzlIL5YVi5a3sdVS7XpokQLH8cVy/V3kaLNz2Ve5zO0/liDG0X"
    "7yVHeR1Kpcu8sn3sKv1FredwlhPPD5QzuA7R6Ew9eorvE0uT2hjO1Wn/vTL1hoBl0MFi7QmsZ9QdS/Qlx/FJ4AR+SOmxJwTXZVNc"
    "tOfAXObkJwu4tWYussYQ6OWYWXcPahevMqCELu93mrky77es8XNbqwUo3zZqI0qTK9TEx28y6OnLC34RJW5ZhSlUZ522FNgB0Xgq"
    "paROW8Wx9bVN9DtAset9bsuzt3LzFKAVfTQw0dYJ+huv8ObV1xXOyD0hPXYgH0A4E4etPaBE6qkEMoyXDypY5zf1/oEoEGTiS+7H"
    "H0WkwAjJ4oc1aeZUUdwPhYUvPwlPqQ74Dco+Sgq65HBNK2xg/bizy9eg6QTKo6ARmxeiZZx0GLCY0I2l1ow0L4TDm9/fyrtHAyar"
    "t/ilY2CfptCATJwb21Hb6d/tVFQu++X6/YuLhS4Yf4VViPZQBxp9Ydr19asRDb+rXZ1YY1kJvFl6keIOSbXYw0THZvdBbyv3hXcQ"
    "a+DdyhtW93a1Uq5fLrKcprNiZ92anZ8nC72109De94HZoA5P8bn7wgH2nEF2EY2yw618DnwokarLIril4b4bo3FGm51TOwWERLvk"
    "bKXN8Ll74B8n0+4Sg0Pe0sl3d/j4r3wTmC2gWBs68jGfFRSes1EYwDq8LHw2ygNhd3xZsNvLmF910eQY2M8E8vnsyxgzjoC1vojZ"
    "VcxeFex9IkuMcnYrNugvUEiEvmL/E3TD/kWHMA4Axr/IX8pT5sk+v8FyeGoUwTCRAbQ0ESFYsAdZhI9LCbvX7mXIhEIwgQwDCLIc"
    "4AVDEyt8OaScLNp7aJ+3hnk2kQr9ZN9n7AP66KxIhrtOxm6lvjnDbXdCw15s3dOJggbzlslNjrxeFYBw+Idrjx+Gk+g3LvAmVEK6"
    "+apQQZgPHf/VxH/1u5AAZdowWwHHmfNN/74+1L+v1f59hapQDXlrgGjwHgVHYzn77xN2i88DfcQT75DnhC4/CF2+jX12NrawxJ0e"
    "zHgYY8YzyPjH2EJAbRJJsvg2g3JT4NzphT5AHmDaIz0hWM0jau8PqIZPrGrw7YTzLMwjWBPhsgE7GdSg3VJSp9qJRFCkE2yST4Ac"
    "2E0iKKhLewSqEtKLSXC7Uwy6HvwJp9xjx2iFex7mXa/msbd8WHa9V3meXWHQY5+m8vPT1GMfyOpQfFPYY6idL2NIdZ+95knXe00y"
    "QI99jiHx6NhjB3Bk6yrvdPjhsVfTaVGJOiYmsuuJ37cZPjlzkP18lwPDh5QHV5/3KY0jgDQ97ebNWQ7jed71tsLBhXSL/qLrfQzP"
    "PdZZg+rxCW8IrsN4iYVknadQP65uCD4T7UNj8AGVvEowFsq/owMXW2t38Rm3QvRk7ZkB2voagWt9HfOO0L6ArW+IsADD+hNsMYIA"
    "tPcmw1d+1p85kF1/bkF2/YUL1o22A9QNqA0YDWACIPzUwLeDY9ztYAB6sruGAejG7joGoMzuBgagwO4TDEAHdp9iAJrefYYBaHb3"
    "OYIK2tt9gYEOVtjGEFWNda9h3R2sfAMqP5xNBDw62Ct7qtbWIPkAqCRMSwLTAuDseoJ8ekwCuutJIos4AcjpSaoKk4+T0vUU5fUs"
    "dfp4YjjJhf1VCy2qVLm/GNWgu64gmaCdT39lBblhx5/VZWi9ZT8RJhQTi2YAF+usXLo+gEjVuwJqxm90Mo2/6gbGxdoF/3mGwmp5"
    "AfLExEEzyd1KBO4K63Si+9uSY0ahWdepg87/pE5r4mZTr5/L/mEp9CntdAtd1zJ8qgKoWpINBIPz+7tizqc8LGVZYhOW7ZOKy7+H"
    "c1gAA8EAuQPZ61+Wu2/oetxY2dU4Hoz/Whf+ciNAdkMiyxmQ3cHE2qH0tV+XzLLLMfyKlzdwP8FGZzmxWShESNGjxjsrMk6IjcFf"
    "ZFrKK2TvoJyoFM3+iLECqjkJ8xsi/x+J/A+gHzMbm4XQpqCWcBP8qL+F/CIyEUvmeyleLJlyaD8iOMyg/aG9PdkvEfzGvjqlWoZQ"
    "y9iGZsSTMlzK4YgUtZPKfEIA8dpKavKWFYfoQVm/3lvlV6fKr3aVX5dU6WRYkq5b/EZsLgQOBAb5bEJDHsOQryfByQvYyGAbgt3n"
    "lN2EwXlar3vbRsxF9BDrlwakHwqpJYH5lFeMA3noVt/A40E+7TPDziaEA6OJaAhdqlZaqNdXPhTsTUQZGis34d3dB+AXn2/i307n"
    "ZfABePmDQYBb5c+BYyP5KVqqSyLlo0p4PNHXAqlaWKgDKtUFjahV7wEyE+RZW3vRWyaBrUpdjVxXu1J84CnJ/aiieidOJWzRYzOC"
    "3GLjiBPT1gcfStdr/2QpMKpiTdnsfqTc2Fpj0xAgyoYWHWvy5QMEfBtmQRaxRKqWr1/sHm00B4N6/edAWg9VZVwVh343E23l/UGb"
    "7gh3gW7P7+4AN+p1Oee4s6HICwVh12GgxGMEEyatRKpW4FIabltIVgBA/uLSliRKaLYvSBaGJM0iJ3QyA6qqiAzaDD/MAWk3RUjd"
    "wGqwYqSw6ScAq4Rlm7HKMl/o7T0T+ibC3ohdE3mFi0y+WiHmZfksIBp9ByaLTOHRyQGKuNUvHsAx7KmPJtXuCQ8LeIxGzwnAkZEv"
    "FuGOQjhRKAp8KgrD9FwVOVQAFnpAGUueiJ9rcsagWpnlFH3FOXpbsPi2D7bzKDxHKpe7dth1vduz/DLLSxbg074j24Jr7LSbOka1"
    "Bhk/R+YO7nuE125pMErwLZws3RbSeJ8ZjQ1hfsivaqOwYXIwdSkhL/zwPpELlSYhF+mWLJFGrEU3nUtfeLuC0LK0Ktm9IMaVD/Gl"
    "UFsfIjFw+VRK+6UpLmu9iiwbdLPKpCtOMRjNQ5KMOTJ2vlTxcWx/bcdAl1IBTov2k4HhdiwfZh8ED3pO6u0O3Dd4dI3Mk6aEAGFo"
    "SdJCyC4z2BY+8+M42I7FleExmc1D149j3D6W7kF3dy82l29OliY+ynR3UVqxWxBBVpov0EPFYqh5/Ufk4zTJGbPnxFijOU/bBkre"
    "Xq/DtKW5rybu5LQHOJdCbYwz8uzgs+OocTHBJ0QsLwETrd0sXHuJS8V+A3vNsB/YnxJC+K7SL7ouPYjpPatex1osvcOJeVYhWLhT"
    "kxbpYo81H7QZKnQSY7Q0ZqrYRzepdm7bWVwls2MWX8HbStGdSdW1mlDLWSEHOZ3HdAh6jI8ic3HRTDophPvDVKGctGkndyLmIR8d"
    "292ZmKVZ5rqvQ+GYzHn0efEhITEM19uPnZoGVeUxIRC2nRaR1z87QqriSaJEtqrOziNV0PKg3cuNn8xcqfwkQXmSC4/g6jHwlCUA"
    "pBUc00lyylDzW4+ss0SD69NAae73iCw7nspcf2OLtGnfcd9IVfXwqkldZOSkGk4jdH2SkW0QXy3tOyt1x8XJECJ/GSjv1rdYFiiv"
    "dC2VNvkcWsnnvCv6bdqAyo6FwScq0TkRyu/CHOONQxT4FDLXOfXfcd34Z8X7ByBdn3AAH1/Xe9hH69U0fKzJjRR1WA36XU9qUhRa"
    "xCe/xVNuyCRAbuXZ9Z1kGGAXbNybiO7fO0/RNbcjzfiKF4tqLnggjwVpMEtgo01rMV6ipwPC8xb6BNrbzYHkSbLfE+8pyVsN5apH"
    "vhX9WcghlZSghQ/4GR8+0gizlJ4tSlRucUsKPRehi0P94Zq4G77JMi8J/31GQrnw1w79zaGdnsqwT/GC1XGigOdxvoHZcb4Vy0Qu"
    "jh3eBHNVntamdHS5blG+d5ZwCyeMkZc/pPA8wqkgqyRNyj8gEVVSJfQQgiqXjivgeh1wrhKngSvnlkk/qLlWgQIIy7hUPCyVl+gF"
    "vgV8Kp0LlJPlBnlFNlsLeaxDRC79suXG4kvwJmonjYSR7SRGcluKa2tF7bTeEw9IF9npvXHp6Fteq/+M+ZXlK2nEpSddaEv4Q7Nj"
    "GvIx5WApxYlNz9TYUYNJDN/cysRdKxsCBrXH0RAH6gIWPn6ZC0tGMtqPyb1wABSyZLG6Zqev3O+hw3PCRGKyya+heFeLt8Q7tIfi"
    "EJsQcpvoI6KAlCCIISYRrsgCmS5AsTp/JvP7tBpSyeARMuFLmcjY0Zw1RItM1Y/sr/RhniSUvYD8MNI+ugCJIlEDaQ0LMDRED5hu"
    "0O+KJwR2lqQxpw5fqqWS/Q0PSrLfN4QTHWdapNUYG9xydf3FEry+oNsnFErDByuzqY74mE3nQrtU37QSlCqvY4jIhtJjddRYAftR"
    "i5WrZyKtptAJJ7ZYTYNWUXkc2hZ+WqU45X55DApOlrK8bFc6sppKpzRv5LljnDnihM9aKVt5+ROrhJw2mCq7zqb8oo8RzrrrjbO7"
    "u91SMT27iEhAqnP0iAQsdLmMDORESnK/nwe3tJK6eYUsMMASOxIQY44ul2BNVehYXiViiwvfr6xyWHq3ZgVBM+aD2UtIp4hPptcQ"
    "JOgws9aQihdfcx9gD6iSN94UjOABU4HrHk6c0wyPnKJPdOTMzZEztY6cMocCojxy4rRVjpypdeSkq3qlSLJbOvrle7nNjN3OtTbI"
    "SWVrPEXdUuep3FL73Fzlp4F3JcMpJqD7TYqdYACiCI3flJarWJxRaN17pSJgVDqMt2A+03lj5Vb2/hLa86xdTiDTvWUEAvrMqDqr"
    "Tn3UMZDffFC35uxVDJBiXyKEF0kxIfjgMVg4QrTH58pEARfkozBvypYNIfPBlmTQYHk4G0HBfPrOiKodMeUdqFhflnHfn+oll1cx"
    "Xo5J3KEPOl+8Ka1oLj38USQrBU19yOEorBVM/hI5FRMxNccKrPNbFEBPPBtw+A5tJTa2MOSsklZITPhDxDtDh+hHkbb0fD8IvPA8"
    "E3ab28IuUthpws+7JLxRvx/FE/XKdhI1kpXpJF5cGxNLVLykPzvSnJPu7EToOhbpb1FvkUJHlzLt2Bh9RjPpdFkYaPLJtIx5VOPp"
    "IL+ZlhSK8C/66amNMjgB0K2PdGcnjT+lQjIahL6WFqLvlIXop2kN372jP5z0B2QQr2Mj9Sl6hLaPlQYmyiWfCKHHPRE6gnZFAEc1"
    "EV72pM0p6S/XUHOZ/uAb9FNVrW0X+9qyi6WaZRjrVkGsXYax/jwb0chQq1nCTBiyCk3mmtBhph9sFpADX7aRZq41ac1dQ0nmJ1IS"
    "Fta825aJ744y8RUwEYrMsimxw9eEvqvIRf2+CgHjoDmh67rUmDYrBbV+FJHhH73x9ZYeq0UXlOrQthMDD7ITb74fKC5kJ1aH/3dx"
    "8H5wshOfsreT4F1cIennGHfSPq14OoZ8QnGz4/egC28nuFl5q+cTfw6f3yL8dEk3ZvvhxlsEGlPP3FRJijHF6N6zij9IkaykYZi6"
    "SyrUVnxGosUs3ULta4r/gxqq0PBeUjRcB47sxKg4M0u9+dTJS+vw13kl/uuaLV1o5uhBV0vo+h8q8bZcIn2WdEYCp6aAIRe3ZfY9"
    "m9aqMj4L11TtmtHQFdlm38r4XLXmVr9oAv8bDW6RAr24ZILxV249mLm0YdZtFJN3PAYo1sUmFavYw+vR3GMHby76lnTRqlygK1uw"
    "LfiPNSAIi9uCsEj4d5sgfweF2rxgk5rKzQp/S7lZqZ1k8Ds7idgCIrMbTOzdQMBjGRW3ye9Ak98HCa+huBIItmmIopz2eNnRhLbs"
    "YyCTntqgaQ9W+xxtaA4ttsujEGYQlo2twrfo7z8qhyQh0bm7U9q2TWK+vR6vKGqX7O24kUNJ6YwMFXSW6HJbZp9D9exZI61vkAsj"
    "y5Zz4WUj1R08ZiYogRBKTigYVqeAHu8qkzjxLjt5MTf+DHPz7Hd7M8jwOW/l6Sk/yU7ZIAhbSvbHIvhwut8jD4Shbo4N0D9BvZ4s"
    "VTJu+L5yaAsQTVjIIrS0G4gbHuxTBmPM9CGol8l3kn6rL+w/0BFyhzhUHjN5EGYV166WPPub8xrRyU122itt4ZeMVOjoK/8sq97Z"
    "mVCV9nolcr/ikJzCvDDO1ui97BJlHRBvndhexy4OtslNdn4XbMApb9iAozKaHoo7xo954AkjBOFFFxfJKsmjYDuMson9csn6U1/u"
    "8mu2z/tcvy158jE/xaep4IdcvkaLbyZAp+htsiq9hw4eTWiI6MkIRoA24rgKRBAXBBr/K7MPR8KA74y5EoZUX6mk2BmEmeoU1LfQ"
    "ODbl+glPh+baV+oMfKCLVOWNS4j9/hxbvj5qG90k+Kpi1O16EkzCeRkkrXM4PjXUYRxHlkgEYCtZBh1FqFj2bfKdI2PmJCME7wcj"
    "SkhNP+8nK5Z+94LvZGzrVvqIUFfx+EJJMsdLgaXZ8THO36j0d2qyH1uURq/SW4cgNOK5USBgHV94bVvzxXt8wna1S/cwPXmv49yD"
    "9RRNKsMROZ7Da5G7O/zZ0FTpPjPTnvSGCvgR2qj0vF4PLdGgZdgrW9jwBelRrl97mWtNPAgy1aHGQPRoQMUAvTHtnv6wgejMoNKZ"
    "QbUzavAZ1CV9URCIQtMN6ulN2Qh9llVABkmyg9TgE9G5p/hGbQz0XDnZhSMz0kfrMmue6xHPj6NGxTglCmI2RJvk0mcTvL+W+8h1"
    "AIcQ9DgiFBGuNUqJYpfBKGTfA95b1NUyujd/oC8J8vanqPByY1jU7roMwontekcb2n6XV9seuwwO44UspKUFecgccyHLQ3ad1bzS"
    "HpguDYW9BnR9ze36w1bES413qzaWrqnv/RaXjl3zZbA1qPpMutd0+d83Cl1u+HwZ/LAp5W8a+lrjtg1/L4PInufat0jYV/6Qv2cR"
    "ZHnkUOY/MGrqYIeyLL0Mvjhdk3akl8HEyb7UIlyqj10G6eTf9fn01y2u/5oBrWWmfRl8HNCef2hYRnYcrBzW6+KWUkCETYPD/rXy"
    "sHy96uk3DUh57Lp3iGtcsYWzIGKj3szQn1EwI9q8HYzcxyJGyh1zvb5t3EeNgm02NZ/bwVnRmLGpz7bVUzGHQmqd5xC/zUa+jwox"
    "kizPgpmiS+3NQyMQvyZW6rJxzb4rlashECdH/n1tyb8P59K/Ne5Bz2CXBxKGJCsw5kkEU6lzYoMZCIaVyeil2Mfz63qdbtfwcu47"
    "uUi3TITu7krb2gq3CiDf34EL+n5ylJ4a/hM3lcu7u2ufBjg0ty/D/rBLMe7brf1r92rjWpJ0cVUubX7YZX95l7QxGAwwAjr9vU+9"
    "IiRg382MHaPHie8+RR1Dn6Xnb5hlFXzq07DFq0bdxqVgj78HwEhfQvJ3cT98CPSJbQcVMco0qMhgZhLSHmtUwbxkcuhZE0B7UbEr"
    "QZkGC2KYmS4Nx8Pj4FKtge6nsnHps1Hw3Y6BQQs8O2xss9mqJ6giuxTIdq2uU44h6NrjjaA7BAOA6BB3t4i6KaqaYlWC/gLyUlWH"
    "qqoRBN2qjqGqQ+zrNrsEiPup0F05DC5hfN9hQG3o9WFv1BsFe2UDFs9sdZXW7ghStoNpb7u3jSnbvj+SKXC4mzVHPf8Q46HuWbOp"
    "4kfNWc+fYjws0JGKxwxyCoNgendnljNFWE86CExOe6pqWdX80HL4IcK9S13Jn4PGhF0DWA/pvGNQ79jNcgzgOmT0VK1avVEfpiny"
    "NaoH15aGx/U9Gh6QzX5t5dJW8rjW+hn0QpSPhO4quJpoPYMPg8a1j5cV7yP/KnglEm6vguMJEcVxcDihYTbsvgCWXrp9cBRLrpc9"
    "l35deS4dMf0q2J4Qq3VFH1fAb0dALW8/RwCeK8Ilra4EVBL9Al3jcbaq/NcYQ+ecF1ih9nHLvOBuA0I+OkcPhV8z9Qk4L56jnUvu"
    "blydjAU3jwi7MVC98f3aLaiKWQZjvKiO1C21v5yfg1TIJW+2F7w/il0V77fb7iZfdQTj8luaUaKbcfYZ0c5Atbfc4wg+rTLxrRxL"
    "mVddF+3QdOC4CeEE9IDyvmKHUJ4fLBM+9hzGs6olXi2D0tB7SyhXJ9VCUgip0WpHqb3RgvhQ9kk5nza1Ze1JxVMFEdSSkKYWAZla"
    "LCmmrgF2IO0NPUvqaLij3QnsXzv4uaRcfycIlvSjXv+AFisXZEAAe9T7NBiiY43f8omBFgZtYErGeE0fsR28nB8bXmSHCPveoLHD"
    "+L3MyI7FjIznPrvo75CSfnDRhV7tkyeyC7PpqkRihiDDaNInY4/S796IX4R4JDpUEZ1j9yLTvaHqXlXC7jisubfjQ6vjEXR8qHs2"
    "58MGKS1bMoA8dx+6vFUyOlSykfV0U+YI67qlJZcZJVVv26lhUFlOp0/3SI6OotBrieFFE8OIGpdfjYSUq+i5M3TqtaJ9eM1S4euN"
    "+h6Tt0yZL3XyKS5VZhIOoyVzuujmfa+0VKoX3keLspoprV4uIot5wVxpNUQufHlayqUDW8qiwBQHqeVqhGUIp1KPHUN5T0lNShKe"
    "mmeMUHrqMPIDXXBAL8oI0hYaqEYGqiEQ6qTfGCDAUGENha0iKbMBC22yEGDWxfeilmZW0FU5UY1K+diYZ0bRuY1Quk/NJZsL8ro1"
    "CR7/M/9n2n88YnsYnrXhv7t/znZ3d18/HhnZ5teBsctqWMZYUiG1z+lReh/6MU3CAW9sTdh//+2/zffehHm2UuZBbj3hlwZQPeAQ"
    "NbJCiull5b2cjbUntmD3MlFPA06kkPm6+hbkaOEtcVd1lLbsDI568RS5G6OAK58LNYNbnqjfmP3V06G2ydoD74tqn7/35GiJN0cF"
    "IghnIplSGy44+S7PXFOQvomWzoPYx4kqMkDD/WWF7ARV7MtAFXsH57O44E4JGacyH+g2fsz4jB/EcJouw+LCKeMmKc8sXwb4gHp/"
    "idnwlwGgUpEll5wkx36rHHNMb4kX535O/Dm0b2b/Jyn9GgA0HF84dFFhk+Pz2LmYYHhVEGX6JS9bzZ0sWOz3yNEZO16a2BJLn7wE"
    "JsLsj174ffzI09LbNjpItatAd87oO1q51c2bTfmUHO7ejzxBmbxHfR1aAcTL4ZwCjcwFVSz9HtVhvViZGsuDFen9EG8MbCX+6jWC"
    "esetI5St143UN6VxieUqzC3JtyL0TuplU59EqO+55Wj0jnXdoqnDN6IwpJKa88sY8F9B3PgIbvd4T71vb0NbO9Qncz7poZF6Vuqe"
    "lapnt7JTbaNslWp4y87COlxdnS/pzMI7VzdF8BuXRGyUBt6Z2HjozaVH3upNwZJcx+KFWyFij0xe7QxZpNxkOoXuGGSBDxMdrW4d"
    "ZMquSXkDHUy4iDfr5MZ+fPBklJ6Ku079Aoz9mIelKiwtQtKgRMkMABeLCiORILW2TEkx9TOr1lbrpMjnY74JAxdHhl+Kfuk3jXsy"
    "m7FiII9hTv+WvxpID+1atsVYLWwEOAK2wuXbaEJio4JPTRA9panwun79T1v5lL/z1prFPrjb2/q6vbt9TeyOniR4b6cR7jvyLGy/"
    "RCNtXSIsTYlbyTR27ZePzjC9/XK/xMdW9SNz37OT/fKUiR+xj+6XzabVlS+CLu6Xq6sqmy5u7uWloViBWrHsHQ+gOwWQxZ8UQlnF"
    "cRkUpeVvpPKWLj0yKs+cuKjpMaYVbfJclPqdDof/ypHblOi9lxLOJQfS++qndAIbC4+IwEonOMhgqjrvLXiwUExaNqBbL1oPcY3M"
    "MZKTGBUsY61gmcuHL+2Xl/9K79L78y92iqwfLJ+vvGI3P7DyEkiZ3AMs83Jkos4aP7nPzhrvbIPPHwOLO3unpxkwv6gyZp2n+JDh"
    "F8iFp4AvUBs9tKytAIdVLRBnBslUYqGnkhvI8c7MHrPzSq+mB3glV8nYMN68E5ys3CeJdiI0aKsjaD9nhyhXIHctwhMcnlt6xske"
    "TL1w+6ztpZwVGrjT7iOhuG8iOZzknIm8uytKXB8GzIygySU0f+p4epzArOjBg5BdWXiS8ukLGFOJzgHkpBxDjfnvdxSOjxayqE76"
    "XRGpZp6uVaTHgS+kBnLkPt5doAvq20OlmNCHEDoJOtQvGFl2x8TEfaFXc6mY9URTKVx6rhzF9fqheULhKFZODXnQBgbla8/Y2B2K"
    "7exr0EFXnfbL5MqOA3Wx4cQJGNVYafvyuKlv4efOuORbx4niJw+tp0AgI4xHOvBc7cAZ7V3UGIZsUNKi1c7DUwGc+QJX8blEIv++"
    "hDFcSGfXVwl8/OAYf4Zj25a2Kttp0GGvgGXwDIwnUvf1c3nyHij3aXCVMB2+SLBOjhVaFoC5Xqg/+MkZx4zbKdPhV1Z4u8TGuaTJ"
    "2/gO6KtUEsn1NXyfKPdhc8rrwb8a+DoSnFBXg4589VZkSP1VeoJ7vb0Zq7e9kmbyfz/pxQGQdSyWQR02NwVMVP7yZZCxpAl/cNSb"
    "m6ayuxIaussREPEqF8ycyBNbSfab9mTxyM0jtnLqCHSwYxE8Oqxt78tXoWGoAX0vgEMBSAJgm833sI0ShE/1bC2L7+nC28BCARQB"
    "qM3mGT8V0JWFoadL47eXxwsHBcIvOPssfx/h0htU3wxNhvbG+4g3nkirGPwDGF8q2ypirb3XO293Pu689pj1GghZHQqooedxctGS"
    "cBLDamfraLymYwNh0DUUj96gFa1c6vY+8Ufl6SNknaSK0ZOuzSYY/xXGEFiY9pXuzQFO6T0XG9L5h36ZA7trjw9gyRGQcIBKLfts"
    "nxSCVqR3Y/12ZWoeNiMmHo8QeBKyu7f+u03SRNjNdNa7y0f8fLHKErBKfdzGURcWMF7+DZPsqvsqnYsby8r728GteWwbKitzziW9"
    "78KWx4F64ttkXfOmHWyFiDid5w7m3I8hkhUBHn3ZGB9wBXRhvcLXQOeUEa93fPkIJndfprX2xatMcuKP1Lnms2A19OmetkeJcJST"
    "WqoKnDrI16SIA67duyR77znqEspa+rCucpQ5q34Fqn/NjfaLZ3drYjkiAHzxXs/Dzf6ylrkFp0fawYAlKTVPri851azbpxrhhUAW"
    "o7qNEEW/4AM533PjMgEB+EhxYNQ+dq3NpE8GgnBDPOkjHr8mnbbASG3lS/DktRjwGkUaYx5GSrXvPItuILyCMjyRyWAtrTF8NZ7q"
    "+MwXpzAbNnzmApTIbtrzJf1jqVjb9ryi0oMYiv3YPcmlK0sG5dlqmfGWvXwIsatv0a93nuGUdvUUWa2yvyrTUGIkIcC4FUTKleno"
    "K6j0HinSiiVPAjolBR1WFXO5SOXTUvD1nvepHaO2Z7doPwlls6g4EZZ7BFiHaGS82GOrRNGgQb23djHL1QvtvwO9ywwE6zgwrCM2"
    "9GnywCM0ZivcKawzDicR+pCZZWP5J7Ftlxe8lkjPGGekcSIFFupTVq7egO9UEaP9wlfkxCKf86Xc+8YzZLYll4UP+aK8XW+GlvgY"
    "hlEdBEW6RtgU1ToTEu4PmBrEfYrsAm5pYWmm7kISTCp6SpGyL00fQzj+dvFPkM1ZatcX44WX6+dFitMrI1t7viHeMl7RUKxkeCF0"
    "nhdFhh+kQa7SPJeOX7RDdM09Ss8thiqsd8Rd/4mYRenY5tTry2mtARsyRhuRonbrrboOZVrfszhteKzm+ave3Oty5w2qme2T/yxO"
    "Y+NAFbD+bBreoDGFVSIcVjzjT9lM4KSoZxRMDS/VG2kOa2pzWLNTNrU5rJFYETNbk7vUNa9w545N6K5ooZvoAUONskJKYJeK03JR"
    "H5aeKpNPq5oZwkuRySnZ4FEUlOmqT3I+eE9jU9NSIlpSCUEqhgJDpgrgMDRVpaX9vikbY1Y2MqVlmRHj/cbIVsphI81IjYKR7Nto"
    "c4aglqBdw84DvXNj7G/5qDPEWkStMbV93FhN6peUrAp9u/eh6D3b1hXMtEL/TMko+41ZsBs3RgAFZJIgM1PKgAHCqQvpSQOB4MZb"
    "p2nTjFDkGTm8NqrW/Sz7Q5GL3HcV+ioMVRHJQ293Zk5RM+ccEQRX+prsyr4Ou9IlrlqPHokckPsN7O2wkK6Qs5tRT/x+Y1uMQbTu"
    "s22iaUDExfTStxzZNowYcicNMQrRPVVSMKwGUg/WYyAU/cZEbGDwHsV2SB65MW7meDIVACOTG8rtRuEkv/mdSdYTc3d3cnrvjA/V"
    "eNjVAyN6hq0ellarkP2vItdErUCzG8zM5Wq9jmjjmXvUmblb9XXHAL1hv5upblQa67k1a/SaabGQPFbONJbJs+VOrk5XI0QYgWxM"
    "0qklCAMNjwzCiHcMRZTsy0ic2g60M0matXs7TpnfpF2hJzxzNwwE3Db0SW8aTHCp5wUQ9ru7K/wxIIJpMs0w8Wqj09YHQbCX341c"
    "VymAgl2fgCE4PAPmkT2BI3cCR4sTqNa5OLIKogbzic1VKtVzN6rO3eiBucMuIpXpG0LW1V5BrckwGaNlGWEiNMUbiblgAjBX0LyZ"
    "hm01DSMxDSN/+UDNIhP6eTQDo3tm4NJekQYo2zakt11Iby9Cego7GlqajNTbtiFiBQIb6+259Wpgb1eBvX0/sFUL2xKWNNxRlz5V"
    "owNqlFqszMDvlI4qpeX6GAfb7vpQEMPumsm5UpOzLSZn278XNkPVkJmfGU7u0vn5blaIOtJcSe9A4ucimLGdABWNDwQLZNTUdjZH"
    "2r0AipsvBHfxcqffOAguoCS134Ww5oKw/r0Ase+CjU52TuVS2dNv2F4Y5uEiOJCnvjnwFxf1+t4SFgPZugvktOLGHgxkB9X0JPyv"
    "gr3uWHNQe5CwB306QDiiluCo4qy3FDU9qtcnGISarrBrF7prxFBWxnwRIDmTI7E1+LBDFwsdurA6dAEJF/o6xm6WbL4ugpw6VG3x"
    "ILiEiiGjbvXAtApwOjBA0vEX6nXdAxs/d7r0KYB3sNDXA6uvB5BwYJTSsMYFy89PesfFOfnkz11YWufdKlEmWmMt4ivnRqxyYnzS"
    "FueqUXAlzj+4eckpqmbt+ObGbBxcLUdotgeokIrrNTOBK3utKEs5gtzK8Ns4/kni+J5QKZVo/um30PzTw2j+aWGmPlkz9QkSPik0"
    "F2P4awh+z8D3CNHNcNiei+u/sfh+A9fvbVzh/PIOcIc2LKL9nov2ewbt/0q3l6N9zh28h897Ef/YIP4v2AMIKQX8nyV+mP6TTVX1"
    "tOKzf5vZkBI8dUBCFnEczHpjR1tlrDgM+lIHKSZOUDKHkC4+829x4BqGCOakMWaLPba4uCk0qMR7+jna8X/ssDUWh60HOyb6Izng"
    "cYWjtftHlegFS0/YiphxoOueW7OnzhrV86U+eowkNjrN/YfOetPA7Pt4Xtd8i5z1sZhx274PID+Tsz326UNM7AYcPO47BgYLx0A3"
    "s3vmCxaPgWJuZu7cPHjqs6eEbh6E8KQ6LxBjCWHmDx02ocZFUBneeax5Z7GMx/fxzorcGs6KTHbsJLMDVpnnv3YQQZEOHTiMjEJN"
    "19N+YzlIl2BaqURjuw8Bx2cIFr9bOuetYxJOh0UQDlG5gA2GFOr47DBBNSlxYjuWt/3/kLf7x2HlBncbH1CCWMgg81ruwS0vvoeJ"
    "UhvpnTUOUcG0dSYjxEuM1t3/YaZE4UpZ1LYbQNUSvWXQzY680sOLwaKe0k1r34m8QxVas+vkbhKA5p5EWdmSIiSuLaVWqWVPYEle"
    "pU7ZMeo2CADJR8LxjgYvaHk6iIUelL4aE5e7SrtI75KtRPQGwgfiEUg3a9W3fZk6Ul8bzgiwY/RKwH26Z7iVam5dztSlEuXDi1yM"
    "phnF6Vc7EpbXD8RXLxDwbusfqJlznDiDDG5pBN02s7vdVZsGFPmHuNUMzB2C0C4sK/i2Qzj1XfWnDyG8c/leLqrrzCxXIeKeIm2Z"
    "l4S1e/NEi7BlF0oGjSBWqIiEflgik9Ejp1UP5N9K6Xl76zFa4WH+Vs4cYExPXZ8Z1CUnimaWS52XXEKzJben6BLXxWqnRubUVkHY"
    "SpWKbOmn360bH/NuzafU0ZV6J5VUhNHZe9SZD27PgdyKp5+q95I011thIV3tifvIJFyMK8ZhzqPurVRbEJEWiFVJQqE548MhvqHd"
    "rTxPE0llEhyl1UOYLbu/4tX69P4x6PBC/+WiMzHVweB0O+lyYLwlArrnvCVDttL/u9S2EBFWMvQ2FqehozZEOKLXS2nvEkDBk9R5"
    "OLgQX2bJWqosaVUxzxp6b9GBS03J1lCRUfb7z/qaWkO5Ui5ZWD/i/jpIu/Imu7JuUtTuk2UBc2mJGOfvWLE148ysSlUtrspcuJe+"
    "r3Z7VZoWjGaCa+STulhi1g4myYE3yvpG58XG2kabND18BcRULFZUKtPaNrTWWHkX5EwmA2mYhqITlgejmatsbHdiYW+zNyaAkJ23"
    "JBsvTdpoyQRaLhqUC8ha6lOFNCXJAgvJypYOC3QT9IhwjqiExjt8ToFCBvnKlgpaKNiL1Rwm6MamGwexmKuMqbcalK2I6plbJDVF"
    "UrFRUGyvtBds/sCCXaA2sVqReXVF5npFMpe+KfEeqvVXl7c65vcXgA195wpvq8VsVmc7qe5R7vIUBFioKiYLM5rho+9ul/BqXAxN"
    "r1P0qaSnvpoqjfrJRVLIomBAve4NZOcRq/QlexxE3UwkRBA7oGJDd08z+DoMhg6+hvBd7Sx6qidjRNnCcAGOUTdULVaLBwOfmPdY"
    "D44M8NCjl8KIXha00QVSMBBDCYNY2VFdo6c5RPBLCGjUJ34y/3+4e9fmOLLsQOz7/gqiRGEzBxfoKrwIZjFZwWeTzQfYBNhsNgbi"
    "JKuywASzMsGsLKDQqFLoESHP+hEb1igkazVeez84vLG7djjCskOWxt7/MqOZsT7pL/icc1/nZmaB6J7R2uF5EJU3b973Pe/H8hS5"
    "zynQn+50aCDszpzKm9KmSxI5lySqX5Ko6ZL4OijTMeDn52Gkgy5N4eCcAvx4ziwPO+iyfhw+N00rxuKY21L4F6PwWArYTsVITK39"
    "DZQ7buTXNoJjZdh1rA27tre2Nm7MOus7ska72uM0bOqz53QYHEM1uSO6O52+kY9H9rAe4BFvz+d2dcyayw1yLexm4fYmNJ/q64pd"
    "KYihi8KD6DCYSnowQndnhBynDfs2/Q32TQwNghqEw/BU9MORH5hDciryWTjVoRUJUUWchK5fU/teMhVwPqFoKr+dsutYvfLhVDRe"
    "6rkCrmg5jhERrRgKhyrYLQn7Iq1fvHpHQ5HZYXNkbe3dARGhxTpMPpW3K1V4WhmvY/i6TG1JYkdkWpVoE0b8APBoLhT9TL9cM9ER"
    "tySZOKZTmTkb5pdivbh3F1q6ZTYUZ8ZDcWYyFKfedly+dIntnn0lG8Z8XupepJeJwG92yJEjlbcFGAaZIuK8QGee8wzZ7vPCF0mh"
    "f+X6F0sxx/3Tz2t2WTc2racIM026Hzn2zF97eSH9Y5JCenacZwI7jJlRr44Ecu2mDN/V6QQY0xSzR7rZZXwk/aJRTPm4X718HJS5"
    "jKfYavmVoIsxxWTa6fEMSchqosEfa0EpxGJpokmu8VmIrcKY5m9hsGrI3L20Pyb3IXz3FqaF/+acJxuSCRMsX14YDxYVthIKzzPr"
    "1lKqrqT0sasy73jOYpXcyuop8UWJaVcxGWww0hQwJge0NtvNO6k2llXcejdzJHoZs/1U5sLuRSBij7F9YcksQEVpM5jJ8A/aypI9"
    "LrV8m1tQy3BNvzfRNs+xdQUO8jSO0t1iEBcsciB9ZI2gG1p0HCwv1LOWVOEZUEUm3uFcGZaq+ETKatYI+d11Uu2Y8KK2wLUuw24U"
    "RWeaMoNQP2gs4wUetncTCrNmXLUjx6i03Y1v3U24M89dzHyw9vYsLz48xhQJFED5q7gYw9cqZ7OciPksbMvTklYNR+8ncEHg/saF"
    "eJxcYlUq7qCnTqmMVofq71T9fUBuUK/GFBO3gIpPRhii2Cg7YuOTbgQ76x1+3Hcjk0qvngTPDXVs029Wwh6j2R/lrCsxZ13JctY1"
    "GO7ejWzsDJHIrBVlmNAMReVCqMycDg2vihRyEbGRRYY2xV8VwSjs/tUoeDPC7EQexu2AVYPepTM+qgXtGq5v3QqTmjwM9ZjJStjB"
    "tR8uHhob0Ne2M4W/oUu8CKzOC2gEmjO3fihZDfUsN192WDpbntXG125EFo8jFUAUwFVB8atVHZopqzjKTMULZ/WkNMIyaeaRJi0f"
    "P9qfjGfUmaAta1XdGHgFpBv+VRJDmKsd0jiTjnhDE75FDbDkbIpjMV8fuQRauIKSdpGwefGYAjUWnaeN+sXrhncv7moHi3iB2LSD"
    "24A1RW0dh1WZml3TIRdV2bVVxZLn+qiLPkoZhyVfv8sCz82mMGxbOOFMtGW3wxWgFDpgzO5+YsXSuE8CsdlHLYYqF60OXiLJQ79E"
    "gTKQiS/jwaQfF8bnbxgTvWbnnWDOR8v+Jpx4Sx12Mdf0qZIjSXmD0JKKOWs1xEhEpUtju5ShlkkVIZNKdKXFuooLoxjRgWVEgT0l"
    "yESs551ymQIPDn0bzAfodcWOXyh2M6L1DAZr8od4H40fREcqJBwUO88i5q/sA2dCYcSVr3q8ahADQNK9ydx9iteWIxr+1kfU7Rv2"
    "KgLmfSTysPADsxAjAP1aXD4UyCsM5wOYApMp2VhH+CvxbYvQVKDaiQTgoKKKQjCUu9KzVJEL1rV8U66e5PHoC/eUqi/myp+DM0wx"
    "Y5hiZJgSzS/ZeSU0r6SJg4p9LQ6rag+QdZJX8qAydBjcQJEPhyzu0T/VlbS9idReRpRQ1ulXe4PKulgKLqheAFqn2EtEro+iwHjb"
    "bHHQrjkFWJpBpatvauJsoxUDs51O/MbNTRRoPEhEwVb1BB2N7ON7x8u1RDEvrTUwy5hcMURCqKjsVkpMe0KqR3e0qVDTQCgj4fp+"
    "5B0NWRx7JJSAUcHMQoKCEexl0cn4fU4kwmyWzGZTSz1MK/AfKf/ljvIU0l4A7c0dMSm8m2Ja7SdFPlKFWpI649NFeG4T/YsAwm20"
    "Z7MRpjvA3MVGAcDICuP7zdx0N3Y2ET2yyQDfKMP+lXPkDitKH6s/QCA1Lh+QJEDpm8ociHCFCd0PiaCU71GxiErAUBcYdqrHqwRG"
    "9chI5CnTParohCHMl+8FwJJTdANdXj53YwkcDd1YfNecaFHONzwE2ZDrfFk/pJ6mEbDYA5lJmEtUOGooZA5fQ3yzuBysZdKpdPyu"
    "1ZYMMsp50RGrPKfAmPkdjWxn11ioNub9hW6Inl+/mPwGEnF0JQWh0JDHKhwrUCroF6J2mYMYXcboQilVqW4n/HzEDz3FwqiB15jd"
    "/0lhd98E5bhAYWMsZI7BALP9jcsiPw9K+HUyDgpOnf12j7OtH2qSTp1r+4af7Yb6mLBTqmyEVtQL9a6o9IABFpmZMoJCHbkEDoK7"
    "akwrVlOE0LEpDQTAHLXu6YBV7szwEwV9Cpu5l8zdufDnm1rzYzqVYe2jbjXTzjCuEIxVmpwANeAhtaHM0gQY5ULgC/QQvmgYP44o"
    "wQTB2nzkSvNNHFuDYuJQ4rCQOxs329tb22IH45qymvuRUxPWhOB6tdqHYbXapliv1DlrqLNZqfN8aMQETeyBb6MDYUpi9HRmYC6T"
    "BkhzxVJx/bT6wPLwznc2BpSrBt+rQdWwXNLaO5UxigA+XSk1oedDJzsMDJHrk59FDpq/56B5Ol9ZmFXOV2boI/cM6ZhN1nOWn6JM"
    "FAedQ79XHLQP0SzFPRgH0O2h4Cjkzn+qoci9+PSAHlRXH8iA9U7PA+QDaBFpszJ8R8nQDf1bEv2LUb0sEiDqjcIamDJSDbEaHWFM"
    "pNxB8Z17PeLr86b7Bs8Cqpk2b5e9MoCTTGoTuT6PE5ZBtes8YRZZRKoxGc7BMrNgOqVwqxbsML64IlT8clSx3dA5WzQvWGjOq6yw"
    "XJijyT5VpCziPqJ0/ymmqyptLvYyZCZTzFxAAsxd2OnuIFNZqoDOeydJuIIbN3zeNGAgdH+T0eJ82YBTxoAmVXsJrTCSOsPESPcS"
    "W+7Ti6yJexFGUOBrUimv1JTIPgoTL8elQ+7FZW4x7kTKmFrJY0Yi93UmItcKzTK6SgKRGvMzVSB5VaFY1rRqfpYa5CEpOHME52Y/"
    "U76fFFIZN1M0bibfzfsOTWkXmsWwLWOZIUtBCiphihEFh16NQxRBto0VnBbOlAuNh1xqgzLOG96QBUodMtWftdX53lY6lGcVjisQ"
    "aQMTdyYTk3F8T6uD92J6VC/lk6LG5MPj0QmlSz2NZYxLXZyN44LimvPKT6PzfFI6RRjyTP3U9Kp+Gqpf8p7I3/fjd5MjabOpC4Yx"
    "oMABL7M5VHUnEwrhv5dPir6utHee9R9MZdy1PaQp9cgH9AMjgsMnb5Px8/jsZYw4E3juAi7vXHw1unTNbARdRjSMaoCPEEcVSwEi"
    "mfMVl02rFSsmjSvO+7sqygfCCY/PRntnEeKv7VfjtJx2iCJq2v2Fn2pSy5wEt6a8QJylakDs4lK0POcnq7pS8uK47Zc251wJkAna"
    "r8okmLgTw0b+9hi1uIFPy+aiaObTvmzg04o6n6bvEo/rXGdV0TbaRC6tsaZyFeWAxpPKPXwW1e9hQxDphgsgm2W3tZLSLQ6BsyZa"
    "I4yBALNjfc2nHiOFJpqaB75Vr4ALAVg/82ZY0HxSUFQll02GuFJSQ6UVrgSTamPkIbiEnm+CTpEo4soio4K6nlc5o1IxbRdKHiQc"
    "KZFRKqXq1AD/NHEFZoD5mcDscqEX1i1rQq9yriBlbcNwcWC7TuO1ZACHKRkmcfGiiIfJtGujgpUY0ZCCF5YYcJACFdrYhb4beHAF"
    "ug9bQWslW2m9bK0g7x4VKyuifQvNFLKVsPUISp1PYAQr+IkOK/1kBPVNI0W1+gq8MGerKpSZX44K3lyOCu4NFwLz/agZfQ6bAOiH"
    "YQ0cnw0N0Lwz5EBuP9FX/nhory3bKTXV/cTrFxL0fofbbKXneskeIJ1aU93F/icvtxwAXGwhG2zkzAiMN1zhk2HzxX0/VEfzxfDy"
    "nfv6/3s79+yKO/fst7RzRm3cqwH84Hvv6rP/N3fVGnZoEgLZJHQ2UjZZMoDdRaZMNDNfuSjZl9amAwMWxz7aa/AsyfSMlhyWZrDR"
    "0K0AJmci8VoMu5KMHshPpdQ7EKgRYd6XGjcvXFbPkXoyakSFAP4INH0yfpZPMgyMV8fFFAjPjTw89nvvkHtFCyK6HnFG6GMPcIt7"
    "CrWyot6EkiAQt5UqZjgJX2Rk39FNtK0pGonrjCpeYo0L0dUoJP8NzFzDXRSU1J0Yu+uF/A2smx7jS5nm5Lc2TjQG64h/uvE+zOGo"
    "Kxt9l95dNNhSDtZKGF4gM1v4KonQusiWrHGptdY0A6SR1AeIMfL0AIkXZrFqJ9wICfh5Ht7cxljXGo41ID4mGKx6dIJ5vUplQ8vt"
    "IxbU8QpqHsPS6shxaIRnw8gl4xeTIpa2X/rT3lJZ0ALMZvgLzaQCbkK1Wwl8vtSBNRuXpJBlke4repqEO2xr4UgvCcvMS1BAEb6M"
    "gSHo7ZUBCxdeuE2OBcZQDgslxO1RsP3UD8Z0WjBQWyaTCtUIDbmqLJagftbMjiwIHLOqIvyIQWV59NeseoKADv5Ng+On3yk4PsyO"
    "QcJkYiGhmaawSX30nr5O0hSAeQwIVUXydUMmLqzoSQGebvDV8707Dx+8vXK7n6ovm7fbAcfzY7rWAHq8TNcSFQ/Ve3nd74UnAiN/"
    "+RC9u8YS+1bV4xT/kdI7oO1tV+fS4kf50jOc6qr6LCeNZ9lWo2Ob+P7CIWH3wHfcjwtYJ1n2sMhHtGKCjYXrPRVOTBDqLGiX7eOi"
    "1nmjxts85TpgmT+uDoJY7aZNJ3zZGHE0Xbu84mzmZTq3m7jkG3c9mmp4vvj0GKvNLKzoSaCvRrbw3KZ6NxR3R25apUQan9onNon7"
    "yaBheNaVRcmJuM+y8hq3mvoWZs8jp4pyJTx7D/ygsEnfdUoAHYi1VFkAEjQs+tE/Izb62hEm4AGyPDu6BiMHQv7aj1YSGPx4HB3F"
    "Kz/6Z/hELxTRprjoWIwlBZoJ+VkqBslRPK45mH6bVHIHVr+XOmryE+z1pPmbakg+srbu5Hb+cPPGeRqvxSQMyHTeUjnD8vJsWuVc"
    "CXO/Mdm/XsfRh2fRiYOBVVmAoUKttbFBlSVSFasdvJ3SUXpDGOfH8EJFOVFKCi1xlpYWxr3akB5siE8xmd5TSiPxDO3ahJr1XJTM"
    "CPeSUZj0M0QONIAF2ngWmKlwPcS0N7yyCjFTqvNVQEngsBqnoUc915oYC8DV10k18m/i3I17JLRz78alXZlMLC5M8q4b84jrkqIA"
    "Gt07KN8n40M/uJ6tRYOBh08qYHEucW7/QxcL60PSZ01cmFd7dHxzjT3yoNWaY7wgtmH5pOpnfQJX7l7Uf+96WV84r2i434zU/VVj"
    "7xYUkJbMo5ShH5lxYcjglHNe5gthv0AS+H0ESBq1qqmcO/J0/SmXEEquKlN564RjvBSR8Y4yT3WCp0tPFBUt3UV/Mmy6Yp2tC4oq"
    "C6Tm1mQ4YyEzVBJN4wLcGO2uP+HZM61kioLw95hz4NbWxrZhDWGeqCzGle+5VQL7SWd9RxhDt85Gp31jXT8vh6tb6zvtLaHDJHTo"
    "hFajfPXk684NjFUt72qH1pYYkS9IxQ0lvrQhJOU2vFfhwT/WwoPvUqxu1GKz0AtPY25QJlMYmP77KJnQFnl+AJuf6TwHlURBE2cd"
    "ZaZOlK0bAgrIKiP4G9N5AnTD/C+IsStDdBFgkUuWnsW9SkyFagwGvaDr7a0NvUHL4e+n4rFkTCkF/XWAFMvLH1D/qT+BtRJq8qSo"
    "VJPnsXCdOXE7e6UjLp3owc2k2NKXEWBNIBAdyQe7ayXBiaiwBqJlc9Wecp7qbOERwGhSidgfKjqvkPOMMURUqfINSKEyObIgH0Kx"
    "cTAwVCZDwDMPKb3v0u1ZZ9USSyZCTOprI6XEddrSMQHUHARpwtThDUrger0czglKhSg0u+xbX1ezQ0aqY7cmxujXaJD0yUEzO6Rh"
    "dcOW3A2LGwZfUC/VEcIbuijQjZPzpIBFZ6tCsRtMjg664yaWjjR/MDOTkEN9KmpTf5CzsTNToAp77Q5HepPqAGLJ5c4nhCzoKKB7"
    "3vtkMIgBZ1PCsExnHfGr0kkKiPBUqdX6iFhe5HkqSS9rg6JtBL/23pTiCZCsT+JZWBr/lCWvXLaJVXxrb2U5/zXTzwwTsujlyli0"
    "mdA2IS4ZZvzpYTZ4Sjkjl3en+5utRdE4u6B0uyqUH6MJyQ6f8bVo9ELzA3QMdtvRUEiBtFRiYVo9RlE75lsSKHsM8Jj8lTx2lEy0"
    "QBndzf3c6qxbOLrevnmjs7XOrbL4YVZ37yWmbnW5YEPOIROckahGoYayhhqKf0LUUCxGDWUzahhWUQPNTk91qd09xjQM2h1dZpLR"
    "c8uYDEkrJ2WSc7FLhlMI9O7lnm4epg4NalsqFwflIWtNRGHFpbabK4FHpCJx5FrsIAYEtGtCjQEXamgiqzdAYcYAFmvQtI3odIRz"
    "GygyeAhNLxRYGLZp2CgvyK8iXeiOWP1PCZUaxQz52pXqA6GLoUSK2Qy9pgaIxicwUUBpMFlhY6hMa94nuWLmp8jiI4WR4072q/WE"
    "an4Kf/qzmc2BOJu9ynpe01JJ6Q4ejiEelFqTvvCi8FU2m6UTqhVB51PRx93peZ9auMWCmfzTgplLaroTyC8Vx+RXFcfkl4ljWHOf"
    "EptkVbEJGrF/749F5Q6GNTewsO8LfTHRjHusYmWYyxkO4M5Hv9koUBKvrCFcIKGimdWBBVzjTEcpzXio1V4U5JhFiqjKyI59AJe5"
    "Qo9MGYTpuxBG70efQxjtjNjrI4Tpw5T7jRCmLyFMX0GY00sgTNcbahBz+v1BjP+fFsKMFAjgEKavIIyoQRfRCF26MtpPFRKx5o8X"
    "QpjTZghzihDmuAHCDDiEGRCEOYYBz2Zw6Hre8BOLJ5f7KstWr7kQztT3sAZojBoMxyquMMSrwBun0QVQp6k1dmfZV1c4mvzTThvp"
    "6QWAomnxMDRHhQtaXp46hbTHKGf/DuP7zTuhmVwBdh43wc5jBjv76HP8/6MlkYBcUcovcocqZob/uRvJQlH6SizpRFChwAuUew2I"
    "6FwzY0BRv+3TdUYrQEUgJ+jJxJHHx5F1g9H+5+bulgslxkuO9z65Qyn5EDMHZby/IfLzno7vEjrCJ2n+aShz+VJGYkNdWqCo90jW"
    "qdqUSg0Mm3G7gVd66dioWxG0wXhKB9uTScQrpbUCStOqziiq4NXP5WX1ucaauPoyqJIbP5vt9UmTzBIzCornkZcyLmZ9a1sw+Z6Z"
    "I07qfu5mRJVMrE2KKqVHJi9qmxksPGUJS78T422n8PBTYo3Y4n7kn0TDGRaULRKI3RwF0lHIedbGkCtLncBLl9el0EZEPQ85NcYm"
    "dtZvaqluU+QWLUtC8TgJWr/2YjxFHd/EazTpcXIvkzGvKjZdLPZyyFNqWsf9nhHG9GIeS6mnRSI7gf5l5SG2SOoVAy/ngiE880Md"
    "ai5BGYMSCSZawALre4ElgZYLCf1xkM/FklfALJmSG21zrFymjQY8XEiW+0ESXk9R9Ce0HWuMMe/JDkYVJFaUx6R6iYnCFJvLnehf"
    "lW2Fc1jWr/f9HIXz36JDWS4Tg6R1Lb/dBwyYx/bBBLTUW/lWOh7hVCKSqpBXJsbkYGua6wVNjeyUAvGx/B/9hQtsN0obFC95Oa23"
    "DW2Vyk2TTRfu4hfu4vdFxjImquNQoDQ1RaoHoN/kHV70hxSgMXUelzub2zvt9jagncga5cCnCEjRlOE5ymRztoc2mx/bz4L/1Ptp"
    "dhHwNkpR+dmLm/YXYzDoq0tbHTBgkztCsksAT85c5cZzkVROSy6co+xEfP/9sulwFXMjtdJ7HYfm2IpCyq3VZp8mWB4377YvmOSV"
    "AjIotyG/eQWdWIMUk43ttPWz9vj+H8SHTKq17bOgAmw/GkNdFUxu6Dr4Zni5F84ww0i3dBv03c/qWbKZ1dLDulO7dRF9jrGZRR33"
    "k+aRLrmLOlg6kdjmrmycH1McqEvOTPBQM+C7lMkyoNOex6SKWzdgt79NPOOGsL6Oujg1H9R7IKJvwiGWqjGT4lpDdWkdEJNqEFNc"
    "uvjseMFU9Aaoi5vCoKoXlx+15FP3Vp/W5eX6juT+YjCdN4LpRKbDZdoHteBmBVXsZvSF5GEFKVSmCt6iciujcQ57pOpjVF/7kkot"
    "1gZHYyNwLkIAaKFNnX3T9+VWoiJNuZjwfZxTZFWAyhw+SCLkGZDskRrRaWx89E1EzHx5NVfhLjeDNFxXcStl4MttKNnhJdubKiTm"
    "+o78AWdO/tjqrKtXwBWod+1NVWuzfVNV2+nc1PUwson8ubF+Y1vVlEpqWYHUVaqp7fXOpqq9tb65vrOjO6M0r7o/kvOrLknQpD7Z"
    "2djZ2W7rb7Zv3Lix3lEfbWxsbW1ubqivtm902lAVV2LDWQoY1c6N9k2YJKzR9s7mxtbm1nYlxmcatudpmCKgHE/GlARC5SHI/V4b"
    "g3JLX2v8Q0dZ0q5kSmyewlTGb0/JTbUg22F0hNFQ/XXk+dVr3alcaxNahse+7HnuHa5e8HDi2EmgvZc083yJQwszfesRmTBCXMjU"
    "587p9gXmDZep6PtZDS98jA/exisrh+G9TJjfd9jve6W4h0xNMhB38G9+GhfDND8T90ppyUyAtWCw1DK+cNKcYAzvJzamjpOTwg05"
    "7yRCsfkoMCOLiY3pxEB4mdRVSLX4GGGzuhNN8u8C0DyLisEYvQqJ1TRug+YRKhcycHOb3AEDoE6jJA1K+vMMQWw6Bzi8xppTYFK1"
    "oMLjr9WbJKoYG8Uk5mvYXliqH9hwyJn3R59W8rLYqALxAraDgFFbMFhivyTjdWY1DRxPEQIBP1t3sIyNHsjzxBgOKw7QOSM2sVNj"
    "J3wsM9pp5pKWl+lgoD+bVV2Z2K9+00s3jGvshnGVDpn1MK7EeZlw4DKtT2Mg17gayJUXmAaY+VBcDeJqDiqZd+sgrsthB8dBvGDh"
    "UHR+E9Uh56twQyoRQwuGTWerRWteGsJYZl/oljZLS8iMhNiVp2i/LOp1KIMNGwYEzcotfZiaDjSQUqAntZ+I0iE7fQH3MRNo3I9x"
    "YnwGulvv9NUwwyen28ZOuql7jACJf2o+1iwp1bm8LGslzC+MlB1it/FcDrWtuJTKaMv8KC7fx0Ur0DOSVv74j8L8FbTTtI3WYKUi"
    "NVKa3AuHsudsPzPyUu4FtQLDUzGjzYxHImcZRdxsSG4GKJ8CnSjRgEAjDG5O4VfTsnCHCH0X1ZWr5dHckJx1NfayAzIw5B+y/LED"
    "zSzbgTEYNL1pLy0767E9jCE7jk1tspbcg7two74wAUXUZcxYQoSN4CVGQxMoVHOolGCI5Q4NF6B5v4zovbxMan/+ejO4H1lvhXqi"
    "PLetdqARABngvtVCwbSqq1MWtl97zwGduYm4/GqBvjeqj42AaNWqaMoQrppErtta9iSUs7hlueM3MS7mnLHT1jMSv6CplTg0J1ww"
    "Iya1k4HkA+rfORO7KSdWPeZEpXPMRrS6nqZBvV0+EQq/WlsiJjVKqyRAKlE8S6SgwpZJ6FkZOuyRCj3O76AksjVFvhFUTMeA19CD"
    "nbsGdMoX8dVQvMvFk6F4Pey+Goauv5sNn60xeumAYm2JuoUx3FXGQMDt0QleNPI58lgmLxbbBysvUTbIsgINSheFl3SN6yi8tBhY"
    "IvCyEYGXVQTOC9R2dqXhKeHvsoq/9RsOTebz7rucG4TPu0/clXNdiWrmg3gmuLcVaUncsP/aBBZnomBNqRB/kp1MyhYwNl8kkiUp"
    "5C/M1YDB4BneGscpqsyhrnReTYVyh5BIi0LtyjdF7U21LYQpETxia1mue6Zfbs8aBRoPlDy7lyaYSaVBdVvotzWvlDzrU/kpEL3j"
    "XLpTkmKqq7PwwbYP0Ac4JXvEAu3Md88wqP1JXJTnHlrepI2FB4ND5f8HHw5CypJ5nsbKFyEKsQI1n2PzkR9VW8lR8lZSnLALtLs/"
    "yA/DVkuZbuFZbg2i7Cgu8sk4Pd+Ly8cZQO5H+8+eKvuolia89fN4cnKCkfiJf8vKB4OEXKhfR0Ums3c6tR4RiIWVqryPJmX+MO9P"
    "xriC34zrc+8lMGbcKhIUJZQOVYr2pDxGJbqmVS10hKgCV0NmiemtwW/RuNJolBFheOglddMitcTVNcaWJGRRq7vUsLyzWR+abCpv"
    "WHa7VX2/37RVEVREQwn4U983LFU7h2/MCqF+Qq5MiRr6sC+hF01l0e72MDp2r7/29u37cpSquySiMOpFlbK+dghGkXmfgoC529H3"
    "/YD6Mkelp21hllhWV1amsrnS+N22Wq2VPrT2WzlozefKM/OhMefZXr/I0xTqf+O1xvI3ii8SqdTu60VuOIeYR6usLYg6PUJBRoxY"
    "XrHjHPiueQRA6ddNUBkxWFGpypJKjk1YgqXrvoK8seHAFQhW6phAOqIkKcszIY2ADZbMGhKKe0pgkjFWy1AvhiIIXJqUg+I+LGd0"
    "Mo4HraCsjqCosn9l0wiKKrNXmEgTyOTSIBqGJH874wpcVQNT196LG+O1McGBKVPEvWEdBCaNKKTFQebrqRk9GWMIS53baTxLGQEn"
    "itkiLZV8NXTLUisySJkOjm48dv8bdc16XNSR8SHi32FUOC47xpjNLH/k6DL5jyYazpSJsmVTjKRX/d0KVHI1nVaJ/t5QMlotWQ6c"
    "3Eubmsy8F1PzhhDt6BecvzlPPV9UaxpK1bUVwbxJ4q33bYz/voB/35FotWIXIXMgK9ud6stabUVOO0p6feC0cv7bAt2tLUwIFmr0"
    "15LxfcPkLC8veUzT41ctcUSfRXV4mHt9WAMlfEXx8DvlSVhdnK3gKe6b8sOrZImScaqkYWUtHgEuokK8T7hji9Am+WS//0mrfOuF"
    "UaiMRnXzc5e739622VvsdKS0rZLRitYaPQ/5xuspGd8vl2pWx7k4OMoOUdN0kBaHYQIsoBWZEM+mieRBEqX5USsA9NOPsn4M6Aeo"
    "VHxKc3iNxCQDqMmwiEZxi063tjOVDzHg1AE1gz6p1e9Ok0Gcq5rRZJDkUpqVAuRKb90d6xRD6cqK/413d3yQHlYakE7J1D45FtcG"
    "NjpSzSej6EiPEEDGB/cbsWCAgxgB9pgql/nRUVqfuuQmnvcx0Ae1k2TACSS1pjQvUay9PSuQw1MRRS/OovEzoPeTkzQOlpaStZF6"
    "mF/SmGUm7jV2LCn+xNfSTI0CiMpLkIZM6oSeJt8ToOi6eSPtFIWGduoVazgKRQgp6jVZW0T6QIWl9vLys8JzvhMRaWXCA9uXiIC8"
    "Zv0pumx5udohkGW/tT6xLei2TpwR/auJs3wxcYZr3shnvihQmb5H24RGb83bKGvd6XvNh0ZerBPi7oJGNjFZwAgWDiNYhNWUVQWL"
    "cO7QdMqKPTUZBGHuN3tpAPwourTeV1kDhXRsK8uT4LPPzs7O1s421vLi6LPOzZs3P5siyS5TAkzRcdm/Qu1eScxOv0hOSmAIYjRu"
    "pyj7Kj+hB7DptIUAOdF8Q9i6JevfvvXDz9SvlsqPPspPYylJUQm/6cE3J6wAfMQOdb27UlwkmFE4Gc9JUVh77ws5YrlVMNkcI9KY"
    "a9zLzU84jUTufYvq0Zx+hPIZkFlQa/r5HsWxFbEC2jEB7UK8kohpqUN2ixy1xJh/VuvAwyJXoWMWw/SYw3S6FMX3g+v1b78HbI/9"
    "bqWROnxvGOSVYHzMYHy9jSY439CTgfUks0mN3IgD39i5wPrOVuel7nV8OTIoGDJIF0qaFvfuoAk1Zi1xavzKav0LiUJS9FmR+COR"
    "4gaUP1SBZGLCYUcHySGpiBXD2TuHiwc8aZB8d77f8MRHsg3VSJ2hZ/eX0mfaeUsfslYLgPjHsRwI+8hgFnonufzkSlx+8gkuP7mC"
    "OCnxe2aGyWVcf2Cq5RFFY+ujkeVidBMTukGzz6XOYnQTE7ppPq2FVHUsGU5zHJd3Sljid5My9lr0knBmWXqqru83n28L+9hpJm26"
    "jMqRqBjOH1HD5NbB4QeF9sv/io+oXtutxxDtInHq5QJTd21h2iWuC1/oOn62y1vQbM3+O0myJbwi91JdrIeIXgfzeVW4kmnOo4Kj"
    "m92BFzCW24EMFFlnc15LbFIRsyO9aaL62jgtRm52RYaGeC2X/xLN3IzSj7kMTWVICg+SjR5SJepISDfpOPzS8nM+Fz1ZBSNRguZL"
    "YO28mHM/FbVjZUmuRGZe0vg8aaCwrqHuzCWx4Ki6JJavyIJ9OF+4NBQ1Sq0F34di0eZL9eNbL45J5VC1j/+E7X3NtL+upKTtu768"
    "/Jrz09pqcclxIvDzoSd1vPbw3tzZ2m6Ty4HRcCUhnQtGnBYLuo15JvalWtbWzo48hrVcddAfixVQ9cpoaAjDXSdy2eXW0STc2dEO"
    "N8QOYLZcXbk7OFvZzCUiDkFu7XJeFbtYsinsZYGrbzcjQcM4nQ8hI1t0vZK0pN7CzbUOFxIOSW2iGjwaOjJ7VC4RYhriHh1kjGgE"
    "Pzb8AK37yPKZ8R2NPAeT4/hak6+mRnItLe6xwRPGhbdYy18TC3Xaurk7kVdR9zfUvnFlYZxUg8sL1nTQXC0/+1oqz2tONnnIrNuE"
    "Nsj3SYf+YuwRZjTg+QQXs+2Gj7DtXWZQlodk8yNyx5bEMS7QvQHcyJ1ADw7X6DKUfEcz1/MBpdKlaFKHJxgEmMz2lKm3ki1v02JY"
    "eyXjnVB3h1HBXrRzgTYTrAygEktH12qwVU/qEUsS1/RH92DDkyojcj60nAu39ShzZSCkx6oqNQ3X9SupjT+vYMmas0X1NDqzcjc1"
    "ka7ouRKOUho0O93q7G10bdRjXMg8EDrWjuS1lV+bZr3l47yiOpG3omZoMlu3znPc+k/ac5rjF8Wef3swdhx04eAigWVPrwaGyoDa"
    "ZixYKnzCIXARcp9lciWZbbW5shLspFx0B0rnDshRtH1tkqo/YoapNjYQuofa4w5P1+tgQ+KN9R/g1Feb7GBpPXB01lvtu61P1zG/"
    "7ZGwQimpKgaGOSUflFa3woahMvXzwNTUtrm5oVKdrcRsiLLANfbVy2bUfc2mv5HMI+f47ZTcJldai/boZAXSjArGXkM5dVugJ9I6"
    "vdmrRHwKk1bVpYhDfYxYbFwOn8TLzj6pIbnqt+1aG35QRUPrBl2ysi1eNq/aFG4r3RYze4ynUoW7UAO2WEmFiEbq6WJFoOgxh/Hy"
    "KpbcmJHJmszSU9FkNeuuam0iRRkTbrtK62b6T6PFRPFlTqOLyN2sFjmwlu4EM8EjkTg3sbe+x/IAbaG9Imms9o1LHF2VzLnM6o1O"
    "+sLzZNhUdp7IBu4RRSC/I0O3TXmI1r24rIVohbIAg1zuK9WEPndflTxOFunbiH9cstSP9nl3goZgdNlSJZiU4WQL/yJVJvraMsVN"
    "JGkDqecmLiu10tgCzXE0cSI4llNj5zDKwxGAgfANZjw8xgDWVKxkA1CZYFSLki3IuV2MsSRAsQqvIgCo8cIH2WAuGaI4uCiBT0Sv"
    "EYcxZGELv0ris9nsLMkG+ZlJBYlREnRrWJc/yyQ/BTJWBYrl7sngQsCoXqBOOMr67/OCnO+lFlUX7Q6H6ONFfnIo3JAhYvWTfEtp"
    "FC1bCwBb/1Rp7Upmk3EtnsuACWjps9oRffxnAE9D+P8I6LmpMgoh+XG3a80qT7sj5P5nM+WDNDLdwPMG+afnK8BFYa1kNisW1OpD"
    "LWCpR5wN30AJ/Uo4sgy9Elj7wjuFYqZKMCTsNBzBeE+7eph4NtAmQzk6UOxVjD5RLi+vrKDyXLpCA92BpQmWYixExBZ9LKWOuAeS"
    "vglSSjEKp/DhaA1DQGYkGJhD7/MyRAuh1c5s1qe/ijqTRy6iM9af68xBEifgEqoKbarQdirQhKZ5eEE7HA9QPYEBofVJeonHB/N2"
    "j1KEAHCvu/uWrgdIGe4La6DuVRBbp624Hmuy7zPf9H1UamgzEtbuBbRqUmBjtBwnc6ThqDCaR4OtecVao7MVONbl0MKxE8XyeXhc"
    "IbP3WIlEGSeO+GoSniwKUuI5gZ4o8BMCtt5zFvHpuS/2/O5JNStBY5iayZwNfoOs2Y/ChWxx94if807viKtGw1YrcN7fXF4+Whso"
    "eKP0UljEFWu1ChU5mhJAKpyleeuKdLYiPNzAdB0SFt8jWJwZh2Zxz5dmEZYgjJkHkz45ujYeIOnCsm8KNUI+DkcTQZBdHFuk8GRc"
    "tQxitL1k2TX32yvWqvm7i0qmVQSNeIm7gxwhgkcpTZZlJhrtY5fqdNNd80vFn6Ukpjpq7a4MEJX46JFJjap4y9IgmtmOvU0Nesrc"
    "8buhnauDz5zBw/UPM2fwZW3wiGakeLJbmrEXgEh10k81RELjfIh3c27eppB9tX8eA6ZBorsVYLo49yRBybwpQ3UPEwQFLNE0G8uX"
    "C1KjZpf4EH2JpnW+9a0nXqDKrMeVOALa3l8F3bbggievwSbiaxmKGoV5SAv2cJ6zh5cj9vBwdEiDckUSLNiHHmZVihE3iUXiRhd+"
    "N/SFnme1w6rshKUVHrK0ibF1gdA/N+zPTfvVlOKYxw4RcFW3w89tmeuBxVwPSVB2FffDbqy8L7aQOZA/t+3Pzo4ehDJrq5rLsdn5"
    "2iUDvSAX+l7OyWHftGdD+dpFZ2f5cV6NXA+d6Zj1sMqFdDJxT1/P0UHs9EpGVawllPJNohwCK0HZUOZVmvDQ+cO2QnmOnW9KtF7O"
    "SFbCHV5iX4qHlJ92nhNuIvSl81TNZpnW1pnguV7GFXjWVaaQbjJebAOHGB0RbrlZLneLDZ3R+J5Fv/6eq920pu4qXHkG+5+YQeN7"
    "IrmP1WWNMoe3eWj8HqVraVkT1n6lfaIctx7LyfE8zqeZsbI/xT26l49GSfkweRcXr7JRNaymTNXdXM97jSFIdGJsraJ10MGdeDb7"
    "qqQs9FrvKfflGO2Fo6yrp2zmKI5R6gwrkMIvFqEoQ9Oj41hOkKWVcs54zK8JJ4lKP6gW+MFxpYh5drlOdTvBdx/Ku8TjoxE0Ak7o"
    "LS9jFToGqPz3A3jERheNAnh/vWq4RuUiepJOT7tpQXlrVYJ70xDeCNzuxNKmfpGGAWkoS6pYEsvHzDicwFLkFOkMNEmVkFTxiLQc"
    "JtdGgnA5Wd70iarClA65L5qpKjOzbpVHkONW5w01G/XMcUUlGGbDiacjX+gkWVWdtwq2WFY9RxvbNfKLiGhmnFa0YALrnaC5fB0g"
    "kc7EcSfGZG93YgzM2iz9tNsOdQu/1qamykw5w1RHE051VWjsjJH0VVKiWycOy5B5hzjUCKakm5ICNi8eRLA2xqXFuBgO3GQqhQ+k"
    "LCZdKchfipKuoMpdpldJKdchn0eauQHeDQ3oiK+sg0m7W9wqtf1bsbKih1EeFIeGpU1C1HXB/oV5VxE9kWV+FfCLHOAHFy/igckJ"
    "qnPTE2AO3TpNN9n9YvM7fDGPoKaippCDXmgZgnJRwBGJjM/tYiFpRsYiFHT7Fg70ORnrW2cQoi/lyR/Qycc07wPYI2l674gb1ne2"
    "NmkzMqOFtO5GbzAWfOw4F9l9fjN0BZRWKYl4n6izJiblUtCXZrLD98idiAIAEkkigQXdELEh230BDN2GMPmynivxpCFPnwO/JT/b"
    "4p9dUn3uALPqMLY66zYzwfIygTjtylvh7hsmcenXxi18Y70pWyBO4+MYNhD9QS8ZPskuNynuBqetUu012Zx8BK4U01E5r4IE7ppM"
    "wiX6dXhUh0JCH0wC4BSRSJqGkWZPYt1WEaHlK5Zk0ciYr70fUE5PUeReBIhHueTRU6LcMQFK5Lf6GkrkK6FarSE5XIoR/lnpHHaH"
    "rq1lKkZ+MLzU1vKI17LGlLToUJxH8HcoRnh/NJhxTQyvJ14twIcxfRsNai+1kZwM2p+6Jq9rzOK1e8m7kLtGqHjkiYrIcGptCFPB"
    "64lTsiHEMNy8mJwG6maFDd8nNavCoKmSsfU+OAxaLezTn6fSxeaKV3B7ATCgk/dJU7t1zBPm3IN62h08pKkVZ195ZBuNI+P3u7zE"
    "wYvuRoxGJZXAuos7d2hQp+NKSA13UDYKqPZORC0pOcKmzbRLytBaMn5E+vcwEUvJbJY2+Fuyssb2gFZ4FJEa2ldLRAROhbiCxRyG"
    "C9fOKJUdEmwgSbCh0DO+g+66NaBNWuELchdvHqHgZ8lOGT1/l4akv5bmisRVAv0xNF6bQ0t64MtRuB8OuTBeAYppuC9Ow6nah+mV"
    "kCDgrE0xhcoN2KUTAO7g76Swf8rwhdUKHn+a1L4owimwUbo9uhMZcCvHivquWpweK+q7qh0+vpz6lqcao+5W7tJWdT61szFttsa7"
    "OJ94I99G8JifGqOJU00ETcV+eOoHVHM+DIeGgJHk41AegVEYa92UlrzR09CYUQ7DkQQW4YhnsOjRRSJMYxLgol24tmd3ZK3OG/TY"
    "GZ+k0XlLtDJYNPiTwOoVZZSVLT8AGCtfh/KtH3iR03UfniqWuDSKPDSG8bWwBaZLv9fX7UsRdyS/Np2eDtj40K7+ErA41zKZkYnW"
    "4qwdLhsbOYO2g14LcKM7jct60h3JnmCz19dRc6l+b8xmo8Zw21BOonms68aFGbniRdRUjhriwnCFpQrtNmqUsY6qMlZWwBqApxHA"
    "4KGi2LFTLW+tvqrKXnVN+siEjnGDDzXgpTrQ7VR0Tc5HjI+jZ8OPSnoeGYjldUmUxwEL6BMbGOKYVH4+NCmpCq2aAM6Ih8ipM0Oa"
    "ziocdk6r3VkiVkM5Y8BJRSSLwgTH3djQcW9IWN4lyR+mLOg6+FyhVql0LxbzdqoVkoASmXq5yq5jVXb96pHu+/PYDnOeLWNIS5s8"
    "GQqh4AYzQhpPtQgREdHXqDGwL78ecgGlXGvX2J7jJrmO+wLBlzzwFNtWXmC8VoVO65UuwOuPKPvuUm7i2zDWrx9G1hRxwfd34m4U"
    "PioUmX+HkNajIswFYndMP7M0UDg3ZQPPYcx9YxiaswHnzfGNjydeSs5CCjMYbjkHzND3A3ov73RipcNA8XyNwdXRHt5Ij2Ek4hEG"
    "7EVKY36K50DlrnW56Z0bmHuRh6hXXabQZeIH8ku7c/R8UVXlyyu3zxX32LCVqFhhAN7DarUr6fdRMgxM9JaoUhhax+uQFLp9gCdL"
    "QHvpgFlkxF3PC+UpY2ydiblRu19lN62uv/LG7xYN6VPgstdlgFewDvDnOiCAw9BaAhTTCSWue7kyIsjrmu+cW8CVOnaig2nMbkh8"
    "wyGasftmi+3sRUOFeSlTM5W+S0jJm1jZNisFNBuI1kw6Ed+CoAjKhvH7uXr1rZsXUvNkIuM1xCBYGxd9yjcMf0N6qjKADt/Dl2U9"
    "qIUSzBqxv7wwg6oxzMBRqg/DQTWiL1AwTpUREI/W6JGMrJQtZIG0ZRUJa4sOjW2rxoXaDvXTFh94SfXOkRDpLub0UEhlWrUDmSoB"
    "nzRG2GcmZXMV48OEsmTh8er2IWXdPsRCrPNPQqyG7jXc0uCUy4G/+xCOLx0CQsQrQUCbf9TwPgAQN4VZ4L5a4BLR9adhZF3D0ZQn"
    "z+anZ/02wtDKKDBxxnxuM1mbj/mZ0JWTypC3DAD7xIc59VIpzBjZcskOR+4OmywmF1HDDkcNO0zLOg2fReX7tX6cpOJ+Wk0ffh84"
    "ExxbXIiXUXNu8Syrlt/FL+7l2TA5El+FbXGqBJbaOOMMA2U/wX/eAHAsvbYvTvBpIINfiQcYPuqLFP55GME/r5WRx776/BEWDsZh"
    "57O2OFMmJU/J9O9ZLp+uq9JXZBj8uXp6hy1+iU4t36p64xRtPQuMCWBNcmPPGId8tbzdQ4FKMEZd3GqnN07hJ8lYmL166ZiTKMHJ"
    "V8sAPs7INap3Fi+vnsXBqxFLS2Jz/6bKWQ1+vBtgDstCRoR/I5RjFfyWdrVr8amMeBHb/OCd7eAlxpYgFIJ54IMOS2bO4qbBCdlq"
    "3/pyrIR3zjoYKLiz5fvdaUFxugtfeEsezMOXvl2nsa9c7k5RgilfwY8v0hlGIyNaA+iV19jnGY7lYSw9/Uup/v1KztNNfwLbiKu5"
    "stVui6+RkcYsnmxxH8auzqOvUmMQEHj13uY7K8L3aHMmhwcrHrR9bQbR9q28634fA2a47WiRly57USR5kZTnoU3Am4XF8mrRUIes"
    "yi4kfOU94J3t+NrQpt17NPI+TJxUAHCohrUy8WzkscCkuMbbvlwV8loy0cQ1yN1F1aDxiyjDYeTq0Mvw/qCSfaIMT9LmLAxl+HRQ"
    "ZbKgMnKPJ14pvhm6g503LFlWXduSIZJvhsYq0N48gVOseC6s31A5P2tbjnsB9A0KC3k5OWFzw6pPHolKHOxieQNuWgHNxtOTpNA5"
    "JmaZn4W7KZ1jue5wEpRB+lfdr2bhumJ43w6B6PJOcSBAQ9C9z/B8a/jEz/mZdDTwu4P8GuKFfKoJNqs9/4hLFfnKEgCjCdxD34j7"
    "qbEfTAC0Ikg1xpRhO/BOOYTNQgAJc6XLbitjTODgSGnVz0lovaRgD8blCV/KsLC+Pr5yV8pwUMgxA5ym212ou02yZlFqKmTbV2+N"
    "ayjJxOV4Gcu6RKuNbGc69Sh6m1ljoQeYqAEmZoCJHmBiB3jlERq16DDJkvH7ePA6Lz6EeOl1gfSVLPB4OvRLUHWqQQipAvFNsct9"
    "gHZZhXuBqethYBa1jXZ7fWNzfdNX1vVZ+CjCk7BKPmOd9i0VgICOa1t668v21Bq6mU+Ely4XvoxBjNgKLSKBBtBntlZ/2cTQXyuT"
    "UZxPykdRNkhjQCHetHRMD+RkDI86XzDDzcoM0W1vfbNN82NBnVGMRSgLHeQwpcVqp9u+VXS1vGOjszpBM4huEnZu3crR3gB1i/lt"
    "mc8gR4la+PvJXGb+wfTI6HCImcS8znr7dtGDf4PNHfwF/wadNv3EP0HnpqwAf4KNeAN+wr/B5gaV4h+osd3+QTH1is/wl4/twk5g"
    "WOerrlLxiVXaajggzdzHxvpNFF5ps3B2dCvQFMBcrwKGA9e49WXOEebrsQ1NqS/iZdEQPQWbWDJJNNvbVanqEdis0wHex3mh7aTB"
    "rA9zaY/McDdZWO8bN134FQf7MQWERWPD9NyDZrhgDeBBbIVqmVEVGHcKTG9kxTIV4UDJI7SiLVRewKkrHWPFT1vAkJyOeU500SpL"
    "6nmV8GdpmHkJXDuTL3Cpo4wCzeNcc4DaWdW1AcFpWA2mbzkygGulgZ5MlC2lZlmjJDyrSsIzLglXQ2p3LTcwz6qibsMncLuTuf7U"
    "7s9rFlc+g6v5MBL45wsywHazMxElwMASVJNWzIRfKXwJQQUACFlXb6kECGTLBgABVuKgPEQ6ATspGCHxgThSmPsi2gFphK48Qwqo"
    "qqxjPOGYvWXMqEsd9a5OXSPxD5Kw61qsTpipq7y5kDQEwuyljGrl69j2i5FnVkeeJSHPJkRjLq+Dt5qQahWTZYIBH1GZq13JVxEH"
    "F0TSdCSLrHpGlhVaBiB0fvEVXHhFxTcT7myLXhBX9LmFD59nmhhGHkDStWybVNfqameMU4LD8MbIXfkLSeq8wdzBxiTds6N9g9jc"
    "qY+jz4RDVDOvG6CvLoApfWN8NcVb7w3PTqVg40VlNxT34C5/25CvDjLRYGqVopdUEA0c9P0RRSk0VJ0vLaAHTdoereOxftLSSJD7"
    "SWPSKHS/JTCkwh+gWHiMNqxyX9BxuqKfafKDdhHb08gNFIl+VZW0KZ2NgByGK+k66mXt4E7kFRU34YpmWovycJO4MgvtuwGooGQh"
    "piQxZu+kUg/o4CeYNc0RLzyMwi/SkIQMgJK0dOG4dKOQwBZmt44NlsgAS9BVPS4PskMytk1Q7J3G0Wk8YF5XTrk1F02VlTCgl1I7"
    "sFBcIEfyiXbDZEss/yDRI3/kc/NVWMyPSyfPDcO5HxWLpWyR8ejou0MMRGwZiBfA96dchVW1KzH524wSq1j7SMjWSYqihyVXXFtD"
    "zx+gRAY36A4u9DQOh0AvKPbk1RjlMhEgYvEyclyjTcYqN9UHLRBsYoc2UQuSNFkbMItVk/AjguveDzPJnJwB9NM0DSVGFNaqkwXk"
    "UyEmbRmZ3NbFiYOwL4ZhJFBQrfwtlrwhE2ugGrstleGdjvq7pfSyU/jIysenPfiQm/ZNHSP0YUXQXrHPgPcycMZU/vWDSmu0psOm"
    "kFBzacMWTbycsN2pPYhOttP+xDsVOWZVR9R1aoIv5RMvEQNBkfBPYaUHXe0JWyHLjkPXkxUtovfisvucDJv7lcBM4XOp6DtWb40K"
    "20RMkUj8wvb/2oAnqNa3GT7Xt31myXCd9KNyh2gke3bue2buS94eD3CFe7nnEMOwHHt2OZ5H3mTs9YFTtyOYA+8aqlJBTt6bMhTV"
    "uo+iTEUMw6+D5DB4PZb5EUj/maMLgQLniRM4zqRupVEhPbSa6Vg+OvfiSXgXbZr7SL1kuDgnvmtL3QmisE9VJ6G0EBVHYeIK1Ze8"
    "xA0npm7CBEni+3GRnKpD9LDIR7TS/HbMZkfVa3XkiNrvIZlciXx43VKuS9czMnw/8tG14iqTvhc+xklHZtL3nI3Q+mAlRzHAdn4d"
    "7SSUuOUMnbnPhGSvuGGhh/Kr0NodG0MVCXeMbIb5vQ49ebji0IpqNBV334G9hi16kQYMgONhvvBkBLPZTMYCUH9J2gq/Nn2UqJs1"
    "8x6Uyzp76hZKVbwvUlYwmwHZeUoiWRZ3Iq2RfetKZvYpSVZVepVUpVepkl6lXHql8Q+SkGwdCkbquPTvOtpz6JVzxFonbLWwc6mZ"
    "GliHsy+GsHFssnm9EqzS7nsYd63uF8wTNzvhXrfA9z9Br7iKn6rrjSr0We5dx4YCRFRVFMdSQHC3365B2RX1aczYM2OAAyhM6cDj"
    "qXT/4Qo+Bb+x2g081/oIzlnGPz92EWJcjfxVdSaWfCmcv22Df7UiyeQFC6+PyOsHVooNqDICxmQyh29sU1fC32Gsjo+p0uVx/bbY"
    "phGnw5wg32CYYU75S0PLZt4hmhodiWEd3KpYz8S2dHeQfQwk1zXiZ+SoP7fDvoRPRQaBMxNd7ZDgcBNdx/6jksDxKswIUVU2EV1F"
    "9X0DR3JllYgktUoFhksWXA6H8+Q9SWiFURNBW/z2YsDK0pWGrLe3Nwls6XNLBbPZq2I2817JwGcn3gmQMVYxohdBBx6a+4g/TQud"
    "rZs32yqhREX0gm9mswQuT4XLrB8Pma4MmM83ijGNJKTcrBOtU+nZ+Ab2CS37Xoy8ae5TPJKlUS6meTjKzZKqD0sxnqKm6O57AosR"
    "HLK8MohEXiz2DS7xKxQhG81mjGpNitRpIJGK9KfuynXtrfTsvePy6cgEOLuJzkR59jLuY4ZoDDtNBwVT+nTLW5nmh0rgh+CWHZTA"
    "C3lKQCYuDK4HGqH/ISAL9/4HMUiO4nEJj/LHnO7EUw3ype42Dp/lRoEba8j/LkVak0liaMvrk13u9PDIfZv3vhyvrASeVm8CDKaf"
    "yOxXRB/YEplMukEf4nB34L1LyQfLOSDlp8QQ27djVMfGuC2qRQmPVFxZGS3288xVSDeAho2O7xslE24JHbp9e4OrdhhJuE8up8a8"
    "cN8ITE1SDdctMHKYXWme1O72b0V6f/taKjoIo4O+TKe3D0R+pedhuK8FEMNLrT+ejL0dMcTYIdrCxwxW2/f4xoR3CJMdNYfdwQ41"
    "F6WRyCn8VvIRaO7LoTf0BZr3DupWOVMzb20ED8zLfjg11hGnc2kXccyjfnYbA/KYCTw3r4552mOF0PfC58ZM47kbj+N5uKeQnGli"
    "DmNISHyc1MEkcF26Xq6Hn8Dwcx2mq7paFHh43wQ1XW9v7vgNDEbjdt0EFicxnnySw0i4wcmJmfaJGYw1ODkxdPi+JcPnkvuwB1ke"
    "qwkfc652+EjbnpLhX9NiaGbDP+KWpkd8MXK3bUqDuK9lAXI9mAFTdOmavE1hTSJjZHxG1jqR0NY24oykv+iIl7sHT0UYu4eOrHb5"
    "7pnlu6eHH9nlu8eWz3i1Yvuo9SVoVg1s8CLHCKcmaAFGrmiObNBQEUMbxCa0AeJcTe8UTJ5aVpGk0REwm5OziSbGMuSCSykhuCtN"
    "pinr7xeZ/p2FUn9pOS6yPekYIXnGbUFURLzSSUa/4VOHiH4ZwMiWXA2JrntxhtacsfEPN5SrrtKxQZeajM1UNMOr8cKNBmpX5IAL"
    "ZIBjuYAUIPIxeQbLRfsi079juYCZs4CwtELid3Qz0DOdZ022ff1pNX4I6mzuRf33VvwnY59jgB+KYBleSedcSh4VScCzeLn0JW8t"
    "GdtNzdjKl45+HJ6Xt9rt26TqfRT1lO4keBiRlZE6Fcz66kRyspkid6znWha+K8S74tYtIPKXvHdcDw/13hUm2KwfZLDvWv8TozV1"
    "eDezGk9+NCnUwEMVPsaOYjLlrhuuiA4Jp8xJHonbUJzjOkEHJ9QWs9macta83eTR3dkI9G4xz+Nqx1xKW4Yp67QiknfauVxP3YHV"
    "mjefCz0RWoSTbnZSyd3pZLGnoMcuJ0257TgvPZt9a1mWZ5i8yGa181SY5+XSrwX4V4DrGYUDNRnfu/hsoxh1NjrtG+vKqUBWvW6t"
    "tjuAF7ZubMME8dadpRQ8aBBPfWuyrdNzu6kZeSb3bqm15tXcjpK0S8bQ9gs7xW6MBSV6kt6NpHY/EwXc81SYfNKPUdTpRtufwfHW"
    "uUW4CDutSuJ0+nIX+KRr16/LCtamUEHDjmjKJVAR11LRS8wJgQ56wKsdp2gHECQUjLXyvfJ4ZS6t+ln1rAqkp9wLipibqu6K8GPq"
    "pJtAB1rX/wC1nvcwRl1BIB5A1YvcLiSMLVFBn2h6bdzxZHn5A3XzNNY1U/mp0t3DT2M5V7i+FSzZ1aKtxgxOa2+BGS9FEaYe/D6J"
    "zjEJFEU0Rv+MAmUVNJ6TKSrw4hAjg1DyJ0OIZOGDnB+IsibYBZJ5cmkNrDK5vMomVBmwKjgOFYjdZ7UrDmQb7W2o22r5JspwpiPu"
    "sASh1ExaX5yqr0rRSwOaP/BfD2TcqEKefzfy8/dtcziptbkRwDYCTHk59FhqhypLtoMykmqS1oZcC3CtdfdiMFTZQVM6klJSoJKg"
    "Vz+Uhom5+TZxvdiJjr9QL4NC8JcBXLQ+IuwA6GX8K9QY9wgjj+O7+SQbREUSj6HGwnfCEnZYjz3N3Su/9g6WTd7npHbDE8HTqV6k"
    "SMFYhcwGyhrwcp3ofSiNd6BS8eiIY2nt480rfIzE3+s4fJstTsvBQ+eKL1E+ex3Blkp5gonCEebLUJoECRRLV3ZLTMYsw2VrQdPq"
    "xgw9CZ18AhpJUXoWNDZNkTp57AYmggE/jfU0/LkBN5VLZKKHD53Tubx8lkszmUXXIAmNYWgFz0rYmmtnRMAJ4iin29GTwpfAOmfR"
    "i8RJzL2x7otv1cFWM8jZMmlnIhNx3B2wE/5c2+Fob8pKVPH7kefkF6pmV6ndRpsPQm1ZNOY7GbAFd4fb+Y3hyqQOV0z2FtVtpb3q"
    "GHYurW73qjb29e/7YVsBPj1nY3zRdJqyWhwbLfP72nuOVgpvFRlD7uZ+tQCTLzDSDw3o1Oe5NH1NzEDxwpgHIO4YEdh4jezFT4y9"
    "nT3B1iMUbbpc2ZUUitlApK5czMrTrIQscvKImMhQksvsm4zWZJlLkzJMZT98kXmrQKktr8JG9OnFunLITaoac+swNwgHa+P3URFL"
    "7Tr6zmnbEe303+tLC5F+4KlfQ2loMlTlvjAfhf353ChQ0TyCZ7Zx4lzpOr54nps1FMTMR+alVvuFsmOrBzITb/t5aIIRKUdUCWN0"
    "QqDqFzsqM5DpM1+U3QCFpLmdTBSyvCUiYvEL3cnkcha5lWWpbFpcftogZrPSBajZzSuJjMgNJK8IG5MwtzlDrOeqEVbZKSbqo9wU"
    "zuFjjSJS9xYvwBUmT0OqgVgVQtpmLKtRZp602vF4lrCOWAwsNxuAJcFBtzNfFasqcArrMLJj8Nv+UAEvql2DldWMWN8XTms6XTM4"
    "inGJGeNCvKBen90hkW7wpeIriDmocBWxHaDZg0cuUls3UPqZfnFJKhSW5kFJN9THLwYV6ceQ6R/L98mYpgXjwZ8f4nPMdYU/tdCZ"
    "HhQ5gz/VQZR1DGMlG8LFo198NSWJhKXED6N+TbYzZK/c8MyyzAn4TCUu3UhFTgojXodFepbllG5QzY1rralkqBTYqmMnILZdAaka"
    "pWfNy9ODG2abKetju9T64sVnfAdYPO+IuwSiUK3Iy5wO7JK3FM9mS2h4L10mtWyQfX4yVebNinOPHTmuapb66HUCys+nk2lKFVNs"
    "eHqiifqR/qbT6aqMhRNbtqnhyDrTjZULQg1q4UNp0qCVIa4MRThFk284dSp6FNw25+zE/AnelbJQhSBgSaR5FFO2HWjjbJ9Kivhc"
    "PWqVRs1JqNo2lJVz4ZvKRkAk079tCq7h1vGopNKx1BnfVMoxVdPEAStrpiIuDVVxxagLDp0LEVei6LtB1GlGPKZ6U260rCk3Wubm"
    "RhM2dVZs/dfVdY/lXwqmOJRR80XJBPSpvgsCY/Api9Z1yduaqE3uaaZjTEnLOzbkNKupMr4CHbGl9TpaIqrkI9+ajEDPS6+0OC4l"
    "Ez0Jf6MoyMMdkc7CHS78/DqxjAqc4s460gZQax3l2/zsfp0ItcvA4SqByTeVjzfkx9VPv2n49GPl05vNn35s+HQw0J9eTzE/tpyk"
    "Fte6a2dkgXElOIYFEGoN+wNYn04l9uoEC2+6ZX1cyE4lrOuECjfdwkcZFm6LwlWEVbDeRhtBlORTdYrk2BUn4QrleoFc5B5bKVpm"
    "FiqzB/J5WYPZtOA3MMouyetMklJmVHY9bf5qfd1+xkcxGPB2GCS70CHugqXO3PGMSrRMnLe/Dc1LumLBwB5VP6O12dQ5IODQW55f"
    "lwQHhwoqZzbNXukIUi8cxjqoxmFSMPaeblBmgRydyBUgTx74xi2Y8114P7VggZEpijJwOtO0i2PTJIkKrZZSRIy2iGEEhx4hw/Q1"
    "Bwv5seOgzFtQDJwZGD4wuqFmDSXLrY9jeJxgNANZ6jo64avVjn4Hc86O0phTIa7NlqRzJpT3HQgFXso9lO3iOAWuMs6Z41NO7Ohx"
    "4MY5g0/g1JbJMImLFwDkk6mmtuqGQaGmyeRY9/JJ0Y8fREdxYfJU34/KqJqDI+Koggyq++w2IGVljg2+kg6/qNTrkGXTErleATgn"
    "7R0mb4absKGuj7lD1leaJ0mNazlKF0lWSyVYlUeAyUepYLGYleaK+ovEcYgcVZStG7ei4ogSF42V2c3ysik52Di0ehFeGjDTywsN"
    "x4NnpYBLHhQc7bdaK4UwgAA4fOeeZ9VLzF31xyeKBF0yvlXjktKVVFQuXSlEeofuXtJk2CQiqdkZtn3t7RUzS/fMsXTPapmjUNJS"
    "UXeguN7kfkSxEP+mEpTqmdrpZ3EBd+Qec4SyIiSmGq/anFbn0JE+frFrL1AqmrMrR1YaLWQ5pFgamUVndo2Lk0vvAFyRUjOY9r0w"
    "ixLCHina1RrUALol9XwaxiVaFyYodyIGNjHgK8x6dD7EFxn0kEi6Q3sUSgSRCtJ2p8aRvnAOcpxYDKnD6+gBJHIAOQ4g9S2/AKOV"
    "ogQjJNOyWg10g6wGh1GFl2GgdvxSqc7sbY3nKLiweks69IWbGtpMulCmJ6nMtcAU+xQlJYX1hdt6XU4792EGLFdUqm5DzFZ6SSFZ"
    "xyLXEFj16GPWEbsSgqyS17JWgV3L5xMTQaPOL3wiZyiLGyntALrsN4UERkfXW1kPNoJ1+ZXyEFVdC+rY8GFAuqsXzBx7yix0ERLS"
    "ETnReTmLGGOv1uxleqw8sKYDPlIn4zwFkovuYMzFI2+Izyb08zZR953snuJ5llimWyu+30T1Mt6ThE315nSAiwYx5Gb7JhpPy/tg"
    "sA+M0el/omIBOwPQhcysWdqfNg/AxuJtmK8xV0a+0E2396LkEWVgpCqIARssXK6D3exQomi2vFlyteWdZGPC/W/HgCwHkzQ2mN9Z"
    "3oS5O+wPyMzm4l2a9z/Eg11FVpaA6GK42OJEkVhwFLs26ClaID/JDK7MlEkwlB2Uh2v6G7JN7kK98Uma9DENSZtU2NJC6NsBhYS0"
    "s/yaCWukdCbmGTrJ/Jg936w8dzrs6JfJb9gWWTCxkh3dgooTH7auEXZbpbOzepLDvqzq9b/W4jZJexPYb5btxKHCMbAIFzEVdSfH"
    "JCy6RfV0DsK7KTnNEWD1BipEWh4CMpN2BW15spY6+L9WS+xNmBt7Q1KtMBcxnb7cQNZx4V2S6ChAA3s0gMwpZxoFnsfkPITau76b"
    "5Ei6XyyeZLRwkn2/G7mT7IdEtbZxYpbQvPpE+2qi/e820crtFX0pbPRFn5FrCd9c7aLRMAhyOTa+xmxt0qa1SWFxK2vTVwdArQ1G"
    "r6NR5YI8vpQq5YickoSkIPSq0IfzuwMHKDSYt0nrNic/oYyJ+ukIJhrL7Y69zGF4/K5CcN4JqpXLWUcZSEoHCB0TwAlroGKRuT7t"
    "7oZIOp6MBTsyuFQl+yaZEw7Iokd0cIFg3wijdhAGvY9qAFLTlRsaUsrGNzbXOzdurO/4TVkqdSdkFKproopB9mS+hR4fDz7dIwW0"
    "A3CpbCDd6JFyxrrHUqgc1YpKgB72B2HdUefNvPts4BgE6rG/4dEm3qBExwnhADxJN8lrpoSadXATg6CXr8oxhsn/MOOJFgmzVCjZ"
    "EvN8AFzW5WkCu37ppA3s6hR0HydxcS6TV+fFHTj5stMD7CRsrXyxt/t8Tcoqk+G5B5xX5q/888MD6lx1ffjPcVwYVsCJKqADORxk"
    "h/oExWhaCT1TNHT6oc/Tm5TiJQFfVqVEbiJ3dUKZomARCjpr80UpUmI365YJLovLJvXymY4P8RFlaEtLpc03kmGCEdiXs0H4Kuo+"
    "H4QvSpkQZRpeTMZIvqcJJuPNYGdfIIJCC6UHKCMZBwenhXhVijepOB6IDwPxKjqci/vj8AK2fEDm6HfPH+Vj4N7g7mf9ODgvxbsJ"
    "Sm8QRAYYS7IYI7Pa6uysbax1WkLScXHxAoj86Ch+DvsRtCSOHOSj1lycw7BYE/fHa/bJNAel6mdjg/fHaw3FpqqMdclrqeiXKCkp"
    "kkH8KM8/7FnLxlrxfTKjfRGV7xdUeBnjQatX4CY9vGhRg/Sy2tg4lmS3FJMVplBLNtxyRePJ8M6yrF8NFvoyHgaLI4niXvNNvntO"
    "O+9Q/YYNvoP0GrPtQR6PZx4Vi07OfRKpNb2azabT2iDGD3McdhGP37sTbS4EpGrWSdVwlgnIWDVxOTdphhQDbd5PoNJX7jFeRfuJ"
    "1WFnY2NnuNPeaa+ut9c325vr2605w9Fv3758cOfe/tv7D77a3919uvf286e7d+88fftod/fJ27e3WhOFuJ8U4eVVCYA8KRB1JmOk"
    "HAfLy/A4npwgCzamEZO/yOs0xGoZ6hG88yk6nUCB9hOZf43Slr0H914+2H/7+Pn+g5fP70BX93ffPt/df/tq78Hb3Zdv3+y+evv6"
    "8dOnb+8+ePvw8csH98PTaRc+lEmbX2AajrQRM6xfKh1bb5SOrSvpGM7va7TrrXqVt9vWq1yJ45Rd5twOingcd0iqwbjW4M2bJlQl"
    "QLkiBEIwDdMTY6S9ZEURlk0CPNEvn8mAbiTJhI/bKOKoil15yki0eai+x2/qIln+FYpm6jUogiJRsx2Xmi3xkeRFklbNvgOtikLb"
    "N7jotJR4v+7vPiOJa5XkWOTKzPOFmpBOhq+tSh4VVy6nquNtKRVSg617z0a5RakxjGKX9GOoHBnDyNaOAVd5LdHyhQ1CsIMeNJau"
    "R2hEdpgL4ZGI5ezTyfj93nnWDxuAGsXGomqKbm1ylVgCXvLy8zu2vDxKCUunydoZ1s02neLN9pavw+iaQLalbmogZfoYDZXSVuFB"
    "T/Cg53jQeexbr7zskKd0yMtLDzmyLfVDXn7ikGPYnwWHnPhStUwdUSrJJ7FtJFZsOuYY2pHScWME4FuFJtZiINbKsDiID9Fuau0t"
    "gHgFxvHKw9zfjmmh8FJ+ShuihZ+fqndQihRg2qfqySAyZA/NbFOyRF/GmrDr+x6zjj5mSnplzFfulE03fYkEIrXT5l/OKfc8l8vS"
    "I1DDgEFwnriR15ZVrVQL+WXMnrfUUaNXp/QdkSQqx8UY6Vn+Vi7bnrQdAcCT2w7cpVQBtnG6ZfNiWrCHEp2q30oFilm3A2cbZFcI"
    "oOUeKIo1/CQRYYVdyYl0el+6Gk1xG2gK48h4edU1WMf+h/v3HizVkgtf8UMvOdEheZrEvnMcu0gHqP9EKiX8WqKG42loC0V+Iu5N"
    "wuNpNz8J700YQodiDhsxmM+4vPZNpGOr771+e3d3d382uyjzD3GGeRQ/wJugdYYjagn0eoDCufgYhUQThLeBTVsi0A8dv07K917r"
    "7duW3wOiWEQn4cfI+yZao8YoT9KrRBVhs4QsX718uhdHRf/9i6iIRmMvzft0o9fGVOqjn6nXwuotfzZTA/HFcRG+Qh1oC3ONRcCO"
    "whbJAqAv4xOJ7F4lZuQfpqpjnAIN5XV4XDgNALmqimwTokjC173Wizv37+/ee3Lt8zv7D1rBUWxL9uDvUyizBfd2X+23xNkUv/v7"
    "n/2rX/73fy2/+OW//Iu//7v/BmrCObh/bff50zetbjQG7HjNHMxvJZ0ld6UMLWLvXUgdbCvLVymka2seXIzi8n0Oe/Nidw86fB9H"
    "cE3HwUWLFEdZuYpEBHSHQWYTuaafHY9xTq2vV/der+7jprSC6GQu3uWD86DCvQPQxGDDZ1FSXhvGdB6RXwaOCjjwi7nKTiffF2vY"
    "sGd8p5GDJ2pggrd6s72BXm6xVHaELToNLXXLzXYXMeq1PElBybvfkmUtyesXa/kH9ZGtopqFg/Fof//FtdaK7teAjHQul/MB0CtZ"
    "H8Dzq5ePDcAWd4CIuX3BpC97tABe3OvBGQFarBhFafJt7LWeP7ynk+FW68K1FHkcXuBJpQ3E9vQm4gTTPdgzwFd4lh+X8chrjc+y"
    "s7XWSsx0gwobyn0AonIcm+hcRpEEHY15J07j42rjoralZoe47P9jI0XaainokIUHrbtwaJ7gP8/wn8/xn/27rUM6DRjZsAhVnrri"
    "dtgBgEs6NEUyrHa6fvEZFYtyZUVN2Ct7BcCFh8k0HnjFrU4brTj9QC0pkC0rLdhNVGmo/TvOcKvMksMKoeizKL110WrDEbFxcQsN"
    "OXHseFTuY+qm+AedeMMs9zE6R8FuPAJaYuxhb0FrRRc+S7IJIMJq8R4yrgMstjLnd/ElnWGuAlWiZ53BnPFZzYM8witFmKRQDgPu"
    "8XvPX+mstD6DpSCHe2yclsZfueIUWFy2iI+VEp6MoqnXFtgqHPUzz/8Mhr1qD2V2a7vdo4rDNMd4oNDJr//HP/3lv/ivYIi3Nrbb"
    "7tvPtttQ4Zc//hNVYWd7s1oDv4E6v/rLP/qHP/8JVXNe0xf4/i/+B3zJXPTJFCPmo2YfooO/My9VLLuDbeCFv4uFOFQ8tb+73TZb"
    "08v0EpbmIJZ2XYHekH3cmYQe7NxttZRw8edAY3tS7wDFeBHwYiRAOSe3gKsDkjk+kA2uDYt8dO99VNwDSOSVK4l/GOozDw9zs/Je"
    "pw03Bqj1DvLE+NRxntbt083NLfhpn7Y77NWNjmhTkIS5D7D1dUEn8ll0Yu/L45QfCwf+qfv9uiAkbKXgik7ToItwAbr0O+DyiYWX"
    "8G5u4BzazZ6kUT/2Pjv4+X/7v6/+/F//5Oc/+ferP//Jfzz87Aj25PadyUHBBBv0GBQ4+LUxtH17PcYMK8VaPwUKwZPlODwUeZdq"
    "j55PaaJAXKZr9/I0RQTvtY6jlrjIJqMYuLIAuMVxTMZMp6hjbSFh0AIKebfUpM3zKUWtAP7eo0USj8k7Yjbz7sDTrTvw0FvtBPhw"
    "mx4QhNmFjTMXncekiwVi5rOWdNyzj119ZjALT3pLnnJgxLWMXGj+C7YEpeWyySTcLb3yID0UBfzjS7WWWufELLgGw7oJtUJpgvAU"
    "x87Godj/az//g7+9xmHqXsbPyMHa2poKYArFh2tjIDo9T57+YpVscQ4OzZRkpHkTMwsDxuA8C4kw0pXOLabMPoDnQxQrwIRWAHHA"
    "bFE1gYwdeZH2MjgMAB/+9b/69V/9zwBj6OkXf/BTRBWpfYHrCy3ZNZDz+sUf/GGLK4enizfI4GWANid6cl5qtBarndks6wHmCVod"
    "AMbc8eHe1AaIVwiyW9o9jfWeZmZPSxlXGSO9o44J/hjBD/w+aOtS+NVTJbf0MxzATgDnAMvXxqTrx/go/IkxmmrwumvmRFMw2UwW"
    "nSZHeGXgjiUn7/KoGCwvKxYhGQMenBSxMk/qNdRdOyuSMt6PMSShH+BJeQFQLwGChi6pgZxFOMj7JLRULMoDadPkWT0N5mEkXUyI"
    "qRZl0uCTXIXeaQ2RemiZF/lJ1EeLVNgVYVpG2hYTLQAXK7XhFCBc6no8Tc8udRQ9az6Lp3Ef4wNF2cBr9fOT85aNDKSU68iI9YDq"
    "DQD2WJpV1gVWW92zl6EH1yVGTmltmKDJkHc3B54uysxtg+N6Zxp+9nteL/jh4KIjNuYHb3+4+sPx2uGK34PCQXT+w/EPDlbfrh32"
    "4IdHldbn/sz8glJAmXDyZ7/+D/+BVzEvem7ln/64XotqbNIT9vXL/+OvDyuVsBg+Pax/2/M/Syy4OHHAhYSdZXhnSquq8MiSm6tI"
    "nwhkPIMSDrbFEr9XXZTPkH9bA0Q1QudyDKqXqbNOH6pbZXBpedA5BP79YJ3+3TgEwjMLV7xqMezjwSa+HJA17ChYwWcxwL9bh3N4"
    "u32IEmj1/hzLtw8F1buh6u0cAgIpNMcxQT7Jhscp+aI8mBzEa8ngUCY3Xs7ImQQVnUdFPjkZY8kAeND3VEa/fOvpqOAVI4Y8VWk2"
    "6/hoYE25eGVTs9nBoU9QbBjeHqKg168eRHULgFLXMGuI2eBulcC33YIfFuWMTORqrCnLTq+hWYmucRyeMjB6MDzsHmvJ6IjCWR/r"
    "mzE1tMiIEDtWwL+3wo3O8jIimdEhmpUX596pgRnHIRyuU0vHLy9PCfsfo5BBeFOiVOgB8DSQkrAWUOd4DY8JIzx+OIbDtOb5//iz"
    "H//jz/7FP/7s7/7xZ//nwQ8Pf/HHfycASfzqr34Kx/zXf/jvf/W//PWvfvpv/+E/+69/+dP/Dk45Eih49OQJuxXuzH050KkEUkBv"
    "sxGfkgSfZL5DPeeEY0a1yLS+mPwTliiRuG6o6Vl0yJW93Q7Xewkc72C1IyK31AD6IKGd7CM8Q+OmW22M963ug1rAod5BOMl4KKbh"
    "7SnfsAj6OPTlkRjhAFH1/iDC3J+wCdPlZVj/KeY2X1lB85twdBs6Gf1g/TbFIvw2VhMdhIBMhoE+hIJOZ6BOqRikQSpO0yAX4zSI"
    "xHgQ9MXToDRXVt+OcCAGzPUjdvE13Sg46opmzTglQ9Lp0/Q2mrsUB/gTrnmrRZkHxinNPAJq5SA6NLcBniN9VNF1WhPAKFgf2JYG"
    "siWZjRo1BOMB7pu7yhEeU9wuvxuRbJ6EYNoA+uI0ziYxLAFAdlyDeBwkChng0OH5CZqxq31tC7jR7DXqrYPioDCUyCGzVJ2cXH2N"
    "iJyXi6SBC1sqdQJTmr00G6Slk7328DceR80/XUMaFL9j6U8mHOLFPUIL3HL/GvBcBE4x2hL+XTsHqkoz0ST6ewi13xCd7wNPvbmi"
    "6o1+0Gm39cMA4L/SMUJ7WXBT/yfoxDf1xUs0VQ+8TTsAKAkMH/6dzWiYq/BvBg+7UrpiwfZw7EyCzn8sMVg2my3JIZgcSAY2Vxj/"
    "a3rcxPBz5p4gPc1Cv5KTx+ySbFHUL12HLYu+cCdIz6Nhsl1CEbt1V1qrxMrGzgjcYtm7z1ZgP3VUJTabksbZdMbMMYDTgnBnCY7v"
    "oLfUDtSthQnQ6NVwv7ACZNKSesMxrH6m1GuPcnVg14ro7EeG1gBaKPAO2qtbhz8c+LNf/eUfeb2lf/jzn2C5LO5B+S9//Cc9v+f/"
    "SDyY8kaIfPl9YBV+8cc/+/mP//Tnf/CTn//Bnx2uQPGPxAuJil7GRw+mJx7vuXdrCZr80cqjfOXBFP71xf0r1PXFU6DnVAGMrAPj"
    "na3DCIHKMONfPKBFX8Bs4d/PxDtqPPi9GVBE40N/cfUQKwCeO5xd9z+zG3q/rPm1MBpMEWyS91eeixhRwNaAqyT9MAxWHoQrOSYD"
    "ccFnbyUK+rqor4r6FmIMboUoKhyilGnwg+32ylA6DclQ3y8MuegXYULkmkBqTRCxhkGmPCLQkDoTSIox19nwKf94Bb/F9q+tUAMp"
    "lmyYks1D9uH9S3u18S8Uer5G8TAtSEU2Dlp5p1rJfbjH1OnvblHGzYvaaFTQCxPTgWnUvVQvXnqLciamyk/7YhwUAvCHYTKKEi+/"
    "I/oiWZyUXKGUyxfPUqwT3w5dmZ6qKSVyrRWq3MN/SJIHLbT8IJa/7Qm6HjWJPVHeySSSOEdXGLniylGhZ2EFUoYTs/m+FOFBvi/m"
    "rCHxA/yZgvf0O4gP8pUO8sb4B0qkNZgkhoD3xkrjntcP014rxTB6MC3UE6KZCipEPXVwe+WtKFDVVzo7bb/XD1tpchq3AvgxyLOY"
    "mE2gnRLyJr0A1qMvEHnDBwI4TKBlgDcMdHNVaSXml/aiVYy/R7dqkpVJGthX1A7Gxjnpl4G9TLfl+I0EAVCf4LR/uUoVfMSJn0H7"
    "8kl1QlpfzZIcj+kMaKvgHnGr6FoOlNnow9tBkZ/0WvivLoAp9+TEZcFRXvZa8A8+AtkUj2+3UZULb4q4f9pDzdmp/jaBB6gt/+KK"
    "0/rtTg0BeiCrC2pQqPXV9eGK5ySiMsfseMzQzO6UQsQiykY1mZkIIB4KcFkbm/oJXalf2J3+SV36c3F3urhH6gZHqnqk4Tb3XusH"
    "mo4SufSK2MzC24De1Zr7Iu7j2yWzC9BQjlYDIuuHF9BWoFSJv/yXf/7L/+svfvU3P0abz/5poLSKUPCLP/yPLaHGEbR+8Uf/6y/+"
    "+M8As/z93/xPLYErH7R+9dN/p3SQYkAFv/7Lv/2//82//fX/9kd//7d/AmXQLVT62Z/9w7/5L6GbX/zRf/73f/Nf/OIP/xTe0PLo"
    "Ifz6r/66NRdJGh60fmdj591guAOb9jvRjZ13wwh/bWwONm7exF/Dd++G65v0a/PG+rttWXZzfaOPv9YHg813Q/y109npy1aGOzc6"
    "NzrU3ka8vbHVOhRfAhgGxJNG4/G1x1O5NcUEDZA95Zazx7yTH7LfwzwdxMWDguzRZM0HT8M8lhrlcZy2VII0evfVg+evHpi3RKC3"
    "SE8s2919+nT3dfh6NjuKe0udQNeDPtL8rCWWtM/waRKf2VbgARpJk3HZQlVPi8RjrZ76G8g32qk4PX9lvqSnFtoY27fPnbfP2VsU"
    "wNqJwQN0ilyCHv1HswLv7M/7d97w9QDyzFkPmPH9kE1z0BIXc71W93bth6f9PGXv0vxoF8AL2kfJ2DNAG8WFeRzlgyjlzul5NC6f"
    "jY/MsKhgL/6ovbNhwzNKf6Gi2ozfA2801jBEFr+8s/8AtTByk588eK0/fqf9wtTYoOnHA/0Sn76CoWmPeMDDg3MzUKqLtilRvzRf"
    "ACp4lWE9XSL3H0bk+Nv3P5hAOicnX2kDFTXBj5OkNL1o6xXdQWVi48m7cb9I3mEqmNueqkJSFHRCRJyoy0wMYr0P4yw6CbEK72ce"
    "j4BQUfdGla2s6L4NwoXOMspkKQHhudSlTC3+B67UCIufrk3GMVr5PZhKSx7UR8feuR28OKfR+OJ8jhj5/gTFCiYLE7IB4QYaCF2c"
    "2+OAH+mjACM8X5MjF6T02ZcRDbz7E6DHJ9p4BfCyfkFLc+4cLt3CHD005LxeoQnj7fO1vd5aAQdFmkrT5NeSASWOFe9jWkOA6lBt"
    "eRn+WUPgLP+uxRnZDfvibknV3sOy9NS7QTymFgnaE+TXtQMUAZmVTDzfKBLhU41tqCkUadPQVlozJM3wkSAT8tl+cC6BFos9U7rM"
    "PzbeXcC0qXA2u0MP2va1c2VpZA6FTeyrjExVYl2EY4D3lnTVYsWkkzXNpzQVzOZNnGxqBr68HFNsQzUvX+teV0j7xKyI7Cf0ynAe"
    "r2KGkpPe5MTD2C+hHTkOJ+Ak+UH7sPKa5dAds9XXNy+T62ap/BKpfDwmuLV0UmALfZWGbzkzS5Y5S+rTciYDX2qC1LpjUyWXzJKt"
    "DAplL/TSPUJvTVmGTHOXfJnxzqM3i5w5yhxjpXhLEp6e1TF+OFdAnkkrgA6SMgKcOrpvK7lV1eqjRAEWVJdCIhT9GCvubC0qfaPC"
    "IUK0wLAPnrdiZDeDE5Q27LfbAf2v5a/ad/i9885HvX+8JX3HbrftSijRQGJIspzEamb/8+XlfC2j3c1WCplRx1hUpyaVOEZs6qeT"
    "AQa0gxn14J+Ay6mGZFygFyuMexenQSyiMsBZzJXvCNnXKDSpq/oWqlhpyVQ2JumJ2HyoKIq46Ztn6hsiHtgnRD7QFwyrkh8XEQ7A"
    "EZ5b/NrU8OdjCRDOD+LDMNMNkwt7vfK3ahSK1rHj0ERO49hfoqM7gnWMGdi1J4+uf8bPfimZZbpAJH6YYHSGtdP0VtvXWQUNeOI6"
    "Zs+5MBqmwqlI5CVBYS480b1RRbTaNT2H1lXvUtRH3Ty3gD8n2sbtg0ElvM8rdLl1p/KDgwRF5naqiaMSyUP93UrSVR/kh3ARzW8g"
    "ceVRjwDXpMTZRGhokKQHKUnVfzfRgtdDkRIwMN+iJT7mX5wDcDUnh2gyNRmNxsu+FrkZBMGh6VKJAEJKHmgpM18jGxnK5Xmhv1d9"
    "xzSlDKW+vxN14L9A/0/JTGtpiY7RfTh2zMdcYaesZ16GnUASLtdMET91A5wDljce19RkolZkSwkzM42X9cZL1M5dtflx38WlcqkI"
    "meI6YWpe0mXcWlcAB7C6PryZq4g4OBRJ6CypQWCIG0njI9cy8Y2lx+1O5d0CdQB0wGJqKdMDaXYA91HNwixRQXQRrUZxSJnp+AIV"
    "h4KccJCGtIfJWSmmjZlWKBcuUIRjTnQ42ZWtugZmXS43clWJBCJiBSIuw5oX0iJUyTGq4CO1F47waDdT+NOQEfDpu/MS3TnaIofR"
    "IwdxkB5KpQ4CQVUQXrwLElEGNHxxquSTJgeqlkjJaeZrFKQiutVZ26oOCe5eAhXe+Z9F3XztNOzfbvfgL/7/B2tbK334J+gH0e3t"
    "XjuAMgFV/x/a3rRnciw7D/zuX9GdYzQywddFRnAvq13gTgaDaywMUhC6GQyuwX1nVBfQVWVoJC/wLkHuGfd4GXmVZMP2WDOWR/9F"
    "6dbySX9hyHiXfLOqGzIMTCYykkEy7nLuWZ5z7r3nfj+eP9vHsr/4WEktrXv3Md/flUY764yXIb13YeH5L76xzLh7jTkfV/DeZl5y"
    "yxi8b+GZ4dYd7fqP/tP3l9G9Xy63Zq/hl5bv8/93DbabDcXCCg+LIZi55O5F3Z88+VPQYr4eHa/HHAU/uKcK+0F8mR/cK3is50Ee"
    "l13o0+Klf+973z0sLsR8+YgT76ZuMc4fGeNXPvz05PrPAuS9/SDPz8UN5dvvLlmLFsHYfuR/1Mv+iY+8iu3sVWx/kVex0O6Tp/X5"
    "3/9rz+vzB7deZoXePSxuzBNXlOUi+IfHiFJZPony68wt8vgN9HnfH/y4veVlPGYqZp81M4BZdlg/U3I5qnLm6Pv72xkK+PlsrN74"
    "/UyNV9r91Uri+/yRu4zr01C8xA+f79z3JL17MJbzGL9YkiF9u/y5EUW2hLmWWqzx7bfLf/fzf/i4JPsvbNwsO9MTn7X3/7+7sN5y"
    "8e7zb60Tf3WW6nQPEtx57ilacB/3byuQJ+jxrCRmFquXTi8I+0m+3KaJwyU/Uv3ui3bh8XsTniIFn719ufz+/eHDwjyLH/ZkPJbe"
    "F/njQvcnF/SxQau5PYvfvwiQlxaN/4pFX03eWncENtvO3WxiFmfu3uKHp0n0d4/yNquDNg6mT55HY27hd2db0Zf3AbqjtGgBtA/Z"
    "/fPexFdZecePHYRHtZ0/q+38MY/fElLK/MVa1E+u8EKnuf6X50/c/PBy48lqIdCSjOallCgOlgQScxfa5q99Y53xaj2/+u1ezqIu"
    "jPd8qEuXFp7+Ro+eXnzZb/eyZiu655mcSffhjtvw8/WyDvquQT4EcADgwVn0zbuHWTRfWcf7YuI70Z7EWBgf51XvO1aaZQDvF8/T"
    "4E9fP/3lx4sZnt4p197jCk9D9bisb9Y/H0T/3p/Pv/sMtpdQ8b1Tz172B1L9lemjUNQvrVAf/tGPnnyFl5DivXcfglH+h6jBU8EP"
    "3312Fd4tv74rxQ/69T7C9V3yHm8+NeZ5PdKPfmT73xinh4/O/M7Kl0war/rxzFUvs+ffataskF5ies9xrW/HcT688uGorQ/xnDX2"
    "QemOd6Ur1MvKq0XXH4rvQw9O+3r28ngf0DfN8FeWVryOrrxq+Wdv/pc3z4tX3j2ET3Prn7i5++iD3Af5HilaVP+rge2/sf7iOL59"
    "Wl91P8R3mW96Tj+98PYiKwvfPE0ixP7lzbt7sDR9PjD1O7/47ekHs6q5v/9U8Dff/7BQWKhnJvze916x1f3OL8E+ej9s4REz3O8t"
    "SYuf/ZawvM+w/PKby2Jp3zxG1H/w+KUIgjTO/Te/8tq7Xlq3nBFULInvn85CuJf6/Q9V/9XxyRh+ft9b5j+Mn+YPrRt+2j40Sxxh"
    "yV53n9x8OBTL6cfFzzHFp/EBQaHXis3+SLHNYPzF+R8iv/YX0t0rTeO3T7fe3fPp3fXYJ02XZW49vbsf+N26cfryPvX2+da7Je/b"
    "BxZ4hb5eXm3vE0/LxOt3Zo5qP1nWsS6ewvKbN3/6L//5H/+Tv/vff/93/ujHv/1m0TxvX+JJL5j/G4rg3Usz3vzyG4B6EsEfpO7Z"
    "T+dafmVZDfToCvzwL/3wFTFOC7JYeP+vPsOLmeZPmcAeD6J/ifz86EdLjO5HP7K+Kaxz4x4ej+Z+5Qov4/O0buh5zfZULkcqL/Lw"
    "6JE/8eedXd/ODBR/Mt5Z6JlfHn4eM71w8ytumn/4yE/v7smJ3qiLMn3ayTabuu88csVc9usHs0tQZ3GzBLaXBQdh7c6K8/Lm4859"
    "mHT+4DzGi617nNpd0rjHL1tK0nssov6wwu8eZXoeMfiDjC1lvm7Ky0vAm//+X/+v91/+7s/+xa//8U/+05uHz+/77dIXfw55jCYU"
    "s4op5j7fmfOzmU9fviw7fu5L8pfZ+JkNlgdt3N457TsLpxUvZF8gwONewz/8p8vc36fLu8/c/e4DrwAfuoB89sO/NLPkDz+9z3bN"
    "crjoxvPjtsnan2FL7T9bnyVbx3e/m3/SLVGR2LtOD83M70tym6ebC3/cY8PP+xb8RxP46XehJTw3oyMvXaZH5r5+XnxS1necwD7m"
    "fpwx0ZOgB482++Hcvb3n7HxETM+rA79IXw/a5x8WSo4P7rcHYabNPZ3pD5q2KEv/8tmbX/7Zl//bH//OP5up8zImv/JE2rfxLyLk"
    "p89vFPdVpJ+9ef/jv/uz//K777/8zT/+yR++//LX3gCPD4A3P/vJP/mTn/zu+x//vQ+j9ThWT+M+K6rikc6PnPY/SeKnqw8UXo5U"
    "+WLJSfZMY28hzl9I4+I1mvrs7Wzni0c7Xzxbv3u1j0Xe8UYb3Q3RfLNoflCUywFFqffNX7379D547svgffH6eM/FAV0W3Duzdnzr"
    "3FfLvX1qF9Vd4uJpc8GPfvR0c/DP17h9/WhWCc7TgQlLq15yPc9Nc5aFvjPL+x82pH6oenrJ6Xuf9/lA0CctOLdnad3Dd52X/LUv"
    "GtFp7ytcnrIkLKYI+ARaL2utn1LTfgitect79z0NWuPFT/uP3j1cXm4L7iyIs4p5zMz1prlrRu+TYOEGP/emp10P6cPlk3B+ddFM"
    "9+yH1L3etyv/ryy7KeN3z8+Xrd/LjtbYTU03K/fF67c/Wa+Xl+fWrtb/Y794Lh8oloOaFidm2S5xWX78/CW/T3HF+V3MlrfucdL7"
    "nrb7l6J8ey9grhWdZdf/7G39FkegB+hhbs4Msd8iJDJfzv/geyqS+i1JEMvTFbY8XcErcr5G58dPfrvUvPbbF/S+jKPUfMuCvUSj"
    "5198gA53AZup+ggqFw74huPwve/9PL/hMTbw8mOpefewNORh+ng2eIk6POunuW7/wwaUu/B/3//szR/95t/5zh//xr//k//9x9+5"
    "e/IffJHFPrz5NFlmGx7ID2A2eZzAfR1ku09Bdfdf/aAtWjd9WU33dq7h7YxogTfvnlRVHb+KNSzt+3yh1dtvNGyp9VsRomv5JKCP"
    "0aGPDOydQ5tWf7GzH8TsLjkvwPwbZVZPA/Y8WJ9rb59WlLz/6t+8//ofv//6373/+g/ef/WHy+fX/+z++evvv/yX77/8vfc//vL9"
    "V//3+6//9fuv/sVy86v/8v7rf7m88OXv/tlX/+bPfucfvv/y377/8t+8/+rXl88v//r7r37t/Ze/+mc//sd/8tP/8/2X/+rPfvof"
    "50J+9r/+P7O2fv/l//v+y5+8/+ofvHnAPuwHXqII98b/ApDxve/9AoxxXwj0qFpnzfNIrYV4D9M94PQ/Vd4LZvkoNvSRUavj2fC/"
    "//pX71T5tceOPuOKN++//AcLYZ56/7f+9Lf/5myf3n/523fC/K33X/77P/1Xv/Oz3/3Hmnwn7m+9ebH5rb+sRnkxNx8pyC+WkNOz"
    "Zblz5TfsiP9B099R/zy6H5rwr/7Dz/7O773/8h/d67835HkY/vwPfu0+PLMl/cOf/erf/pN/+NM//4Nff/OAzGPzCtu/HHr+GAT8"
    "fDE1s+NwNzWf5l98HBC8v/Pu4SkW/vBzXeXnWTPoMXI4/1s8X/7FGX789uwF3ycVHucBp4+XFb3EGZcA42PY6bNP7rvyl/XbswH7"
    "+aGIl3Cr7+fzuH2jO+8+aSN/HuT8OdJ4p/cXj1pQLhbN9mFT9+sYolw8ez33tx78b8rgUH4j+vM8N/yxqbsfz/3sGOdPnvrdh31M"
    "VPkSNP7hvRePFPnsTru//Dm3BPTuQdsvvvdIwKd7j8Dgix8+5zdJX+wwt32KSXyo9VUYYplH/zCt8LTC6/U4pJ9kftO4of8yHM9i"
    "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"
    "aBsvEmeDpMo+1w+/i+ofzw=="
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
