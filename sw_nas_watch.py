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
VERSION = "1.16.10"
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
    "HUb4a2NzsHH7Nv4avn07XN+kX5u31t9uy7Lb6xt9/LU+GGy+HeKvnc5OX7Yy3LnVudWh9jbi7Y2t1pF4U4QRIJ40Go9vfD2VW1NM"
    "0ADZU245+8w7+RH7PczTQVw8LMgeTdZ8+CSMYqlRHsdpSyVIo3evHj57+dC8JQK9RXpi2e7ekyd7r8PXs9lJ3FvqBLoe9JHmH1pi"
    "SfsMnyfxB9sKPEAjaTIuW6jqaZF4rNVTfwP5RjsVpxcvzZf01EIbY/v2mfP2GXuLAlg7MXiATpFL0KP/1qzAW/vzwb03fD2APHPW"
    "A2b8IGTTHLTE5Vyv1e6e/fC8n6fsXZqf7AF4QfsoGXsGaKO4MI+n+SBKuXN6Ho3Lp+MTMywq2I+/1d7ZsOEZRibSUW3GI+CNxhqG"
    "yOIX9w4eohZGbvJXD1/rj99qvzA1Nmj68UC/xKdXMDTtEQ94eHBhBkp10TYl6pfmC0AFLzOsp0vk/sOIHH/7/nsTSOfs7JU2UFET"
    "/HaSlKYXbb2iO6hMbDx5O+4XyVtMBXPXU1VIioJOiIgTdZmJQaz3YZxFZyFW4f3M41MgVNS9UWUrK7pvg3Chs4wyWUpAeEGD+npq"
    "8X8SW7eG52uTcYxWfg+n0pIH9dGxd2EHLy5oNL64mCNGfjwJ27apPWQDwg00ELq8sMcBP9JHAUZ4sSZHLkjpcyAjGniPJ76A1pRk"
    "GvCyfkFLc+EcLt3CHD005Lxeownj3Yu1/d5aAQdFmkrT5NeSASWOFaOY1hCgOlRbXoZ/1hA4y79rcUZ2w0BblVRtBMvSU+8G8Zha"
    "JGhPkF/XDlAEZKSCiecbRSJ8qrENNYUibRraSmuGpBk+EmRCPtsPLiTQYrFnygrzD413FzBtKpzN3tCDtn3tXFkamUNhE/sqI1OV"
    "WBfhGOC9JV21WDHpZE3zKU0FgxwSJ5uagS8vxxTbUM3L17rXFdI+MSsi+wm9MpzH65ih5KQHLBjGfgntyHE4ASfJD9tHldcsGMGY"
    "rb6+eZlcN0vll0jl4zHBraWTAlvoqzR8y5lZssxZUp+WMxn4UhOk1h2bKrlklmxlUCh7qZfuJXpryjJkmrvky4x3Hr1Z5MxR5hgr"
    "xVuU8Ak5xg8XCsgzaQXQQVJGgFNH920lt6pafZQowILqUkiEoh/rDLMWlb5R4RAhWmDYB89bMbKbkzOUNhy02wH9r+Wv2nf4vfPO"
    "R71/vCV9x+627Uoo0UBiSLKcxGpm//Pl5Xwto93NVgqZUcdYVKcmlThGbOqnE7iRNKMe/BNwOdU5GRfoxQrj3uV5EIuoDHAWc0mq"
    "R2Rfo9CkrupbqGKTCU9lY5KeiM2HiqKIm755pb4h4oF9QuQDfcGwKvlxEeGA8fgtfm1q+IdjCRAuDuOjMNMNkwt7vfIbNQpF69hx"
    "aCKncezfoKM7gnWMGdi1J4+uf8bPfimZZbpAJH4YYHSGtfP0TtvXWQUNeOI6Zs+5MBqmwqlI5CVBYS480b1RRbTaNT2H1lV/pKiP"
    "unluAX9BtI3bB4NKeJ9X6HLrTuUHhwmKzO1UE0clkof6u5Wkqz7Ij+Aimt9A4sqjHgGuSYmzidDQIEoPU5Kq/3akBa9HIiVgYL5F"
    "S3zMvzgH4GpODtFkajIajSdG5GYQBIemSyUCCCl5oKXMfI1sZCiXe4X+XvUd05QylPr+VtSB/wL9f05mWktLdIwewLGzqO6mwk5Z"
    "z7wMO4EkXG6YIn7qBjgHLG86eI9Sk4lakS0lzMw0XtYbL1E7d93m876LS+VSETLFdcLUvKTLuLOuAA5gdX14M1cRcXgkktBZUoPA"
    "EDeSxkeuZeIbS4+7ncq7BeoA6IDdd2V6IM0O4D6qWZglKoguotUojigzHV+g4kiQEw7SkPYwOSvFYmJMK5QLFyjCMSc6nOzKVl0D"
    "sy6XG7mqRAIRsQIRV2FNaWiu5RhV8JHaC0d4tJsp/GnICPj07UWJ7hxtkcPokYM4TI+kUgeBoCoIL98GiSgDGr44V/JJkwNVS6Tk"
    "NPM1ClIR3emsbVWHBHcvgQpv/c+ibr52HvbvtnvwF///g7WtlT78E/SD6O52rx1AmYCqYQL/lrLtuQukcHS+e+4JaJQAM8yW0hTw"
    "zM8rZsZDTnNKC96PcJais+QzcuEBcouo3VjyTyHuLv3EIuAa7uAz/CUItg+IAo+CQEQAp4S4KHqj+Kk2oi/JeMkYBccUKuw4GcAL"
    "6kD2I76cohf6BXLpy8tLr5GFgJ+STiRUh8j5/6HtzXtfx7LDwP/9KbrfGI33wJciJe5ltwvcSVFcRYmiDKOboriK+05WF9BVFXjs"
    "OEFW27B7Jj1OMnbixHaCJBPPxBl/l7y0l7/8FYbSb62qbiQIMO/h6VEkdZdzz37OPfcrwviVDT89mv4LgXtvX+j5qTm9fPvtW9Wi"
    "G2FYX7E/6tv+ia9YFdZiVVg/y6q4we6jx/z87/7SU37+4Na3qNC79zcz5slqKm+E/70Hj9JUPpLy68otm/Fr2ud9f/DD9pbn9Vig"
    "mH3SLArMbYf1EyRvR1UuGH1/f7uoAn6+CKs3fr9A4xV3f5VJfI8fubd1fVyKZ//h0537nqRFltxyHj+7FUP6ZvvLIIrs5ua69fLz"
    "49tvtv/up//wISX7vzu4hXamRzxr7/9/+4Z6t4t3n34jT/zVWarT3Ulwx7lHb8F93b/JQB5VjycmsaBYfZv0TcN+pC+3aeLwVh+p"
    "fvdZe8Px+xAePQWfvH2+/O794fsb8tzssEfhcZt9kT8kuj+aoA8DWi3judn9NwLy0qLxX6Hoq+Dtz981sEV27hYRczPm7iN+/xhE"
    "f/dAbws7aONg+uhpNZYRfnuRFbvyvkB3LS25KbTvr/fP+xBfuvDDrxoID2w7f2Lb+UMdv5tLKfNv0qJ+NIVvcFr6f37+iM3vn288"
    "Si0EuhWjeW4lioNbAYllCm3zS1/LM16tl1e/OcvbNtHwXg/1NqUbTn9tRo8vPu+3e87Ziu51JhfQvdxxG365vuVB3znIiwMHAN6n"
    "4S3O+X4hzVfS8Z5MfAfaIxnfasDe4qr3HSvNbQHvF09h8MevH//yw8Wint4h1979Co9L9ZDWt/CfF9K/z+fTbz8p2zdX8X1ST1b2"
    "C6j+1vQVV9QvrlAf/sEPHm2FZ5fifXYvzij/xWvw2PD7bz+ZCu9uv74zxRf+el/h+k55DzcfB/OUj/SDH8j+19bp/VfO/L6Wz5U0"
    "Xs3jCaueo+ffGNbCkJ59ek9+rW/6cV5eeTlq68Wfs8ZemO5wZ7rH+pZ5deP1RnE7xLl5Hb1s7wv6phn+1m0Ur70rr0b+yZv/5c1T"
    "8sq79+pjbP0jN3cfbJD7It89RTfW/3r3wdfyL9pbzsUvPOTBLqLwFm96Kj99w+0brdzw5jGIEPuXN+/uztL06cDUb/3st6fvLazm"
    "/v5jw19//yVR+FgvSPid77xCq/udX4R99H766IPOcL93K1r8ZLeo5T3C8stvLjdJ++bBo/69hy9FEKRx7r/5ldfW9W10tzOCimVA"
    "xeNZCPdWv/vS9S8Mj8Lw0/veMv/9+HH+vnXDj9v3zc2PcKtedw9uvjeK2+nHxU8RxXX4HkGh14yt+QpjW5TxZ+N/iPzav4Hu3mkR"
    "v3289e5eT+/Oxz5quixz6+nd/cDv1o3T5/ept0+33t3qvr2gwCvt6/nV9h54ugVev7VgVPvRLY/1ZincfvPmr/7gn//FP/0H/+1P"
    "/+i//vD339w4z9tnf9Kzzv81RvDueRhvfvkNQD2S4PdS9+ynSy+/cssGejAFvv9z339dgmthbZ/ecP8XntSLBeaPlcAeDqJ/9vz8"
    "4Ac3H90PfmB/nViXwb1/OJr7lSl8W5/HvKGnnG2mvB2pfKOHB4v8ET/v6Pp2QaD4o/GOQk/48v6nIdMzNr/CpuWHD/j07l6c6I16"
    "Y6aPO9kWUfetB6xY2n79YDEJ6ixubo7tW8JBWLsL47y8+erkXoLOL8ZjfJN1D6HdWxn3+HlLSXr3RdQvGX53L9PTisEvNHZr8/VQ"
    "nl8C3vy3//x/ffj8j3/yL379L370H968//S+3y59tueQB29CsbCYYpnzHTk/WfD0+cttx889Jf8WjV/Q4Pagjds7pn3rhmnFM9hv"
    "KsDDXsM//71b7O/j27tP2P3uBVeAlykgn3z/5xaU/P7H92jXQoc33nh+2DZZ+4vaUvtP0udWrePb384/6m5ekdi7Tu+bBd9vxW0e"
    "b97w4+4bftq34D+IwI+/Dd3cc4t25KW38Mgy10+Lj8r6riewD7UfF53okdCDB5n93uze3mt2PmhMT9mBn6WvF+3Tl0TJ8b37zUVY"
    "YHMvZ/q9pi3K0r988uaXf/L5//YXf/TPFug8r8mvPIL2bfyzAPnx0xvFPYv0kzcffvgPfvKf/vjD57/9Fz/68w+f/9ob4OEB8OYn"
    "P/qnf/mjP/7ww3/4sloPa/W47gujKh7g/IBp/5Mgfrx6gfDtSJXPbjXJnmDs3YDz34Vx8Vqb+uTtIueLBzlfPEm/e7cPTd71jTa6"
    "C6LlZtF8ryhvBxR53td/9e7j++K5z4v32Sv2VN4M0FvC/c0Af+vfg15vH8dFdZe4eNxc8IMfPN4c/PM1bl8/uumUj+d13Eb1XOv5"
    "Vuj9FspbUN5/2ZD6ykH+XNP3Hvd5AegjF1zGcxvd+2/7zbtvqC/NPcPlsUrCTRQBH0HrW671Y2naF9ead3vvvqdBa7z4cf/Ru/fB"
    "823BXQhxYTEPlbneNHfO6H0U3LDBz73pcddD+j74KFxevXGme/VD6t7v25X/t267KeN3T89vW79vO1pjNzXdrLSK129/tF7fXl5G"
    "u1r/j/3iqX2guB3UdDNibtslgtuPn77k9xBXnN/J7PbW3U9639N2/1KUb+8NLL2iC+36n7yt3+II9B56vwxnUbHfIiSyXC7/4Hsp"
    "kvotSRC3pyvs9nQFr8jlGl0eP9rtSvPabr9p77d1VJpvSLBnb7TSvFId7gS2QPVBqbxhwNcMh+9856fZDQ++gecfK82797eBvJ++"
    "Gg2+eR2e+NPSt/+yAeVO/N/1P3nzX3/773/rL37r3/7l//7Db90t+Rdb5CYf3nxM3aIN78kXZZZ6COC+drLdQ1Dd/Vffa4vWTZ+z"
    "6d4uPbxdNFrgzbtHVhXHrw/RWcb36Q1Wb782sFuv3/AQceUjgT54h74iYO8Y2rT6s5x9IbM75Twr5l9rM35csKfF+lR7+5hR8uGL"
    "P/zw5e9++PLffPjyzz588ee3zy//2f3z1z98/gcfPv+TDz/8/MMX//eHL//Vhy/+xe3mF//pw5d/cHvh8z/+6y/+8K//6J98+Pxf"
    "f/j8Dz988eu3z8//9ocvfu3D57/61z/83b/88f/54fN/+dc//vdLIz/5X/+fhVt/+Pz//fD5jz588Y/fvMde9gPfvAj3wf8MJeM7"
    "3/kZOsY9EeiBtS6c5wFaN+C9Z+4Op/+p9p51lq/4hr4i1OJ4EfwfvvzVO1R+7WGiT3rFmw+f/+MbYB5n/3f/6vd/Y5FPHz7//Ttg"
    "/u6Hz//tX/3LP/rJH/+uJt+B+ztvnmV+69+yUZ7FzVcY5Gc3l9OTZLlj5dfkiP/C6e9a/7K6L0P4l//uJ3//Tz58/pv3/u8DeVqG"
    "v/mzX7svzyJJ//wnv/r3/vKf/Phv/uzX37xHlrV5debD86HnD07AT2+iZjEc7qLm4/yzrzoE7++8e//oC3//U03lp6gZ9OA5XP7d"
    "LF/+2Rh++PZkBd+DCg9xwOmraUXPfsabg/HB7fTJR/dd+bf87UWA/XRXxLO71ffzZd2+Np13H7WRn79d7MpHT+Md3p89cEGhuHG2"
    "lzBF+MqHKBRPVs/9rff+12lQL7/m/XmKDX9V1N2P534yjPNHS/1uwz4Uqnx2Gn//PosHiHxyh93Pf0rdHHp3p+1n33kA4OO9B8Xg"
    "s+8/1TdJn+Uwt330Sbz0+soNcYujv4QVHjO8Xq9D+lHmN40b+s/L8UTW/2ON3/1q/Hfrry/u7dz2GyChF6b2urTwjUe+ir/+lBjS"
    "TQX69FXwFvop73iPcaYnlLgpVC8oUfvpHSEeILaYmtrb9nm2qP8kGg/Faw+He/dwfLrc9F9JAC98ruJ2KN4tTx82OjxC6mnhnzyC"
    "7QMW37n0hy8Xwv1XH7781x++/OGHL/7RX//WwlD+/p1k/+Qvf/TP/+r3f0tn7qzkRsP3i793J+/feSDjVyx2afVFa3xs+ocfvvyt"
    "W9Nf/MmHLxcx8OXtYmnjp3f5rx+Ewd/82X9+4GF/82f/5b/+6j/68MO/y41lWtR+/S3wW/wtCaP+1tLI469++PeWFu4y5t/fW/jt"
    "OwtaWvs/bhzp87+9sKDH5MrP/8OHz//0ZhT8l3/31z/+81u/twn9ww9fLO38+MMXny9dLzztJ3/6p7dh3Br8zQcWemdZ+Ku5Pi7q"
    "+58BvL/9ign+zs0b8H5F3MT+bSlPj2cFvZSYKJ+Y35PxeqofMuTvW5Q+ffzBe9m/7659Be76VkH1tm06v13ctqO1X3EB1R+1v4ig"
    "0He+cw8GuOfmVrL/Xrb0uDwb3/0i8VMeOcujaXn00vGCWK87Xm5/Wn+cv7/5c9qPX7p7P3783Pz76fna+exp5F9nVufHMk3erYxo"
    "nb21P/n+hy8WveC3b4jyxT96yFt9Eum/8+Hz3/ibP/vxzz0nvn744ovFyLs9++LvPLyxrPPrtNgbvt7W5vfuSsUNs/7i3/zegiB/"
    "9R//009+4zfv7f54UR7u2Lyg5yI7/85f/ug/PPe3rPmHH37x/Xtpn//usN58/D8w9AdauukrT3LzaxO49ffutV72xDNuoYV7CuYj"
    "Z32s1fh2UboeC3sWwbdu5YAeS8ItlJc/c5HXatBn02N64gun+oY79tb9o+x/kvhPVtb7uyf21eEeN+H0NVnnpundGfB1GeffeJv/"
    "NKrXjNYpvupSfYxsPmYf3EKiz86+e+Sov3/8EvTJ8vkx9NLO5TaaX35zLxfv18v4b6WQll8/Xg2Rv2gPv/LsW1gG9Cy8vxHS8t8/"
    "uqa/kib6guyfvf+0vMWSev9WZ8Jzy2V4/n3e797/7Fa/OrYyfjbWv/nmXe168zyKb5gir2yGRcbf9ZlXmsmLTnRPJLoJyMfgwNd1"
    "E/9nKiN3zPiqUTXdc19fpWt+9h72kXfvn5os76fYPTR4j4q+zo99LuV236f5ElP7arfvvxqA/fQrIvuJdJ9F0E3DvLli/W9oCM9b"
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
