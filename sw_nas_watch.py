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
    "+DI/uFfwWM+DPC670KfFSv/e9757WEyI+fIRJ95V3aKcP1LGr2z46cn0nyeQ9/bDfH4ubijffnfJWrRMjO1H9ke97J/4yKrYzlbF"
    "9hdZFQvtPnmKz5+/PcXnD269rAq9e1jMmCeuKMtl4h8ePUpl+TSVX2dukcdvoM/7/uDH7S0v4zFTMfusmQHMssP6mZLLUZUzR9/f"
    "385QwM9nZfXG72dqvJLuryKJ7+tH7jKuT0Px4j98vnPfk/TuwVjOY/xiSYb07fLnRhTZ4uZaarHGt98u/93P/+FjSPZf2Lh57kxP"
    "fNbe///uwnrLxbvPvxUn/uos1enuJLjz3JO34D7u3xYgT9DjWUjMLFYvnV4Q9tP8cpsmDpf8SPW7L9qFx+9NePIUfPb25fL794cP"
    "C/MsdtiT8lh6X+SPge5PJuhjg1Zzexa7f5lAXlo0/isWfbV4a90R2Kw7d7OKWYy5e4sfnhbR3z3Ot1kctHEwffI8GnMLvzvrir68"
    "D9AdpUULoH3I7p/3Jr7Kyjt+bCA8iu38WWznj3n8FpdS5i/aon4yhRc6zfW/PH/i5oeXG09aC4GWZDQvpURxsCSQmLvQNn/tG3HG"
    "q/X86rd7OU91YbznQ126tPD0N3r09OLLfruXmK3onmdyJt2HO27Dz9dLHPRdgnxw4ADAg7PIm3cP89R8pR3vwcR3oj1NY2F8XFe9"
    "71hplgG8Xzwvgz99/fSXHy9meHqnXHv3KzwN1WNY3yx/Pkz9e38+/+4z2F5cxfdOPVvZH0j1V6aPXFG/tEJ9+Ec/erIVXlyK9959"
    "cEb5H7wGTwU/fPfZVHi3/PouFD/I1/sI1/eZ93jzqTHP8Ug/+pHtf2OcHj468zsrXzJpvOrHM1e9rJ5/q1mzQHrx6T37tb7tx/nw"
    "yoejtj74c9bYB6E73oWuUC+RV4usPxTfhx6c9vXq5fE+oG+a4a8srXjtXXnV8s/e/C9vnoNX3j2ET2vrn7i5+2iD3Af57ilaRP+r"
    "ge2/EX9xHN8+xVfdD/Fd1pue008vvL3MlYVvnhYRYv/y5t3dWZo+H5j6nV/89vSDWdTc338q+JvvfwgUFuqZCb/3vVdsdb/zS7CP"
    "3g9beMQM93tL0uJnuyUs7yssv/zmsmjaN48e9R88fimCII1z/82vvLaul9YtZwQVS+L7p7MQ7qV+/0PVf3V8Uoaf3/eW+Q/jp/lD"
    "64aftg/N4kdYstfdFzcfDsVy+nHxc1TxaXxAUOi1YLM/EmwzGH8x/ofIr/2FdI9hxPHbp1vv7vn07nLsk6bLMree3t0P/G7dOH15"
    "n3r7fOvdkvftAwu8Ql8vr7b3hadl4fU7M0e1nyxxrIulsPzmzZ/+y3/+x//k7/733/+dP/rxb79ZJM/bF3/SC+b/hiB499KMN7/8"
    "BqCepuAPUvfsp3Mtv7JEAz2aAj/8Sz98RYzTgiwW3v+rz/BipvlTJrDHg+hfPD8/+tHio/vRj6xvTta5cQ+PR3O/MoWX8XmKG3qO"
    "2Z7K5UjlZT48WuRP/Hln17czA8WfjHcWeuaXh5/HTC/c/Iqb5h8+8tO7e3KiN+oiTJ92ss2q7juPXDGX/frBbBLUWdwsju0l4CCs"
    "3VlwXt583LkPi84fjMd40XWPS7tLGvf4ZUtJevdF1B8i/O5epucRgz/MsaXM1015eQl489//6//1/svf/dm/+PU//sl/evPw+X2/"
    "XfpizyGP3oRiFjHF3Oc7c3428+nLl2XHzz0kf1mNn9lgedDG7Z3TvrNwWvFC9gUCPO41/MN/uqz9fbq8+8zd7z7wCvChC8hnP/xL"
    "M0v+8NP7atc8DxfZeH7cNln7M2yp/Wfts2Tr+O5380+6xSsSe9fpoZn5fUlu83Rz4Y+7b/h534L/qAI//S60uOdmdOSly/LI3NfP"
    "i0/K+o4T2MfcjzMmeprowaPOfjh3b+85Ox8R03N04Bfp60H7/EOg5PjgfnsQZtrc05n+oGmLsvQvn7355Z99+b/98e/8s5k6L2Py"
    "K0+kfRv/IkJ++vxGcY8i/ezN+x//3Z/9l999/+Vv/vFP/vD9l7/2Bnh8ALz52U/+yZ/85Hff//jvfRitx7F6GvdZUBWPdH7ktP9J"
    "Ej9dfaDwcqTKF0tOsmcaewtx/kIaF6/R1GdvZz1fPOr54ln73at9LPKON9rorojmm0Xzg6JcDihKvW/+6t2n98FzXwbvi9cnhS4G"
    "6BJw78zS8a1zj5Z7+9QuqrvExdPmgh/96Onm4J+vcfv60SwSnKcDE5ZWveR6npvmLIG+M8v7Hzakfqh6esnpe1/3+UDQJyk4t2dp"
    "3cN3nZf8tS8S0WnvES5PWRIWVQR8Aq2XWOun1LQfXGve8t59T4PWePHT/qN3D5eX24I7T8RZxDxm5nrT3CWj90mwcIOfe9PTrof0"
    "4fJJOL+6SKZ79kPqXu/blf9Xlt2U8bvn58vW72VHa+ymppuV++L125+s18vLc2tX6/+xXzyXDxTLQU2LEbNsl7gsP37+kt+XuOL8"
    "Ps2Wt+5+0vuetvuXonx7L2CuFV1ygX72tn6LI9AD9DA3Z4bYbxESmS/nf/A9FUn9liSI5ekKW56u4BU5X6Pz4ye7XWpe2+0Lel/G"
    "UWq+pcFevNHzLz5Ah/sEm6n6CCoXDviG4fC97/08u+HRN/DyY6l597A05GH6eDV48To8y6e5bv/DBpT75P++/9mbP/rNv/OdP/6N"
    "f/8n//uPv3O35D/YIot+ePNpsqw2PJAfwGzyuID72sl2X4Lq7r/6QVu0bvoSTfd2ruHtjGiBN++eRFUTv/I1LO37fKHV2280bKn1"
    "Wx6ia/k0QR+9Qx8p2DuHNq3+omc/TLP7zHkB5t8os3oasOfB+lx7+xRR8v6rf/P+63/8/ut/9/7rP3j/1R8un1//s/vnr7//8l++"
    "//L33v/4y/df/d/vv/7X77/6F8vNr/7L+6//5fLCl7/7Z1/9mz/7nX/4/st/+/7Lf/P+q19fPr/86++/+rX3X/7qn/34H//JT//P"
    "91/+qz/76X+cC/nZ//r/zNL6/Zf/7/svf/L+q3/w5gH7sB948SLcG/8LQMb3vvcLMMY9EOhRtM6S55FaC/EeprvD6X+qvBfM8pFv"
    "6COl1sSz4n//9a/eqfJrjx19xhVv3n/5DxbCPPX+b/3pb//NWT+9//K374T5W++//Pd/+q9+52e/+481+U7c33rzovNbf4lGeVE3"
    "HwnILxaX07NmuXPlN/SI/0HS31H/PLofmvCv/sPP/s7vvf/yH93rvzfkeRj+/A9+7T48syb9w5/96t/+k3/40z//g19/84DMY/MK"
    "278cev7oBPx8UTWz4XBXNZ/mX3zsELy/8+7hyRf+8HNN5edVM+jRczj/Wyxf/sUYfvz2bAXfFxUe1wGnj8OKXvyMi4Px0e302Sf3"
    "XflL/PaswH6+K+LF3er7+Txu3+jOu0/ayM/fznblk6fxTu8vHqWgXCyS7cOm7tc+RLl4tnrubz3435yDQ/kN78/z2vDHqu5+PPez"
    "YZw/Wep3G/YxUeWL0/iH9148UuSzO+3+8ufc4tC7O22/+N4jAZ/uPQKDL374nN8kfdHD3PbJJ/Gh1lduiGUd/cOywlOE1+txSD/J"
    "/KZxQ/9lOJ6n9f9Y4Xe/Gv/9+puDu5zbvhAS+iDUXjGlusjIV+uvP2cNaYFAn79avIV+zjvp0zrTM0ssgOoDS9R+emeIR4rNpqb2"
    "tn3pLeo/q0areO3h2Dz6nOeb/isN8JfHlyxuVvFufvq40eGJUs8D/+wRbB+5+C6l3389T9x//f7rf/v+6x+//+rv/9lvzALl79yn"
    "7O/9yU/++Z/+9m/ozF2ULHP4fvG379P7tx6n8SsRO5f6ATU+Ff3j91//xlL0V7/3/utZDXy9XMxl/Pwq/+2jMvjzP/ivjzLsz//g"
    "v/3Rr/799z/+W9xYpkXt198Bv8MvQRj1d+ZCnn714789l3DXMf/xXsJv3kXQXNr/sUikL//6LIKegiu//E/vv/z9xSj4b//hz376"
    "h0u9S4f+3vuv5nJ++v6rL+eqZ5n2s9///aUZS4H/6FGE3kUW/qqvT4P68AuI99dfCcHfWrwBDytiUfvLUB6fzgr6sEu5fBZ+z8br"
    "sX6MkL9vUfr86QcPtn/fXfuK3PWSQXXZNp0vF0t+2/YjF1D9SftLCAp973v3xQD33Cwp++9pS0/zs/HdLxE/55E9P5rmRx8qnhnr"
    "dcXz7c/rT/OHxZ/Tfvqhuofx05fiH6aXa/uL55Z/U1gxT2mavCWNaJ29tT774fuvZlzwmwujfPX3H+NWn1X6b73/8m/++R/89C+9"
    "BL6+/+qr2chbnn31Nx7fmMf5dVjswq/L2PzTO6hYOOuP/90/nRnkT//zf/nZ3/xH93J/OoOHOzfP7Dnrzr/xJz/5Ty/1zWP+/sdf"
    "/fCe2ucvbNabT/8Hmv44lxa88qw3v9GBpb53r3HZs8xYlhbuIZhPkvUpV+Pb/DvxU2LPIvjOkg7oKSXcPPPyFynyGgZ9MT2FJ36Q"
    "VN9yxy7VP+n+Z43/bGU93D2xH2SbH779INiedJ2bpndnwDd1nL/INv+5VR8tWRQfu1SfVjafog+WJdEXZ9995ai/f/w16LP581Po"
    "VV76pTW//OaeLt6v5/YvqZDmXz9dDZE/o4dfefEtzA16Ud7fWtLyH55c0x+FiX5g9i8ePi+XtaTeX/JMeG45N8+/9/vdwy8u9eO2"
    "dfGLsf7tN++w681LK75liryyGWYdf8czr5DJB0x0DyRaFOTT4sA3sYn/C8HInTM+Nqqme+zrq3DNLx5gH3n38FxkeT/F7rFA//7+"
    "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"
    "XE9wCU02K4+28SJx1ouK5Gsz+gN9SBlf"
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
