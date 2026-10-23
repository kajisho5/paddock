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
    "eNrcvftb20jSMPr7/hVGJ8eftbQdG8jNRvEbbjMsCUkgl8mwfLzCatsKsuSRZAMD3r/9VFXfZUMy++15nnPePDO41feurq6urq6q"
    "3l6LskF5O+W1cTlJXv9tG39qSZiOAu976GEEDyP4mfAyrA3GYV7wMvBm5bD50lPRaTjhgTeP+fU0y0uvNsjSkqeQ7TqOynEQ8Xk8"
    "4E36YHEal3GYNItBmPCgg3WUcZnw1x/e7O293z3afio+/7ZdDPJ4Wr6+jtMou26dfr3Yef/+U3BXZlc87XoXF5/eH+0fX1x47Apy"
    "YMSbDx+ODo/3MOoyLDhGfdk/OT18j7kWve2nssa/1Wqy8hqOPPAmWTRLOPQ7z4oiy+NRnL5uDGfpoIyztOHfwXiKspYGAKrZBAbW"
    "GuQ8LPl+wvGr4SVxeuX5rZwnb+Oi7MXDRlqvp61iNkV4FHa4IRubQuYsjDzfz3k5y9PeMMsbop2klg1ruqk/Zjy/PeUJH5RZ/iZJ"
    "Gv8LWzuD4kGlqvP/BZU1Er+X8uvau1kZYu/fXxY8n3OID17fmTZibCPxoadxi2AQBN5gHCcRDsDzTcYMM8atMIp4dJxFvPCzVhmO"
    "jnHGoczbw+Mjr17PcOz47faoXs8bmb/wW5noRUONit3pxrprbVbMLsuccwgu/J6Ce62EsUjQx8HdoicAVUtaMWDXKI/L23oduq+/"
    "AivFZwl0acjznOcfsiQeiLxuVFDNg6UIB94TDuCAZgVvwmxH0GnA2sLrxy3rM/DidJDMIu51l0qGaZbeTrLZcplsEpdetxJZAESb"
    "Avc8Fi80FHBG72CekhafKlzBcLDW7ingIKR6Q14OxpBtDGNisb9Y+A2/Nw/z2pNZcMdvCPu6d4sF+5gANBmPKrEI4qd///vfan+v"
    "/RcAg6cFr53wcFBiTI6B1jSH6aVutSZx2vpeQBKm7mbTW+j5uKw1Bn7tIBzwyyy7YrXDdNCqhWlUi8uiFg6HcRLDsilastincVzU"
    "imyWDziQjIjX4FO2HNVmacTzWjnmtXeHn1R0bZjNsLoUE7CKt4e7+8en+zWomsvoWp5lZS2Kc1oxt4i/pdUQIhp24CmCZp4Hp7eT"
    "yyxpIcZ7YpRcLGvPZ/l4RTKCLEwgNVmVOszDkSwdr0ovyjwelBewTjhkyVY2kGc4nBzSwwfS53FE6YNV6UR9b7AHs5U9zPLrMI8u"
    "AE0gS7Syk7NiiuCG9OGq9AmfZJA2XZWWhH/eQtr1QKXFJc9DmAmzsMfjBvfv5HJGMpLOkuT+HukQTBZfgxVy+R1mz+tjQrfBg+tB"
    "vc7Prgfn9/f8zPuv/1J1eudMlYIVpxrw+ryLJf0FznEKiB4X7wBxSh51LaouOrDWgbWQApWd8YMMEOTzNAIctfPp9BM+TQC3T8uH"
    "MpzycjlxwcooeE8DaoVFEY9SVkS42DQ8rooGZykr/TtEVJzfaRFwRh9yMoNUfMKkFUERiY8ZdTUPyvv7NFpcUckyQ4C04oKW7m42"
    "mWYpbsXQnpOhkF0NdFehC0RolqehXrfiNJBhRtZo5vxynGfXtf08RyxQFTdarZbfrZXhFYe1n9ZEXbgaC0yuwdTE4WUCiWVWEyOp"
    "ZXktrGmwXI/jwbgmZunxKlqe37Mh0qrMRwMTGcJYd8/zKwAZmsm3YCKnpFKvhSiqas8qj3Ub+h0hEuSRaSqw2zUZk/A/gQWI8XEY"
    "JKHVHvIDedSLwxZtGPkMCSNk6ZVRIw6Z3R0fc8XFh1nOKwgE2w3WfTwI3uR5eAuZ6JclGrkNLMdh8f46/QAj4Hl5y7IwuBvMYJtN"
    "S1qXCxbDArjit7j3w1jw5+Ki4IkKEaVGbsBAJ4sUdLAXOaM9LCb8Yxn9ENslMRLpUY77QYqwWguCeRZHtTbwAJAXo3yWtqADdkoc"
    "eN46xUKin0QtYFCTRspyv15fi6PKoBoY3UjO8vMghT9ipw2DMB8Rg1O0Ep6OynFzA7sVAo3r+MAhINMDYAjKHk9gN4OkznboE1+G"
    "5SVsGyHQ3aDdG26HveH6uj84G56bms+G6xvnPauywQLq4bAcWxEfhrOkxD4WBgZh4Kaw0Kd+W2On75DGIdbb3ZMnYs135zmR2C5n"
    "OGExzVfGCDu7CbvIrlOedzNALTHBC8O5TMaCpjxYI3GeVG1K1XKcGVk1FwtANcBbImBVH4bWLmLtAppoAXkibEDIqMZx0Lmp44Z2"
    "Itolgjsv8Lpe0PYY/EBgw1Msp/fEW8e+EfVvPD0LuudPR0wTiVL3Ij0rzxdi1zkdBE//+XT96cig8Ci24fHDLhN64kcfeulhDxA1"
    "u2mrzE6BiUhHjc3nvhnKH7lYIAzWhhgS8IWyiR4gN/KywFIN45RH3v09RQCXlvAw9RCVuVg5hMdZsNZBvFV7s5/h8ieULa5jZDNj"
    "4MzhiOUV1BOvSx/pbHIJbEmXcl8CO3DVo3g5vK4sa2ZDVAJcGJWv5WMqukB8ziSvC33hsNgTiGA8yLHXXt9reesAzYy1/W7OjgfA"
    "/vYbcNz0mNySYDxlYKbsdMC8J/Wnnr/uwR8GoEoIVFBAz+JQT8xw4fvdRFcEeJbQWg8AoRNWrjfWEpyK+/sMDz4Qgk5RTN/zujhT"
    "9OE/0Po695H4TGcF1AZBAnQWACG0RtfN1wEFcWSQW1GHEEhCuM0lZemFQBnu4oCfhec9QTxyBEoMy7uXrQcwyJgGOQB8WChyMwiI"
    "+VJc08DmmqghHgwE4YNM2OAaoA5vpbD5NHy/FcFe0PPjIG7Nw2TGmWkTOsOqrWoiR8gmsUByC2kgkRjakZyD2EZgp895LQUWHpoA"
    "8hRChDiH1Iji1Rp0BujWvPUGnbPOJFsgip8D/GQEYNu4BjNR1O68dblH4Sc02fqexWnDYzWclIXXTeHHb9UOh7XbbFabwJookS0B"
    "goaHkBBOJwkewGkjGtYU5WU1OB0iYxIi1QZSW5Q8jJAZUbhrludervYvsa5oWSkWmOYvD87OAdPbqjAt6Bxx1EbT2BAbMU8li1kC"
    "0F/AccU0NyLChk21LpBZmhUAqmZH0TqIzXkBG0IvDYBJBXyEg1PasEmaU7INfLdbEVIMHdNhusKg9Bfs361nw63HZ25mJ2/bypv6"
    "i8pQOxq2KpPaAnsC/3Q8Uev3vMqhXOTBXZmHaRHjQGTkfBzcCbZI5N2Li2kIJA02qPec2Sk7GL2bpcN41L3InaT3cse0mJsQeUSH"
    "i4bsxEDjkRjXghQfcTr7mmN47XIGqFggUlITgHuLj61dxRncTcJpdy9nsLD3w8G4a/P6iIqElNZZJW2F02lyK3hazXDAhOKkDvAE"
    "1bVZY4FLGmGXaltfhylMoXRGbI1TdmUZszmmC//+/ux8wbI0cQvCRK/R1u8eO8Tw1chbWKzGb6awaAFmtJQHPJ7Daq0VQHUSKdqo"
    "ybO+WNLWyuWLRQ8AqbnfqwI+D+TZPkjG8PVBHtODjL6AYzbZgbf+2Dqlo/47OOkHMWY5lafqIMKvi4vT/d2T/U8Xh8ef9k+O37w9"
    "vdh7f3H8/tPF59P9i/cnF9/ef774evj27cXO/sXB4cn+XjDHctDrIIwgMEigLSmCDKozaxGZFWCyi8pz2qcxwEbOeG0yK8raJdeE"
    "V0KJAbqVRCGncJAFuAJTsu4h1AT9guMEnoUF5+YDLSOWhcWBYOyyQHFxNquOXV3i0mPBpUMRw1muYNkTi2UX3CQyTnQEcVhhsXuu"
    "SBFSVzooWBz/YDXHj9GN/GyAHP/AZp9D3ad+CCldTBZc4OCBA8FAkKjVB4KBfxfKg8DA76ndXxwIBnQgCFccCKzKwsVPsNwJsdyx"
    "ZLdzzckT4gv59q48da5Yt0AvdeWDMbuQc/QFuQI4KjjfGxgBWAh74y7RkDb7IEVYRFcZtFPAUOTXhZwgUZeIGiXZZZig0FlSYt5S"
    "VVgdCbEjos9djnlUxQE3g1IrJot01EFIksJgmbZlUesyTqMG9YJr6pAKmTmsNVPvCR8GS8Ild1PBzFL65uTmy2ek2ZgJ5qMrKFFc"
    "fEFuSHU+RPqCkrZHK5kCPKbhLYriu3dyb+w2O0zufAijC7yO6Y7G1AiK9SryoGqVw7E6DQ6A2AGn1k31QhDSupSqgsby8pPeP1eA"
    "9iJvmf2153yhsKrMb+94A843cQqL8vbOzSAamQHDhfKfC00TgR/bheyX4eBq5UBgo1fkxM5LWRay/MNIXyksMkK6LLnHL2cjwlob"
    "EXQiXTRElfSHKneymyb2h0PY0X5maCKnPbDDaBk/K4UOgQ9RuSdTFLHClvlrmEYJX9phVldQKSUzqzph88uxjp8fRqWIPZ63IexE"
    "5c9XZee363n3ENZXymM+u9wJByYMaMtPAUZmduGxmggslRya+a+KbB8oI4SeptRtOti/KXkOS+kUKN1PTuZSMbf3q1b3AzWZrAK/"
    "5jwvsJzXednabHW8Ho9a8i4q+EjMxF5gon5wK9X8Xtw0c9hX4gn/n3dDdTsO9tj38aPXVFc/uIi6Hv9QRHs8Dm7H/wZP2lo62bDT"
    "8V+V7Q5+LNstlyS15Y9EuA9JfntGOOxfjx0p7+n4R1LexyWtaVXSmq6WtKYrJa3fxz8haT0eG0nrx8QcSa7gbJAAvt8Eg0iGCgw+"
    "mZmVldDSKgITx2aVW+DfOcI+qsQOo0cvhws4AeO1f/4/a/k1bDqrkTVt7LADgalHwY4Sxu0Igd6B3+NdRIdee/uoJ8WwPDhqdl6/"
    "ft1hEx7snMX8HNGovZ00Jhyq8ikqOGA7Z0fnAUQdBTEXxwGSoeJZ1NKJ2NE0VjWOchXBe+2ctc9tzYEdOl3Z+ZRYhBYV9u4gwEIM"
    "hzLNpg3C8CNYNjBETAiO5IDkSNo0Blkh28+hvziyXsy393M54HEZbPy9EfP1jg/M5k0MLYzLczYpg3G53gHeHyImpQDC66RxE7Mj"
    "35+U2xNYWRjxIYdCfr8h4AJflD04YtD+pPS7MgHKUcUiYVwacaNb15GCcLWmCowlZA4MABN3qgtYD4eAdDfNAxNWRwKEWbt/1N1p"
    "xRGkx9HCXKUCKQEQTsJ04Aj7l1NbaXbtSGSlHN/K0uOG7cXcy1tvjLXAPksy3zshzt+DVcXCIBNJP65DZmyGC3mMPTtnQ/wzCTos"
    "EpT5Jthko2Ctw77jnyv8c6xuHApefoLtGPgt51reRItz3VjlHyQ8zFeVsBNEmZnVxuFkwiOkGNvejGrXEV2xa4icaTiPR6gugNnq"
    "df3ZkoQrTkfWRrEqGc5fh+l0Vn6AM9lfzi2PkCsyWspOc1ysaqEdBGUDNqoDeRvUo2V8QFsVHW2U+BgzKaQ/kGcugNV2sENpzMLT"
    "4ABpfpyTUhhmYmljwA58axH0RLMWtdmVFIQmF3vI1r6jzlgJVFz2zYfZb7PjtHEqqrpb0f96fVo2dpnVw+aO3cypWGcCj2CPpObG"
    "jX2f7aOIGLFMXD4fBTd0MCQ4AbEFVMSu9CLdUGOtEVUG+vrAv7/fgd39c8P3DU2ONDh7ZqXG3F1+JpPCebzHjzNUMXvL51zQUCCJ"
    "MV9qdxtoKIDUXWsNffUycTVWrJYmvBvBFJckcMrhL8OxiiucnIZLaUhg1MBJwgXUWN7SKTJMszAu3WkYl9Y8HODtC4BbUb/9XJ+4"
    "9TI/omUuKMEUp+ZapODksJPgGTuEgMHkz0a1plEdfPNw+8S6s4QjBeHXtRoGdXxnCWa9w2BH7lYwQsSAg+C6AXi3YwQEB304KMPm"
    "YPVQ0kDqNPV+xq25njlT7R7aZ40cT09qbckS73hRhCO+Ow7TlCdITESHhyWpWLjJ7APUKLTFNnoy0Gll6UTkCnLO3DY/wOklK0pZ"
    "S8MegJvxGDrH2raOCSw/WKjXwQ6b3t8jBNoMgWFBGmae1th+cGwrtu4szZC/YIhrJvYQjvEfJMrDXNspitjq5I6d/Da71glbdsIx"
    "bmWJTtu004RQHUijQDEr5XPB850kG1xBoi67YecY4P6YLMt/ADQ77jpeOMUyODqmM75/wwez6nH2+/39CEBqiJzvlCWlH+DBJ/zE"
    "OZhDk+3XO/f3nY1n2zt91LrJEt7iQgbvFlIaUjWY/BglJ8ClovC9vOY8rbWJO4ZqWA2LwdhrQyxZy5FPro2BpyYmOEwxU204LZZu"
    "jDy/exK0oRvvwnLcGiYZ9KHDN5/u+N1nzmBGXB3kPtgkbgV7cFMtdxDnRakgj2rCKwoRzbLLpY6YDUAm9QNupFpAR2gFbIifza4g"
    "AJtSs0Ces7oHwc1C7Q2wyxF1UAyyJT8EMrZwWp+GKCVbNedOtpz/MeNF+SGM7VuWaqZZ+jUuxxotzaBwzclh7TwwLPrZEj/Puu7g"
    "doJNa3A79uAOHhucOpGtWAzsADhitQkuEVrZV0nwjmx29UgS6X7jKDiCY24S3sKxwcop1T+A8d4+6gP7f9SNud/F0wwzY5f7JWwY"
    "RkEEYAFRG89spREABcR12i82X2x1Xm5s2klblMS3KpgAkc/4ptrJ4OtoHdicneAujrqT9XWmSED3gDl7eHeH6Q2xe8TcXRxqZZqJ"
    "6jY7C3b0OuZwOLFYqyPgpYYwRoYoHqjNdof28CEKEK76DcPOdK+QmNBWfNQECPl4orFqk6wZVLdMfHy2487zOJsl0beYJ1Hw2U64"
    "zsPpSkooFpE+tlgY/dAieuBO2ME9VDYfRsCZGDneMKIde3ccRD8tyYuyyf88Cd4blOD9xoPdsdmwL0mkILn9NPDGZTktuk+fEhi+"
    "F60sHz2NskHxlLaMZsSx63kLbXP6cUp6r2hes85ZGXR65Xb1lrFXrq/76Xrg1SGlODvHrCnW8fnkUN9SN8wNYqnFUd67OI2HMQBH"
    "Xv1iB2r/F9309mrzGPaomreernu4HxEohoDtNcnVoAYv6sRgfJqlzYmqLOLzGk/ncY4MEOxvWJgKUv0FTWAYRSQjDpPamCdTSK5d"
    "h3kKe17R8gT3GRGjdcpL9qRwVKgPhUj/bkCq1D7D33VvN5zCmLiHQnsjbRRZCPxPijN+HqSMB8A4b6cKehygN43Q6KWRQgZxl7uT"
    "BmuKMAqbpNfAAWq1dWmmpCxcHktzbyIxp8/+iH8oo90fB0//91n3TfP3i7D55z9n7fZuu4k/e8/p70v6OKCPA/rYODiAv5svKNvm"
    "iz36ewAfnQNM2YAamvSzh38p20bnJabstunjYB8+NtvtDnzsvcAyB68o5WBvFz/2Dujj4GDv/P+rHftns9VuvsKmd15gM23R5nNq"
    "ZvOAmtlqn//9yVO2O0Dh55uBg1kfbGOFP2IhL34zYNzvr7W7KmJXRHS6++MWUB+8Fey/GSByQSZIFSG21rEQcW+sNDaF3r0+ppXK"
    "JEuJ69Y6lY05leqX+vwiFDALugXwurJUW6hfKi1PGV3LsZ+qtf5a2QoHAz4tix2Rr0CDC94qM2Dgeb4LNTT8VoHEsdFmz3xUsQy8"
    "KCzDplRY9ZAcNT1fb8TasMKM9a071rRq9JGK9WKBxNeDgPy5AYQFKV8BheAlWYxN1XyqmAUl8oQ2obxkLpSwrDgOjxupL6KfV6OB"
    "g3+dLvR49HB2uFG2ZTHLpM5+BZABNrlxf48/m+JnS+jsh2WZx5ezkpMdXb4ispjCDhckIgX1ceD8oyhBUDJtIoDfVIm0FBAK/yJc"
    "hGhr+ScQ/bdBrCwHJtmc70+m5a3QvwwyIm7XKPfveUqFpBaF6Yjn2axIboHaHsKBNv/107u3NVs3Q33sjvngijTTVC48e+SwI+wK"
    "O9B9oOvIlXwV1Fwn/3obCUZLJ5S3CfdaxTSJy4ZX8/yW1FxzRPHXnIg2bAQ0Dbiq0LYDz4sQwiXm987OPDEZu8Ji1WPyuylNWL1z"
    "duYNkrAoEHqQTGGKxV32IMs9sumQMeV0/49ZPIc4DDc5fZyfr+yfVLE8a5/3oKup7mrKOtTVs855tbfewIUUtAOgGY1kuJjyJCEw"
    "wwdp3nrnPwOaDWrPXcpLTYezMjvheCWLTXF54XvCBS9TnOBYczhGIjgGs0J2CScQTTrfJNNx+Fd6U2nfA+qZXR9A3CnsioB5YXGb"
    "DmrYqQNsjkIf4KxBRsV5lhQK7fAXuLcopi5FKvAhHuCef5jKgIo/AcwvOdaEPDEyIJPjjJRq8BA+jqMIGofD8RQYl3dkxQoBnQ4L"
    "La1NoXBxmCZxypFhjd6jkmEu4QMBgmFUKwaQG354OEkAy4Ex5ZNTjPurmL35M9M3EKsPpmQCQImnNDuTWUlRBdkNQ/D8J9trL68k"
    "b6C4KA+YmFSYGv9MdVsrFyagelJAXXl2jT8F0CfCcNigfqrW56trhepOsQ6oCs9yP1fXsx8DmK4/wuDp2T+b3fPGGfA3575t1DGz"
    "rVBwaUNtn6dTVduCyE5aNseczi6ATyPigJtooU6YFObhZTxoIkLWVGSzGMfDEhqeqoKDJJ42p2E5FqEc8RMgCYcDtHnOp1kSCu52"
    "Oa4JBxf4LGSaNC+VX0LLDIkvHL7gSGf3jKe4cJq4XkY5HYqgYNLMYGuCs7P4oI6gUClqUoUyrPPAom0Ow0mcyDDOtwk1w+g76pqK"
    "CDg2wXauPm4TmVEed8THtQDHKLmdjpvod0AG4TgPUBXjHcPHn5AZDhLLiXPUJxrgGQNzQQfmzRsZFtbX8BlP4CxjgSbhJQCwiXsy"
    "fWIXICBHPAnzK0iF3Co4iXWQsLEGe25O8yqEfGhGoGJgWx5cpUgnpihjgk7gmRRQOSt4s1ObZjSXTSAucFCr6T7RFANQinE4tbta"
    "lNlU9ouCaiLQUOeKoy7wbDQ23XCjTV8gPrvizSiE+sm4wYrIhkPYQFUMDgLw1P5E4wr1PUFT3SSGHxVj9Qg/yStEDTXpmmE6GOOh"
    "EsN45BXMgfg2I6RDuwtME2VGMEtjPPA2L+Mo1h85sjX4VRbNKUJ1Ups3Q9zCLjlgBXyMIQe2Mm/GEc9GeTgdU/wElh6HP4Q6czr2"
    "NznpktUQowiPbkVQo5H9dVu7hpnVKHSdx4RBaAdeu5kkwHXfoF+H2o1c8D/cK5Qhh7IyGoRsFvqrOY7qnktNdeF4P8O9TX7lA9hd"
    "1ZcVhAm/lkHyzKHCtz+xof2lThJr1X369Pr6unW9STKQzqtXr55Se55N7AFgXaRSQO0xiN5KZJDYZu/8/5XO/PbuLXbo5dNU8edO"
    "p4BxIwEe8pLGE8TPbUSdH29E17xFgPg150NV0NMxnqhCzuyYYn4ETzqOQseLfICZRZlQnCeJ9528ER//p0OAhtq+7dkjCs1pEGcl"
    "Ca6r0g44fPVpZsRNfiNR59WEjjiobdHN7+/XGhtabAOntRSYbjyRZnjNL8PvPYzvUDileBE+JrNHOJhiRxJSAGuU4lzJoOZEHlH7"
    "HyCHSJMRXJ6i3qjzGqR3yaLeimGkouZ3k+rhrc/PEufkdh7omhN18N/EI7rndcsuHJUT92TI8moM4SJ7vH+NJBC1Q75EnEfxZ6te"
    "x3JrbbRdxC6zvO8O5fi0kZNy3vIQYXy+kI0dpMGbf0d9kL193AHHr+VjDjg+l4/rPQ7DHzrguIgfd8Axjh53wDGJHnXAMQ1/6IDj"
    "H/HjDjiePJZ+kZC7HjYOH/bScZQ+7KXjZlX3cX+nsxhk2H/Ejceb4q+68dgnNx77/5Ybj4JXnGjMY0v8W0jTsHmslS19vMSwjZ/8"
    "xSAkcZHaCkgRYnDVAoyYNPzWhFKf/jNt1P7eCMua3/efwgEgDlJBNO7vPU/Kgv77b/+9Po/XOfXsNka5ku7L91i70ljj9/e3sZRd"
    "eV4PcwpNljKgPgEqcbSiOMV+fMphGfceiJeDopsZFKD5JEWzrm/ckTIJK2HwbYiqkS7jET6bwhHsDlZ198GKFlph5YQP8TBpXwnK"
    "KONWAkpD/5aigVacnSvwD6WabzBcLGfkkBGl9aTFgnVJK1erMBbkUm3Xclxhiqyac1UOR6RjAITDej3XmnhDgQ8wQmnWbu5okkAm"
    "So4HEMBncZAvR2ZAZ6WpV4eFQaw/ep3tIMPL0SCs15OzDDehGI23/bDZJKVkK0cvazYZxOM0W3mpzxl8dO7v0eqs40cZKqjI3Kz9"
    "OgS6bucX6nuIrxiteR+vBgiOezfs9Bi0LB9bUVygpAN3lnp90JIeroqGt61dWr2mvXMQDEyFdiJzKvF9Nlhcj4GiNswAfXF5u1jo"
    "i0RaRuwh9C/lykPZdN+pHk2KkSOD7cvvEyGAkBHVXpL8XrseKMORFBRrGTCWERJkIQXuPLdSvLdEKWXKpp1yqom0TH21KlU4VBM5"
    "2s7Vf0f3gAdINMT2DDwZ47LCzooMLXEScvKtrKeN6a5IHuBiAMMzZSLuWqMrXyqrKLK/CknUBACbtVxUrSRt6q5mQs7CZ903pcru"
    "iUH9qhM+iP1eRF/EOlrt0iJhGKoEY3crk/6hy+gpEwlPlhJothbuEJTjgofcV0yirsJNFyzermIE1j1tiyibHluFlNHiI6WVtaMs"
    "PQ275jSD6KBXb+D0gUE96NnDrTmV04X+MgK6wfH63oE2TGzQZa8P/KCJ8zSyjUNzoVIZL3H7qWLU0y5imFhY0BaaT8neH6VdckEg"
    "bROxEy0yRLT1DrAwbHOSgN9p/WzS39JI/H5sn+zIodKKpb6hLoG8XTjFqNlXy7WR/vy0ddqm0F+fts5L1Y89PqbLDx5V0N5e86la"
    "6zx4YMHBDFY63/jZ+RTNvXhg9WnSVLlFcxejIofeSZapkop4ep8QCFWKCrOqLtte2hdzw7Bvr9uuZy3fjQ1V5XvNmcp6Nx4gBhsd"
    "vbBJ8F4h31U6oCm3SwdkXc/0iHIS3rwjyZ4q2rUpe+eFS+G3NKU3JCVdRVAfWKEVgpouE9R09brIS2vXU7RMXhrr+2DHac+yOx/j"
    "LkjPnuvPR8c+ssuMoqUFajbyVgqzTCwC2e3bogP07BKjEj2wmcLPC110XGY3nrhJ9fIwiuF8Y13KWrSAmu3ry5GuvDWDw69kjEe8"
    "tKQNe1z4g0UHOLaTNItdTn04eKMbprOUTFfWVkgsNCdZCksD9YWtBY7rPJ1SuClKHkJFgMGkDIq4r+bpUZKCblKH8WiWo8AeDe1G"
    "Lk+vXacKlzHjGJ16OHx/hgwyDC9jscnEMjoAPNIuT5E4UqtwbtcfUOgOuiBM+Jf7kVPjlVTdA0gssykuNtT1tYvDNkHzSGk8FzrC"
    "EU94yWs4L6iIZhi/HNGhUgQJZKUSQhsLjeaRcjPCjdaBdptjFyU0SI2igjjYpS018oZAGb03o/sIiZmAZQI1+x6gGhK8YQjnF6/L"
    "hWclcnZFqhZlH7YaBS30lgSMXdfWRRgmmo9D+i8xS+kakWWM+ujKk7E+bZPukc332RswuhqJ50pNCTedyyy6lfuxzkRxpjepsJG+"
    "U7CQw1QwgKV9t0DEcXUHZMeY4/pBxs3tD1ldt+wDCEnLEZCRzJ1b0rG0rHFhzeiHgdsnuxXJrHhe142HmdOdl27Y9LfJKhvrlQEQ"
    "3FRMnc4tOl6SFyO7p8Gd29Vurpxii3GXTF51J9SUcc9s6J+OFESwX+lq1+mKNTu3kYBEagbHUuXpjKSy5j45dbWVSjmxsgqJ7GbY"
    "PkGMCLxQ0RFnisAoBvdJhNpGUj8XoIfFgWgl+1oKZ1AijcSnXZ1G39VkbZ9BrRSzS/SrfH9PX6ieADzY3bIwVG4F6sC7SKt0XGXo"
    "FzRkKTVFz3vVjDbC4InYLkCQsTOQ2zcJXaXpVUUk7XSOVxKCtbVqXluTbGD5/XlwPIg3j49ASWbMPK418jUD23qdvgRssTo1O9oa"
    "TsfQ7Ct/1SltnKvXq1htpdjU5fQSlRYTneLycRZsukDXfsgfsZIQg8AlXNB7Vm4DuccpxVItpQVZMaMIWXRYpFH5/h6pbotMsvck"
    "cUWLOC4vCqQc3un3D0DQdbPbKF+tppRS90+F64vVyCB54ajbIauVTTGlEKsfFRy1ZKvdS7ZLpfqKruTSM/R4WZ4l56i0SDlLyFUa"
    "34OoXpwEy+iEjjLPynO9h2FY6aDAiAiz7bgg8VlCIjgRL0d6qpLx3ojkeqIPMHZYVmj5L7Z+0Xdu952GCz3XJAamjr4LUycT7SUr"
    "29NkYU0JtEVOqWYEqIm6Xcm5r3Mgg2pXb5s25pkWBsP6Xa1Ut8KL8mXjVcf3lzZNZytctVcq/b3uD5DN3h3fVnZHaoRoeGA8dImt"
    "XLo9TCt7KCttX16rh7Phk2n5pwKmj/J1NM5Vs25C1jIo0ZY9DUr4X0OZFjh0ZfHQjiqAQThiTcL3yB6hu2Utk+leafkQpSsxJBCS"
    "HllbEDmgWGYlLO8QaiGvWMUABJYvU3u9xHNrgi4HzhEKjtVSr7InSObD0wwEWdI2C1cNZTVNXEW2kFT5dp2P1BlvxVXyRrvdfopZ"
    "xJkQ9SMeyU335miARn/evfWqZ8aH7qpRGdM+TyaZ46KH60WKm/6jlfRhkHhRuzqjHg7ACnMAweHxKH0vb7Aer7orLoLe5+w6WuWd"
    "R9mPnr6ZTsXJkIItfsMHn9MiHPK3GRy6DmTJvnGIqPz5Ppq/sXzC4rooLHXoXmPJzbvY7Ojq+PPJ4drjQLm/97R2L4Rq3EdEkxFB"
    "2tM0+n0evIdD1kMPpUTxHFbw+9wq7G1DA6/RbQuh5fthwzcejv11b/sppQPRgWJDsjNEOtTj9oev2Dz6bNhpwt9LL61kxxWTRiK7"
    "nYYHXmsfzQ35VvTDaRhJo7hCh10olLGowY+SjU/yMt+/E9+Sf1E7zMJZzEDVsP5fi+AuTOMJqT4d0v0oBITfPNi5wgJdWp5gJH5e"
    "krbYIaqrvZ+VeKB3I09Rbb8S9xUVrkTczUHCb6zgL7A5TeX3+zzCixkdNciS2cR0RHwWGBzKSoaihmsV/iANWtX36ThH5RT5dcxH"
    "oZ36HjtIoos8jt4A2qjwiahRBvfTyPpClU/7E5Xt1Pcu9dD9skqLCLsCGaPqQHXDr6SLhV+oXbabhJOp+vhVJ0mFNgqqQWT5dBwK"
    "8JTh5Wn8J43zOo6ya4r8U9gTYijLJtRcnCTvTU2kRml9o0jE+UTluT2lnudGCQU9E/dO6+CZuKW6FFos2OE4OPO+8surGNXmJ6il"
    "+y77E/6+9857th/lX4vVWl+H4+VocehcR7lHmL8pG23fVZSFFDhkCPljo+OzXwvUyvoV7bMWju7QcVRxWpZWTUksx+ZSVOjh+b40"
    "OdYsRj4Vbol/LarMLPLy1H4ffXqnvlQT6Kbr3vTGumA8ldwFMtmktapZ61I4mVp1Jiv1WasEWgioAHTPazY9lHsCfgUwypKhO3ng"
    "4HslbUhJFpIwFJiSQVEc0Kev1HVMxUDyu8hLB4nw2PBpHCD/CPR3horoNMN3oVxf9EwW/uZyTeMPB8jQMhlTbDwZ0Q8KYzEAUz/i"
    "qVwGtJzxDTD8nYZ5SLisnXyxEiVlhPrUhD2RcWbTVuQNxwBsYqYVp7kmZ/ZHrHOFg+xsvmBc8Js/KikYc7e9Sm3P26IqhTwP16gE"
    "46iW5l1cEGtAb1A8UKLa7+fA8y+oQ4RHij3UDcvYiid1XRpYbItRyjJrqzcoRhjW1O6xdd1xYe4WKne0XpimmdSevkFuhyIdZXIZ"
    "J7W9B0vfTdQxrMbN8ngpjtwclUvRyKrIyElcoAfnJml2a1O3TtX4rC2wP5T+48yjFI6+PvLTYT7iJN2EPmpZp7DYZHgZkOfAJWXk"
    "yedzoVgZejDhwVSUQtgMAKxRVGdIS3SNIJnFgegZQzMx/C2LSk/fD7Rc9wpF2fbjPIPMfomngggbLxFj1XmBnsrBdnspHaF+Txpo"
    "H4tXszpJOk9mqYNBu3QoSIt+if8JB2fc70JHYZ12od/c5H0TCU8uaSHoGrA5BbBsZUErB4YmR0mDgnbEUwNLRreQLAxuTc37kcvw"
    "N+xzywd6XAcbvHKVsPYiSyJ2Ffs2W+z3rmLlR0a5vVHZtTYK1cdgPFoMUKogyniwYYaDtrua5vY50wa9OE0vq1mILQCmpCQSk6/K"
    "AydWvHLi6vkMZfsJXCFwd1dyWcgvZfGsIvey2WXC3YxWXDX7uwx9z2bX6XLMyqzvgOVejlmZ9fO0+r0y2z5aO3hdAMVaroUuPmkx"
    "SCSFFHqYxLuclWWGezw3l4XyQ0hj1Bdy2bjjeT5eq6zlPenzTdMMjg6CcKUt6cCYm7rHFtxmB5FHZjRyG/G2wEy9prKTkkoiuWoi"
    "6/XV92r7BfPQvzrwxh7dotk3YDPxQIrPpEl5GEX7aBmC99UctpWGh9bHHoNK9gudS1p9PpxRXupQVw0+n4xdK1cWsoH0eCQFj9Z7"
    "YnjSEDeH2q0A2/R7QodPupBgQ6WPN5EWs1kqgDjxBb3+XOCymyaCWowT/BpKSvnnOLiT+Z0XAbBMG8ugq2zd+XcrO+/WfzKWPftz"
    "7Li2UHUcrKwDpvLdeLVXDPa5oPTPhYLTNOk5bQqHThV+5dVLQJox0JgGjhiPHoHjh+1TaUmAGJAW8kPaChOy1Sy5L4+4Utzup4EO"
    "08kcD51RRoXhrJuEo6K+1X71Uii8y5y4NHQpoa3H/YVxeB6OaCeTrsyN9DDSD42ILJ1NI6tCDWQ4+kQkmepZdt9y+9QDYNySpVYL"
    "4sXJWoUwwqJRCjSrFSB21O5JsCPRfAXoL1/at76/OopEumPyilfYrFNVTI1hVX3aQTw2KNSeYZNUx4GAbhV7PXPJL8GNSp6qVuHT"
    "Rvh9TNyOxIElkc3p9VIsjoJEGQ97RU/5s1oIBUt6OpQYXCgdi5DQa8X6B0KKITwMxiQuV35f8FUlptvN3XjoM1RWxJfoq2uxCrJI"
    "PWUHoXu5wrIySAAIsZEYqfemWKi7E4ruhEJ6jxSPqWJ6TCH1SSTmaCevE8Mg1B3D2cvEaEM1+NXVx1jLQ9XH2P6D1VdH/wqZAhq+"
    "nj2EQDXfq7aCEiycNRQTPYJQpWEmlP9f7D5qyFuC4sjhbQml9crqv8fUyup9X129z5ARFsHnRmdTcGtcwo8bt5RivVAt8k0Pd5n2"
    "6FAsoWWvU3KoEgW/PeKzih0OnHTXvRv7PHZLG09I7MhNsl14sZA7aSkw+V/d7A+4QWM3oZNtyfsdO3THs8phHZskTh7XFR776PbE"
    "8qDHPrmV21752C9yO/ueVo4Qv6hXoL6nmpH5jo/j7GaTSVwexJc8R9U9RwMJd+xVmRq/JIwzedHUMP7dxX7S2XiJJ0v80RqbtAOm"
    "AfmdGyR/bm70TbD725h9GYu0JBuxbzL89njD9P8356HY169f46tP5O4YKtjsNBtfMMPTb+P7tn/fFkiVB8+32GEebHVebW22t0xl"
    "J4V9x1Fvcu2TTDbQUc7I5PdGxYHIVkVv8WVVubHzXKpF6io2ZR3PlSLgxkupIPjsufT41lG6gu0NmWmjvSVzwSYts73svFL5nm++"
    "lBk3N148lzmfP3u2KbN2NjvtFzLzxvONzpbyLbextfHypWps6+WzF89Ve69edJ7pPvM6gm5jqy2HL+Aou7H58uXztqrk+YsXLzY6"
    "spbNzWfPtrY2ZcPPX3TakHXLVNrZbLc3NqFepYu5tdGB4hqaOkLOwvOXW5vPtp5p4OoIqaC6+fzli/YrrQFqIpSirvQcp7tgYiqy"
    "AsfB9k3inuGmwofv2zDlhTrGaS/abXmAa9NbR8IoK+IRZaZnj6ZQVH1nQVlXg3jWk3YcbdFSGGT1fyW9kJxI5wGgauh3G3E9yFi8"
    "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"
    "u3daJm+fbr2719O787FP2j7PvWZ+dz/wu/OS7OV96u3zrXe3um8fUOCV9vXyancPPN0Cr99aMKr75JbHerMUbr9582f/8p//yT/5"
    "u//9D373j3/0O29unOftiz/pRef/GiN49zKMN7/yBqCeSPD7mXcKsqWXX71lAz2aAj/4Kz94fYL7wto+v+H+Lz2rFwvMnyqBPR5E"
    "/+L5+eEPbz66H/7Q+TqxLoN7eDya+5UpfFufp7yh55ztbXU7UvlGD48W+RN+3tH17YJAySfTHYWe8eXh5yHTCza/wqblh4/49O5e"
    "nOiNdmOmTzvZFlH3rUesWNp+/WAxCZo8aW+O7VvCQdR4C+M8v/l4ch+Czh+Mx+Qm6x5Du7cy7snLlpLs7otoPmT43b1MzysGf6Cx"
    "e73WV0N5eQl489//6//1/svf+9m/+I0/+cl/evPw+X2/XfZizyGP3oRyYTHlMuc7cn624OnLl9uOn3tK/i0av6DB7UGXdHdM+9YN"
    "08oXsN9UgMe9hn/0T2+xv09v7z5j97sPuAJ8mALy2Q/+yoKSP/j0Hu1a6PDGG0+P2yabYFFbmuBZ+tyqdXz728Un/c0rkviX+aFd"
    "8P1W3Obp5g0/7r7h530LwaMI/PTb0M09t2hHfnYLjyxz/bz8pGruegL7WPtx0YmeCD18lNkPVv/2XrPzUWN6zg78Inu9aJ9/SJSc"
    "HrxvLsICm3s50++3XVlVwfmzN7/ysy//tz/53X+2QOdlTX71CbRvk18EyE+f3yjvWaSfvXn/o7/7s//ye++//K0/+ckfvf/y198A"
    "jw+ANz/7yT/505/83vsf/b0Pq/W4Vk/rvjCq8hHOj5j2Pwnip6sPEL4dqfLFrSbZM4z9G3D+UhiXr7Wpz94ucr58lPPls/S7d/vY"
    "5F3f6OK7IFpulu33y+p2QJHvf/1X7z69L573snhfvGJP1c0AvSXcf2fhjm+/c8+We/s0Lqo/J+XT5oIf/vDp5hicLkn3+tHCEr7z"
    "dGDCbVQvtZ6XoX3nlui7oHzwYUPqq/LDLzV973GfDwB94oLLeG6je/j2d17q175wxO909wyXpyoJN1EEfAKtb7nWT6VpP7jW/Nt7"
    "9z0NeusnT/uP3j2EL7cFbyHEhcU8VuZ60945o/9JeMOGoPDnp10P2UP4SbS8euNM9+qH1L3ft6vgr952Uybvnp/ftn7fdrQmXmZ5"
    "eWWXr9/+ZL2+vbyMdrX+H/vFc/tAeTuo6WbE3LZLhLcfP38p7iGupLiT2e2tu5/0vqft/qWs3t4bWHpFF9oNPnvbvMUR6AF6WIaz"
    "qNhvERJZLpd/8L0USfOWJIjb0xV2e7qCV+RyjS6Pn+x2tf3Ibo8eN/Gr7Tck2Is3Wm1fqQ53Alug+qhU3jDga4bDd7/78+yGR9/A"
    "y4/V9t3DbSAP88fR4JvX4Zk/LX0HHzag3In/e8Fnb/74t/7Ot/7kN//9n/7vP/rW3ZL/YIvc5MObT5lbtOGB/KDMMo8B3NdOtnsI"
    "qr//6vtd2XnZSzbd26WHt4tGC7x598SqkuSVr+E2vs9vsHr7tYHdev2Gh4iqngj00Tv0kYC9Y2jbGS9y9gOZ3SnnRTH/WpvZ04I9"
    "L9bn+tunjJL3X/2b9z/+x+9//O/e//gP33/1R7fPH/+z++dvvP/yX77/8vff/+jL91/93+9//K/ff/Uvbje/+i/vf/wvby98+Xt/"
    "/tW/+fPf/Yfvv/y377/8N++/+o3b55d//f1Xv/7+y1/78x/94z/96f/5/st/9ec//Y9LIz/7X/+fhVu///L/ff/lT95/9Q/ePGAf"
    "9gPfvAj3wf8CJWOxRX++jnFPBHpkrQvneYTWDXgP27vD6X+qvRed5SPf0EdCLUkWwf/+x792h8qvP070Wa948/7Lf3ADzNPs/9af"
    "/c7fXOTT+y9/5w6Yv/X+y3//Z//qd3/2e/9Yl+/A/e03LzK/C27ZKC/i5iMG+cXN5fQsWe5Y+TU5Enzg9Hetf1ndD0P4V//hZ3/n"
    "999/+Y/u/d8H8rwMf/GHv35fnkWS/tHPfu1v/+k//Olf/OFvvHlAlrV5debDy6Hnj07Az2+iZjEc7qLm0+KLjx2C93fePTz5wh9+"
    "rqn8HDWDHj2Hy7+b5cu/GMOP356t4HtQ4TEOOH+cVvTiZ7w5GB/dTp99ct+Vf8vfXgTYz3dFvLhbg6BY1u1r03n3SRcHxdvFrnzy"
    "NN7h/cUjFxTKG2d7AU0SvfIhCuWz1XN/6yH4Og1y1de8P8+x4Y9F3f147mfDuHiy1O827GOhyhen8Q/us3iEyGd32H3nc+rm0Ls7"
    "bb/47iMAn+49KgZf/OC5vkn2Ioc55ckn8aHXV26IWxz9Q1jhKcPr9Tpkn+RB23pR8LIcz2T9P9b43a/Gf6/5+uLezm2/ARL6wNRe"
    "IaVx45Gv4q8/J4Z0U4E+fxW8hX7OO/5TnOkZJW4K1QeUaILsjhCPEFtMTf1t9zJbNHgWjfvytYejvHs4Pl9uBq8lQPRSxW1fvlue"
    "Pm50eILU88I/ewS7Ryy+c+n3P14I91+///G/ff/jH73/6u//+W8uDOXv3En29//0J//8z37nNw3mzkpuNHy/+Nt38v7tRzJ+xWKX"
    "Vj9ojU9N/+j9j3/z1vRXv//+x4sY+PHtYmnj53f5bx+FwV/84X995GF/8Yf/7Y9/7e+//9Hf4qYqK5ug+Rb4Lf6WhNF8a2nk6Vc/"
    "+ttLC3cZ8x/vLfzWnQUtrf0fN4705V9fWNBTcuWX/+n9l39wMwr+23/485/+0a3f24T+3vuvlnZ++v6rL5euF572sz/4g9swbg3+"
    "o0cWemdZ+Ku5Pi3qwy8A3l9/xQR/++YNeFgRN7F/W8rj01lBH0pYV8/M79l4PTaPGfL3LUqfP/3gQQ7uu2tfgbu5VVC9bZsubhe3"
    "7WjdRy6g5pPulxEU+u5378EA79TeSvbfy5YelmfTu18mfs4jd3k0L48+dLwg1uuOl9ufN58WDzd/Tvfph+4epk9fmn+YX67dL55H"
    "/nVmpTyVafJvZUSb/K3z2Q/ef7XoBb91Q5Sv/v5j3uqzSP/t91/+zb/4w5/+lZfE1/dffbUYebdnX/2NxzeWdX6dFnvD19va/NO7"
    "UnHDrD/5d/90QZA/+8//5Wd/8x/d2/3pojzcsXlBz0V2/o0//cl/eulvWfP3P/rqB/fSPn/psN58+j8w9Edauukrz3LzaxO49ffu"
    "tV72zDNuoYV7CuYTZ32q1fh2EQ9PhT3L8Fu3ckBPJeEWyiteuMhrNeiL+Sk98QOn+oY79tb9k+x/lvjPVtbD3RP7irfdhNPXZJ2X"
    "ZXdnwNdlXHDjbcHzqF4zWrf82KX6FNl8yj64hURfnH33yNFw//hr0GfL56fQh3b622h+5c29XHzQLOO/lUJafv10NcbBoj386otv"
    "YRnQi/D+RkgreHhyTX+UJvoB2b94+Ly6xZKG4FZnwveqZXjBfd7vHn5xqx+PrUpejPVvvnlXu968jOIbpsgrm2GR8Xd95pVm8kEn"
    "uicS3QTkU3Dg67pJ8AuVkTtmfGxUzffc11fpml88wAHy7uG5yep+it1jg8H9/Vf5sS+l3O77ND/E1D7u9uHjAOznH4nsZ9J9EUE3"
    "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"
    "v/v2j/8D86pyTQ=="
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
