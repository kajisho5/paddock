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
    "N2X87vn5svV72dEau6npZqVVvH77o/V6eXlu7Wr9N/vFc/lAsRzUtICYZbvEZfnx85f8PsUV53cxW966x0nve9ruX4ry7b2AuVZ0"
    "ll3/k7f1WxyBHqCHuTnvHuq3CInMl/M/+J6KpH5LEsTydIUtT1fwipyv0fnxE263mte4ffHel3G0mm9YsJdo9PyLD67DXcBmqj46"
    "lQsHfA04fOc7Pws3PMYGXn5sNe8eloY8TF+dDV6iDs/6aa7b/7AB5S783/U/efPffvvvf+vPfuvf//n/9sNv3ZH8Byyy2Ic3H1+X"
    "2YYH8oMze32cwH0dZLtPQXX3X32vLVo3fVlN93au4e3s0QJv3j2pqjp+FWtY2vfpQqu3X2vYUus3IkRD+SSgj9GhrxjYO4c2rf5i"
    "Zz+I2V1yXhzzr5W5eRqw58H69Pz2aUXJ+y/+4P2X/+z9l//u/Zc/ef/Fny6fX/6L++evv//8999//sfvf/j5+y/+7/df/pv3X/yr"
    "5eYX//n9l7+/vPD5H/3lF3/wl3/4T95//m/ff/4H77/49eXz87/z/otfe//5r/7lD//Zn//4/3j/+b/+yx//x7mQn/4v/8+srd9/"
    "/v++//xH77/4x28esA/7gZcowr3xP8fJWI7u+5k+xn0h0KNqnTXPI7UW4j0k94DT/1B5Lz7LV2JDXzFqdTwb/vdf/uqdKr/22NFn"
    "v+LN+8//8UKYp97/5l/83m/M9un95793J8xvvv/83//Fv/7Dn/7RP9PkO3F/582LzW/9ZTXKi7n5ioL8bAk5PVuWO1d+zY74HzT9"
    "3eufR/dDE/71f/jp3//j95//03v994Y8D8Nf/eTX7sMzW9I//emv/r0//yc//quf/PqbB2Qem1dBi5dDzx+DgJ8upmYGDndT83H+"
    "2VcDgvd33j08xcIffiZUfp41gx4jh/O/BfnyL2D48dszCr5PKjzOA05fXVb0EmdcAoyPYadPPrrvyl/Wb88G7GeHIl7Crb6fz+P2"
    "te68+6iN/Pxtkz9HGu/0/uxRC9rFotk+bDJ9HUO0i2fUc3/rwf+6DKrl16I/z3PDXzV19+O5n4Fx/oTU7xj2MVHlS9D4+/dePFLk"
    "kzvt/udPqSWgdw/afvadRwI+3Xt0DD77/nN+k/TFDnPbp5jEh1pfhSGWefQP0wpPK7xej0P6UeY3jRv6L8PxLNZ/s8LvcTX+u/XX"
    "B3c5t30hJPRBqb1iyt2iI1/Nv/6MOaTFBfr01eQt9DPeiZ/mmZ5ZYnGoPrBE7ad3hnik2Aw1z2/bl96i/rNpNIrXEQ4/vMec55v+"
    "60TW4UsWN6N4Nz993OjwRKnngX+OCLaPXHzX0u+/nAX337z/8t++//KH77/4R3/5W7NC+ft3kf3jP//Rv/yL3/stnbmrkkWG7xd/"
    "7y7ev/Moxq9U7FzqB6/xqegfvv/yt5aiv/jj91/OZuDL5WIu42dX+W8fjcFf/eS/POqwv/rJf/1vv/qP3v/wN7mxTIvar78Ffotf"
    "FmHU35oLefrVD//eXMLdxvzHewm/fVdBc2n/+6KRPv87swp6Wlz5+X96//mfLKDgv/6Hv/zxny71Lh36h++/mMv58fsvPp+rnnXa"
    "T//kT5ZmLAX+00cVeldZ+Ou+Pg7qw88h3t95pQR/Z4kGPKyIxewvQ+k8nRX0IYV1+az8nsGrUz+ukL9vUfr06QcPB/++u/YVuesl"
    "g+qybTpfLpb8tu1XQkD1R+0vIij0ne/cJwPcc7Ok7L+nLT3Oz8Z3v0j8jEfO/GiaH32oeNlW9Kri+fan9cf5wxLPaT/+UN3D+PFL"
    "8Q/Ty7Xz2XPLv66sqKc0Td6SRrTO3tqffP/9F7Nf8NsLo3zxjx7XrT6b9N95//lv/NVPfvwLLwtf33/xxQzylmdf/N3HN+Zxfr0s"
    "duHXZWx+9+5ULJz1Z//ud2cG+Yv/8z//9Df+6b3cH8/Ow52bZ/acbeff/fMf/aeX+uYxf//DL75/T+3z1zbrzcd/g6Y/ytLirzzb"
    "za91YKnv3Wu/7FlnLFML9yWYT5r1KVfj21m7PCX2LIJvLemAnlLCzZKXv2iR127QZ9PT8sQPmuob4dil+ifb/2zxn1HWwz0S+yoT"
    "fPj2g2J7snVumt6DAV+3cf6i2/znVr1WtELx1ZDq08zm0+qDZUr0Jdh3nznq7x+/BH0yf34MvcoPvrTml9/c08X79dz+JRXS/Oun"
    "qyHyZ+/hV15iC3ODXoz3N6a0/Ien0PRXlol+YPbPHj4tl7mk3l/yTHhuOTfPv/f73cPPL/WrbbvEL2D9m2/e3a43L634BhR5hRlm"
    "G3/3Z155Jh98ovtCosVAPk0OfN038X+uM3LnjK+Cqum+9vXVcs3PHmAfeffwXGR5P8XusUD//v6r9bEvqdzu+zQ/zKl9tdqHr07A"
    "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"
    "7vXmLyUZg2I="
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
