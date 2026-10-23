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
VERSION = "1.16.8"
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
                     r"\u2605\u2606\u25c6\u25c7\u25ce\u25cf\u25cb\u25a0\u25a1\u203b\u266a\u25b2\u25b3\u25bc\u25bd\u3007!?#*+=~^:;'\"]+")   # ★☆◆◇◎●○■□※♪▲△▼▽〇 などの飾りも無視


_MK_NUM = re.compile(r"^\s*[(\[（【]?\d{1,4}[)\]）】]?[\s_\-.・]*")      # 先頭の番号（00_ / 17- / (3) など）
_MK_TAIL = re.compile(r"^(?:み|済|済み)?(?:コピー|copy|\d)*$")            # 後ろに付いてよいもの（受付済み・「- コピー (2)」など）


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
             ("あり", "有"), ("アリ", "有"))   # 音声あり／音声有、動画アリ／動画有 も同じ


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
        try:
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
                for rel in files:
                    s = (fs.get(rel) or ["todo"])[0]
                    g = group_of(rel, (0, 0), self.depth)
                    cur = a.get(g)
                    if cur is None or CP_ORDER.index(s) < CP_ORDER.index(cur):
                        a[g] = s
                    if rel.lower().endswith(PRES_OPEN_EXT):   # 発表ファイルだけの状態（大きな動画のコピー中でもスライドは開けるように）
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
        pend_groups = set(group_of(k, s if s is not None else com.get(k), w.depth) for k, (s, _t, _f, *_q) in pend)
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
        meta = "/" in rel and any(m in lr for m in META_DIRS) and any(mark_norm(x) in META_DIRS_N for x in rel.split("/")[:-1])
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
                return r.stdout.strip() or None
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
    "a+ymhpuVZvH27U/W69vLS2tX67/cL57LB4rbQU03EHPbLnG5/fj5S35f4orz+zS7vXX3k973tN2/FOX7ewFLregyd/3P3tfvMQR6"
    "gB6W5nx4qN8jBLJcLv/geyqS+j2B47enq83t6QpeEcs1ujx+wu1U8xa336z32zhSzTc02Is3evnFq+lwn2ALVR+NyhsHfA04fOc7"
    "Pw83PPoGXn5MNR8ebg156L+2Guy9QtKlbv91A8p98n/X/+zdf/vNv/utP/6Nf/8n/9uPvnVH8q9Y5KYf3n0a3lYbHohXYzZ8XMB9"
    "62S7L0F19199ry1aN32Jpnu/1PB+sWiBdx+eRFUdv/E13Nr3+Y1W77/WsFut3/AQ9eXTBH30Dn1Fwd45tGm1Fz37Os3uM+fFMP9a"
    "mfzTgD0P1ufn908RJR+//J2PP/4nH3/87z7++A8/fvlHt88f//P7569//OJfffzi9z/+6IuPX/7fH3/8bz5++S9vN7/8zx9//K9u"
    "L3zxe3/25e/82e/+o49f/NuPX/zOxy9//fb5xd/4+OWvffziV//sR//kT376f3z84l//2U//41LIz/6X/2eR1h+/+H8/fvGTj1/+"
    "w3cPm9f9wDcvwr3xv8DI+M53foGNcQ8EehSti+R5pNaNeA/j3eH0P1Tei83yFd/QV5RaHS+K/+OPf/VOlV977OizXfHu4xf/8EaY"
    "p97/7T/97b+16KePX/z2nTB/++MX//5P//Xv/uz3/okq3Yn7W+9edH7r36JRXtTNVwTkD28up2fNcufKr+kR/1XS363+ZXRfm/Cv"
    "/8PP/u7vf/ziH9/rvzfkeRj+/A9/7T48iyb9o5/96t/5k3/00z//w19/94AsY/MqtJ2XQ88fnYCf31TNAhzuqubT/IdfdQje3/nw"
    "8OQLf/i5UPl51Qx69Bwu/27Il3sBw4/fnlHwfVHhcR2w/2pY0Yuf8eZgfHQ7ffbJfVf+LX57UWA/3xXx4m71/XwZt69158MnbeTn"
    "75v82dN4p/cPH6WgVNwk22vi3rc+RKl4Rj33tx78r8/Bqfya9+d5bfirqu5+PPczMM6fkPodwz4mqnxxGn//3otHinx2p93//Dl7"
    "c+jdnbY//M4jAZ/uPRoGP/z+c36T9EUPs7snn8RrrW/cELd19NdlhacIr7fjkH6S+U3jhv7LcDxP679c4Xe/Gvfd+uuDezu3/UZI"
    "6FWovY0duMnIN+uvP2cN6WYCff5m8Rb6Oe80T+tMzyxxM6heWaL20ztDPFJsgZrn9+1Lb1H/WTVaxVsPh/Poc15u+m80gD2+ZHGz"
    "ig/L08eNDk+Ueh74Z49g+8jFdyn98cfLxP03H3/8bz/++Ecfv/wHf/Ybi0D5u/cp+/t/8pN/8ae//RsafRcltzl8v/g79+n9W4/T"
    "+I2IXUp9tRqfiv7Rxx//xq3oL3//448XNfDj28VSxs+v8t8+KoM//8P/8ijD/vwP/+t/+9V/8PFHf5sdy7So/fpb4Le4WxBG/a2l"
    "kKdf/ejvLCXcdcx/vJfwm3cRtJT2v98k0hd/YxFBT8GVX/ynj1/8wQ0U/Nf/8Gc//aNbvbcO/f2PXy7l/PTjl18sVS8y7Wd/8Ae3"
    "ZtwK/MePIvQusrA3fX0a1IdfQLy/8UYI/tbNG/Cwwm9q/zaUx6ezgl5TWJfPwu8ZvB7rxwj5+xalz59+8OD49921b8hd3zKo3rZN"
    "57eLW37b9isuoPqT9pcQFPrOd+6LAe65uaXsv6cttZdn44dfwn/OI2d5NC2PXiteGOttxcvtz+tP84ebP6f99LW6h/HTl+Ifppdr"
    "54fPLf+6sBqe0jR5tzSidfbe+uz7H79c7ILfvDHKl//gMW71WaX/1scv/taf/+FP/8pL4OvHL79cQN7t2Zd/8/GNZZzfhsXe+PU2"
    "Nv/sblTcOOuP/90/WxjkT//P//yzv/WP7+X+dDEe7ty8sOeiO//mn/zkP73Ut4z5xx99+f17ap+/sFnvPv1LNP1xLt3slWe9+bUO"
    "3Or78NYue5YZt6WFewjmk2R9ytX4Pv9W/JTYswi+dUsH9JQSbpl5+YsUeWsG/bB/Ck98lVTfcMfeqn/S/c8a/xllPdw9sW8yjtyU"
    "09d0nZumd2fA13Wcf5Nt/nOr3gpavfiqS/VpZfMp+uC2JPri7LuvHPX3j78OfbZ8fgq9llPdWvPL7+7p4v16af8tFdLy66erIfIX"
    "6+FXXnwLS4NelPc3lrT8hyfX9FfCRF+Z/YcPn5e3taTev+WZ8NxyaZ5/7/eHh19c6lfbdolfwPo337ybXe9eWvENKPIGMyw6/m7P"
    "vLFMXm2ieyDRTUE+LQ583Tbxf6ExcueMr4Kq/h77+iZc84cPsI98eHgusryfYvdYoH9//0187Esqt/s+zdc1ta9W+/DVBdjPv6Ky"
    "n6fuiwq6WZg3V6z/DQvhZesM033383uOsE/f3VYhP42z5TWwzMO/dksIskEe4iOlGgMk8WFBLn+U/SFiD+FyJd6+0stfZ/mfYbRM"
    "2N3ukLayNyCRrBvE2+gkub2utgbLHfzt3Oa6Tx4VCx0xHDvbfXDaX3c01Bzdo3TlBtbwoVZOhLRKdgK71iS5CPdXakclsWnzFX11"
    "8XHHhYUUEuKGFtkop1e9A1dnrfdBMDebWcVkrMPnZm4maxZxtEUHzMNxFAY9ED0hswolB7OeAHu8XjjISpzcPEir044dyXSvMCYr"
    "qqqTNe1JAsZrdDTCJCRO/nV1kqkom0KYXVmOp9LMiorjlg+9luLPpnLa8KMdHrZUIbIKzalZc0l21roLBYPMZKYto6ZVT37Ytx2s"
    "XglyHQ9XTKQCOsdQc+coOno4Fi5J+2pVK0avcPzeE425oYfDnHT9IDg6Eit7/5hQ4ma3OiqrfotV4hYluNC7RDNsgVnFtlTZ02NK"
    "cQNjY/Lo+DGllsjUN4eUiLvuuKGUo8Ffqthl1rSwIY8lt9kazMqczpUQ+ycWPEp2vbqs0zQuVZ+BjyJr6GQfbAgIW/PhFlBWFz4F"
    "6pM0dmOo1rjK0SyfHOfZ6FSU7Q31CiUFFhzRa3kIOvUI0OWl5bPBHJAMS8OrUBK8ezoYGUGt8iiLkIgQmJ3HsvB00k8m4mtpK7QE"
    "sjb76xGq1vGR3CU8gWRxsNo7qdhb6FR3QTIulOLHYTM2tC9vN36D0+C6UfYreiC3CDD3KXIOi1PAVw5UQifPHAVHOriSVFNQvUjy"
    "HgIkKCklT0dNj6J9EjRQYxXh1dG69JrExDtI4Z0128WFle+BruH3mDJuogtAW8yJiY+zJVWTQxzGziJGbS/GFy7ejDBXF0xKNKzk"
    "ygJAH0Wp4JIsJ5UEHQj1ABq4n5rKTmywnuMNmlI8FSp1T9pe+PzasOhokj0CitsZIbbdhXVzLA/TjpaGU2WmCGgpclDi8L4IGV+d"
    "4t6yFSlPlb0A5LM6qSfP2F6gKzATzSnKru2wKZWMCpjKbnyGOtuSB3c7Ecf6WZzLXcpZYW+eO/xSHBdi0CbC4dpAbU1N3ZYEjY8A"
    "Aw3xRRB0pswromxxZkA7lYIHCZFggmitQEC9vj4L4ZaV8u2kWEWZE6VM9Pwmwxjp4iuUQDYVLMmixnsWc5GMNGfPhdSAbTnRZR3h"
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
