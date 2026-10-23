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
VERSION = "1.16.7"
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
CP_ORDER = ["err", "off", "busy", "copying", "todo", "wait", "srcbusy", "edited", "ok"]
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
                for dct in (self.man, self.mnames, self.fst, self.gagg, self.dest):
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
        agg = {}
        with self.lock:
            for did, fs in self.fst.items():
                a = {}
                for rel in files:
                    s = (fs.get(rel) or ["todo"])[0]
                    g = group_of(rel, (0, 0), self.depth)
                    cur = a.get(g)
                    if cur is None or CP_ORDER.index(s) < CP_ORDER.index(cur):
                        a[g] = s
                agg[did] = a
            self.gagg = agg

    # ---- main cycle
    def cycle(self):
        op = self.mgr.cfg["op"]
        gen = self.gen
        if not op["enabled"]:
            if self.fst or self.dest:
                with self.lock:
                    self.fst, self.gagg, self.dest = {}, {}, {}
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
        meta = "/" in rel and any(mark_norm(x) in META_DIRS_N for x in rel.split("/")[:-1])
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
    "Xx5xpbjdz0IdppM5HjrjnArDWTeNxmVzq/vsqVB4lzlxaehSQluP+wvj8Dwa004mXZkb6WGsHxoRWXqbRlaFGshw9IlJMtW37L7l"
    "9qkHwLglS60XxIuTtRphhEWjFGhWK0Acqt2TYEei+RrQnz61b313HEUi3TF5xSts1qkqpsawqj7tIB4bFGrPsEmq40BIt4r9vrnk"
    "l+BGJU9Vq/BpI/w+pm5HktCSyBb0eikWR0GijIe9oq/8WS2EgiU9HUoMLqrZiJDQa8X6h0KKITwMJiQul0M4xFeVmG63cOOhz1BZ"
    "mZyjr67FKsgi9ZQdhO4VCsuqMAUgJEZipN6bYpHuTiS6EwnpPVI8porpMUXUJ5FYoJ28TozCSHcMZy8Xo43U4FdXn2Atd1WfYPt3"
    "Vl8f/TNkCmj4evYQAvV8z7oKSrBw1lBMdA9CVYaZUP5/sfuoIW/R69jhbQml9coaXGJqbfVe1lfvI2SERfCx0dkU3BqX8OPGLaVY"
    "L1SLfNPDXaZ9OhRLaNnrlHwOxOGf9/isYkdDJ91178ZeTtzSxhMS23OTbBdeLOdOWgZM/js3+x1u0Ng8crIteb9jR+54VjmsY7PU"
    "yeO6wmO7bk8sD3psx63c9srHPsnt7HtWO0K8Vq9Afc80I/MdH8fZyafTpNpPznmBqnuOBhLxKCsytT6ljDN50dQy/t3FftLbeIon"
    "S/zRGpuke56F5HdumP7Y3BiYYLA9YW8nIi3Nx+xchl8fbpj+b9u+V9DRML76RO6OoYLNXrv1FjM8PJ/cdv3brrgTLcLHW+xtEW71"
    "nm1tdrcsn0ulfcfRbHPtk0w20FPOyOT3Rs2ByFZNb/FpXbmx91iqReoqNmUdj5Ui4MZTqSD46LH0+NZTuoLdDZlpo7slc8EmLbM9"
    "7T1T+R5vPpUZNzeePJY5Hz96tCmz9jZ73Scy88bjjd6W8i23sbXx9KlqbOvpoyePVXvPnvQe6T7zJoJuY6srhy/gKLux+fTp466q"
    "5PGTJ082erKWzc1Hj7a2NmXDj5/0upB1y1Ta2+x2NzahXqWLubXRg+IamjpCzsLjp1ubj7YeaeDqCKmguvn46ZPuM60BaiKUoq70"
    "HKe7YGJqsgLHwfYkdc9wM+HD93WU8VId47QX7a48wHXprSNhlBXzmDLTs0czKKq+87BqqkE86ks7jq5oKQrz5n+n/YicSBchoGrk"
    "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"
    "t8iFkWXLufSykeoOHjNTlEAIJScUDKtTQJ8H0iROvstOXsyNP8PCPPvdfR7m+Jy38vRUnOSnbBhGHSX7YzF8ON2nuyiIVM2xIfon"
    "aDbTlUrGLd9XDm0BoimLWIyWdkNxw4N9ymGMuT4E9XP5TtIv9YX9GzpC7hBHymMmD6O85trVkmf/5bxGdHKdn/YrW/glIxU6+so/"
    "y7p3diZUpb1+hdyvOCR/o/shtkHvZVco64B468S2m7g42CU32cVtuOWzb+iEn6PpobhjfFOEnjBCEF50cZGskzwKtsM4n9ovl2w+"
    "9uUuv2FhfFXotyVP3hSn+DQV/KByQBkvv5kAnaK3yer0Hjr4ckpDRE9GMAK0EcdVIIK4IND4X5l9OBIGfGfMlTBk+kolw87gA1eq"
    "U1DfUuPYlOsn/Jt17St1BrbpIlV54xJiv98nlq+PxlaQhh9VjLpdT8NZtKjCtHMOx6eWOozjyFKJAGwtz6GjCBXLvk2+c2TMnGSE"
    "4P1gRCmp6ReDdM3S717ynYxt3UgfEeoqHl8oSRd4KbAyOz7G+QuV/kpN9mOL0uhVeusQhEY8NwoErOcLr20bvniPT9iuBnQP05f3"
    "Os49WF/RpCoak+M5vBa5vcWfLU2V7jIz7UtvqIAfkY1KT5vNyBINWoa9soUtX5Ae5fq1n7vWxMMwVx1qDUWPhlQM0BvT7ugPG4rO"
    "DGudGdY7owafQ13SFwWBKDLdoJ6Oq1bks7wGMkiSHaQGH4nOPcY3ahOg58rJLhyZkT5al1mLQo94cR23asYpcZiwCdokVz67wvtr"
    "uY/MQjiEjLlSRJhplBLFrsNpxC5C3l/W1TK6N3+gLwny9qeo8GpjWNTuug6rqe16RxvaXsirbY9dh4fJUhbS0oI8ZI65lOU+u856"
    "XmkPTJeGwl4Dur7hdv1+K+KVxrt1G0vX1Pdui0vHrvk6fDes+0y603T5XzcKXW34fB2+tynlLxr6WuO2DX+vw9Se58b7WNhX/iZ/"
    "/4whyxeHMn/BqNzBDmVZeh2+crom7Uivw6GTfaVFuFQfuw7/mvyrPp/+vsX13zOgtcy0r8PXQ9rzjwzLyA7DtaNmU9xSCoiwUXg0"
    "mCkPy7N1T79pQMpjs/4RrnHFFs7DmI37c0N/xuGcaPNOOHYfixgrd8zN5o5xHzUOd9jIfO6E38rWnI18tqOeijkSUuuygPgdNvbh"
    "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"
    "3iq2w9cU2wzGX8j/EPm1v3TdvdI4fv906sM9n95dj33SdFnm1rcP9xd+t26cvtxPvn8+9WHJ+/YqAm/Q18ut7X3haVl4/c4sUe0n"
    "SxzrwhSW37z7s3/xz/7kH/+d//qHv/dffvw77xbN8/7Fn/SC+b+hCD68NOPdL78DyKcp+IPUPfvpXMuvLNFAj1Tgh3/ph29zry/I"
    "YpH9v/IMLy7lcyawxxfRv3h+fvSjxUf3ox9Z35ysc+MeHl/N/YYKL+PzFDf0HLMdlcsrlZf58MjIn+TzLq7vZwGKPxnvIvQsLw8/"
    "T5hepPmNNM0/fJSnD/fkRO+URZk+7WSbTd13HqViCeB5c2GmBHUWN4tjewk4CGt3VpyXd19/uNdF51fyGC+27nFpd0njHr9sKUnv"
    "voj6NcLv7mV6HjH4dY4tZb5tystNwLv/+p/+r49f/v7P/vmv/8lP/8O7h8/v++3SFz6HPHoTilnFFPMz34Xzs1lOX74sO37uIfnL"
    "avwsBsuFNm7vkvadRdKKl25fIMDjXsM//ifL2t+ny73P0v3hVVaA10dAPvvhX5pF8oef3le75nm46Mbz47bJ2p9hS+0/W58lW8d3"
    "v5t/0i1ekdi73h6aWd6X5DZPJxf5uPuGn/ct+I8m8NPvQot7bkZHXrosj8zP+nnxSVnfcQLzmPtxxkRPEz14tNkPZPf+nrPzETE9"
    "Rwd+kb4dtM9fAyXHB/fbgzD3zT2d6Q+atihL//LZu1/+2Zf/65/83j+de+dlTH7lqWvfx7+oIz99vqO4R5F+9u7jj//Oz/7j73/8"
    "8jf/5Kd//PHLX3sHPF4A3v3sp//4T3/6+x9//HdfR+txrJ7GfVZUxWM/P0ra/2AXPx299vDySpUvlpxkz33sLZ3z3+zj4i2a+uz9"
    "bOeLRztfPFu/e7WPRd7xRhvdDdF8smh+UJTLC4oa75u/+vDpffDcl8H74o16uiwEdAm4t2ft+N6+R8u9f2oX2V3i4mlzwY9+9HRy"
    "8M/XuH17aVYJ9tMLE5ZWveR6nptmL4G+s8j7rxtSX6uOnoHKd+/rPq8d+qQF5/YsrXv4rv2Sv/ZFI9rtPcLlKUvCYoqAT6D1Emv9"
    "lJr21bXmLffd9zSojRc/7T/68HB5Oc2780ScVcxjZq53zV0zep8EizT4uXd72vWQPlw+CedbF810z35I3ut9v/L/8rKbMv7wfH3Z"
    "+r3saI3d1HCz0ize3v3Jer3cPLd2tf7v+8Vz+UCxvKhpITHLdonL8uPnL/l9iSvO79NsuevuJ73vabt/Kcr39wLmWtF57vqfva/f"
    "Ywj0AD3MzfnwUL9HCGQ+nP/B91Qk9XsCx5erq81ydQWviPkYnS8/8XaqecvbF/R+f2Vh8y0L9uKNnn/xCh3uE2zu1UdQuUjAN4jD"
    "977383jDo2/g5cdU8+FhachD/43VYO+Vks51+68bUO6T//v+Z+/+y2/+7e/8yW/82z/93378nTuTf+Uii31492m2rDY8EK9gNntc"
    "wH3rZLsvQXX3X/2gLVo3fYmmez/X8H5GtMC7D0+qqo7f+BqW9n2+9NX7bzRsqfVbHqKxfJqgj96hrxnYu4Q2rfZiZ1+n2X3mvADz"
    "b5SpPw3Y82B9fn7/FFHy8avf/fiTf/TxJ//m40/+6ONXf7x8/uSf3j9//eOX/+Ljl3/w8cdffvzq//74k3/18at/vpz86j9+/Mm/"
    "WG748vf//Kvf/fPf+wcfv/zXH7/83Y9f/fry+eVf+/jVr3388lf//Mf/6E9/+//4+OW//PPf/vdzIT/7X/6fWVt//PL//fjlTz9+"
    "9fffPWxe9wMvXoR7438ByPje934BxrgHAj2q1lnzPPbW0nkP0d3h9D9U3gtm+Zpv6GtGrY5nw//xJ79675Vfe3zQZ1zx7uOXf3/p"
    "mKen/5t/9jt/Y7ZPH7/8nXvH/M2PX/7bP/uXv/ez3/9HqnTv3N9692LzW3+JRnkxN19TkF8sLqdny3KXym/YEf9V099R/zy6r034"
    "l//uZ3/7Dz5++Q/v9d8b8jwMf/FHv3YfntmS/vHPfvVv/ek/+O2/+KNff/eAzGPzqrSdl5eePzoBP19MzUwc7qbm0/yLrzsE7/fM"
    "s3R8Xuj6OVT5edUMevQczv8W5su9kOHHb88s+L6o8LgO2H89rOjFz7g4GB/dTp99ct+Vv8Rvzwbs57siXtytvp/P4/aNx/nwSRv5"
    "+fsmf/Y03vv7i0ctKBWLZnvN/vzWhygVz6znfteD/805GJbf8P48rw1/3dTdX8/9TIzzJ6Z+57CPiSpfnMY/vD/FY498du+7//lz"
    "dnHo3Z22X3zvsQOfzj0Cgy9++JzfJH2xw+zuySfxWusbN8Syjv66rPAU4fV2HNJPMr9p3NB/GY7naf3fV/jdr8Z9v/7m4C7vbV86"
    "EnpVam93jy468s36689ZQ1og0OdvFm+hn3NP87TO9CwSC6B6FYnaT+8C8dhjM9U8v29fnhb1n02jVbz1cBwffc7zSf+NBXDGlyxu"
    "VvFhvvq40eGpp54H/tkj2D5K8V1Lf/zJPHH/1cef/OuPP/nxx6/+3p//xqxQ/vZ9yv7Bn/70n/3Z7/yGRt9VyTKH7wd/6z69f+tx"
    "Gr9RsXOpr6jxqegff/zJbyxFf/UHH38ym4GfLAdzGT+/yn/9aAz+4o/+06MO+4s/+s//5Vf/3scf/012LNOi9uvvgN/hliCM+jtz"
    "IU+/+vHfmku425h/fy/hN+8qaC7tf1800pd/bVZBT8GVX/6Hj1/+4UIK/vO/+/Pf/uOl3uWB/u7Hr+ZyfvvjV1/OVc867Wd/+IdL"
    "M5YC/+GjCr2rLOzNsz4N6sMv6Ly/9kYJ/tbiDXhY4YvZX4by+PSuoNftxOWz8nsmr8f6MUL+vkXp86cfPDj+fXftm+6ulwyqy7bp"
    "fDlY8tu2X3MB1Z+0v4Sg0Pe+d18McM/NkrL/nrbUnq+NH34J/zmXnPnSbb70puLxaxXPpz+vP80fFn9O++lrdQ/jpy/FP9xejp0v"
    "nlv+TWWVPKVp8pY0onX23vrshx+/mnHBby6C8tXfe4xbfTbpv/Xxy7/xF3/023/pJfD141dfzSRvufbVX3+8Yx7nt2Gxi7wuY/NP"
    "7qBikaw/+Tf/ZBaQP/s//+PP/sY/vJf72zN4uEvzLJ6z7fzrf/rT//BS3zzmH3/81Q/vqX3+m8169+l/R9Mf59KCV57t5jceYKnv"
    "w1tc9qwzlqWFewjmk2Z9ytX4Pv9O/JTYswi+s6QDekoJN8+8/EWLvIVBX/RP4Ymvmupb7til+ifb/2zxn1nWw90T+6rb7MU4fcPW"
    "uWl6dwZ808b5i27zn1v1VtHqxdddqk8rm0/RB8uS6Iuz775y1N8//ir02fz5KfQm/8nSml9+d08X79dz+5dUSPOvn46GyJ/Rw6+8"
    "+BbmBr0Y728tafkPT67pr4WJvgr7Fw+fl8taUu8veSY8t5yb59+f+8PDLy716227xC9k/dt33mHXu5dWfIuKvOEMs42/45k3yOQV"
    "E90DiRYD+bQ48E1s4v9CMHKXjK+Tqv4e+/omXPOLB9hHPjw8F1ne32L3WKB/v/9NfOxLKrf7Ps3XNbWvV/vw9QXYz79msp+n7osJ"
    "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"
    "Z7y9TjXTaQ6i5bYvIMxo2l1q9iaDwtTKebdcnd12ux0deVLeWXocLQHMotlELNHIj/mdQrQSHBUa4TnrivTE7TTbkLb8bGwCppUz"
    "HWzyM2czEA1Mc2xzVh2zHarRjrU3E7FsOB6JCpOglasJbl+F8zKVukNw9udcp5TeavTa3aloZ9mhi+LZMjq9WNwu1jOe9C5oNm2X"
    "lIqj0yzctNXPzXa5Uq82zef5eXuU9jZaxZJ/V2ykooGcvx0YR6179iLjdfp60e1SkIlF/CVmWhbSk46UEvpcv5sAXu3cjM1E617F"
    "1QQd2T8u7YxYf31kZcKxNjWJdCOOCFcIF6kuGwdjbrjDDDLd3X53s8+7GXbuzATq1KTTz+aEbK+bmuczm4zbxyYy3Xg/HE+nyl6m"
    "Rzk6xWjRGtztjPx9qdLcbXn3PMlBrhPcmc6d3XwxnA+nBpFomZ00vMmh6OvE6HF1kovt8Fkp1tvbyor1bqrqYYPNQMoKdnCQo8su"
    "iWW2p+6g3SFMMsWkVLZ6sGztDkaubDPSAgkT3tkNQw03cEfrroMNj5iddLWU7bGRHJfyJ7LhfB900e4oYBdTdpc/5ygwZY6O54Yu"
    "b8It9LKOhr2Yavv8vmivC9pkL5iogM23JXr20qXcVoIOhytb+TrtdIPGsZedpWqdViW4tR3dq0fsIhN0u6eOTqUSLyXycY7v5Kre"
    "yZCtCp12hN8VJuF2pLa7me1WpCQ3LzEdR9vdCKS76egmE9yr0sPaVqaXQ3xLyNOOIttzs7EuU3FTSUoatPlZoZtMs4l0rNDYtPtT"
    "YoxOIn8KRyVL3PZmd2sYztc7gZ3UdiORaoepxHY27ImEXREmOC8M+kBc+bCUK1WqQtCa8uxslrLx/LQ0irockXSw7xR69goXoQJs"
    "mUnN06l4pRa09uuReZAKh+dSIJ6pDBJbpWgzXvMDaWf6FX9+kk4GXexk1xopOF2BWN5R86esHUexHBam8Vg772gnqoU4k6H5IoCV"
    "SpZjsVos6OrsNOI1a4bitnbbvsqE7zjy7RjlnNW2XFFvKZPartbZmJ3ealZaiUS9FOmBFTzbYlNSJRbjGMYruoBwOtPdWVKYS735"
    "njscsaYKfNhqtYulcMSRiwrCXpyOxHupqSsycNd3nd3WoL0VK/vi00Cr7JNqwqxg3QvWNxOVsiNsLdSlWqJDCfk675wEqtuNcrnF"
    "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"
    "4PHRYvPiCLmekKq1+HvzmfNBDlcLtTJe1kHSED/pTosnJfy3HHCkvfli2s22C1Acg+3PZo+/KS5QpGginy7msaaxWJvkZpV618P6"
    "B+sn3BwnAUZmAay6PcfN3jnerJ6DMW97pt+jRSrNXJzrhMuCWpfeYs1ln2ZJ/KKpXrVyiezRP1rclVsqBX/2ctj+27d2JjqTuT4E"
    "CZBm8mb+gx3NId7fKFM9pp+9X3nRb/Xe5cXC71cfM9HwHnslu27er2G5TTNy1+WzNyaTd+85GqosPJsaHmNyV2vKStwxJkZR5HhV"
    "Utr7NU5EUVQ/ySQZUT2PIDKq55AkSPUsGYGyz6pD8qV6en7/73GScWpojxxIK1VPrlBSt8q07z7NqTber7PL1IuUNIlUIxvG+g7r"
    "H0VaqO7UH/mz0K99+qO1zyAa/Gjh1z4FVKDyAX6+GqZh7RFkq/36J7THh7/+MfbqI0HszYIVew3Pn1vXfi1M58GYFfCKH8Q3Yd1J"
    "bpLUX7bWgYONgEmLA1SLIb8+rP+6n3449uDkqb1C0S/rDz1Yy2gSIJ7DFdztHpb/ov+G95k1awT7ug6oGGLoHPkLY9UwgxcU0TFD"
    "AyU+FAs0RgHFuL9qKxnjuyG9Y5GB7k4P4E+HRwW664/gz0CEA+L2F1kcoOkR/DmUcYDuTrvTrj/lAYDu+j48T7OgP3f9HvxpK8F+"
    "7k768KfDovvc7Qzgz0jE9cF29Poyrs/d/hH8mfJ4PnePevBnnMXxyTLr8XuUED53+wf9PnUtvMCQV95BzzvhAjNoyXg69o9OOI8J"
    "3w8H7QPUKgNXO7zb7g5646MTIdWDrrShb/6JYHohxUH/2MPCkcOE4o6Pjtr9Eyk7g8b40wMqgrOgw7tep99t4xtgubEB3X63fyJE"
    "mpjB7/rdE8GRD++OjjvjDvYZ2FwYgfGB509OhCAPmjTxj6lJjAuG/k66g8nxCWO7MRDYcWfUPZHixuHd8XTqUQ7Ol0Ma/6h3jDO0"
    "olhUXgf+ePyRNaoHf3DG0ZGJvZlOYZHIN7hKJn5/4Ik3Wk+lErjDglto4anavaZDJuE1NKcxP/GQS9mkAg9B1K/+CudWWaZpK4pg"
    "/nwPpnPM31z4N8qMUprJVJkAfHMZTHx1kPGdt57gwLcPj/v9Y/4uWMJZBiPpDbx2j79DW9Lh3e5h/4DGBV/512PcEWzR5TclBvsz"
    "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"
    "XEL1Bx+6D8+YiH+9P0+Xiwe/8v8BkB3mfg=="
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
