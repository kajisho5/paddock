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
VERSION = "1.16.6"
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
        """目印ファイル（00_受付済.jpg など）なら (role, 表示名, 設定での順番) を返す。ファイル名だけで判断し、中身は読まない。"""
        if sig is None or sig == DIR or sig[0] > MARK_MAX:
            return None
        name = base(rel)
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
    "cdmF3i8s/Xvf++5hoRDz4SNOvJu6xTh/ZIxfcfj+ifq/e8i9tx/m83NxY/n2u0vWomVi7D/iH82yf+IjVrGfWcX+F7GKpe8+eYrP"
    "n789xecPbr2sCr17WGjMk1QU5TLxxUeP0gxmH6fy68wt8vgN9HnfH/y4veVlPOZezD5rZgCz7LB+7snlVZWzRN/v381QwM9nY/XG"
    "7+feeKXdX0US39eP3GVcn4bixX/4fOa+J+ndwzQuUcdLMqRvlz83osgWN9dSizm+/Xb5737+Dx9Dsv/Cxi0vsn+Ss/b+/xIEeD94"
    "9/m34sRfvUu1vzsJ7jL35C24j/u3FcgT9HhWErOI1ctDLwj7aX65TROHS36k+t0X7SLj9yY8eQo+e/ty+P37xYdFeBYe9mQ8lqcv"
    "8sdA9ycK+tig1dyehfcvE8hLi8Z/JaKvFm/NOwKbbed+NjELmbu3+OFpEf3d43yb1UEbB7dPnkdjbuF3Z1sRlPcBuqM0dwG0D979"
    "897ED1VM48cE4VFt589qO3/M47e4lDJ/sRb1ExVe+mmu/+X6kzQ/vJx4sloItCSjeSklioMlgcT8CG3z178RZ7xaz7d++ynnqW6M"
    "93yoyyMtMv2NJ3q68WW/3UvMVnTPMzl33YczbsPNx0sc9F2DfHDgAMCDtOibdw/z1HxlHe/BxPdOe47fGh/XVe87VpplAO8Hz8vg"
    "T18//eXHgxme3nuuvfsVnobqMaxv1j+vaH/5NNKPYHtxFd8f6pllf+iqv9p/5Ir6pRXqwz/60RNXeHEp3p/ugzPK/+A1eCr44bvP"
    "VOHd8uu7UvygX+8jXN9n3uPJp8Y8xyP96EeO/41xevjond/3kXnMpPHqOZ6l6mX1/FvNmhXSi0/v2a/1bT/Oh1s+vGrrgz9nvfmg"
    "dLu70tXrJfJq0fVC8X3owW5fr15y9wF90wx/dWnFa+/Kq5Z/9uZ/evMcvPLu4fK0tv6Jm7uPHOQ+yHdP0aL6Xw1s8I34C258+xRf"
    "dX+J77Le9Jx+epHtZa4scvO0iBD7lzfv7s7S9PmFqd/5xXfffjCrmvv9TwV/8/4PgcJ6PQvh9773SqzuZ34J9tH7yxYeMcP93JK0"
    "+Jm3XMr7Cssvv7kslvbNo0f9B49fiiBI49x/8yuv2fXSuuUdQcXcoOLpXQj3Ur//oeq/1j0Zw8/ve8v8h3HZK+aGn7YPzeJHWLLX"
    "3Rc3H4Rieftx8XNM8WF8QFDotWITPlJsMxh/If9D5Nf+0nX3StP47dOpd/d8enc99knTZZlb397dX/jdunH6cj/59vnUuyXv2wcR"
    "eIW+Xm5t7wtPy8Lrd2aJaj9Z4lgXprD85s2f/qt/8cf/9O/99z/43f/2499+s2iety/+pBfM/w1F8O6lGW9++Q1APk3BH6Tu2U/n"
    "Wn5liQZ6pAI//Cs/fJ17fUEWi+z/tWd40ZXPmcAeX0T/4vn50Y8WH92PfmR9c7LOjXt4fDX3Kyq8jM9T3NBzzHZZLq9UXubDIyN/"
    "ks+7uL6dBSj+ZLyL0LO8PPw8YXqR5lfSNP/wUZ7e3ZMTvVEWZfq0k202dd95lIq57NcXZkpQZ3GzOLaXgIOwdmfFeXnz8cN9WHT+"
    "QB7jxdY9Lu0uadzjly0l6d0XUX+I8Lt7mZ5HDP4wx5YyXzfl5SbgzX//L//X+y9/72f/8tf/+Cf/6c3D5/f9dukLn0MevQnFrGKK"
    "+ZnvwvnZLKcvX5YdP/eQ/GU1fhaD5UIbt3dJ+84iacVLty8Q4HGv4R/9s2Xt79Pl3mfpfvdBVoAPj4B89sO/MovkDz+9r3bN83DR"
    "jefHbZO1P8OW2n+2Pku2ju9+N/+kW7wisXe9PTSzvC/JbZ5OLvJx9w0/71vwH03gp9+FFvfcjI68dFkeKRZM/ElZ33EC85j7ccZE"
    "TxM9eLTZD3T39p6z8xExPUcHfpG+HrTPPwRKjg/utwdh7pt7OtMfNG1Rlv7lsze//LMv/9c//t1/PvfOy5j8ylPXvo1/UUd++nxH"
    "cY8i/ezN+x//vZ/95997/+Vv/vFP/uj9l7/2Bni8ALz52U/+6Z/85Pfe//jvfxitx7F6GvdZURWP/fwoaf+DXfx09KGHl1eqfLHk"
    "JHvuY2/pnL+wj4vXaOqzt7OdLx7tfPFs/e7VPhZ5xxttdDdE88mi+UFRLi8oar1v/urdp/fBc18G74tX6qlbCOgScG/P2vGtfY+W"
    "e/vULrK7xMXT5oIf/ejp5OCfr3H7+tKsEuynFyYsrXrJ9Tw3zV4CfWeR9z9sSP1QdfkMVL57X/f50KFPWnBuz9K6h+/aL/lrXzSi"
    "3d4jXJ6yJCymCPgEWi+x1k+paT+41rzlvvueBrXx4qf9RzOQeDnNu/NEnFXMY2auN81dM3qfBIs0+Ll3e9r1kD5cPgnnWxfNdM9+"
    "SN7rfbvy/+qymzJ+93x92fq97GiN3dRws9IsXt/9yXq93Dy3drX+y/3iuXygWF7UtJCYZbvEZfnx85f8vsQV5/dpttx195Pe97Td"
    "vxTl23sBc63okgv0s7f1WwyBHqCHuTnvHuq3CIHMh/M/+J6KpH5L4PhydbVZrq7gFTEfo/PlJ95+bl7z9gW9319Z2HzLgr14o+df"
    "fIAO9wk29+ojqFwk4BvE4Xvf+3m84dE38PLjc/PuYWnIQ//xavDidXjWT3Pd/ocNKPfJ/33/szf/7Tf/7nf++Df+/Z/8bz/+zp3J"
    "f+Aii31482m0rDY8EB/AbPS4gPvayXZfguruv/pBW7Ru+hJN93au4e2MaIE3755UVRO/8jUs7ft86au332jYUuu3PERZ+TRBH71D"
    "HxnYu4Q2rfZiZz9Ms/vMeQHm3yjTehqw58H6/Pz2KaLk/Ve/8/7rf/L+63/3/us/fP/VHy2fX//z++evv//yX73/8vff//jL91/9"
    "3++//jfvv/qXy8mv/vP7r//VcsOXv/dnX/3On/3uP3r/5b99/+XvvP/q15fPL//G+69+7f2Xv/pnP/4nf/LT/+P9l//6z376H+dC"
    "fva//D+ztn7/5f/7/sufvP/qH7552HzYD7x4Ee6N/wUg43vf+wUY4x4I9KhaZ83z2FtL5z2Ud4fT/1B5L5jlI9/QR0atiWfD//7r"
    "X733yq89Pugzrnjz/st/uHTM09P/7T/97b8126f3X/72vWP+9vsv//2f/uvf/dnv/RNVunfub715sfmtv0SjvJibjxTkF4vL6dmy"
    "3KXyG3bE/6Dp76h/Ht0PTfjX/+Fnf/f333/5j+/13xvyPAx//oe/dh+e2ZL+0c9+9e/8yT/66Z//4a+/eUDmsfmgtJ2Xl54/OgE/"
    "X0zNTBzupubT/IuPHYL3e+ZZOj4vdP0cqvy8agY9eg7nfwvz5V7I8OO3ZxZ8X1R4XAfsPw4revEzLg7GR7fTZ5/cd+Uv8duzAfv5"
    "rogXd6vv5/O4feNx3n3SRv48yPmzp/He3188asFDsWi2D9mfX/sQD8Uz67nf9eB/cw6O5Te8P89rwx+buvvruZ+Jcf7E1O8c9jFR"
    "5YvT+If3p3jskc/uffc/f84uDr270/aL7z124NO5R2DwxQ+f85ukL3aY3T35JD7U+soNsayjf1hWeIrwej0O6SeZ3zRu6L8Mx/O0"
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
