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
VERSION = "1.15.1"
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
MARK_ROLES = ("recv", "got", "done", "drop", "direct", "warn", "info")
DEFAULT_MARKS = [
    {"w": "受付済", "role": "recv"}, {"w": "受付完了", "role": "recv"},
    {"w": "動画有", "role": "info"}, {"w": "音声有", "role": "info"}, {"w": "動画のみ音声不要", "role": "info"},
    {"w": "PC持込", "role": "info"}, {"w": "Win持込", "role": "info"}, {"w": "Mac持込", "role": "info"}, {"w": "持込", "role": "info"},
    {"w": "Backup", "role": "info"},
    {"w": "持込リモプレ", "role": "info"}, {"w": "OP卓PC 発表者ツール", "role": "info"}, {"w": "発表者ツール", "role": "info"},
    {"w": "ミラーリング", "role": "info"}, {"w": "Mac PPT", "role": "info"}, {"w": "Mac Keynote", "role": "info"},
    {"w": "変更有", "role": "warn"}, {"w": "演者変更", "role": "warn"},
    {"w": "演題取り下げ", "role": "drop"}, {"w": "取り下げ", "role": "drop"}, {"w": "取下げ", "role": "drop"},
    {"w": "会場直", "role": "direct"},
    {"w": "会場取得", "role": "got"}, {"w": "取得済", "role": "got"}, {"w": "受取済", "role": "got"},
    {"w": "受け取り済", "role": "got"}, {"w": "DL済", "role": "got"}, {"w": "ダウンロード済", "role": "got"},
    {"w": "発表終了", "role": "done"}, {"w": "発表済", "role": "done"},
]
MARKS_V = 2                       # 目印の既定を増やしたら上げる（保存済みの設定にも新しい既定を足す）
MARKS_ADDED = {2: ["PC持込", "持込"]}
MARK_STATUS_ROLES = ("recv", "got", "done", "drop", "direct")   # 演者の状態を決める目印
MARK_CHIP_ROLES = ("direct", "warn", "info")                    # 演者の行にチップで出す目印
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


_MK_SEP = re.compile(r"[\s_\-\u2010-\u2015\u2212\u30fb.,\u3001\u3002()\[\]\u3010\u3011\u300c-\u300f\u3014\u3015]+")


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
             ("受け付", "受付"), ("受け取り", "受取"), ("受取り", "受取"), ("受け取", "受取"), ("取り下げ", "取下げ"))


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
            lab = sorted({(m[2], m[1]) for m in mk_add if m[0] in ("warn", "info")})
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
        ps = ("Add-Type -AssemblyName System.Windows.Forms;"
              "$f=New-Object System.Windows.Forms.Form -Property @{TopMost=$true;ShowInTaskbar=$false};"
              "$d=New-Object System.Windows.Forms.FolderBrowserDialog;"
              "$d.Description='%s（ネットワーク上のフォルダも選べます）';"
              "$d.ShowNewFolderButton=$%s;" % (title, "true" if dest else "false") +
              "[Console]::OutputEncoding=[System.Text.Encoding]::UTF8;"
              "if($d.ShowDialog($f) -eq [System.Windows.Forms.DialogResult]::OK){[Console]::Out.Write($d.SelectedPath)}")
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
        p = filedialog.askdirectory(title=title, mustexist=True)
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
                                                                   "marks": DEFAULT_MARKS},
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
    "+aOoe9tODYPKSjp9ukfyJODktcTwoolhRI3Lr1ZCylX03Bk69VrTPrxmqfD1Rn2PyVumzJc6+RSXKjMJh9GSOV12835RWSrVS++j"
    "jbKGKa1eLiKLecFcaTVELnx5Wv5JZraURYEpDlLL1QjLEE6VHjuGyoGSmlQkPDXPGKH01GHkZ7rgjF6UEaQtNFCdGKiGQKiTYWuG"
    "AEOFNRS2iqTMBiy0yUKAWT+5u1udWUFX5UQ1KuVjY5EZRecuQuk+NZdsIcjrb5Pg8T+Lf6bDx2P2O4ZnXfjv7p+z3d3dt4/HRrY5"
    "mhm7rJZljCUVUoecHqX3oR95Eka89duE/fff/tt8/w6rz1bKzAvrCb80gOoBh6iRNVJMr2rv5WxtPLEFu18L9TTgkRQy/1Z/C/L3"
    "pbfEXdVR2rIzOOrFOXI3RgFXPhdqBrc6Ub8x+6OnQ22TtQfeF9U+f+/J0RFvjgpEEE/sGFMQTr7LM9cUZGiipfMg9mWiikRouL+q"
    "kJ2gip3PVLFPcD6LS+6UkHEq8y+6jW8zPuMfYjhNV2F56ZRxk5RnlvMZPqA+XGE2fD4DVCqzZM5Jcux3qgnH9I54ce6Pib/of4nN"
    "7P9BjIIBQMvxhUMXFTY5jmPnYoLhVcEo0y952WruZMFiv0eOztjx0sSWWPrkJTARZn/0wu/jR56W3nbRQapdReKz92SrIJdx2W7L"
    "p+Rw937kCcrkPRrq0BogXgnnFGhkIahi5Q+oDuvFqNRYHqxJ74d4Y2Ar8devEdQ7bj2hbL1ppL4pjUssV2FuSb4VoXdSL5v6JEJD"
    "zy1Ho3es65ZNHXKiMKSSWvB5DPivIG58BHcHfKDet7ehrR3qkzmf9NBIPat0zyrVs1vZqa5Rtko1vGVnYR2ury9WdGbpnavTKviJ"
    "SyIWpYF3KjYeenPpkbd+WrHdUsfihVspYrdNXu0MWaT8EusUumOQBb5OdLS6dZApf5qUd9DBhIt4S5XVfnzwOEpPxF2nfgHGfszD"
    "UhWWFiFpUKFkBoCLRYWRSJBaW6akmPqZVWurdVLk8zG5MHBxZPiV6Jd+03ggsxkrBvIY5vRv9auB9NCuZVuM1cJGgCNga1y+jSYk"
    "Nir41ATRU5oKb+rX/7Sz6+pn3lqz2Ad3e9vctHe3q8Tu6PFueSKZG5yJP2JU396p0EjbDM2ilbeSaezbLx99w/Tuq50KH1vVj8z9"
    "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"
    "+X797dOpd7eyby8s8Ap9Pd/a3gNPt8DrdxaOaj+5ZbHeLIXbb9782T//p3/yj/72f/vD3/uvP/7dNzfJ8/bZn/SM+b8hCN49D+PN"
    "r74B9Mcl+IPUPfvp0suv3XKBHkyBH/6lH74iRr2Its9vvP/LT/BiofljIbCH99A/e35+9KObj+5HPzK+uViXwb1/eDP3K1P4Nj+P"
    "WUNPGdv87ct9PTxY5I/8eWfXt9btpRbjnYWe+OX9z2OmZ25+xU3LDx/46d29NtEb9SZMHzeyLaruOw9csbT9+sJiEtRZ3Nwc27d0"
    "g7B2F8F5efPxw70EnV+Mx/im6x5Cu7cq7vHzhpL07otoXvL77l6mpxmDX9bYvVzrq6E83wS8+W//+f/68OXv/+yf/eaf/OQ/vHn/"
    "+X27XfpszyEP3oRiETHF8sx35vxs4dPnL7f9PveE/Fs0fmGD24U2bu+c9p0bpxXPZL9BgIethn/8j2+xv09v9z5x97sXXgFeHgH5"
    "7Id/aWHJH356j3Yt6/AmG88PuyZrf4Ettf+kfW7FOr773fyT7uYVib3r9L5Z+P1W2+bx5I0/7r7hxwz32n9QgZ9+F7q55xZ05KW3"
    "8MjyrJ8Xn5T1HSewD6Ufb/taHxZ68KCz32+6t/eSnQ+I6Sk38Iv09aR9/pImOb53vz0JC23u1Ux/0LRFWfqXz9786s++/N/+5Pf+"
    "yUKd5zn5tUfSvo1/ESE/fbqjuOeQfvbmw4//9s/+0+9/+PK3/+Qnf/zhy994AzxcAN787Cf/6E9/8vsffvx3XmbrYa4e530RVMUD"
    "nR847X+SxI9HLxS+vVHli1tJsicadwtxuv8ujYvXaOqzt4ueLx70fPGk/e7dPjR5xxttdFdEy8mi+UFR3t5PxLrf/NW7T++T5z5P"
    "3hevxNP55na/pdsri3R8q9xz5d4+jovqLnHxuLVgkU0PJwf/fI3b15cWkaA8vi/hNqrnUs/L0JRbmu/C8v7LftRXHv/nkr73uM8L"
    "QR+l4DKe890zrjyXr33ZWNbeM1weiyTcVBHwCbS+ZVo/VqZ9ca11t/vuOxq0xosfdx+9ex89nxbcZSG+++XuoTDXm+YuGbtPghs3"
    "+Lk3Pe55SN9Hn4TLrTfJdC9+SN37fbvy//JtL2X87un6bef3bUNr7Kamm5VW8fruT9br283LaFfr/7FfPLUPFLf3NN2MmNtmiej2"
    "46cv+T3EFef3ZXa76+4nve9ou38pyrf3BpZe0WXt+p+9bd7iCPQeer8MZ0F5bxESWQ6Xf/C9EknzliSI29UVdru6glfkcowulx/t"
    "9qB5bbff0PttHoPmWxrs2Ru9/OIFOtwX2ELVB1B544BvGA7f+97PsxsefAPPPw6ad+9vA3k/fRwN1l/eSfrF0rf/sv3kvvi/73/2"
    "5r/+9t/6zp/81r/90//9x9+5W/IvtshNP7z5VLxFG96TL2BWDL7/0S7DpxBUd//VD9qiddPnXLq3Sw9vF0QLvHn3KKro9JWv4Ta+"
    "z2+0evuNgd16/ZaH6Bw8LtAH79BHCvbOoU2rP+vZl2V2XznPwPwbbcaPE/Y0WZ8rbx8zSj589a8+fP0PP3z9bz58/Ucfvvrj2+fX"
    "/+T++ZsfvvznH778gw8//vLDV//3h6//5Yev/tnt5Ff/6cPX//x2w5e//+df/as//72//+HLf/3hy3/14avfvH1++Vc/fPUbH778"
    "9T//8T/805/+nx++/Bd//tN/vzTys//1/1mk9Ycv/98PX/7kw1d/78177GU38M2LcB/8LwAZ3/veL8AY90SgB9G6SJ4Hat2I956/"
    "O5z+p9p7xiwf+YY+Umr0ome+8+HrX79T5TceHvQJV7z58OXfuxHm8en/xp/97l9f9NOHL3/3Tpi/8eHLf/tn/+L3fvb7/1CT78T9"
    "nTfPOr/1b9koz+rmIwH5xc3l9KRZ7lz5DT3iv0j6h9cJv33zMoR/8e9+9rf+4MOX/+De/30gT9PwF3/0G/fpWTTpH//s1//mn/79"
    "n/7FH/3mm/fIMjevUtqfa7U8OAE/v6maxXC4q5pP8y8+dgje73n3/tEX/v7nmspPUTPowXO4/LtZvvyzMfzw7ckKvgcVHuKA08dp"
    "Rc9+xpuD8cHt9Nkn9035t+ztRYH9fFfEs7vV9/Nl3r7xOO8+aSM/f/sD/8nTeKf3Fw9ScCzuku157374yoc4Fs+7Yop7qPCba3Af"
    "fMP78xQb/ljV3d/O/WQY54+W+t2GvW+Sa56dxj+8P8UDRT670+6XPt/dHHp3p+0X33sg4OO5B2DwxQ+fypukz3qY2z76JF56feWG"
    "uMXRX8IKjxler+ch/STzm8YN/efpeFrW/2ON3/1q/Pebb07u7bXtN0JCL0LtdWXhm4x8FX/9OTGkGwT6/G286Mvaji+3/UIrBIK+"
    "7b15dE49xXihn9cd+xiPemKdG/B6YZ3aT++M80DZxSRV3rbPVEH9JxXaF689Ie7dE/L5ctJ/pSm68LnYW1+8W64+bId4pOgTgzx5"
    "DtsHbr9L8w9fLwv8X374+l9/+PrHH776u3/+W4vg+Vv3pf0Hf/qTf/pnv/tbOnMXObe1fj/4m3cx8DsPy/2VKF5afUGXj03/+MPX"
    "v3Vr+qs/+PD1oi6+vh0sbfz8Lv/1g9L4iz/6zw+y7i/+6L/811//ux9+/De4sUyL2q+/A36HvyVr1N9ZGnn81Y//5tLCXRf9+3sL"
    "v30XVUtr/8dNcn35VxdR9ZiE+eV/+PDlH96Mh//y7/78p3986/f2QH/nw1dLOz/98NWXS9eL7PvZH/7hbRi3Bv/Bg6i9izb81bM+"
    "Tur7X0C8v/pKWP7OzWvwfkXc4MFtKtWH8k4v82Y8vWzvOTVDrR/y6O8bmT5//MF7Lr/vwX1F7uZWaPVWmSW/HdzK4LYfuYqaT9pf"
    "QVBoQda3oIF7vtXA8+7VTY/LtfHdrxA/55KzXJqWSy8dL4z1uuPl9Of1p/n7m9+n/fSlu/fjp8/Nv5+ej50vnkb+TaHmPQIL71Zt"
    "tM7eGp/98MNXC3747RujfPV3H/Jbn1T/73z48q//xR/99C89J8h++OqrxRi8Xfvqrz3csczz6/TZG7/e5uYf38HHjbP+5N/844VB"
    "/uw//qef/fV/cG/3pwvIuHPzwp6Ljv1rf/qT//Dc3zLnH3781Q/vFYD+u8N68+n/wNAf1tIN1zzp1288wK2/d6/x25PMuIUg7qma"
    "jxL4saTj2wWcPdb/LILv3KoGPVaOW1Ze/ixFXsOlL6bHNMYXUfUtt+2t+0eM8IQMnqyx93eP7atQ/m0Gv6ET3TS9Ow2+qQtv+xxu"
    "KdYPo3otIX/Qfex6fYyAPmYp3EKnz07Be4Spv3/8Feiz5fNT6KWd4DaaX31zryrv18v4bxWTll8/Hg2Rv6CMX3v2QSwDelby3wp9"
    "+e8fXdgfpZO+MPsX7z8vbzGn3r9Vo/Dcchmef3/ud+9/casfj+2cPhv1377zDs/ePI/iWybLK9tiwQJ33PMKwbwoqnvC0U1zPQYR"
    "volh/F8IWu6c8bHxNd1zZF+ldX7xHvaRd++fmizvL7t7aNC/3/8qj/a54tt9N+dL7O3jbt9/HKj9/CPV/rR0n1XQDYneXLb+t5DE"
    "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"
    "CeivE6/MM6ihdJPrt1o+i83DcuQOhaW8hOVQfe+MK0Y2cmMiQj+sDUnlblTW20yuj+OdpNxQOBySh1RVc5ByXGnudNyUg9SpfThI"
    "nRUi/5l8XszJ1IBcIEj5Sbe0yGY3Khw8n0raee3A1tmKVD2UNIl9B2Pykw5Yp8hj6pThgIWju5XnYdRdsOI77IMF11lOWKrKL9sJ"
    "a6wPFoiASa+pM67d7ozzm2p37tFx6oxLUP4dAtRM0OcZleOrcK8eVScmsd9K2EtNCGe+TGvzibR7FrUW0ejce3O3Qt256W7luLZe"
    "8wr5fwH14pJgaPp1isCBcalFnJNsRO+iyVSmXJuRy0yoUIW/F+xQsO9q7l64IUtr1CkMGtIctqIB2ivhVIUDxlYbyinl6iWOZfS1"
    "lntZjVT6nTqeKmKDEUdy3GnU3Y8s1UE9F/pjN9E+0zAKuGEGzt5SeVWDRl0twirsbeb7ncLwOO0RMhOt66SnQXG9tjOJzn69Ze3b"
    "xeKeRCS5NULL0FBU0GUmeQ/q6H9ZiwZhJfVRnupMgANeaxjBS+dNWIcM9e2BraVKKq7KiLRS+/f5pNp21Z5ayg57gjqFHjodAWXD"
    "guxXR2ScMePKqHRhpKp3ROibpicxQ6bURsTcdTqUSt0fg/5b6za/MK5lS6gGaxXdlaApOAaOXBwL0N0JNvwcrfcx6ccEnu5IgjdS"
    "lJzM13ACmpiMztg4sz2SeqadhuAycRjyVEEhhlourWf2d33y/o7t6t7v3txPP9dHe1ybXWsH0KOQUsC+TvhEl+5cvE4dJets2xmg"
    "9wbwkpHnF0iQfVrDmS61DZyRYROacKzL7uTrv2O+Orm8L95SHnjCoW5lcnUOinqyid2JlTuetMhP8a/vVNAkuvvzNw2VtCj2HVVs"
    "saJvhreSeoCU6iMhy0eDfOzoo5yFN1OOOxkutHykoc+77ZXZ/TIoR8V6z9lwe9C+qYj9VaO0v2qU4a/qZLpu1oXrZj3TdbOecN2s"
    "s+tmPem62S97CTfKYY5cE/pYms5dNlAs+lihashL+IhO9KGEA2mmanr4x/bZq9EOp6Pd2PSPj/xilmvg9LSHHj7CcnBvnn1xu5zs"
    "lk3kDzfPp0YLyHXJbpTP5H1OH5A/6Sx7KxTGcTAvelA5z1l5xeWO7qTHTzR3vPMl8SoalNC/kl4WrgsHtp5w40dG4a4vSmqY3vRN"
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
const MKROLES=[["recv","受付済にする"],["got","会場取得済にする"],["done","発表終了にする"],["drop","取り下げ（数に入れない）"],["direct","会場直（未受付にしない）"],["warn","注意（黄色のチップ）"],["info","チップで表示するだけ"]];
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
