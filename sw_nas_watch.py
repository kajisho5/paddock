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
VERSION = "1.15.0"
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
    "L7Ppqbuf9H6i7f6lvLy9FwBrJeDajT57W79d4tgD9gCbA1HeW5zG4Uf43+KeiaR+S1PUdHdGTndnixkNPxPw9hNvj+vXvH1C79M8"
    "xvW3LNiLNxr+4gN0uC8wOKqPoHKSgG8Qh+9972fxhkffwMuP4/rdw9SQh/Hj3WDzwztJv4B1Rx+On9wX//ejz9788W/9ne/8yW/+"
    "+z/933/0nTuT/8BFJvvw5tPNtNvwQH8As5v4+x+dMnzegmrvv/rVpmz8/CWW7i2s4S1EtMibd0+qyshf+Rqm9n0+jdXbbzRsqvVb"
    "HiIpflqgj96hjwzsXULrxnyxsx+W2X3lvADzb5SZPk3Y82R9Lr99iih5/9W/ef/1P37/9b97//Ufvv/qj6a/X/+z+9/feP/lv3z/"
    "5e+//9GX77/6v99//a/ff/Uvpotf/Zf3X//L6YEvf+/Pv/o3f/67//D9l//2/Zf/5v1XvzH9/fKvv//q199/+Wt//qN//Kc/+T/f"
    "f/mv/vwn/xEW8tP/9f+B2vr9l//v+y9//P6rf/DmgfxwGnjyItwb/3NAxve+93Mwxj0Q6FG1Qs3zOFrT4D3Yd4fT/1R5L5jlI9/Q"
    "R0bNgHbmO++//rX7qPz6Y0efccWb91/+g2lgnnr/t/7sd/4mtE/vv/yd+8D8rfdf/vs/+1e/+9Pf+8eGeh/c337zYvObaIpGeTE3"
    "HynILyaX07NluUvlN+xI9EHTP75O+O2bD034V//hp3/n999/+Y/u9d8b8jwNf/GHv36fHmhJ/+inv/a3//Qf/uQv/vA33jzgcG5e"
    "hbS/5Gp5dAJ+PpkaSBzupubT4ouPHYL3Z949PPnCH34mVX7eNcMePYfwv4n5Ci9k+PHbMwu+byo87gOOH4cVvfgZJwfjo9vps0/u"
    "h/Kn6G1owH62K+LF3RpFBZy3b3Tn3SfNMSreXqNnT+N9vL941IJDeddsL2f3k1c+xKF8ORVT3rcKv7kG1fgb3p/nveGPTd397dzP"
    "xLh4Yup3Dns/JFe/OI1/cO/F44h8dh+7X/h8PTn07k7bL773OIBP1x6BwRc/eE5vkr/YYV578kl8qPWVG2LaR/+wrfAU4fV6HvJP"
    "zlFd+0n0Mh3Py/p/rPC7X034fv3NyZ1e2z4NJPZBqb3OLDzpyFf7rz9jD2mCQJ+/TaG9rLZpOJ0XmuEY9m3vzZNz6nmPF/tZ1WlP"
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
