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
VERSION = "1.15.2"
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
    "xUK7Tx7T87//V5/S8wd3KZ8zj35xY57Sq4JF8P/yQ0RJCR5F+XXhluWBP0Kf9+3BD7tbnudjpmL2WTMDmGWD9RMllzdVzhx9v387"
    "QwE/n43VG7+fqfFKu79KJL6vHrnLvD5OxXP88OnMfUvSLPdLxuMXSy2kb7c/D6LIljDX0ksevv12++9+/g8fMrL/u4NbKmg98ll7"
    "/39JAbwfvPv8W2nir16l2t+DBHeee4wW3Of92wrkEXo8KYloKcw8P/SCsB/ly22aOFzKIzXvvmgXHr8P4TFS8Nnb58Pv3y++X5hn"
    "8cMejcfy9EX+kOf+6II+DGg1j2fx+xcB8tKi8V+x6Kul23te8+ez7dzNJmZx5u4jfv+4hP7uQd5mddDGwfTJ02zMI/zubCvOwX2C"
    "7ijttoTn31v3z/sQX7pow48dhAe1nT+p7fyhjN8SUsr8xVo0j67wQqe5/+frj9z8/vnEo9VCoKW6zHMrURy0b+9c0TZ/9RtZxqv1"
    "fOu3n3LJsAnv5VCXR1p4+htP9Hjj83a754yt6F5mcibdyxm34efjJQv6rkFeAjgA8L5Y9M2797NovrKOzV2MF6I9ivESi1hWVe8b"
    "VpplAu8HT4vgj18//ZWHgxme3inX3uMKj1P1kNQ3658X0b8/z+fffQLbS6j4/lBPXvYLqf5K/1Eo6pdXqA//6EePvsJzSPH+dC/B"
    "KP8lavDY8PvvPrkK75Zf35Xii369z3B9l7yHk4+DecpG+tGPuPwb8/T+o1d+W8FzIY1Xz/HEVc/x9G8Na1ZIzzG9p7jWt+M4L7e8"
    "etPWczxnjb0oXf6udNV6ybtadH1ffB96r7Sv1y7r+4S+aYa/sozidXTl1cg/e/O/vHlKXXn33nxcWf/Ezd0HH+Q+yfdI0aL6X03s"
    "+RvZF/WScfFLD1mwsylc1pueqk8vvL3IysI3j4sIsX958255Vep9f+nzouQvuHv6waxq7vc/NvzN+1/ShNV6ZsLvfe8VW93P/DLs"
    "o/eXWD5ghvu5pWbxk99iBvcVll95c1ks7ZuHiPoPHr4UQZDGuf/mV19718vollcEFfOAisdXIdxb/f5L17/EPxrDz+9by/z346f5"
    "+9YNP23fN0sc4dPmfX1f3HzfF4vKK36OKY7D9wgKvVZs6UeKbQbjz87/EPm1v5Du3qkyuw0Pp97dy+nd9dgnTZdlbj29u7/vu3Xj"
    "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"
    "Tntcj3pinQV4vbBO7ad3xnmg7OySKm/bZ6qg/pMJTYrXkRDvHgn5fD7pv7IUl/C52FtSvJuvPmyHeKToE4M8RQ7bB26/a/MPX88C"
    "/q8+fP2vP3z94w9f/b0//81Z8fztu2j/wZ/+5J/92e/8ps7cVc4i6/eDv3VXA7/9IO6vVPHc6gu6fGz6xx++/s2l6a/+4MPXs7n4"
    "ejmY2/j5Xf7rB6PxF3/0nx903V/80X/5r7/29z78+G9yY5kWtV9/B/wOvyRr1N+ZG3n81Y//1tzC3Rb9+3sLv3VXVXNr/8eiub78"
    "a7OqekzC/PI/fPjyDxfn4b/8uz//6R8v/S4P9Hc/fDW389MPX305dz3rvp/94R8uw1ga/IcPqvau2vBXz/o4qe9/AfH+2itl+dtL"
    "1OD9iljgwTKVzEN5p5d5E55etvecmsHUD3n0941Mnz/+4D2X3/fgviJ3sxRaXSqz5MvBUga3/ShU1HzS/jKCQjOyXhYN3PNSA8+7"
    "Vzc9ztfGd79M/JxLznxpmi+9dDwz1uuO59Of15/m75e4T/vpS3fvx0+fm38/PR87XzyN/JtKLXgEFt5SbbTO3hqf/fDDVzN++K2F"
    "Ub76ew/5rU+m/7c/fPk3/uKPfvqXnhNkP3z11ewMLte++usPd8zz/Dp9duHXZW7+yR18LJz1J//mn8wM8mf/8T/97G/8w3u7P51B"
    "xp2bZ/acbexf/9Of/Ifn/uY5//Djr354rwD03x3Wm0//B4b+IEsLrnmyr994gKW/d6/x25POWJYg7qmajxr4saTj2/w78WP9zyL4"
    "zlI16LFy3Cx5+bMWeQ2Xvugf0xhfVNW3wrZL948Y4QkZPHlj7+8R2xfdVi4z+A2b6KbpPWjwTVu47HNYUqwfRvVaQ/rex6HXxxXQ"
    "xyyFZen0OSh4X2Hq7x9/Ffps/vwUemknWkbzK2/uVeX9eh7/UjFp/vXj0RD5M8r41ecYxDygZyP/raUv//1jCPujdNIXZv/i/efl"
    "subU+0s1Cs8t5+H59+d+9/4Xt/rx2Pbps1P/7Tvv8OzN8yi+5bK88i1mLHDHPa8QzIuhuiccLZbrcRHhmxjG/4Wg5c4ZHztf/T1H"
    "9lVa5xfvYR959/6pyfL+sruHBv37/a/yaJ8rvt13c76svX3c7fuPF2o//8i0P4nuswlakOgSsvW/hSSet9jk3vc/v5cS+/TNslr5"
    "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"
    "CCupj/JEdwwc8HrTCF46a8I6ZKhv921u1FJxVUaklaLfZ5Nq2zl7YiM77AnqFHrodASUDRtysJyTccaMK6PSuak9w5zQN01PYoZM"
    "KULE3HU6lErdH4H+W++1vjSuZVuoBus13ZWgJTgGjlwcCdDdDdb8Au33EenHBJ5u7oI3UpScKtZxAlqYjM4gnNkeSX3TTkNwmZbd"
    "8ItUQSmGWq6sZ/Z3ffz+juzq7m/f3ks/1/M9rs2urQfQo5CSpr9B+EQX71y4Th0l62zHWUfvDeAlI88vkSB7RcOZrnQMnJFhE5pw"
    "rMvu5Bu/Zb46ub0v3FIeeMKhbml8dQ6KerKJjbGVO560yE/wr+/U0CS68/O3DZW0KPYdVWyhphPDW0k9QEr1kZDloWmxo49yFl5N"
    "Oe5kuNDykYY+77ZXZffLoBqVG31nze1D+yYi9leN0v6qUYa/qpPputkUrpvNTNfNZsJ1s8mum82k6+ag6iXcKPOTEI/0sTSdu2xY"
    "sehjhaohL+EjOtaHEg6kmarp4R/bY6/yHU7z3dj0j+d+Mcs1cHLSQw8fYTm4N8++uF1OdsvG8oeb4VOjDcv1lN2rniz6nD6g+JCz"
    "6C1RGMf+ouhB7Sxn5RWX27qTHj/R3PHOVsSraFBC/0p6Wbgu7Nt8yo0fGYV7viipYXrTN/HR9s7rv1JlpeMmFd994zxMHAOGyOql"
    "M2dcvQj7F29I4z/WLvxGVcmmj/uvqaDXzv7L3ddv7jz/YaVwdj/dF1vyZLFJeFEKue0C51bYX2yXB0CXwjOYbxzdxATOJaUCO/sv"
    "qG1ErMgbCcmXuaezeo7SlJdgYGTBPRXEWWxlItfUK5HmN8ikJ/ZQNmorRgkPQ9uoP81EoVUkTADFwRZmXYKX7TodSNfp6KtxnR6q"
    "nWAOthdncSHf6qbhWx0rDZqoM2gmVQZNU2PQTCsM5rt6gEKGykB4YXu5XETHYFkJBOEf5gMdtRJCwhBfV3U4nqIU5O6owAebfVyM"
    "SAiJk6a8S4E/m/dd/Hls49GGSmRmAJorbBZXy5CMgh6csq6N2WGglmPouwbUdI6SOj9JmZjhdB76IcQTgSlF/9BVdTj7NQ9hDSnt"
    "8wHKiBC6nCD6wPRMJSz3MVcg/KQTfchHZwMudtSrdcUQnXCb0f4qMXF11/OLosQBr1RBn7dm9I2Q/uyfnoFFpb91QHtLlTnAL5W0"
    "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"
    "+en47S//DxmSbmw="
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
