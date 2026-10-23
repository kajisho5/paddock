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
    "vbu/77t14/Tlfv3t86l3S9m3DyzwCn293NreF56WhdfvzBzVfrJksS6ewvKbN3/2L/7Zn/zjv/Pf/vD3/uuPf+fNonnevsSTXjD/"
    "NxTBu5dhvPmVN4D+JII/SN2zn869/OqSC/ToCvzwL/3wFTHiBVksvP9Lz/BipvlTIbDH99C/RH5+9KMlRvejHxnfFNZ5cA+Pb+Z+"
    "5Qov8/OUNfScsS0uX+7y8OiRP/HnnV3fmstLLcY7Cz3zy8PPY6YXbn7FTfMPH/np3b020Rt1UaZPG9lmU/edR66Y2359YXYJ6ixu"
    "lsD2km4Q1u6sOC9vPn64D4vOH5zHeLF1j0u7SxX3+GVDSXqPRTQf8vvuUabnGYM/yNi9EP6robzcBLz5b//5/3r/5e//7J//xp/8"
    "5D+8efj8vt0uffHnkMdoQjGrmGJ+5jtzfjbz6cuXZb/PPSF/WY2f2WC50MbtndO+s3Ba8UL2BQI8bjX843+yrP19utz7zN3vPvAK"
    "8OERkM9++Jdmlvzhp/fVrlkOF914ftw1WfszbKn9Z+uzFOv47nfzT7olKhJ71+mhmfl9qW3zdHLhj3ts+CnDvfYfTeCn34WW8NyM"
    "jrx0WR6Zn/Xz4pOyvuME9rH044yJngQ9eLTZD3+5e3sv2fmImJ5zA79IX0/a5x/SJMcH99uTMNPmXs30B01blKV/+ezNr/zsy//t"
    "T37vn87UeZmTX30i7dv4FxHy0+c7insO6Wdv3v/47/zsP/3++y9/609+8sfvv/z1N8DjBeDNz37yj//0J7///sd/98NsPc7V87yH"
    "b4tHOj9y2v8kiZ+OPlB4eaPKF0tJsmcadzNxuv8ujYvXaOqzt7OdLx7tfPFs/e7dPjZ5xxttdDdE88mi+UFRLu8n0txv/urdp/fJ"
    "c18m74tX6mm/hN2XdHtl1o5vlXuu3NuncVHdJS6ethbMuunx5OCfr3H7+tIC3J7el7CM6qXU8zw0ZUnznVne/7Af9VWA/KWk733d"
    "5wNBn7TgPJ79PTKuvJSv/bCxrL1nuDwVSVhMEfAJtF4yrZ8q034IrXXLffcdDVrjxU+7j949RC+nBXcWxHe/1D0W5nrT3DVj90mw"
    "cIOfe9PTnof0IfoknG9dNNO9+CF17/ftyv8ry17K+N3z9WXn97KhNXZT081Kq3h99yfr9XLzPNrV+n/sF8/tA8XynqbFiVk2S0TL"
    "j5+/5Pclrji/i9ly1z1Oet/Rdv9SlG/vDcy9orPs+p+9bd7iCPQAPczDmVHeW4RE5sP5H3yvRNK8JQliubrClqsreEXOx+h8+clv"
    "L5vXfvuC3pd5XAJC37BgL9Ho+RcfoMNdwGaqPoLKhQO+4Th873s/z294jA28/Hh5pc8ykIf+49Xg7Yd3kn4x9+1/2H5yF/7v+5+9"
    "+a+/9be/8ye/+W//9H//8XfunvwHX2SxD28+3S+rDQ/kBzC7D77/0S7D5yWo7v6rH7RF66YvuXRv5x7ezogWePPuSVVJ6esqpkvM"
    "Z6HV228MbOn1WxEiOXgS0Mfo0EcG9s6hTau/2NkPYnaXnBdg/o023acJe56sz5W3Txkl77/63fdf/6P3X/+b91//0fuv/nj5/Pqf"
    "3j9/4/2X/+L9l3/w/sdfvv/q/37/9b96/9U/X05+9Z/ef/0vlhu+/P0//+p3//z3/sH7L//1+y9/9/1Xv7F8fvnX3n/16++//LU/"
    "//E/+tOf/p/vv/yXf/7Tfz838rP/9f+ZtfX7L//f91/+5P1Xf//NA/ZhN/ASRbgP/heAjO997xdgjHsi0KNqnTXPI7UW4j2I94DT"
    "/1R7L5jlo9jQR0ZNmu3Md95//Wt3qvz644M+44o377/8+wthnp7+b/7Z7/yN2T69//J37oT5m++//Ld/9i9/72e//480+U7c337z"
    "YvNbf8lGeTE3HynIL5aQ07NluXPlN+yI/0HTP75O+O2bD0P4l//uZ3/7D95/+Q/v/d8H8jwNf/FHv36fntmS/vHPfu1v/ek/+Olf"
    "/NFvvHlA5rl5VUv5pVbLYxDw88XUzI7D3dR8mn/xcUDwfs+7h6dY+MPPdZWfV82gx8jh/G/xfPkXZ/jx27MXfF9UeFwH7D9OK3qJ"
    "My4Bxsew02ef3DflL9nbswH7+aGIl3Cr7+fzvH3jcd590kZ+/vYH/nOk8U7vLx614FQsmu3D3t3XMcSpePZ67nc9+N+UQSP4RvTn"
    "eW34Y1N3fzv3s2OcP3nqdx/2vkmueQka//D+FI8U+exOu7/8+W4J6N2Dtl9875GAT+cegcEXP3wub5K+2GFu+xST+NDrqzDEso7+"
    "YVnhKcPr9Tykn2R+07ih/zIdz2L9P9b4Pa7Gf7/55uTeX9tePDHJY8OvKwsvOvLV+uvPWUNaINDnb+PZXtZ2fFn2C60QCPp29OYp"
    "OPW8xgv9vO60p/WoZ9ZZgNcH1qn99M44j5SdXVLlbftCFdR/NqFJ8ToS4t0jIZ/PJ/1XluISvhR7S4p389XH7RBPFH1mkOfIYfvI"
    "7Xdt/v7rWcD/1fuv//X7r3/8/qu/9+e/OSuev30X7T/405/8sz/7nd/UmbvKWWT9fvC37mrgtx/F/ZUqnlv9gC6fmv7x+69/c2n6"
    "qz94//VsLr5eDuY2fn6X//rRaPzFH/3nR133F3/0X/7rr/299z/+m9xYpkXt198Bv8MvyRr1d+ZGnn714781t3C3Rf/+3sJv3VXV"
    "3Nr/sWiuL//arKqekjC//A/vv/zDxXn4L//uz3/6x0u/ywP93fdfze389P1XX85dz7rvZ3/4h8swlgb/4aOqvas2/NWzPk3qwy8g"
    "3l97pSx/e4kaPKyIBR4sU3l9LO/0Kqf/+WV7L6kZ1/oxj/6+kenzpx88cPl9D+4rcjdLodWlMku+HCxlcNuPQkXNJ+0vIyg0I+tl"
    "0cA9LzXwvHt10+N8bXz3y8TPueTMl6b50oeOZ8Z63fF8+vP60/xhifu0n37o7mH89KX5h+nl2PnieeTfVGrBE7DwlmqjdfbW+OyH"
    "77+a8cNvLYzy1d97zG99Nv2//f7Lv/EXf/TTv/SSIPv+q69mZ3C59tVff7xjnufX6bMLvy5z80/u4GPhrD/5N/9kZpA/+4//6Wd/"
    "4x/e2/3pDDLu3Dyz52xj//qf/uQ/vPQ3z/n7H3/1w3sFoP/usN58+j8w9EdZWnDNs339xgMs/b17jd+edcayBHFP1XzSwE8lHd/m"
    "34mf6n8WwXeWqkFPleNmyctftMhruPRF/5TG+EFVfStsu3T/hBGekcGzN/Zwj9h+0G3lMoPfsIlumt6DBt+0hcs+hyXF+nFUrzWk"
    "730cen1aAX3KUliWTl+CgvcVpv7+8Vehz+bPT6EP7UTLaH7lzb2qvF/P418qJs2/fjoaIn9GGb/6EoOYB/Ri5L+19OU/PIWwP0on"
    "/cDsXzx8Xi5rTr2/VKPw3HIenn9/7ncPv7jVj8e2T1+c+m/feYdnb15G8S2X5ZVvMWOBO+55hWA+GKp7wtFiuZ4WEb6JYfxfCFru"
    "nPGx89Xfc2RfpXV+8QD7yLuH5ybL+8vuHhv07/e/yqN9qfh23835Ye3t424fPl6o/fwj0/4sui8maEGiS8jW/xaSeNlik3vf//xe"
    "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"
    "CKNN"
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
