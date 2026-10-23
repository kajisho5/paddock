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
VERSION = "1.16.0"
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
    "7nLsk6bLMree3t3P+27dOH1+X3/7dOvdLe3bCwu8Ql/Pr7b3hafbwut3Fo5qP7lFsd4shdtv3vzZP/+nf/KP/vZ/+8Pf+68//t03"
    "N8nz9tmf9Iz5vyEI3j03482vvgH0xyn4g9Q9++lSy6/dYoEeTIEf/qUfviJGd0MWN97/5Sd4sdD8MRHYwzn0z56fH/3o5qP70Y+M"
    "b07WpXHvH07mfmUK38bnMWroKWJ7f/tynw8PFvkjf97Z9e35dqjFeGehJ355//OY6ZmbX3HT8sMHfnp3z030Rr0J08eNbIuq+84D"
    "Vyxlv36wmAR1Fjc3x/Yt3CCs3UVwXt583LmXRecX4zG+6bqHpd1bFvf4eUNJevdFNC/xfXcv09OIwS9z7Fbm66Y8vwS8+W//+f/6"
    "8OXv/+yf/eaf/OQ/vHn/+X27XfpszyEP3oRiETHF0uc7c3628Onzl9t+n3tA/m01fmGD24M2bu+c9p0bpxXPZL9BgIethn/8j29r"
    "f5/e3n3i7ncvvAK8dAH57Id/aWHJH356X+1a5uFNNp4fdk3W/gJbav9J+9ySdXz3u/kn3c0rEnvX6X2z8Pstt83jzRt/3H3DjxHu"
    "tf+gAj/9LnRzzy3oyEtvyyNLXz8vPinrO05gH1I/LpjocaIHDzr7ve+9vafsfEBMT7GBX6SvB+3zlzDJ8b377UFYaHPPZvqDpi3K"
    "0r989uZXf/bl//Ynv/dPFuo8j8mvPZL2bfyLCPnp0xvFPYb0szcffvy3f/affv/Dl7/9Jz/54w9f/sYb4OEB8OZnP/lHf/qT3//w"
    "47/zMloPY/U47ougKh7o/MBp/5Mkfrx6ofDtRJUvbinJnmjcLcTp/rs0Ll6jqc/eLnq+eNDzxZP2u1f7UOQdb7TRXREtN4vmB0V5"
    "O59Icb/5q3ef3gfPfR68L16JJ+Pmdr+F28+LdHw732Pl3j62i+oucfG4tWCRTQ83B/98jdvXj27A7fG8hFurnlM9L02bb2G+C8v7"
    "L/tRX3n8n1P63td9Xgj6KAWX9hh3z/j8nL72WSLO7T3C5TFJwk0VAZ9A61uk9WNm2hfXWnd7776jQWu8+HH30bv35fNtwV0m4rtf"
    "7h4Sc71p7pKx+yS4cYOfe9Pjnof0fflJuLx6k0z35IfUvd63K/8v3/ZSxu+ent92ft82tMZuarpZaRWv3/5kvb69vLR2tf4f+8VT"
    "+UBxO6fpZsTcNkuUtx8/fcnvS1xxfp9mt7fuftL7jrb7l6J8ey9gqRVd5q7/2dvmLY5A76H3S3MWlPcWIZHlcvkH3zORNG9Jgrg9"
    "XWG3pyt4RS7X6PL40W6Pmtd2+w2938Yxar6lwZ690csvXqDDfYItVH0AlTcO+Ibh8L3v/Ty74cE38PzjqHn3/taQ9/3Hq8H0y5mk"
    "Xyx1+y/bT+6T//v+Z2/+62//re/8yW/92z/933/8nbsl/2KL3PTDm0/l22rDe/IFzMrB9z/aZfi0BNXdf/WDtmjd9DmW7u1Sw9sF"
    "0QJv3j2Kqjl9ncX05vO50ertNxp2q/VbHiIjeJygD96hjxTsnUObVn/Wsy/T7D5znoH5N8q8PA7Y02B9Lr19jCj58NW/+vD1P/zw"
    "9b/58PUfffjqj2+fX/+T++dvfvjyn3/48g8+/PjLD1/93x++/pcfvvpnt5tf/acPX//z2wtf/v6ff/Wv/vz3/v6HL//1hy//1Yev"
    "fvP2+eVf/fDVb3z48tf//Mf/8E9/+n9++PJf/PlP//1SyM/+1/9nkdYfvvx/P3z5kw9f/b0377GX3cA3L8K98b8AZHzve78AY9wD"
    "gR5E6yJ5Hqh1I977/d3h9D9V3jNm+cg39JFSmxc9850PX//6nSq/8dDRJ1zx5sOXf+9GmMfe/40/+92/vuinD1/+7p0wf+PDl//2"
    "z/7F7/3s9/+hJt+J+ztvnnV+69+iUZ7VzUcC8ouby+lJs9y58pu6+kXSPxwn/PbNSxP+xb/72d/6gw9f/oN7/feGPA3DX/zRb9yH"
    "Z9Gkf/yzX/+bf/r3f/oXf/Sbb94jy9i8OjvhOVfLgxPw85uqWQyHu6r5NP/iY4fg/Z2lQeHTQtfPMZWfVs2gB8/h8u9m+fLPxvDD"
    "tycr+L6o8LAO2H8cVvTsZ7w5GB/cTp99ct+Uf4veXhTYz3dFPLtbfT9fxu0b3Xn3SRv5+dsf+E+exju9v3iQgkNxk2wvqyCvfYhD"
    "8Rw+UNyXCr85B+3gG96fp7Xhj1Xd/XTuJ8M4f7TU7zbsfZNc8+w0/uG9Fw8U+exOu1/6fHdz6N2dtl9874GAj/cegMEXP3xKb5I+"
    "62Fu++iTeKn1lRvito7+sqzwGOH1ehzSTzK/adzQfx6Op2n9P1b43a/Gf7/55uDejm2/ERJ6EWqvmFK4ychX668/Zw3pBoE+fxsv"
    "+rK248ttv9AKgaBve28enVNPa7zQz6tOeVyPemKdG/B6YZ3aT++M80DZxSSV3rbPVEH9JxV6LV57QsoH3/Ry03+lKaLwOdnbtXi3"
    "PH3YDvFI0ScGefIctg/cfpfmH75eJvi//PD1v/7w9Y8/fPV3//y3FsHzt+5T+w/+9Cf/9M9+97d05i5ybnP9fvE372Lgdx6m+ytR"
    "vJT6gi4fi/7xh69/61b0V3/w4etFXXx9u1jK+PlV/usHpfEXf/SfH2TdX/zRf/mvv/53P/z4b3BjmRa1X38H/A5/C9aov7MU8vir"
    "H//NpYS7Lvr39xJ++y6qltL+j5vk+vKvLqLqMQjzy//w4cs/vBkP/+Xf/flP//hW761Df+fDV0s5P/3w1ZdL1Yvs+9kf/uGtGbcC"
    "/8GDqL2LNvxVXx8H9f0vIN5ffSUsf+fmNXi/Im7w4DaU6kN6p1cx/U9n6j2HZqj1Qxz9fSPT548/eM/l9z24r8jd3BKt3jKz5LeL"
    "Wxrc9iNXUfNJ+ysICt1gfht94p5vOfC8e3bT4/JsfPcrxM955CyPpuXRS8ULY72ueLn9ef1p/v7m92k/fanu/fjpc/Hvp+dr54un"
    "ln9TqGWPwMK7ZRuts7fGZz/88NWCH377xihf/d2H+NYn1f87H77863/xRz/9S88Bsh+++moxBm/PvvprD28s4/w6fPbGr7ex+cd3"
    "8HHjrD/5N/94YZA/+4//6Wd//R/cy/3pAjLu3Lyw56Jj/9qf/uQ/PNe3jPmHH3/1w3sGoP9us958+j/Q9Ie5dMM1T/r1Gx241ffu"
    "NX57khm3JYh7qOajBH5M6fg2/078mP+zCL5zyxr0mDlumXn5sxR5DZe+6B/DGF9E1bfctrfqHzHCEzJ4ssbe3z22L7ItvI3gN3Si"
    "m6Z3p8E3daF/k23+U6teS8jc+9j1+rgC+hilcFs6fXYK3leY+vvHX4E+Wz4/hV6dS3Vrza++uWeV9+ul/beMScuvH6+GyF9Qxq89"
    "+yCWBj0r+W8tffnvH13YH4WTvjD7F+8/L29rTr1/y0bhueXSPP/e73fvf3GpH7fNSJ+N+m+/eYdnb55b8S2T5ZVtsWCBO+55hWBe"
    "FNU94OimuR4XEb6JYfxfCFrunPGx8dXfY2RfhXV+8R72kXfvn4os74fdPRTo399/FUf7nPHtvpvzZe3t42rff7xQ+/lHqv1p6j6r"
    "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"
    "KR47h6zUyxbn6x4ojfXWL8/RvmykBbIT3WLZTB4nJD6S7U5Cvkrra2Pts80Zm+ZYBCJsXi/KaT8XvC+vOALo7b3PQOl4jVbMQXB1"
    "p7qu7emAH0HQv4oadx5SlzIvlLQ+dX4CbSTVV1bIYiKTwjU+sQwLK2p9FQMAdpOtwE5utebFsbnQKHyxJVXog15sDCQB0xojecwy"
    "Oe84GfWUurwq+42a5/lhkZXnRj8bhevGsEvZQ70xC0XxywUh+vaW2x0Ndz6y8cnkwBzIMWLy+1URkhc55D2TjiDfrowo1SSVNY4T"
    "dKj0Q1OtU6FsWb2gitBfrGAhW63NA29BPns8L9IxIOh1NmHrzaTt9/v7lpnd/qCZMso4kvT9+wkYfnlPmPL/15acpH21JecSHvij"
    "PRLA+cQ4pGRc0+i0dIqWsAV58rRx8NZQacL8wVzx8LZrNnK7G+yqwlcN0ncoHuz2BneQF2Sy24g+s4O4/TULdqfsNCszrMOBPwu7"
    "neSlymmxKoJ2xqc87eEahnMdwJc/cLSYBYlnnSOrx6IxZIDQKdMtR1/7DZZRu0jP8cths+kLtXSOKX+VFxSwoaJdpVb1hiYOfNfz"
    "K6fYTdfD2lzGXRIq9siT0KbQulGO8fB6oDMJAOWrFeFYMx9Ohi3gu9wx5X0WmPiumLHL9qCvfaGsHSeI5JwmziEFN/DJPzbnHGPP"
    "IG0DR0clDyK8FLYexircIhN7PZTmrm44L2GnxoNZQFgzprmT5vq4ZqTtSKEMJR+qWDbymVDpisVzBm38rXfY65uyBmAxKJJLrzjn"
    "yKNyMjfHms3DfL0PYU64EIvRCXa5K5O7rMKMXbHCcE1I1VA67LqqcK/2JsigwoxSN4mQq2XrBk6s9vwWThZzgdkaG6dWr8fVQciP"
    "tBUjM7guErefbSJNgXCiOpwPjjtKEhAJu5oXkJH7KoRTgdzsgfI6h+EldQ4aWW08iq/MHie9udKP+fpYqiAJSf61Rg+HmPQ3JQfO"
    "i2jf0qztDBWp7jbXdhZPzYIEqd28W0aAYvEEAU1gByrVLgMX7RHu6xZIG7EsXUYaL3VI1myvB3gWrlg83BVg2FIUMLUIKRGmSHqV"
    "HMY6AFxwSh2usSRZ+NB3+2pYY8GMn85NFGdapeyHjZPml2EihWnecPhqsYTQyi4Va7gmeSGaOkHI5y0oy7MdW8XG4fB1mp/J4ND3"
    "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"
    "CzbpwvhrQ7qJTn4QJiI9XI6CvSx2GsjKRGBYm9WD3jgzqS3IDo1F2WmNSNDZmCOwcYRhWRSGdAef6w/gWiYcgLfKjI2RbDrXe9q2"
    "KGW57IZp5D/Vp6hIUcNU8ZOVU71Mmv4zcyVjMOUHXiAmFbZ7jE9gSpEMMl2zaXTw8V2aWxa0epNfFvEpqIROJjXQGfIyRVnNxSTg"
    "9zw6uZQ9vgnFBYeMjmACEjEc1WdyKEFlFmjp+nXlnD92+Zy/1X4jEsFaAm2/xqw6n27haJXLVU6DPBzqdLAiJvLyU7ef8bRtQSjx"
    "ejQ4v5zvC8CRrJqVyK48bluZGIimldr43c9IAS04GZ+JuwJDQDmHVyor/oKk5F+sQvxgxb0Zt0x+1qvfb+o+vsoZNso56WoQ3lNi"
    "naXFYGchiVQZJdaZJ3buAqCxgc0unOn6bDk0ZMN4QS9eOFHKEGinxDdz2OHAXphpgyjE6LzUhSSITEIxqsR0sNgPe+splzKuNNz0"
    "OzL+tydwCsmGdniCIjB0ugBbDhvp+LEpSxItmuYwIfRwidZ7kdb9Tyd2mkZPZMDS6MnjlaPHry4Z/eXCY3FWD9XU63/1xFRFeXlh"
    "lBerl0bVUw3M6gJ9VdWWr5B8sgJOJ/eNpod+Y93/flwuIPtJA5tiRBnAhu2ra5cAbsHzR/KALzC5jAA0BvriE4fu67V+94qy/YaB"
    "gu4wQgem/grdMIk25+6h07BOT9TkFLJXp95GZT626l+AVmYILSOWZoE+BUIm5LoIrdAs0XEybyi3IJ3cQ6fSA/loyY7LroCnnSO2"
    "4Nq86FSmFQqucnLYsppO1tSA0cr5ucolb+pxWw8XzlMymJXKkdXKFj4KCn/49RfvPfrlb85Ov6dsuaJNFuRfNZ9Q9fH5F7978v6X"
    "yCP7fXzfiPn2SqNZgTZujMc9YftDYzrqeO6hI8JOPn78/i8xcr172XFZq47XQMdFKOEti/eirTrLWMmy0g76V1fnI+0aRh3e+Oo1"
    "7SYOw8G8C77tDDq1GZmVKUk9upQoucxqn7PubndAjZtXc7QrargD3m+xA0YYkVAH7IQNu93arkH0qM/MkKYhi/SMBBr2hAb5MhQ4"
    "bs2Nz93FTYHWPEQ7Csy0ya0BC7GAfuzoKke7ioxyjC/gtrwJTVD4ID8GHemr7UvgAsioweemMHyrxnDkIYonlvSvcZRfcM3jmHZF"
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
