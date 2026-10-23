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
VERSION = "1.15.3"
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
    "tWTDLVc0ngzuLMv61VChL+JhsDiOKO413+T757TzDtVv2ODXfS/2mW0P8ng876hYdHIiEqk1vZrNHo5qgyge5TjsSVycuBNtLgSk"
    "atZJ1XCWCchYNXE5NyqcxECb9xOo9JV7jG+g/cSNYWd9fXu43d5u31hrr220N9a2WnOGo4+OXjy8t/Py6MHDr14+e/Z0/+jx02f3"
    "7z09evLs2RdHR3daU4W4Tyfh5VUJgJxOEHUmBVKOg+VleCymY2TBChox+YucpiFWy1CP4D0dodMJFGg/kfkXKG3Zf7jz4uHLo8/2"
    "Xj58sXcPunrw7Gjv2cujV/sPj569OHrz7NXR68+ePj26//Do0WcvHj4IH4y68KFM2fwck3CkjZhh7VLp2FqjdGxNScdwfmdoPlz1"
    "Km+3rVe5Escpu8y5HRTxOO6QVINxrcHbt02gSoByRQiEYBruDY2R9pIVRVg2CfBEv9yV4dxIkgkft1HEURW78oSRaPNQfY/f1EWy"
    "/CsUzdRrUPxEomY7LjVb4iPJiyStmn0HWhWFtt/iotNS4v168GyXJK5VkmORKzPPFmoCOhm+tip5VFy5nKqOtqVUSA227j0b4xal"
    "xjCKZ6QfQ+UI5iNd/RZwldcSLV/YIATb6EFj6XqERmSHuRAeiVjOPp0WJ/vnmUtu6XAGJYkxoJqiW5tcJZaAl7z8/N63vDxKCUun"
    "ydoZ1s02neKN9qavg+iaMLalbmogZfoYC5UCLeNBT/Cg53jQeeRbr7zskKd0yMtLDzmyLfVDXn7ikGPYnwWHnPhStUwdUSrJJ7Ft"
    "JFZsOuYY2JGScWP83zsa+nRjINbKsDiID2ENgLsCEK/AOOZthbkfFbRQeCk/pQ3Rws9P1TsoRQow7VP1ZBAZsodmtilPU30Za8Ku"
    "73vMOvqYKemVMV+5Vzbd9CUSiNROm385p9zzXC5Lj0ANAwbBXjbz2rKqlWohv4y585Y6avTqlL4lkkRluCiQnuVv5bLtS9sRADy5"
    "7cBdShVeG6dbNi+mBXso0an6rVSgmHU7cLZBdoUAWu6BoljDTxIRVti1M5RO70tXoynuAk1hHBkvr7oK69h/92Dn4VIttfAVP/R2"
    "hjokT5PYd45jF3t91H8ilRJ+IVHDs1FoC8X+UDyehs9G3f1h+HjKEDoUc9iIwXyK8tq7SEdW3399dP/Zs5ez2UWZv4szzKL4Dt4E"
    "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"
    "+6Tpssytp3f39323bpy+3K+/fT717lb27QMLvEJfL7e294Wn28LrdxaOaj+5ZbHePIXbb9782b/4Z3/yj//Of/vD3/uvP/6dNzfN"
    "8/YlnvSC+b+hCN69DOPNr7wB9CcR/EHqnv106eVXb7lAj67AD//SD18RI74hixvv/9IzvFho/lQI7PE99C+Rnx/96Baj+9GPjG8K"
    "6zK4h8c3c79yhW/z85Q19JyxLd6+3OXh0SN/4s87u741by+1GO8s9MwvDz+PmV64+RU3LT985Kd399pEb9SbMn3ayLaYuu88csXS"
    "9usLi0tQZ3FzC2zf0g3C2l0U5+XNxw/3YdH5g/MY32zd49LurYp7/LKhJL3HIpoP+X33KNPzjMEfZOxeCP/VUF5uAt78t//8f73/"
    "8vd/9s9/409+8h/ePHx+326XvvhzyGM0oVhUTLE88505P1v49OXLbb/PPSH/thq/sMHtQhu3d077zo3Tihey3yDA41bDP/4nt7W/"
    "T2/3PnP3uw+8Anx4BOSzH/6lhSV/+Ol9tWuRw5tuPD/umqz9BbbU/rP1uRXr+O5380+6W1Qk9q7TQ7Pw+622zdPJG3/cY8NPGe61"
    "/2gCP/0udAvPLejIS2/LI8uzfl58UtZ3nMA+ln5cMNGToAePNvvhL3dv7yU7HxHTc27gF+nrSfv8Q5rk+OB+exIW2tyrmf6gaYuy"
    "9C+fvfmVn335v/3J7/3ThTovc/KrT6R9G/8iQn76fEdxzyH97M37H/+dn/2n33//5W/9yU/++P2Xv/4GeLwAvPnZT/7xn/7k99//"
    "+O9+mK3HuXqe9/Bt8UjnR077nyTx09EHCt/eqPLFrSTZM427hTjdf5fGxWs09dnbxc4Xj3a+eLZ+924fm7zjjTa6G6LlZNH8oChv"
    "7yfS3G/+6t2n98lzXybvi1fqaX8Lu9/S7aVFO76V7rlyb5/GRXWXuHjaWrDopseTg3++xu3rSzfg9vS+hNuoXko9L0OTbmm+C8v7"
    "H/ajvgqQv5T0va/7fCDokxZcxrO/R8all/K1LxpRau8ZLk9FEm6mCPgEWt8yrZ8q034IrXW3++47GrTGi592H717iF5OC+4iiO9+"
    "qXsszPWmuWvG7pPgxg1+7k1Pex7Sh+iTcLn1ppnuxQ+pe79vV/5fue2ljN89X7/t/L5taI3d1HSz0ipe3/3Jen27eRntav0/9ovn"
    "9oHi9p6mmxNz2ywR3X78/CW/L3HF+V3Mbnfd46T3HW33L0X59t7A0iu6yK7/2dvmLY5AD9DDMpwF5b1FSGQ5XP7B90okzVuSIG5X"
    "V9jt6gpekcsxulx+8tvL5rXffkPvt3m8BYS+YcFeotHLLz5Ah7uALVR9BJU3DviG4/C97/08v+ExNvDy49srfW4Deeg/Xg3efngn"
    "6RdL3/6H7Sd34f++/9mb//pbf/s7f/Kb//ZP//cff+fuyX/wRW724c2n+9tqwwP5Aczug+9/tMvweQmqu//qB23RuulLLt3bpYe3"
    "C6IF3rx7UlVK+rqK6S3mc6PV228M7NbrtyJEcvAkoI/RoY8M7J1Dm1Z/sbMfxOwuOS/A/Bttuk8T9jxZn0tvnzJK3n/1u++//kfv"
    "v/4377/+o/df/fHt8+t/ev/8jfdf/ov3X/7B+x9/+f6r//v91//q/Vf//Hbyq//0/ut/cbvhy9//869+989/7x+8//Jfv//yd99/"
    "9Ru3zy//2vuvfv39l7/25z/+R3/60//z/Zf/8s9/+u+XRn72v/4/i7Z+/+X/+/7Ln7z/6u+/ecA+7Aa+RRHug/8FION73/sFGOOe"
    "CPSoWhfN80itG/EexHvA6X+qvRfM8lFs6COjpix25jvvv/61O1V+/fFBn3HFm/df/v0bYZ6e/m/+2e/8jcU+vf/yd+6E+Zvvv/y3"
    "f/Yvf+9nv/+PNPlO3N9+82LzW/+WjfJibj5SkF/cQk7PluXOld+wI/4HTf/4OuG3bz4M4V/+u5/97T94/+U/vPd/H8jzNPzFH/36"
    "fXoWS/rHP/u1v/Wn/+Cnf/FHv/HmAVnm5lUt5ZdaLY9BwM9vpmZxHO6m5tP8i48Dgvd73j08xcIffq6r/LxqBj1GDpd/N8+Xf3GG"
    "H789e8H3RYXHdcD+47SilzjjLcD4GHb67JP7pvxb9vZiwH5+KOIl3Or7+TJv33icd5+0kZ+//YH/HGm80/uLRy04FTfN9mHv7usY"
    "4lQ8ez33ux78b8qgEXwj+vO8Nvyxqbu/nfvZMc6fPPW7D3vfJNe8BI1/eH+KR4p8dqfdX/58dwvo3YO2X3zvkYBP5x6BwRc/fC5v"
    "kr7YYW77FJP40OurMMRtHf3DssJThtfreUg/yfymcUP/ZTqexfp/rPF7XI3/fvPNyb2/tr14YpLHhl9XFr7pyFfrrz9nDekGgT5/"
    "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"
    "OKz2RBhS8tDVE/xhvnaYTvXozDY/C9q9rCzH+t2+L5Yb7oq1w1mcC8i9eBjM9TlPR2h5cyQfcsO4p+N3l1N1us0dRuiedxTf6+/F"
    "PYXwdm8S39nv0RtCL3noSUzRyT7F/co01E0MO/XUJNycZCtsrtwUYu29esXe3uhVgp5ELzs6LOXmudgw4wumXHy8PdqwN9OT5jCW"
    "nDYOQyAyZik6Ee4LpcyslNke0bvinmB39QMlN7fJtrcjkfl4uDOOtaqp3ViFZw/d0qzSKDZ3xp1xdhyP5+n9cIYNptv98iQfmxU3"
    "OrntcHMzPt+pl/h5Yq++MW0JrWI73asm6Uipv+tJF8OVcJw+5Ohhp5OchMGcjqXYdHkvnxnTnul+chpJS4lglh34/fbZZFrq8HIs"
    "OZ4lS1U3qI2NeqjT5rY3Oru0azRpAfcKHe7su3rZTjg+2XR12fpWetavVNuw9jtbXVd5wxWcuqVxuZ1y726E+/HWuB0e7eyWEnte"
    "1zhZGiT3YnuxZJGbBRplwV9MDhOecF5kc2kW6GsisXy4iX2F00zbB6YtPxrz2ynfzhQYMtfeL3Jxd7kc6Lu6/n7Hn3ZzzGwzc9hN"
    "FbpbFW++2gRGuuPb4njWfyh0djf6EtP2ZKv9ULoW3tgPxkXRnbJX0pNwJVaq0bJnMz/tlQd9IeWPbQQikV2wyULM2F0cpPdjM64w"
    "7I/qoWGq5LLP4pFm0peObObdyYjA0cC887t7Pc9gu5zrZeV0LVneostgYYaCTHvOtjKVGVPtbGT5/cy2P5zIBEMNJnIYG0UqvFcq"
    "zPZ3tuNNMANbjUSNnsqNzEbTleRyyaKUm42qhVbHn2hvlHKJWKeT9TftHnlbnDY205U83Rnvz6vJClcO5+Xw3F4dlPLdSlrcm8UK"
    "dL4lemf+XMHNb9CD+RafP9wdDMvD/U2+vneY7iSE3M5mrJPYTbGNbtNVFcXQNJH3DyvleLjvdyU95VQy1tyejEv+QSUbawdduRg3"
    "j212K4HUHp+c89vBXLq37d1IJty7vm0uHIwnI+NBsxTpuOvtQLxSTm82K7GEf2u+WYnFEnKn3kFxccD9QXuplXaTk2BiPzlpJ2JC"
    "brjpcjXc4Ypnsp2OF9KFeg2osCD2k0EuvjdxZWvF7iYjHuYCIA/3I7keP03F/Vv0ZNQQJ6ndcn8vUfamprLozybqh6UI0EJymJxK"
    "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"
    "JZtDAWWLHZtBORBaNGcRwNYHmMrrmEIYCkMVTQtggUtQDoEvANyYJJKIHMyEc8q02GFkmAznVMy4bfyEzMkAp2PVfdCIHmF9kB9x"
    "HJYK+EtjJM3WrnkcPaFBHsjsADDUDUaIOFDKikxr7ejYgDZTowuk4UTN3mTb1muMjcDyqEtLqFGZlUEXo85Of392982zu5+fv/DS"
    "3z9/6ezu62d3756dfnJ2+jP05e7bpcTZya/PTn71989fPjv59Ozk4aN//+XjP/347PSNxz/76ze/fvXs5O2zOydnd//j7PSDs9Nf"
    "nN39+PyF3z1672UocHbyt7OTj85OT85OPvzmo9+cP/wxKowevkMd3yRj5KPID9MUxJZDjl67ZuVv37YyyGPTAhAf3LI5OYbvyF38"
    "FDluTE9tNw1zkpUpyevfPTv5IQwUjfzjs5NPlPGcPCRjgFl+64i/fp13AsjW8V87dXb3M7S2x2Ryj+6+cP7T38Gzs9M/n919ANA5"
    "u/vS2enHGCIvYUjcf/Tw3tnJz2FmZyffI3M6u3OKAfDO2d3fo/In9x//EZ68hou9f3b6MoITGhn8/x78/Pvnn52/cBfG+Oilz6D6"
    "3z//AmD26JXPMZCgWaj407OT/4D2v/t/cJ2Oy9evS4y8DagnjBTCJWh1+/aGlXLRQ9YlDF0gtyibU+4yvJUxlLCSL1HGMXYyA1a2"
    "2mzHNmcTee1IU0ACDj/js92kpRnftGhovNcGNJbFmdJSlJ7QrGxZ7NBB3jqBQq5fv9Ygn1b8GdVfoWL4Df5wSjItM4jViCOeB9Ud"
    "eE2bA8Iko2JsapdHjCgK4hrjHDCSRHeY42N1DscLgy1D9SNEZA0nolnUAvqMXnNr075J5gK0vXIqLuySAw50bBoHKr48DLV1j9b6"
    "sc6T0VSAjzG0qC5Zw4n5BoIC/hKdsDwwQadhVfF88HqgYarcY+VAAYKU7SYBMYP+kvEeHcP8Lwez7UgdrgMNUqHdY9ILWu8LlqmF"
    "nF4mJCxzjrDbDZjjAczRpz5EUx87MV+OUghBoEXEK6OEnWJw4q/aQFC3BGvR7NE6qix5IkQxQNT2TPUM/FZuWo+kNeZYZbqIoQl9"
    "GPc19zol9Kk19adnnQIgrFE8Td00inFphfBBDYEM10XFgSrxwVBZKMpSejFSqugAzYFHoIP+1ymYNUV+Qv/r1BTGgPCbAlRTxJ8+"
    "BHN/K54DF6YbDHf9ulJAdG6IdAcJ3KXaVqphrKrUhD6pszt3qFvwBXBa6iCtgvzosrysNbwCKF3DTA+or158w0IptUh9kZ6AiEUf"
    "16JR3LbS2qrGRMtA4AVDi7jise0W/r+OVGMkT5X1aoP8JuhwLUoQbB2hhQL2HOfQtKGJQHQg4ACgLaCiwnhpnWYdTO+GzmaoM9TL"
    "TbMEv3376NiBMKvFtOkRJ0v4gazLTimKicbBIRkqAbGsID/HAesQbkWxGlZFb62EOuAF7RiZXrhtji75XWHa8Ovmku6GuB2LSBUN"
    "T/3UhqcSQzPKO6bRI2SgM8/LXVZaazr1H9cQVage1aaTfEHo4MBl1LL4CXSPyqAP/HsIKzmBmcMz9St5zjAi6gV/4ie8IHEMM4Rn"
    "yjfSLbCT57VGrl1rOo0PYPHaLH6KvjhERpJFFixc9ET94aA7IgMr7Dm+qXCZqUOwToEX2xwXqLrN6BS+T5dUXesUlksYZgcDpsUC"
    "/EuiMKQ7NEIJ4FETAXGlZ1GFm45r7mfShnEFUIhvqYg3jLKAYoZ1u+ZWF0pbHn5xeYzLoi2FYQWgDTPUPQqcPQYIe3S4OtrRpgY7"
    "QCOn0zl0wJ/mIsQdA4T28jOpjo5JdLiEi1tRKMsOSckD9y1HIoqlhgOk9goR2VwtImGSoyGwGwP4jF2pgBwqGK+AUylCQDnEmK6D"
    "c6hhuQLWIcFwDbZDFbvNIB6uQOvhAlIPNZQ+VgV7EzOTtvVIWwubwyS8FSWlaTvKWpuqZuIIIXF87GgZgAV8gv52EnAaxjcBPD4a"
    "WfVf9gBUcJiUla5qMgEHUr+uUFhQ2yPEpgIeUARUVQI9ufnU5RlBY1jTMk32ytN7qvBucR0L9AMflONCgWoqfqN7cUlJnoFRc9Tm"
    "mOma53hZI+h6jUIWDJlXiZVydvcTZLecKuYPthmI4v97MBXAtFllQSCL50tcCEp/XEpYNJuCOtZM5eHC+BmpaRj+M1oqYKD9Av+8"
    "f3Z6D9tFb3zz6y/PTv6i21R6gZfxl+8hY+UEDJpPVhs0Jx+ff/nCNx+CNfNrxZpZMHE+uH928pLWPoUFvqYINUayLCzoWJ2uIIEy"
    "iSW5hAU8MvsTHNvsI0m/uCZY/wI9C6k6T96CAf0I5kYRxQLUFKzPa5rJAjThpUknwYWX9TSjqjhgLsGzpyuQfdPiaZbzw/PXXz1/"
    "+VXDujcWHSQL6lNTGAxHMpbPX935cAGs/9hwsiWMNS+f3f2vs9O/GMayXG9hOAY+DuTN8lasdNrw2N5UxgbKpoydAP86mGEMvDLM"
    "cO8IS4BOKIfsRE5B9ONlSqsvYk7luGQkBiAvv26xA5PSfHbyGSIyZbhGUiW+EjKXs7s/AHAj4j15+PWnv8FPgMx+BTR2dvcOotvT"
    "Nx7d/77JUeDYeopNAAtwSnDq7OTBNx/ew3R9b5moLdQl81kA4AH1Hfgf9O2g0IdMROgtVYuH/6/9r1vbp0GbwpD5qcGjovmK3j07"
    "/SGlDlGbbtdnGiH11Q9+ajEvke7X0THkIn5lkQYqy6ogDy8r0Q2Oaa0R74HGv8qcPmLyap0iHiNYeUTHiKMDE37x60/vnP/1Q/JK"
    "IaDEeoIwqPWrMLOEyszgGwgNWVJUsXX154AeWq1Nx1RXmKsgnEFZHUrONqgA1lT0uZRqTdscs2j1+vWqk2eYFtKmkeIHunTTiSbv"
    "6ESvVdEPUlsSBgyp3cd2MC2BOdRDuh1UOiBVboHCi3UvXrUyMDIZdFreaGqQl0/VBnasAP8W5aiuUw26Ra111imAaEcQWjCCK2gH"
    "UHlZOViwrJuaZX1V7tjErOayCjJt1F5g9AYx/IqOw2g+un9Rf0wVcwqOqEuAFzfl2IbFJZ3KTVBu1lLH8AjWUpWHPbCJ0WqsKevI"
    "8qy81nNIo+FQEGUGmWqMU/uFugB8MZD5AgYi5wDYK0SHGtBih+W3heGa+9jEFE00dt9MtsD37i9QLjDGv3/+mepN/uKrF984u3Pf"
    "wCm+/vzH5z/9A9Y3DA3feRUxTtA3Fnm7gcncpxyrFphapUQh9qy2rwzz9N75yR8UZY1Cq4V9zl9/ihi+5asffADq3AMYudYf6FrK"
    "LN+BugYH9DvY9fwDKF7MwR9FUdLY6QVgvoCPmFnfO8BTsGRZ1OoAZOevw/NPPOcvvYjl1K+wqLqHFcMfYvkAUD5V8e8dNNE1RZyr"
    "YDOzUArPeYWGqG8FYDUZoPgeUnzv/l4BnhHHLtXULsUsZWEf/er9b+5+gSTbLrZjJIsG3a+/+HJBFV1QmAj/3gBblzLsBE4wEwGD"
    "jzCoK7AR7F6WLE2BWxgz2Rr0D0FbXdEO5iurxCbLg6oHL1DU7Bol0i0W2AuvcKyC0IJRjWluBD89FAk3BdKdIKHTRTuNa8h+A/PS"
    "5GAw+SNVjnQp4zOKZ6OGAmisrjRCbEpRsa5gAGHDBJkVS5QFL5Et8p+YHfwE/33gOX/3JwhjFuT4vwBqbh1q1y4Hm+efApu2OfY2"
    "IUINVCYzUAeLQX08fePJW/fUXaofAHAeP/zg8esvfnPnBXivUv4n59//q4FvqqC6dZlF0xHZlncFaXm8RhSdXM0FvQgQyogYRpy5"
    "XI/mJVGYrJDD5hWVmalmJm5g346RahUhTFZYc/7gU91viAzdmqG9AtWDuu5ZczukIcNxCYQHyC+mYUETI4HmNyXbzU7cro4MV7Bk"
    "SyzaclIVwas4uIa4xhFS1zDB3iSKxPXrxvEQ1WK1CyVAPESG5Xjt9PELDzR78dayTqIWBaZH1g6MCOB+j9/99NHL9zS9HD38F69g"
    "lXBXdb2Id07DyukuiphZ83qB41+6Tqove2mZdAy+guGGdjtMxhuxnDRr6QJTk8ykxps8NNhmsltNFrvKEiibncJvlQk7ZZEdWJHd"
    "rMPZpjAJ7Qk2HH+lDOwBmAvnr99HXg9kUr6tC+vL11fp4PGbHyGGfPrx2emHZCP9X72uNQnRpbqs2M+6uKqewNNWVdmPuIj2liZH"
    "TGrFKXfXaEZePNASTFIfqObEffbBGjZLnjbgS4zZCxZYkbCXrSwRFBrFApZd1vHiij4dTsgTfgmnJZ7yIUc3ma6yh/H13+6tWQqx"
    "7NaNUsJhiccSuVrpBtapVRfFPbPvCeTbN7/4/qP/+C3CdRQJApj5k/P7fz1/6fugkGKXzeVLoOxLLcJ/CRCXIvsKc2bBljl/4ZdY"
    "N3kfK0WmcBbkBdXiYh6/89mT+/9NgkIuNDq+jyYOChJSA5CChNZ7VUQMsTfu3AfwlRIAQAAHMKuHYDprW0Q690AlX4XBfP3Fe5oq"
    "j0NnNI1LNRew0nVy/5vXQXn+AIXQKC4irIzAUO6cYHx6gNHre6iS3sYDXFLVqxGvpR7/6q+P/ut7Cv6aDQHMwMxVFGY1uWRD+kKl"
    "ellbeUbVELfcEKaaKEI7O7pKqG/2LGCZvtep4JlSA+MZ9eTdzx799XWDzx0DAwP6yVs/VPzpum2I+dWv8VK/jeOQ3iWVsHqov8IO"
    "wk8MxE1kk2rakG7ePzs9UUSA45+FBSOXJkZYmHa4FoWvcTNsNVQIK1PJ/uGC8ME25zsYTh9j4/OeeffBxNURVn/6CtJJXnzh/OFf"
    "0E7EL15GUEDG9Uu6foyMj9+cnf6WWCOKh3Wx308MxqFBe/5nwVdR9vqMENS2tBegp20RroacgZ0obAdB5yFCHeR1QIAAprDE/BH5"
    "K+oLMYM/fvLO6wRECzz35D6C3+lrKtQXXAavYReHkYVcYLT80GyxoK/AAT56cvcjlV2awu3+RZDeZdusEcp413UBwnhDdjV0d9kb"
    "G6zFzK6ImwZw4hWMlO/gDS3d74Yt1D9iOL0ICIS0qT//OB/b0kw01TP1EDe+khN8/de/Kqtzeoq99C9h6JBOXjRRspE/XsXztkaF"
    "h1MUm02ZnCQLNARS6+2fEecMFh54mxARm7KVdvL+49f+BrOAeZ2//gPiR1F3ChX9GM3hVNs4fH15TxRXIezuHbzX+KGq25y/9Ett"
    "A8Qwpo+XgzIX/TWMTLOctKjKNLsdfIUXj6Iflq3T0QBAM7vAOH8A2P/o3T+QZScsBfU40farRtzKmC2ONe8jKG4n3RGGWM2H2PL9"
    "HBm/WJReoAQYcAiI+UTR+5Y3mV98wWSXIHzTfAl37i9JBxUjX0Wd3z05O32g+GIQmN83sdiT/1yqhx2pK7Z+obNqIY7e3v0MKyII"
    "mX7x3uM/AE/5bMjyHQt2ef7u/LVPCFC/+fC185e/jx5++cX5Kz/VCQx4M/IKIPmGmrlzv7pr2YpVLcVSqhLbLlbQyAHhViDWw8cf"
    "PXzywU+QRxiQ6O5bWE6iqf3989eQIL37KzVIGKtQd7CThEiJlZx+cTmplf7Ms9M/4gZ/SPbtqow4ZkSY9K4g9lEkGAou03fdYb7f"
    "//X5vf9AG3F//DP+gt0hpy9hEteV+guGcJGlpmp1ZmlHaA1zmUfvPHxy58crpN2dU5/70du/NLhEF/k7XhV9H0p1U390/tmfzk5+"
    "j/t8GfMAo7AGZP0tQSDcyN9w4y/ildPl7+M3P3vynz/Duu3pNx989PgXf1W9/qrheiEgFCFndj0iEODIcN23pqLxkpD/+Jtfg/D/"
    "8tG7nwLCI+sDUzxmeQ8fffQrLBjf+PqzHyFiuWxFLtPVLiKvO6dEIVSMhHdONeK6uJ9lYb5sZBgkLhI0hPeApv377z/66edKMbMB"
    "cnVLw4hhBPiqAn/fwMpfxEv3GhZrPzdOGEjYQCyvY0sBbXvrgzHSoHkDebRSBfhfDh+FIz3ryC9kHqsgfefEPGIFcY1ojbeeL1+S"
    "S3pd3EXHGvAF0gjFIC1QCTH4FtnkQoTJVfSP4LL+cUCtyMM4eYC/v6uxHpWm318NgrufGdbhffOCnz7600uaGwyzHiNYP0IrgkTH"
    "l0hh00uq6hwowgAEtDeFVdpPvvnyTWgGmyofr8wVUTcZkcVLuAmxax6/8qdHL9wjUMRKxUNMGL9HPOijHxlwCI0RpKgHr9GCGvRr"
    "XOihHlJ2+t+4AMmJIRbL94zjf/zH+09O/p1I8lX7Aw8Rm0bU+bGymYAw4ed43V9G3y9gygYDfUlJ11GAa3AWXsIhjE91EC4q7zG1"
    "lqq942YW1XcSHrlafzdbgg/MZK8FphlVPOrW5YFeDZmXVsUCrPDzD0VWM/hGvCH6w7izefs2d/v2NcPU8D5AX++BQ4HkNA5NR2ET"
    "JK51nTp/+P43H9xXw0Mm69SFG8ovrVrz++qekLKDayIXtGn+NCYz0GyOi4NfSEKj7gBHIZ8XAUGbeuvCqeOYUbQBofGJxT1tao1+"
    "To9sXadWKyum+jhuas3Y6DuUFpY2bNH65vOVtgiAzs/f/YmGXGsWylEF853vWLXmbGDqYz+oldqmHJSF0gOlHNJlqRcSSvsxdCaZ"
    "sivMrNeQe4ADfqjbtw2PmjTfZGARAJpoB/1KIRq4NxiiVSLBJCSszxAuZIwoaaKIEJjOUgLRpYLCODWhv0599d4PLUr6nqKBYs0J"
    "+A7S+u48ufuRWc14Ved6SP1EhQH9v3oPWPLDJz994fG7D02ZeKt59jKxISwEaI1hJuvm4D2DF15V2w3y4B4J/cARZCcPUczHUgwX"
    "kXML4bfwClc+WWHsrlH67q2estLrWEnADkNidXhDrI6sZkUdSA7OlGDCr8hGQTFddHSkBX91ccS/hCL+RyjiH8dqMbeiXQdn7dqO"
    "r5BEhUPClB1W9B1vfhozlQ8u3DdH7mzKwRBn9ZLibjTPVu1LGJ3EI3UjQlJi+o37EGd3P8TS/08oSAg5xy/YRACo0Mqm0+jCPZyn"
    "jWTo1YeipxOYh2Pepbp8OJpjdfRMe9BYNumLghZE58zy7dvsii1pwXrNFNo/uiCLEi+4io8YXNJCJoU+9WPbzazVqo5di0akFvR1"
    "s4aNCBs4q12vpkQX3/2MsqHscDu0iNme3uDZnTtqIw9WcgrSoFJrRXtSnx0OkTDQvhrbRnXVx4bKdsqC7W7CMx5cqKAqQVX3iGtP"
    "1bEXA94usFPu/gT7QACDPz27+3Oy83IJlyP58xEUBEDCA0YoPGCkhQcE0RsBcwI9yRVlZR6vjMk1GJEnpshUNYezg3M4JyihjmNk"
    "S02OUpSeutnvWBkHD49sR/CGdzBOYYiyN4e3bx8xvIKQHocoCDJKYxozPArNAT0CRauuHdxyDOjp84PGUELCCtUzhbXivCP1WfTg"
    "CCuo+uhRXKncRc1pXbmPb9kcNRD/1wyN4dBVKfqcIsolHF6Bcq5syta87fp1Q0cH7lu4RLQm28iYnm/h7ChShJ6ZsqCUbC+cSAiz"
    "VKI0gVkD1CQni+Jc/2/KztluWsmQUCFQGWUnyze5EXRo1R7r40C/ojIMBI9SlxRbhkzKC5m2MFSyp54awvQJFn0nxH7FyjYSek9+"
    "iiShBQTf2Z33vvrBzyw4Fkxx8oMc/PrL/zz/zY+w7HuaQ3dxaDQnP31YK4LKlGhMZMlYSrFkspjIWdKx7ZRpaLpvVZXm+hzwrjR6"
    "R9z3igfPFFZumoU5So0ElkL72IWAYIScfyjE8uEqbwDasvnmv9599PmbiNDfegfLv0/Nu7OKUYwa/hUe7NuqF2zBL/nJ15++ijNx"
    "HhBtX7fbFAqVmlFEg3rEN0JFDblQJIrt9m3X/zyI3dinb8xvrbmcMmC5lQEFG96tUS4tl5rRVFvXwXe+47pl/5bLgdinbOePHWOW"
    "pKRZmOhzVrPkwFQtrWOkvY4ph7JXGejBZnOSd47N6JHKA1qsKJGTN6RRY+0IyF5EeY+GfPAZaz1qIuEzBFVoSIuyrgVZJMxdbiq/"
    "+maqA+MDJWxqVNe03ezroJAIkQFTId+ifYXAQGnEw0Rs7Fg9UUVtGEXNZ/kWM7Va+44WNG/ta+3Dz2hUadbBRrnnou51pd4Bd4tM"
    "Uoiy66xTZVRLacKoDChyju5i8vAQ892utR99rm/3XJA+LNy+LaM8ajx8SjmeBPPpfvSaW13XVeuEV4hdJ1NBks6wcIJNSehvQTd9"
    "EJnWI3y8Z0tdTbJihKsLx/pxFAvlgb2jki1NNukVcGbtEQzSc3zsOBBurcj3RfOTEOsFbnmleVpNKZObeB2gkgBMlfyICo5NJ0I/"
    "chLBJliwjSgg4CbSG9DiO66R9zakJSlFCaqPWYCKInBbtiNSQ58YTHqoH8eARg44tigpVBRuRUnTgFqczIjWZvS5fd7atNlukjpR"
    "q6abtNaUohIoc4AWDr+NGG1Qx6qIw6YiVZt2IOVjm005DaIkCgNWYpw0x1lNg0HVCSW3DFnVyto6pSHHyoAvFMrdRafeNEGWYkgd"
    "NG8pcCE/dMhITasAlKfCZ2rTy6CTN9am+rkbMD4HWlYYDiyraVxYSrcQ+eJ5YcqCt1go4m9RY3EY3TopiPEXrYAVlsDB4+NRrAsI"
    "hvEIbCU1N7sdBbI6wk+jfVSXhf+D9B/K3W/7oSXle1T5tHscWSuFN1fMOxUn9z2PHv7x/GdvkwgFov9hX/DPv/nwLXNRvJH/438/"
    "/90vSPAOKKxq80jN/NioHlNYjcOzQZnZ+rwdEyUxmPAibfkGB/1bjmm0ubSKCuZ41BQ+eIRXVQEycEyF97UQ+jha2mq3jKvdWlzt"
    "lrbaM5teBq/2TF9tNQNJLXBzev16DJ0z6GQl/Gmt2lD+kcaip2ixTSOyTxUobEVXzfmmWri5Cn9xAy00qQFKdk/RCDsNmVHTVZUc"
    "M2W8VRgv8A8ggCpAZUVZz63F6cxg/DN9Oi0bPpiAjLBKRoOYH55QIkpfv04TxgRcap3G8gItDvpN0a2xyugsV4nSXkjbMGgbD5/c"
    "ef/8rx9SVwgYf3rsN2kLJzW+8uSd16krBM6bbWp+NGioXkVhWADVn3IMUAweMgXWPIzPgfxTax7NzFYthNu33br1TMhXfRUtgOxC"
    "v4BD2vsmSxpqEXgjDdJSiLseP3gD9C63JWo5f+lPaHMQe+RXpCA8xcdlgvCj32F3LIpifOn84cvnL3ykbA6QQI/ldCW0Q7OUOAo6"
    "OAkuAf319JWvPyXb6J9hbZg4dH//989fQ2olCoBazCYl+u2jB/cevfQ63gQ2xQauHMMFAQtYy/0Yq553zl/6PtlZ/eZvMNEvjTtH"
    "ODIBbb6e3jHEFJyev/b2119+QCKylseKYz81wL17dvJjolZj64OEId7T08WU/AJFJVa2Mh58qG5iKDskV4DvgwumenmHyPv+zl+/"
    "+eAjPBst4R7g8goBiiljj0Rwnqrp6i+rrSJ74dFbv8Vlv/f4ZbTa538G7Hj70bvm1KVV0zCXfP/R2w9wC5+Yp4dky/PGomjDCqSM"
    "CfAf4/PW3l7R32rOobRsXIDTN/D+2jtqMtknhmQyI1bAgp6f/AHtAaLi2Bdyemrs/sI8vqWFe/znj568+6LiOzYhwycEc3BH9x+9"
    "+wcMY7LBhfbt8cb/KyuXSrehNHaLLX/KptkVkuYLuPkMTPgqG6j4YE23OVtMITmFXIhVqexo3sf27SsXn4P36SoiexOWRwtQWbY8"
    "EZm+9J+P3nv//M4vFoJWr27Smjok1ulLj7/3AY6zQFEjWv9GVqSEmKxMHDPHKn2sxWEvmPwn91Xr2zizd5TISX2b8IfGoEr1PItF"
    "jDV6LIwZgy1kwVDG/RNDgjWxMy8+jgQH3xP3LEuBgn6lzApSvg8WubIPSwSgog6bncwk1BZtqqMgfC0pD8saTUYiTUdVpqcmoagK"
    "xCuNBtmFJic4aKwWY3ZAixy6YBxgE0jKvb4iVOI73zFiEbSeXDM/slhcFgvKriFRhKUEfMOekIWai9PE1uuls7wkl+uy/K3p0/K3"
    "pkr+llUbBAYHNkQ0gyhrnV4tgesfj5jVV0zxhupb7y2n8mgRaspjHXBKDU1jQgkHr/zFuFfz9P1iFZoYkCrdILUZ7JCmw6Oov4bp"
    "vwya5C+w1xlbkc8Sj7KUiS6ZHMjImLviqTSNZKzVumDww5HUVc1taqXXeXFSpmNs0An6RDswijY1YhKouFaN66cEIVgjDzZYpX2M"
    "SmCD1OSn79er00gy7YVp9FV39iLkn0afpj31q8Jxi5ET7Y55COhYyQuAg44AxDkECr2bPaXvaNkCACblOFZQipTgmZcRzegbqqaT"
    "nVfKadWpp7hXrm4OmSs+5/lHM2d/8yGo+CtzZpdLq48ZjkG5BkfEYqrAOPQ9SDSqRauI+DbNrFD3cDoUJ9PBLZMzzIwZJq8qMbuV"
    "0QhD5KKF0ZARGHyheu2+6pghiHeMvQW2y/PbFnwlWLz/4NFbf7k8c9GYPvSvSb0XhsnByhRyxYVkTiO/5iH5L3hZLSjBlFhw+OuC"
    "6YafEV2N+mdT3U2jNBwPcO2CYboXh/no7V8CQSVjeyhGDT68+EiJlxenQA6awI6vN0mMGV4Yk8FkMJ1x5+v/EGUY+lAO/7iKa0HX"
    "1wAigNUGLMAu2vULMyQXzHlc+timuFs1xiAjBr+4uwYPV3hKZHSz2RL5ojbEVSNHOtXi9B9ewBgWyhIVmdTQ9qEWYKZUInxRf9YQ"
    "WqZMiYGRwjXHWn+lW2y64vkK76JDdfc1kSfNSgCqeHhxYdtN5FI2eMma2GmGZWxTddB2oot+wvWqWn/tQLPJptBSx+w+7JCWpjry"
    "4AXQtPHWiqVbuW4a39UVq7ZKc02dwnrR5yZgEPRM/HZZ2C0yTsqYGAw09gRFB/9JCTye4WXpXcR0e3rVkrUHfLtnW1jnq05orE5o"
    "aprQ1r96Qh3ThKTLZnSApuRY9hJfM7iJe7Z11AVKYnrvI8M5aK+YIrhxsBWCjQP5b5dbXJyHHkFjSDOqEsbwNPA+s148UDXi1mUa"
    "MdaJW6rwXLsqN6NISgRx2SlBpse2f0Gg95V1aXq2UpvGiofT6Rw4dG1ajQk5vnUlHRrxPVV1xnIUxe94MAY8VNJfFCfqGwQFkUwx"
    "HLuCy3ysRf5pSatqXt99LetF818QD4wpbPqZIBm+BJL/UGIkFnZJVtQFP4bt88BqySG8Cxqh8k5XChfNvAVn9LI0UpQFUwKUnqSD"
    "lTU1+ppayK68wrEVaqAUWpyriP0FlRiAoWvEeGeRolaAYFEnNmPbQN2ORRvuRIEle6X9i3Vf4plZ1HuPHWr9Sw+HWKRZQGPNkaPm"
    "Uz1UIuA//URLKCWnJSgOYcXJTK6ZWDiu8dn0r4sViauZJTt4Z15bBUzUi2tATJBLVyFxJe3xCqJHCQ00h86h8xadyLH3lIU1ytc+"
    "DK+Pg6Hx8EGSKE0Y4krwG5vualhoTwWHUcaplRxXEGT4nEgkh64osxKazFpbPcGlASkPgHAukBxm5LoS2zMd40b4ioUEUz9YNoMN"
    "+aPLMY8vGVNLVXZOHLwLzP4vpt0FPHCiTyY66HqgpjBA9wweUNoeFeVAdxBRt5QDxZ/nmQm8fvTWb7/58DWTNu6g6GYTytGtFhRQ"
    "xA88bKHK0ASqhbcgtBZh3gg2B4qzlmSpwFt4Dm9bIPwOVEHvoOCnPgitpnEEqBVzE0pp0pKpqLlVod3mWB61pwStvvUb/R2vvDr/"
    "26/OP/2tNqOmMGSZlulgx4f3v/7ri8YCs+fRdr+hyDcfnigRpErzx44qwJ2A7O+f31MqO1TwqYD76r1/V6DmUIFoAN9XL76pTNlh"
    "BqUKxK9eekPp0KEC9BaKMnt+uWMjlLRBoKLLLa0A6PICGce2erEIpFDR7/9MH4YKMQSiOB09EvpGOD76FIjlSygn9KE+vsjRuBB/"
    "e+Hs5AM0TnagNE+QWitB8FocISRBvmsN4ckaLjQgiU18S9YBpe3aff3Fl4/f/Ig0M6FF1I5SxLTHqLajFGFarLyAM3gHT83PQvsu"
    "htIK7nyE0rkBEg58uCvGVg1TF4K91TLHjhiglcg0x2sIRI4OCizsILcYSlNZI8kqjpYoDPFezJBSb1ekyCflQGNYIyMht8hiWBw7"
    "Ulq7CGCf/QhWQmme8Jnz1946/9vb+CnpimwPP/7jKaYN0uWjz9988sF9KEo28c9O3tAHQJp5jKiYjOHR7z969L3X1FGoaXok999R"
    "0qjnigznIm6DrltfRhLE3JXKhujLXeuRbL6KTrkUzLAHJC3fo7eo3+xYyQG4lHyDsjMOyaY3Y7y8Teu2y1mP+qZLgBLkwrwDRuG9"
    "N5/SI9Vn+ZalD93xB55bhm4O3KZ0mwKt+vLRWXQwv4HUMUWYxukDHnXMKySymCazwg85tDSH0LGEOibzZOwUyklAO8jk8ruv7rwJ"
    "v2Ucvq9rAtodQ0ZjB103BLIWv1Po21wA3c1q2pPDD1AV5Mtl9ODgejvKRJ/DKVyIQNaJIeGl1si9NoDqlHLFkqkv0t6anvq1TqFr"
    "VNUniKbQYcxaEUJW6+qXNQoxLUOawD46R0jGq/u0RZRkllJAGKOVGxNX3s5Ub1uRW0KruXIGFGW+Hehw9UBWLqoI+GtBuLvSIr1y"
    "9w5tGiYszAIW0oaBXAPt6xrj5A3XIV2kBTNOtCbfhsKqQrgLduLScXPfPPj5o5+8jrg4Oo73GmPUIEkFxE1XVHj1/LVP1DpjtsUI"
    "T9ntwOUQO7u09fNfvIVOC7r3H2DcfPXjn1L4IodxG0qtL9VSblY0nLVDTv0lR7q8+OrjN99XZQM+9/i1T765+8WjO/Dk/pOPf4Se"
    "fPGz889fQ6YT7m/h2GPTsHABUn4rjWgIjQrNxjQsIiuUcWmt6/m46nUZK/tDKuyvPjx/8Z1H//7R+S8/wtv0iyOA6qSMRsY6VK8p"
    "gFK+LYMaX0a21KQicontjRaJxm1cBG18+sXv8REXJIrm/Sfv//785781R93cX3HvANLH/4Zz4T8hAvGbOy+Qowp++odHL98hVx0s"
    "5Psah6v2o/SvYAcaMb506PK5GoatTNdBCCSKbjDj0XVm6NdzCv7jMztZ09oKpvsKEsUspRk6xsU3FSFhgyjemkB2JAvmYS7WId6k"
    "J+hc5FfU2fFCE7nHLiUbvDurnH/z+HsfoN14Y/aH2IweYU3CreoYHqJLeA0ivcJbjzog7VCEJa8JOhnd1NTmDJnAnIO1RZ874JC7"
    "n0OijMVx2aKsvrKKzQP04tb6us92A/1i1V+3b3MH3ls3WPiDo6quyWrYu8JocXSrKmJ5lKCtbKby67IW387f8NjW5CuFXCm7kwcc"
    "GqVmyi+z8TZnaXMgm1kVzx+/+/D81d/+/fMfU/aSlbMZjX10pS2HjX0lfkAd5GVJ5KSDgYBOulV0HGU+ajMEvFz0OegBYGvT71M5"
    "MSkDlB1dwEHq3FArL2YL9wW8mIuCA6XumGQHwSb0WB3Wd4lSe/43oO2Pv3VE6hyfv/sTVUNfOKj/HbXM87KEHe6P3rsDqi7IxB3G"
    "qr2x2dXv0miAigFc9Qc4/5JS3PHH3zUl2//5IRgS+AJCVNo0yaqk5JCAijZqt1kz3m5zSPZKURVWDg6+Ku67OafmWzjYqLSOI4NF"
    "YcS3rNz/43G7XZJtzf1UhQ6U16EogPYKvAdnIqwTNWiNw8fGzxlRoGxmqFq+dcQdu751JJkmeSFWNmhxxfms+mVV+DLxNdZO/Q98"
    "X7TNwTlQfL7k4Jc0ic22CqtjcoXqtWtjZ3Vd2cLHaRUskC7r7AAchsZsCyH6nOAc9J/voJRE/A3N0mZbQbKXAz090NIhrwBa6K6p"
    "g/b6dQJbm1nqa6YWOf5M+0mSyQkNE45vFqfI1kVFAa8UkJmAleyAAsjyTUY3NQ4c/ELy1c3Lr9s23qaW5WH+Y5rD73mUZSrZPTZ8"
    "q6qalgQv8P1sWlGZ3BPouCRQJTsw3PHmgtbssKS51O4NxqTODsBoEoFGOibygKKwTihlFwk/Fl3tIqtZpYjvwld0SMKYMf0AIuTQ"
    "gQ+iLO2yctfKozsWUc6Cbd1QiiQpKJyHdyqGJSgm0hUU12vGGhcG34hTTSXBYbH4xh5DDDpotPjk7I++/uKHyoFO6AgkMJs/IUc8"
    "ff3pnW8+fKCd762GLLxsPEkVJYtinwhxthga+UhJcTh9g1jjC+h1IUWLQNIWwIvVZL3yigGjrbGAwpp/UoPYcx5yK7362059/dmf"
    "KHw5pHPYmMmMhN8LjFX9bcNBak10j1fLwdvg9f/3Z1JCfwjM2SWpreDVv9wDT9pQUDfZcSjEpFYmTmKK0g9EMd9TLzllQaY5wpbb"
    "nCCIKKkLyJ/wZvIWODTwbqusZWQTlqXwGmBaVsn4XHPECzAlJT8OczZlE8eQ0P/UAy/EqQX5iwj6IS89EIXtqqt/BYbO6Qz9qsjA"
    "osxnPSaO8LX/QZZBGaExImMoDK02NSLOZjXrDs+3sXNHt36Z9YuHIaGrro0jmQqANRK+f+8ajhpbp76680PKjp8zNrSF9R6+4Qa9"
    "0zv9lmJzO7CQ4hUhxawUMry6ylVaE+Mo5VfCQfocMCAKHwpAfvMoVPn2be01cEyRwkxvxMss9+2oz42k1PXr0mXTnNwY6abdk7fu"
    "nT+4h7aE73725M5/k0OaMON4iDZG3/s1kfZ6bguy9JZNmgNKKwrLJKtA0TOtyYiJb+VZNuwM40ahBdjTqRsLiiMSqQu3sCVrgNsV"
    "upEu6gc3YJydBhqivQ1UfEBoifI8wMaxNzmsGA4UfmAeEl66f3BIoEKgQeEmHIa1Bk1CEgTerFI/+q8P0KDIIWnIZ2Y1JIsplTG9"
    "kPFxil2V76hZ9cVGD+S/EwYnsvi0hiZNLo/WOJL1QEYWCDogguZpEKpogqXSNmVTrSfZIaHjIMBWuiHDH5tu79h0K40ZEiuNX/SS"
    "rQRPHp+8oRhuB9DBLUNKwqpISXZoaYIZZPC/olqKVJFIsIxs07fMYkwUnf0tg6iR1vTDPNz47A6cyN/gwPhhUYDcYMTJLIrlncA7"
    "6pgUwVxAnx4/1M+uMJw5gw72dan9UEriOQMiI8Y41cdR/asjxmDeHyUf+nXyag46FjcwCZLirDv+ZAQuB1oIzH6whswJTZA2R1kr"
    "pd7D89CYDYOTU95G1vfpGzgS5N7iwfoPcI0vjQffUw6/rvsd63kE3PJxO2jqsEo4Kx50OKSdr/EO4OdrMvZ6doUJ8rSjI3Y456RL"
    "Y7wiW1DUOrWwfaqf4K+yI3Qjpp3DYFIsML0VCdpGbaCTishpui/rh8YZrwNQG0O+bM6Jtr3s1HLD1DNWAJuRQweSrX/3//quHX/D"
    "bnHyLMT41nz6+TZ4gTgteyKMsyfKoFgghHI0O1b19Au0rAakUZMb8PoiGKGDhD82ulPUib6m5V8u30mnp2SZQKVe3IQzuc9OsQdq"
    "1QnXFL7xWMUGBQlhaY3jBDoC9FUjH4sd5LFfMQ8k1oQh+esciqDuad+chPDWjCfzxMHQ2cCivo1jLpVNFUPDDjmqEJOuzyt9YY8C"
    "Rkj8DR3nc002Kfirjp1psCuva14VLAZFLR3BHCCGoEMC2pW+EaAIpmq2IXEvLuQkXorFr+pnHxtS3PQMA2QYrFTx1bgzekY9++1g"
    "q0ZkamZAc+awL1mJJqKWh7fixq8LYHoVgGKOfTlAFwBXEiaMWAItWjZcZn0BvHDrzwyvi0fxmjESaRFovBMLHqJPYNGzTnnPTn7x"
    "9We/xIFT6PZG7O1CUERRfMpRxp+dnbwITGux6EL49YqT+goaUf3L6ekpx7wJAoo/Vi5EUx325G5EPWnUJBAWkjpVlMK8WEE2zIwJ"
    "dCyp6ZATREa0LBDOlVCKjOuiFB/lNcnvXRZarylXNyv4r0Q8KVpIthM9oJzDoYwy3OBTUj7lgfJb+ZSVn9QtB9eMHmUYurViqQyL"
    "Y7mExfJ6AkDXfKShYcD8woCJvuNIMByHe3awsskro3Z/gZgyIIbJMoLivBPeAq73bebNUxyHfGzTnerOJho8/AVuwrZuretfD9y3"
    "kMoGBriy33z7Nv5GYjYoZG6DCQ/KJJK4ru84D/6nE5//ZAMTGzRDlAAAtnkeMYIELYFAcQjRrCHynkXnThLnKEYwa5w+kNAe+lLc"
    "yi1yMIf5uqL76jmhKLwLw/gH+vG2i0Y7nrZqVXdh/NUh3UQnSwgTkR4uR9leFpsNZGUiMKzN6kF1nJnUFmSHxqLstEYk6OzNEdg4"
    "wrAkCkO6g+8NAHAtEw7AW2XGxkg5nes9bduVslx2gzXys+pTVKSoYar4ycqpXiZN/5m5kjGY8g8vEJMK2z3GJzzFSIaartnMO/h4"
    "MM19C1q9yX+L+BRUQiefGugMeaOirOaKEvB7Hp2Myh7fhOKCQ0ZHPAGJGI4CNDmeoDILtHT9unKOILt8juBq/xKJkC2Ctl9lVp1/"
    "t3B0y+Uqp0EeDnU6WBFzefmp3s94mrcgFHk92pxfzicG4EhWzUpkVx7nrUwMRNNKbfzuZ6SAFvyMz9xdgSGgnMMrlRV/QVL+L1Yh"
    "frDiXo5bJhfc1e9PdR9f5Ywc5Rx2NcjvKbHU0mIwtZBEqowSS80TO3cB0NjAZhfOjH22HB2yIb2gFy+cWGUI5FPipznscGAvzORB"
    "FGJ0XupCEkQmoRhVYjpY7K+99ZRLH1cabvodHP/bE0SFZEM7nEERGDpdgC2HjXT82JSFiRZNc5gQerhE671I6/6nE0dNoycyYGn0"
    "5PHK0eNXl4z+cuGxOKuHamr3v3piqqK8vDDKi9VLo+qpBmZ1gb6qastXSG5ZAaeT+0bTQ78R738/LheQ/aSBTTGiDGDD9tW1SwC3"
    "4PkjecYXmFxGABoDifGJRvf1Wr97Rdmmw0BBdyShA1l/hW6wRJt499BpW6cnavIL2dNTb7syH4v1L0ArM4SWEUuzQJ8CIRNyXYRW"
    "aJbouJo3lFuWTu6hU++BfLRkymVXwNPOKVtwbV506tMKBVc5mWxZTSdrasBo5Xxe5RI59TivhwvnNRnMSuVIbGWrHwWdP/z6i/ce"
    "/fI3Z6ffU7Zm0SYL8q+aT8D6+PyL3z15/0vkkf0+vs/EfDum0axAGzfG46Sw/aExHXU899ARZCcfP37/lxi53r3sOK5Vx3eg4yiU"
    "8JnFe9dWnZWsZHFpFwmoq/ORds2jDm98tZt204fh4N8F3/Y2OhUam5WSejQqUXKZ1T5n3d3ugBo3r+ZoV9RwB7zfZgeMMCIhEdgJ"
    "G3a7tV2D6FGfmSFNQxbpGQlk7AkN8mUocNyaG5/ri5sCrXmIdhSYaZNbAxZiAf3Y0VWOjhUZ5ZhgwG15E5qg8EGBDDoyWNuXwAWQ"
    "UYPPZWH4VpXhyEMUryzpX+Mof+GaxzHtiuThSGqsHaknuQxpIAKyYwFmOzPAR5NLjD6olsiOGfT0+NiR5KPaAbUxFCSxYieTieI3"
    "YCC3mGmxbaVua5vPxN9PXqvbQIxNcf8bHzN2DzonaE7j7q5ds8acyH8UcwI8r1/HH/oFHSjbw+aYkKGpmyK6zbSBUEQd2thZTeUd"
    "fJRB/g7cr3JqsR2GaVceIWcyD5wfj+j6dSv+jPKOmBMtLMGFmBOtXFQFUgzdgqq+QcuIDhnB41TOGIFmdiTAl20abKUlNEavtDEm"
    "wZC8adwn1j3YaCD6PQZ46yu6fObtwYb1uxjpxakLjZgce/ytoyqjGKe24+t4ouoz/MN2/F2bw1ATzUIQn6EyCX7EYwTg8ergFajJ"
    "KmAkJ0YzZF8q2xyy7YiAOIqCI61KhSOkLmJsxEGeB0fcWIkQxUkL2lGrKE1IpoG4gDtMUErlIougEWxRFJJKvDEnokbbzasCHJni"
    "MrHEEezlqHYIuAYsWOirAwrFZTTI3I+OV4FM9WpdjO8E0gi9ZHLjj5kajhAgHGSehogtFQDbtMPvdhsPbTa3oVx5g9xnmAwUNnT9"
    "uoRWSvkVRa8dshOlnpAEgAFQHq4GtACSHy8lIgv1AQwIcbED/lZUj/BapKTnGSAQaJbcZ4FaM92Hcf161qo9UnmIT410sbgswArQ"
    "vpODLBEiLHWa0Ngq/NgS8C6a4dwzwwKjN3i5bqrQ1ucPzBODGSGYjsloeOqGXQhv2C30J6PNYNRZzIkZ9YKgAmTCjym1TcamlTxq"
    "sfj0caCfIYr4kJRzxgVxjdGPHsaTJDOp4B01RnXj8IY4PhxuwuBdStVn7/qf1u84W9LziO6Z23J3NGhI8KBxG6RgXxaG3wGeztq+"
    "5WLJMfoyOppCNsbNUc7nqeWH/++3YC4Ghtzo6PvRqviAxVc4mBpvrTmr0Lt6IZ+R5WGFORwhP3LMCbIsKjgEJ5LpVqpUrG5TDo0Y"
    "R2CgoNSKq9EjOf0dP5MxDxQQqShdIWc6AI6q36ju3tgW+mjXOtZGZUgnToFH0bKA37COSOelnegx00JFBB59JxIT8RA6enSMOQgd"
    "3awWt5wgemG+AqKOIUyW2Wamsk3lCwImxxFyVXvd7nXOStvWWCsCRgotOHSEF/72bSqzvV1CsW1KBZAuuG/8GndurEbhMPz7y7fI"
    "UDYyZLohiPJyNdAoH/3mZ6aDum0EVHzLytuWNbMeizBXVxTQVrRyxILqC1uZrE4Z2dIcSUtc8zXo8gcksRB5y0zn8j58cudNHKqE"
    "lHC9vsrEK4BvhL/z2nH05iYXjtq9v3i060KTMpYYDrTrIDKtEbAg68jRBYiN7F1CVRI7ZxzAYJHaEj1iQfFDO3ZKUBdOn3QrUkty"
    "NEeYpiddgahADnLHGWhsx0a1AlE1lkRc1K0ICBaUjJttWB2iDcAYbgltC6/F69gw/NEYnKRNW0Nk6D4elZONjuweB3k5EqNdFExH"
    "OsEYinkSUCoopXhKDlJgiKJTUB2cZcLZh7jKscqrhhf0yJKTiXAbdhInP1QZlu2Ys0eNcDO0f6wyAfwMQOSgo4bWCXyJ6qoebJe1"
    "fvdbR+qv468/+xOyl/Slvr/qprUfoxqrhcmx3thzvnV0Wj06TEWJ6EdXEa3RSCStog8HiuRwqJqNsK5LpLVVciiD0FTbsUNHxTBE"
    "U7pl8sKr4pZsn6guSdY5YRp9Vk4zckxKwfrP1pcfWclGHUhXpXmsYYG2j/DISB9oy00Nnr/GajHxsnaSPPLEKkdDojbWWBy6w2Jp"
    "gvKCpJsLk+OsrEPAyME6WWkD6qhTpRX5ZxIBhJxYPED8A10QYeiPxv0JdrXHY4aTGIvSehInA4HqqnfBouvfQGBWCDsnhDS62RKO"
    "Rqu67zqG0D0N2Eq3UgoxoWc2ndosXQvQ2shGanPwWh0Njhs/nnTx0FWGc3ys12RRTV6ryaKLZtTdE+l4AKaJ1aAMrIwPW221OpE1"
    "iIxW+ECH3iwGhjmQ6uH41gC3oSLasvlzU1PTrl/X9bQb2tNve8KM//p1PYzs+nV1vBJjCOsi+2DEolKaPlYm8TyzGLNmc4zR0WlS"
    "U2QbjDFwGpmTinW7Wkfv8qp8v4msB34510OOPicrVKhKfaybKs2uNO5T/MJGng34ORrmAdUS6Y4wRv4ukg58SyMLgKuibNOtVmoM"
    "fDgPFg8DohhfFfYcj0KW0OMk06ZBIUamIMFFVl7Y6atpVusBs5CkgWWzHD2CIbDtGXIi9Blm+DxeCvRr2HyeePAobP4/ryiNKE/v"
    "eZzhD2XQBqGGOSiiE2FHVDKEq6M9QgaVk45vQm/omEzuomsT0daNOL3SDh9xb116IcO/xNlr3sMTpzsYWLr38v8n792/26jO/eHf"
    "z18hT3P8lZqJsJ0QglzFixjT0AYTSEpP6/pNxtJIGnukUTUjX2p7rVwKTSAcWlrgcDkFWiApKQm9UwJlre+f0mAHfuq/8D6Xvffs"
    "PTMaySHtOe96Dz2xZmbPnn199nP9PG6Zhy/WWULno6Ic1DDTiscxGTHzgYfIWyIH8bnzjB9zR6jD3hO5ey+8eOfpqzs/vaSS2mYA"
    "RNlfsXPfhvnXuxavh2T3tJWS3cX4qBSaToXGjl00FJIXnhO5oS+jSlDLqycB719N9JY0lO8jr6VpIpPQ/bI+quEloaH8FMo8v/vC"
    "6ypnQEbSintsyeSFyqG8hCth5aOG80ycrEl9uVsW+9CELyfUcq570krOjty5YSoj5l603iLU8Xfv7n7wRy0/t5H/mpWzwI9XYk+K"
    "tNmFoc5V1XzACJwzoCSut+rW//HJfw9cM+fOLzm1lX4Xy2RNc3L53+Mp5Eg5DHG/+MIgiNHY3CQ+UvdCdHzE2FYXNljT6VYOo/L1"
    "uxTEkvXdwavhESC/hFUnl4SkxxlrAoHfJx+cKk8ePlKeKE9O/OAHYcvpuT/4AfdCDQI2qzJptCixihTRD/eUWFWAGHIvZIE8ePgM"
    "zQUixNc9NhpMhwId3mwSwSJLeSFESSwcDA/Pxh9G4jJtjfmbwEJYsbcEng8j9bHnugyevLHz9EVeGJgRZ+KMwrwpL3ebhdvn3ihM"
    "HjmjI9zwfQ0CUKVoSBi0dq/8RKUwF0STLToXf0bJTq+zIUQ05MKLZOz5GVlxnt1552VhSkHpM3ashw0rV/FNhsCl+3/LzKsYu+6f"
    "vyLekunPB+UuUaBhZjKIAWdyajceznO92dtJ9hAwKfpJppiWBLgjr/SYpRl4mNHwatapc+cpolbMth5Rq8YqK6nIRyqbBo6w8egt"
    "mr5E3lpca59//LGA21SfO09ZTURQpuaZg0beV2nGr8eFL97Sw4HhUl+PWiBwDNsp16QJoJdpOPu2NJx5Ub7hTBdBbGQKvUhxmF4k"
    "DznhBRYznPBI/hbP4gyb/w8IG/vua6Lcs406kixhRjDEJLJsI4fcFHz66Z7g17uYjTfRq7mwmBnjItOd3uTsdFr8ijRgalEsGREs"
    "yUGBuw2vCSWhVZoqj36G5CIHTCTBbWA5EIih1WhMJK4/xLbHUhrFuzwxPr7SLDZ9Oy5F6B3idznonkFTJCf8Wy23g7rjV60aJhtQ"
    "YUBKXfxo0U2Q1NgYBsLvpnyfxjF+nXr6RLO6sMDoSLalLVzlPQYCEOGNJWPVzSIcnWeZK9YoQOBklg4VhigLL32oZb95X2BXUnkB"
    "XxbDiBEog4pJ5AAU/Q1GIREoYwiNeevHX1z+PfEB5znjgyzJsCqWug+rQaKRMRUnTLLFRfu7NDgSTFEM0Gdvc+AkkV7N/s7dPf/T"
    "2LwuAOPhizHkIrZQJshKEx4qrOH3CRWlwu9bENCB+kOGRkv4mcgPM3xf4g0dsm9BxwCUzyUGoGq4WU0G8p8qmYMouGAJeEaLJKsY"
    "oZEedeInAqBxcTEWj70aiGoVhFmtdNLIWtKlULBd8bERIVDB/iiB7y28f7Po/g1OW6mnmKG8lTrDPWlP2QftQ/b99uFF0sdFA10E"
    "I8M7harmGFkRfqj6900t2zUGMfGORW8k3PNbW2NNHfGk+G3f3kRWLQjdyiM9e82ruwYsKpd6qsnB+PFnnoq1DLabTMPbqQI9YlOA"
    "K3Px2guh7RsFN7vkXU9RkZWDqCDx7MDM81v2mp2g57Ja9ey/nQV6mEoGDKVqgXdmxd1YC3p1ob3RX2jZXeMFJIQLDbtt3MTU7wtr"
    "9rxZcskJMexntmpkyQVWVPous23i3Z1nX+fcfcirXfgrHBcYFCcy1XyKnMGzn+jOLCxEZUW+HbrfNK/KIah6Il4dOyWReFdkM6Se"
    "91gQ+K7TgRkwxqTq7PFl4NBWQoxuoB8x2NEKZtBdq6yU1+Sx3YN34Br/bMdVUfVrJcQadSO3wPUQv5W4BQcCfC7oqqRKT2AshpmE"
    "nipTwSbCj3wl7Uduy3fP1NtxTrpix0xAH+cPrsmMKzUJK1yvrmjPx2pZ2UvZHrSi7EHdYkYaDpjxSeWsONxYVddrM8B5xXs/5gOK"
    "PmSApGHAaF0mN1YdsmT+EUNyhTMPqtx99pcUTKqjKam2oCKfRwsIxQoPf1wxelmIx5RgWF5QTnABHLHdxsQpdhd3GdmDYFKYA0KH"
    "Kxt11HyJbOS0nKTBnFAHGodxqytiYmdW5HRWiytDZnZ8PHsGU8mghb+1SAnN78BqrsTfWliUC1c2pGSvUNiTWo8CK4aXpG7F/hpa"
    "tuMCmDN7Wia1zmQO7ZXSNLJbdr2MrAhytePj8e/YXqXdS3oxVNCyFFMZZXnVtdVnXPsgOaER+7eCq28ltq21KVHPUPCPut8sxGx+"
    "Wuua9cKBVk7JlBp4ysRcJ4bcGijPA+GoabU/MWMh9t6F5xjlxjijZawf85qksJPgidcMt8Vz5xnlkaERSSJ+UQoGWmrQStudkTo0"
    "SgOK3zQ/qIAwRD2qZpDRpFyfVbMlkmMTW5nZld133iCvxxuoPkPm600C+PsQHn157jVkJc9fG6kXw2NmEwkAgW3IDmFcJw9Xmdr1"
    "Oal21W00K9UctIZUvqJeIr9kx8xM1tETcG3Yzbx0kz0z3WTzK6Wb3MhKN8mCALC2MuMkA7jTDT3j5DIMhqigauaPsaN7mXFyg+NI"
    "Et8lF5a8z3o1YEHhZWJekWvm9zjV+7JR9h4nYNxIB0zxtyWvsJzMzBHtPQFjDJt6C52v7zz7592nn0Ml3Zsf7378spAOYXe98f6d"
    "X31MW+UGiCo7V15Gpu75a5SkFwU4ucc0UdJM5IJcwwbG7mwqysyYgqRnvJTUICglios8KEs0bB3FSqQ1FGuG6nZ/+7aGq3o1ryvi"
    "M9KIuozvLyuibybU4fcQyYNysl28ZN11Rks62Xrt4tnb567sk8t9a4vX3zYjQjCJ27n5ty9+97YIahBaTSJN52GY3+Q0yVmO8pR6"
    "+9OXyE38FV2RdZZZFQHsx/mDmpg/CI2og1JqNkulyiCN5sAExUcS+YmpFW+lsz2TirFeHQnHJ/V1kOl7HIA0ojGhczJJGXSqALJM"
    "vL02qkf9ImrqQrsL6ywRKGdQNzQ68Dn06EmZbRZIG/yUVI6S0n6/krxz31OB34f1dp965z5VIGt9UWqkk5Q/Ns+ksJGdcXa7NL0h"
    "jAl6zwxTAnmYbYyWaTbX5sRTM7WXuTmhHyNwkGXOhT9kLoyT5tYtUlpdthIUPCwjHdWrBQprBHQOBFOgKUinppIDH4vDmYpakpc2"
    "BKAMScdkAgGROUP+VfRPblh23aGQgw2b2XUYJil90ilEXTPSyvpp3UI0QpasOD+W4FRq+Xt0xa5jqfWhPMwIpleMZCGtDtDCakFw"
    "e4ZCCQkiwUi/l6VuugK0b/fGnyjy6boMj3suKyInM5KJv32QhkHjVMzIsBeYO4YfiSydcGdAhNTExOQZbq7Y3iCavsAJMjM/gsfA"
    "q7e+vPJ7OkCTsUTcyqmKyLaZaN3IjRL5REUaNPgf1ztZSWYfTXxgaHXJ9qrcIJgInnw8WGu98+EFDNDDI+w9Mnj/WUQuCXPbsyqn"
    "u1Hg/FWZ4YP3zbMyCOr8F++/s/vz5ym32FX0oYj9TM7LWK8bbGnaufGmCjkTAd2nqqNg6SXj7UncsEYwwY9gbReMC8o2X7788y9f"
    "+8UoYDgmTe3020vIdSCtwtgFCntCa7ezXjk8Aae124UrGR2OJc6Ebs0gt5vx/er+jUyW2CrcufqilRu4Slwih83tvnoBuvPV+oKi"
    "NYHFIVAB9QZE9mR3uFBWh+Ine+3S8CxsOZmr9PDHnavPEfODDh4wIndQPXpVmFIJrlXggZHJI2aj0dlcwsui2zaaJnZfeRdqIBUY"
    "ye1XX9x96UNgxwkFhZFqX6B/yZkE7sC2k/GGXIMIDzSiI2WyARKO7/zpp7u/fIOw+p/nU3QxDzvCmpxI5ym8pyASvbVQj5yFEzbo"
    "RWfISRTDLbpdXT7iSc8qU90YJCzpgH3oiIwkgxHp3oTVy/IOGjqBsQZC86e/7Dz3Ek3CdTlXSWyIFK3Qwtd5kP9n4DicjqOPJFz6"
    "Gz9yk4Mnbg8eL5Em4iL87wUSPn6G61zlU7h4CxMdXLylpy6giNpkRgLUvgh9THoEhzipKEUOx/AWCOsJuGvCehLOJoTp/MEXHxPC"
    "gHn+0C4Qy94MiLiZEJ7glPi2u9EJIhe30CtXOYlHEb9XQhc8EtZITLuq1Ef2yOnuUg5ZnCTiGjUF+vDq7ss/2fngFWjl5BdvX6F8"
    "pRg4fJVv73z4Av8AUeLaF1df3Hn+WfgXW3Xl451LsSyOPhLnrsyCBAq8axSiDzWhirthxF4cX7zzE6Qjn/4K+/iLv8KntNl9ieZV"
    "JD7V2vZK7E6oJbkFzt7puY6QW2oBcM9h1/X9WVxEGErLJNsxVl2/aJLmkdfBcOWGzrD3i8XTvRk0DKVsZJqwc+m/d994c+fcOxhu"
    "c+kW58gcuLOVU5Qui2f4RcF4Tj5wRrf7m15R1h6Tw2ZI2wvZVljlqqWSrdy++MztCx8Q5gYat00twg2Z2lYcMbzAMH9OfIqxkw56"
    "zeAhFbu5XqXtg2fQAEZR+ONx2P815uJ2L/9OoX/CQjVWctZaR0Xxbz6+8+qnFPN/5QyuYFi1z/1255OrBPr/09vnfhZ7myEeM1Kg"
    "z29hz9AqLdND7l4BOv8273vgbeESfmt+avE2eh1dac+d33n60pdvoY3zzkvv77zwF55l/QUyTPEAoRKGx+vHcdTMuQs6gMf1HQSi"
    "f4/G7G8KzAMBBl76C5q6xMDfUCgYpCf7cUZC4cyM8+0VIWLTj+SOSeV0T5s6EwrkAQnps5JaZwn7RsvWYpXsGrJ0J0h9XTk0kaAV"
    "hpCfcLuQzi7PKRLJOmY6nHbfuJylY17LVvQmcnQb0OtTh1LHseYlYfSqF/cKrcHJj+O9rO9rppqmwGVetue05DSDs57PUaLyr5Bk"
    "fL3g1YJOAhoSyf+FF2U6UEPjIRZJUou4nZlqjcwfIht5U2/mcG3AHowvRrtYWbKGWg+yy7N/0qjaD+q3niM8FyovryE59lw8geKd"
    "lmxZ9vGDjXli5i6EVOZQ93i4GI7aVhLUGshVJloTCjCxA2dsUbwqQWlE/owBR4PgpS9c+PJN4jbQkveKrjPmlMcS5E1PeSkEG40h"
    "iUFPKnc9aMyUsqljuHuvtni/K3cx0E8dXX3PlqGYUwf2E5bOwsZiwpV3mVacejrQHtSEHbhRGszFyB4Ls+i/OsQo7NT13va9coip"
    "l5KCibw/WDLhftAKevHLP/yRRGLDr/vOc78FsQS5AChz7sLjpygCWr4ER6946SXNH/KrxhiF0UqydxHQi42s7tGDYf1DIkWyFerD"
    "/nxJa+0lE+6OPTD/hsVETNE96E4QPk4A9EaPgvAMwglkdEk8SfdJf7q1VaRLymtXtZxu1yrF4vm5Kwpl+L7CI4iNE8MNvyCVhiKs"
    "KoHYyHbJnY8+IrKF8VNxLsWskRCEsOvUMVfOCbcRVaYODo1bMbC/an5yuqlX6H+4FKAdykD62kz2OzXX8YQW/v7MiwW1lHeeeRo5"
    "bpPZV/KuTEJ0iUxU1xE16tJPvrj6nukc/C8dgaoagRg+NnvxpAaGX9vDyHD3C//45LlC5trBc4ZxUfcIi/b3c7cya7yZOiZv3Lnx"
    "9p2fPqOrBrhV0uPkOq3VXwsR4MKfbl98C6NciL9FVLNLsXoDC5uIiazMwBA1YFqEtg+V5qcJeaRcX4KpF+lPKebmx4Xyw6fOnEJ0"
    "EnjymFPjSByxOlBtLusQVIOjXQxXO4x9i5HXML9WjKp24woIbrTtWAX5qjrvE/svDsDJSnyQCaCGY65yut750y+hQVJbg/hnTAsF"
    "Q4DqjJvMJaDj4cVrKEP+5T0SuK7CFoB3E1rPOPiSo1FuyFQOGhdBXnvcrO80dc1wUhvw47eVj1JCXFEqHLQAfkYKMziBzn8d1s61"
    "wkyB7FefGTGaA5Uq6CCXpVPxDPIbDNKpjMh9j8zzBqxVYS/dvSpWyAAld8SNuwqtDLvSXCld9Z6YuTvPgtBtFmqNJgjToZQfULAm"
    "lyvL6XnOAaaSFRUUc0NfUnlDaIYGqrr5SI2OoZe1+ATLlm7dqqwRxaRH+njPK6/seGz//rO3Cpmee1kOBflt4dM9sy2ceSbRFrpZ"
    "GgjPncafHrEdD9VXBzTDwSeJVuA9vRFf/OYPd/744TB/BfgarC4Y35ZXr8Nra2NqxLX0g2tNTInIrZ/Xtj8hMNeEbG5kQHO7NadX"
    "z+KPTYKRk6YL6jASAU9aKor+BhuOzWCXvWidWX2IhhvDW0f5FcWG6VR6COWSbbj3E3gneyCZ2vQYsxMPrAsi5C+OmUz4Lw5xNlDz"
    "6EaO54dJqtBzs2yt/TZ0esOMT7/0buYoxtI/uicJAbJ2zz6rezjQYL3DyY/wa+sJPuRft7CmhDpWAbkyHdFW1IYHNVQ6CMAZIeZl"
    "VLHIQdz6n2oye2kYZC63tRRKkQqDHo0aBELYMdRbP2rSN/LR4DOrI9qV7HNGk7EceibcvRYj7UGDFdbsdaoUczwOHAi3J2zvNfql"
    "6mzldbcRBJkqvL0bzxce822rsIrhmSARPeX2QlhW9hNbW2135iyCgT/08MOPz367cGr28e+cLqzu2zzW3i7cvvgqaaH+ig6PqP+j"
    "pIL/9zeFU3NPzc2fPv7duRMnDIFnKHTBkbyUIOQRNktIWtl+4BaaWC7+mmxntwTWcQ5fFbuZnXJW9WQiDVX7rFY5M0rZ2YZmAx0M"
    "y5XOwpj3iwIDq6hDmqEIQoygFA41V3WMZWuxopWmHI0L0OxwA+NSyVcFBE30B8RyIrFsXEK5B6uiBQRIEuUWKxihiBXRAsVkkHgL"
    "3zv/xu4Hv6IbNgIIcwNmzu7bpHDgfifa2pooUUKZmuO7Iu6khEBlONeYdjysOZ0z7VDklSyqG5gLGd98xFt368XJ0n6Lstdu4zuI"
    "SXkGy8lMt3ONona3RHhliGsrgHgxR6HdrkRaaPD3dJxcjDlEmNzyKegFxdI96TaKjB4WxjcmSjYloU/F4AW2k7rZr3YM5/529Wi7"
    "7NX3t81stVsWthb9DVM5qD2qJ0TAOgQtrsKGW+gvlmwqeMLZCPpROmV1uxrJF6bH2ltbPuxBGFJg1XxC0IBGgIQOT+lq/+T4eDH+"
    "glHS9jAqCunlgOzY+qfQXxK+hvxh0Cg86SK03eNLodtbdXtHrb5lRt2vEcylWYpr9sfHVXPGx422Hq2qJzM0NJUxH4t8tc5JAWSt"
    "HHBDiu2SjU1ZK8OGhuZ2sNeYx9tfzBgJ7Hdgdq5dXYMHa0p5hmGqYVS0aC10g65d7mGOzrLTbFqlrS3HCFmqB7U+HhZpSC1gW+Db"
    "9WANNqJooircc9vBqptXHtofQPvHOonMUukYE1ywwNq7DdguMuarVTW5vqOTdrfalgsBt9cabK/57SoQsjaGnp4symWOCaDOWfvX"
    "FiYX9xfnKQ3kPKaA3I+/2uTUvB8KE3znDN9jiFcsAw86ZzBcLIRHxI5K10DtjCzgO6KYSpVdGiU9Pc0DHPbj4wjn23XQPtjWSS48"
    "QJIrY6ZnR8kPXQ+iAvZ3YjE3x0Om9K5zA/EQQj1j2MYCD2N+vW293taM0Z2ZAUdHRZaagW8OptpicLENlXk7nhqiwX9/7S0rngeZ"
    "GNxGklfi9E4NAbqoL6RSo5qTHZunZ7QxJ/4yzUDtvvG+CL5DZYPETRwDqjiGH9cJdJefK+Imn4kQzdnq0dk4ondWH1eVwHot/6Xi"
    "rHlCb23NyiO2pOqYV3VItNVZewU2++z+4ko8OQi3mjN2cnEXkMjYbbWOWWKX3Aywu48ibH1lwpDNHSRpcZIwI41qlpP3jc8/OvfF"
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
