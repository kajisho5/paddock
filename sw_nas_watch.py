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
VERSION = "1.16.2"
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
    "qXygvJ3TdDNibpslqtuPn74U9yWuuLhPs9tbdz/pfUfb/UtZvb0XsNSKLnPX/+xt+xZHoPfQ+6U5C8p7i5DIcrn8g++ZSNq3JEHc"
    "nq6w29MVvCKXa3R5/Gi3R+1ru/2G3m/jGLXf0mDP3ujlFy/Q4T7BFqo+gMobB3zDcPje936e3fDgG3j+cdS+e39ryPvh49Vg5eVM"
    "0i+Wuv2X7Sf3yf99/7M3//W3/9Z3/uS3/u2f/u8//s7dkn+xRW764c2n8m214T35Ambl4Psf7TJ8WoLq77/6QVd2bvYcS/d2qeHt"
    "gmiBN+8eRdWcvc5ievP53Gj19hsNu9X6LQ+RETxO0Afv0EcK9s6hbac/69mXaXafOc/A/BtlXh4H7GmwPpfePkaUfPjqX334+h9+"
    "+PrffPj6jz589ce3z6//yf3zNz98+c8/fPkHH3785Yev/u8PX//LD1/9s9vNr/7Th6//+e2FL3//z7/6V3/+e3//w5f/+sOX/+rD"
    "V795+/zyr3746jc+fPnrf/7jf/inP/0/P3z5L/78p/9+KeRn/+v/s0jrD1/+vx++/MmHr/7em/fYy27gmxfh3vhfADK+971fgDHu"
    "gUAPonWRPA/UuhHv/f7ucPqfKu8Zs3zkG/pIqc2LnvnOh69//U6V33jo6BOuePPhy793I8xj7//Gn/3uX1/004cvf/dOmL/x4ct/"
    "+2f/4vd+9vv/UJPvxP2dN886v/Nv0SjP6uYjAfnFzeX0pFnuXPlNXf0i6R+OE3775qUJ/+Lf/exv/cGHL//Bvf57Q56G4S/+6Dfu"
    "w7No0j/+2a//zT/9+z/9iz/6zTfvkWVsXp2d8Jyr5cEJ+PlN1SyGw13VfFp88bFD8P7O0qDwaaHr55jKT6tm0IPncPl3s3z5Z2P4"
    "4duTFXxfVHhYBxw+Dit69jPeHIwPbqfPPrlvyr9Fby8K7Oe7Ip7drb5fLOP2je68+6SL/OLtD/wnT+Od3l88SMGxvEm2l1WQ1z7E"
    "sXwOHyjvS4XfnIN28A3vz9Pa8Meq7n4695NhXDxa6ncb9r5Jrn12Gv/w3osHinx2p90vfb67OfTuTtsvvvdAwMd7D8Dgix8+pTfJ"
    "nvUwt330SbzU+soNcVtHf1lWeIzwej0O2Se537Zu6D8Px9O0/h8r/O5X47/ffnNwb8e23wgJvQi1V0wp3GTkq/XXn7OGdINAn7+N"
    "F33Z2PHltl9ohUDQt703j86ppzVe6OdVRz+uRz2xzg14vbBO42d3xnmg7GKSSm+7Z6qg/pMKTcvXnpDqwTe93PRfaYoofE72lpbv"
    "lqcP2yEeKfrEIE+ew+6B2+/S/MPXywT/lx++/tcfvv7xh6/+7p//1iJ4/tZ9av/Bn/7kn/7Z7/6WztxFzm2u3y/+5l0M/M7DdH8l"
    "ipdSX9DlY9E//vD1b92K/uoPPny9qIuvbxdLGT+/yn/9oDT+4o/+84Os+4s/+i//9df/7ocf/w1uqrKy8ZvvgN/hb8EazXeWQh5/"
    "9eO/uZRw10X//l7Cb99F1VLa/3GTXF/+1UVUPQZhfvkfPnz5hzfj4b/8uz//6R/f6r116O98+Gop56cfvvpyqXqRfT/7wz+8NeNW"
    "4D94ELV30Ya/6uvjoL7/BcT7q6+E5e/cvAbvV8QNHtyGUn1I7/Qqpv/pTL3n0Ay1eYijv29k+vzxB++54r4H9xW521ui1VtmluJ2"
    "cUuD233kKmo/6X4FQaHvfe++aOCebznwvHt20+PybHr3K8TPeeQsj67Lo5eKF8Z6XfFy+/Pm0+L9ze/TffpS3fvp0+fi31+fr50v"
    "nlr+TaGWPwIL75ZttMnfGp/98MNXC3747RujfPV3H+Jbn1T/73z48q//xR/99C89B8h++OqrxRi8Pfvqrz28sYzz6/DZG7/exuYf"
    "38HHjbP+5N/844VB/uw//qef/fV/cC/3pwvIuHPzwp6Ljv1rf/qT//Bc3zLmH3781Q/vGYD+u8168+n/QNMf5tIN1zzp12904Fbf"
    "u9f47Ulm3JYg7qGajxL4MaXj2+I78WP+zzL4zi1r0GPmuGXmFc9S5DVc+mJ4DGN8EVXfctveqn/ECE/I4Mkae3/32L7ItvA2gt/Q"
    "iW6W3Z0G39SF/k22+U+tei0hC+9j1+vjCuhjlMJt6fTZKXhfYRruH38F+mz5/BR6dS7VrTW/+uaeVd5vlvbfMiYtv368GiN/QRm/"
    "9uyDWBr0rOS/tfTlv390YX8UTvrC7F+8/7y6rTkN/i0bhedWS/P8e7/fvf/FpX7cNiN7Nuq//eYdnr15bsW3TJZXtsWCBe645xWC"
    "eVFU94Cjm+Z6XET4JobxfyFouXPGx8bXcI+RfRXW+cV72EfevX8qsrofdvdQoH9//1Uc7XPGt/tuzpe1t4+rff/xQu3nH6n2p6n7"
    "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"
    "9UQYUvLI1RP8YX7nKJ3q0Zltfha0e1lZjvW7fV8sN9wTd45mcS4g9+JhMNfnPB2h5a2RfMQN456O311J1ek2dxShe95RfL+/H/cU"
    "wtu9SXz3oEdvCr3kkScxRSf7lA6q01A3MezUU5Nwc5KtsrlKU4i19+tVe3uzVw16Er3s6Kicm+diw4wvmHLx8fZo095MT5rDWHLa"
    "OAqByJil6ES4L5Qzs3Jme0TvifuC3dUPlN3cFtvejkTm4+HuONaqpfZiVZ49ckuzaqPU3B13xtlxPJ6nD8IZNphu9yuTfGxW2uzk"
    "tsPNrfh8t17m54n9+ua0JbRK7XSvlqQj5f6eJ10KV8Nx+oijh51OchIGczqWYtOV/XxmTHumB8lpJC0lgll24PfbZ5NpucPLseR4"
    "lizX3KA2NuqhTpvb3uzs0a7RpAXcK3S0e+DqZTvh+GTL1WXrxfSsX621Ye13i11XZdMVnLqlcaWdcu9thvvx1rgdHu3ulRP7Xtc4"
    "WR4k92P7sWSJmwUaFcFfSg4TnnBeZHNpFuhrIrF8uIl9hdNM2wemLT8a89sp3+4UGDLXPihxcXelEui7uv5+x592c8xsK3PUTRW6"
    "xao3X2sCI931FTme9R8Jnb3NvsS0PdlaP5TeCW8eBOOi6E7Zq+lJuBor79CyZys/7VUGfSHlj20GIpE9sMlCzNhdGqQPYjOuMOyP"
    "6qFhquyyz+KRZtKXjmzl3cmIwNHAvPN7+z3PYLuS62Xl9E6yUqQrYGGGgkx7zrYy1RlT62xm+YPMtj+cyARDDSZyFBtFqrxXKswO"
    "drfjTTADW43EDj2VG5nNpivJ5ZIlKTcb1Qqtjj/R3iznErFOJ+tv2j3ytjhtbKWrebozPpjXklWuEs7L4bm9Nijnu9W0uD+LFeh8"
    "S/TO/LmCm9+kB/Minz/aGwwrw4Mtvr5/lO4khNzuVqyT2EuxjW7TVRPF0DSR9w+rlXi473clPZVUMtbcnozL/kE1G2sHXbkYN49t"
    "dauB1D6fnPPbwVy6t+3dTCbce75tLhyMJyPjQbMc6bjr7UC8WklvNauxhL8436rGYgm5U++guDjg/qC97JT3kpNg4iA5aSdiQm64"
    "5XI13OGqZ7KdjhfShfoOUGFB7CeDXHx/4srulLpbjHiUC4A8PIjkevw0FfcX6cmoIU5Se5X+fqLiTU1l0Z9N1I/KEaCF5DA5lQA3"
    "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"
    "FjCugtl2Go3FdaDDx0DiceEopnxeh7vosoS3j7pNBxhiFAV5LXpRwtL3TSW1LruJ4As6m6PqFjTBa26iEmHNdXunaSrwqlc/zRo8"
    "i8T/04JpxDi60xR7D2XQQKhWDnp0YmrPaqi5oaON0MVy4c48fA2xLP1RuQ3RdNPfmMjCx+qt3KwJ90TZa9rw+huP02DF2ku3zMMX"
    "6yyh81FRDmqYacXjWIuY+cBD5HWRJPjceQZ5uSPUYe+I5LoXnrvzxNXdn15SWWczUJzsL9m5b8P8612L10Oye9pKye5ifFQKTaeC"
    "TMcuGgrJC0+L5M2XUSWoJb+TqPQvJXpLGsp3kdfSNJFJfH1ZH9XwvNBQfgJlntl79hUF7J+RWeIeWzJ5oXKcLSE+WPnQ3jwTJ+pS"
    "X+6WxT40McYJWpzrnrOSsyN3bphKW7kfrbcIRfzd23vv/VFLoG0kqGblLPDjldiTIm12YTxyVTUfMAKMDCiJ6627jb9//MuRa+bc"
    "+VWnvjboYZmsaU4u/3s8hRwBh/HnF58dhQMam5vERxpeiI6PGHvqwgZrOb3K11D5+j2vEbUrWd8dvRoeAvJLgHJySUh6nLEmEJ19"
    "7n8fKs997cHybHlu9j//M2w7ffc//5N7oQYBm1WZM1qUWEWK6If7yn4qkAa5F7JAHoZ7huYCYdwbHhsN5kMB4W42ibCLpbwQoiQW"
    "jsZwZ+MPw2WZtsb8TWAh9tfrAmmH4fTYc10GRd7YfeIiLwxMWzN7WqHRlM/2WoXb514tzD14Wsee4fsaTp/Ko5AwaO1d+YnKMS6I"
    "Jlt0Lv6MMpJeZ0OIaMiF58jY8zOy4jy1+9YLwpSC0mfsWI+56sUqvsk4tXT/r5nJD2PX/fNXxFsyP/moBCMK2cvM2DDiTE7txq/l"
    "ud7s7yQ7AkyKfpIppiWBwMgrPWZpRh5mNLyaderceYqUFbOtR8qqscrK/PGhSnmBI2w8ep2mL5FcFtfaZx99JDAx1efOU+oREWyp"
    "eeagkfclmvHrceGLt/QwX7jU16MW4Btja8o1aaLcZRrOHpeGMy/KN5zpIoiNTKEXKQ7Ti+QhJ7zAYoYTHsnf4lmcBvP/AWHjwH0t"
    "lHt2UEeSJcwIhphElh3kkNcFn/5Qn//6PUyZm+jVibCYGeMic5Le5BRyWvyKNGBqUSwZESzJQYG7Ta8FJaFVmiqPfobkIgdMJMFh"
    "YDkQiKHVaEwkrj/EtsdSGsW7PDo9faRVXPftuBSha4jf5aB3Gk2RnJVvvdwJGo5fteqYEUCFASl18SNFN0FSY2MICL9b8n0ax/h1"
    "6un3W9XlZcYtsi1t4SrvMRCACAksGYNuFuHoPMtcsUYBgg2zdBAvREF4/n0tRc27AmCSygtgsRjgi0ATVEwiB6DobzBKiMD/QvzK"
    "Wz/+/PLviQ84z2kZZEmGPbHUfVgNEieMqTihha2s2P9BgyMRD8UAffoGB04S6dXs79zd8z+NzesC1R2+GOMiYgtlFqs04aHCGr6e"
    "UFEqfL1lAe+nP2TQsoSfifwwg+sl3tDx9JZ1hD75XCL0qYab1WTA8qmSOXh/y5bAULRIsophFOlRN34iUBRXVmLxOKiDqFZBLNRK"
    "N415JV0KBdsVHxsRAhAcjBIg3ML7N4vu3+DcknoeGEouqTPcc/Yh+377Afur9tdWSB8XjXQRjAzvFKqaY2RF+KHq3w+0lNQYxMQ7"
    "Fr2RcM9vb0+t64gkxe/59hayakHoVh7r20Ov4RrYpVzqhy0Oso8/88NYy2C7yVy53SrQIzYFuDJhrr0M1MsouNUj73qKiqzcjwoS"
    "zw7MZLxlr9UN+i6rVc/8yxmgh6mMvVCqHnin19zNYdBvCO2N/kLPbhsvICFcbtod4ybmZ18e2ktmyVUnxLCfhaqRyhZYUem7zLaJ"
    "t3efeoUT7CGvduEvcFxgUJxIJ/MJcgZPfaw7s7AQlRX59sBXTfOqHIKqJ+LVsVMSLndNNkPqeb8RBL7rdGEGjDGpOvt8GTi0tRCj"
    "G+hHDEa0hmluh5W18lAe2314B67xz05cFVU/LCEcqBu5Ba6H+K3ELTgQ4HNBT2U+ehRjMcxM8VSZCjYRfuRraT9yW757utGJE8cV"
    "u2aW+DjJb12mRalL7N9GdU17PlXPSjHK9qA1ZQ9qFzNyZcCMzylnxfHGqoZem4GgK977MR9Q9CEDwQwDRhsyA7HqkCWThBiSK5x5"
    "UOXeU7+iYFId7Ui1BRX5PFpAKNZ4+OOK0ctCPKYswPKCEncLQIidDmY3sdu4y8geBJPCHBA6XNmoo+ZLZCPn5SSN5oS60DiMW10T"
    "E1tbk9NZLa6Nmdnp6ewZTGVsFv7WIm8zvwOruRJ/a3lFLlzZkJK9RmFPaj0KDBhekroV+1/Rsh0XwMTW8zLzdCZzaK+V5pHdshtl"
    "ZEWQq52ejn/H9irtXtKLoYKWpZjKKMurrq0+7dr3kxMasX9ruPrWYttah7LpjAX1aPitQszmp7WuWS/MtHNKptTAh0xgdGLIrZHy"
    "PBCOulb7ozULgfEuPM3oNcYZLWP9mNckhZ1ENrxmuC2eO8/4i4xbSBLxc1Iw0PJ3VjpuTerQKFcnftP8oALCEPWomkFGk3J9Vs2W"
    "yGBNbGVmV/beepW8Hm+g+gyZr9cIgO99ePTFuZeRlTx/baJejI+ZTWTpA7YhO4RxgzxcZf7Vp6XaVbfRrFVz0BpSSYX6iSSQXTN9"
    "WFfPkrVpt/JyQvbNnJCtL5UTcjMrJyQLAsDayrSQjLJON/S0kGdhMEQFVTPJix3dy7SQmxxHkvguubDkfTaoAwsKLxPzilwzv8f5"
    "2M8aZe9xlsTNdMAUf1vyCmeT6TOi/WdJjDFNb6Hz9Z2nPth74mlU0r320d5HLwjpEHbXq+/eefMj2io3QFTZvfICMnXPXKNMuijA"
    "yT2miZJmthXkGjYxdmdLUWbG/CM946WkBkEpUVzkQVmiYesoViKtoVgzVLf32zc00NOreV0Rn5FG1LP4/llF9M2sN/weInlQ4rSL"
    "l6y7TjtJJ1u/Uzxz+9yVA3K5b2/z+tthRAgmcbs3//r5794QQQ1Cq0mk6TwM82ucyzjLUZ7yY3/yPLmJv6grss4wqyIA+zjJTwuT"
    "/KARdVTey1apVBml0RyZRfjBRBJhasXr6ZTMpGJsVCfC8Ul9HWT6PgcgTWhM6J5IUgadKoAsE2+vzephv4iautDuwTpLBMoZ1A2N"
    "DnwOPXJCpoQF0gY/JZWjzLE/qCTv3Pd44A9gvd2n3rlPFchaX5S/6AQlec0zKWxmp4XdKc1vCmOC3jPDlEAeZpuTpYPNtTnx1Bza"
    "z9wc048ROMgy58IfMxfGSXPrFimtLlsJCh6WkY7q1QKFNQI6R4Ip0BSk80fJgY/F4UxFLclLmwJQhqRjMoGAyJwh/yr6Jzcsu+5Q"
    "yMGmzew6DJOUPukUoq4ZuV/9tG4hmiCVVZzESnAq9fw9umY3sNTGWB5mAtMrRrKQVgdoYbUguD1DoYQEkTCe38lSN10B2rd3408U"
    "+XRdhsc9nRWRkxnJxN++n4ZB41TMyLBnmTuGH4lUmnBnRITU7OzcaW6u2N4gmj7LWSwzP4LHwEu3vrjyezpAk7FE3MpDFZESM9G6"
    "iRslkn6KXGXwH9c7V0mmCE18YGx1yfaqrB2YrZ18PFhrvfv+BQzQwyPsHTJ4fyAil4S57SmVeN0ocP6qzL3B++YpGQR1/vN339r7"
    "+TOUAOwq+lDEfibnZazXDbY07d54TYWciYDuk9VJsPSS8fYkblgTmOAnsLYLxgVlmy9e+PkXL/9iEjAck6Z2B51V5DqQVmHsAoU9"
    "obXb2ah8bRZOa7cHVzI6HEucDt26QW634vvVg5uZLLFVuHP1OSs3cJW4RA6b23vpAnTny/UFRWsCi0OgAuoNiOzJ7nChrA7FT/bb"
    "pfGp0nLSS+nhj7tXnybmBx08YETuoHr0qjClEgyrwAMjk0fMRqOzuYSNRbdtNE3svfg21EAqMJLbrz639/z7wI4TCgoj0D5L/5Iz"
    "CdyBbSfjDbkGER5oREfKTAAkHN/500/3fvUqAek/w6foSh52hDU3m04meE9BJPrDUI+chRM26EenyUkUwy16PV0+4knPKlPdHCUs"
    "6YB96IiMJIMR6V6D1cvyDho6gbEGQvOnP+8+/TxNwnU5V0lsiBSt0MLXeZD/e+A4nK6jjyRc+ps/cpODJ26PHi+Rw+Ei/PcsCR8/"
    "w3Wu8h1cvIWJCC7e0lMLUERtMmMAal+EPiY9gmOcVJQih2N4C4T1BNw1YT0JZxPCan7v848IYcA8f2gXiGVvBkTcTAhPcEp8293s"
    "BpGLW+jFq5xho4jfK6ELHglrJKZdVeoje+KcdCmHLE7icI2aAn14ae+Fn+y+9yK0cu7zN65QUlEMHL7Kt3fff5Z/gChx7fOrz+0+"
    "8xT8i6268hFlr39RpsGAlXtlASRQ4F2jEH2oCS3cDSP24vj8rZ8gHfnkTezjL/4Cn9Jm93maV5GdVGvbi7E7oZaJFjh7p+86Qm6p"
    "B8A9hz3X9xdwEWEoLZNsx1h1g6JJmideB+OVGzrDPigWH+rX0DCUspFpws6lX+69+truubcw3ObSLU5kOXJnK6coXRbP8IuC8Zz7"
    "99O63d/0irL2mcE1Q9pezrbCKlctlQnl9sUnb194jzA30LhtahFuyPyz4ojhBYbJbeJTjJ100GsGD6nYzfUqbR88g0YwisIfj8P+"
    "rzEXt3f5dwr9ExaqsZKz1joqin/z0Z2XPqGY/yuncQXDqn36t7sfXyUw/5/ePvez2NsM8ZiRAn12C3uGVmmZw3HvCtD5N3jfA28L"
    "l/Bb81OLt9Er6Ep77vzuE5e+eB1tnHeef3f32T/zLOsvkGGKBwiVMDxeP46jZs5d0AE8ru8iwPw7NGZ/VWAeCDDw/J/R1CUG/oZC"
    "wSA92Y8zsv5mpoXvrAkRm34kd0wq8Xra1JlQII/IGp+VeTpL2DdaNoxVskNk6Y6R+rrywGyCVhhCfsLtQjq7PK1IJOuY6XDae/Vy"
    "lo55mK3oTSTSliBx5CN66IHUcax5SRi96se9Qmtw8uN4L+v7ce3fbwlc5rP2opY8ZnRq8kXKJv4lMoFvFLx60E1AQyL5v/CczNlp"
    "aDzEIklqEXcyk6CR+UOkDG/pzRyvDdiH8cVoFytLhqj1ILs8+ydNqv2gfuuJvHOh8vIakmPPxRMo3mnJlmUfP9iYR2t3IaQyh7rP"
    "w8Vw1LaSoNZArjLRmlCAiR04Y4viVQlKI/JijDgaBC994cIXrxG3gZa8F3WdMeclliBvejJKIdhoDEkMelK560FjppRNHePde7XF"
    "+x9yFwP91NHV920Zijl1YD9h6SxvriRcec/SilNPR9qDWrADN0ujuRjZY2EW/WeHGIXdht7bgVcOMTVSUjCR90dLJtwPWkHPffGH"
    "P5JIbPh133n6tyCWIBcAZc5dOH6SIqDlS3D0ipee1/whv2yMURitJXsXAb3YzOoePRjXPyRSJFuhPuyDS1prL5lwd+yB+VcsJmKK"
    "7kF3gvA4AdAbPQrC0wgnkNEl8STdJ/3p9naRLinvXNVyej2rFIvn564olOH7Cg8hNk4MN/ysVBqKsKoEYiPbJXc//JDIFsZPxYkO"
    "s0ZCEMKe08AcOMfcZlQ5dP/YuBUD+6vuJ6ebeoX+h6sB2qEMpK+tZL9Tcx1PaOFvTz5XUEt598knkOM2mX0l78rkQpfIRHUdUaMu"
    "/eTzq++YzsH/1BGoqhGI4WOzF09qYPi1fYwMd7/w94+fLmSuHTxnGBd1n7Bofzt3K7PGm6lj8sadG2/c+emTumqAWyU9Tq7TWv21"
    "EAEu/On2xdcxyoX4W0Q1uxSrN7CwiZjIygwMUQOmRWj7UGl+ipBHyo1VmHqRm5Ribn5cKB89efokopPAk+84dY7EEasD1eayDkE1"
    "ONrFcLXD2LcYeQ3zZsWoajeugOBG245VkC+p8z6x/+IAnKzEB5kAajjmKuHqnT/9ChoktTWIf8a0UDAEqM64yVwCOh5evIYy5J/f"
    "IYHrKmwBeDeh9YyDLzka5YZM5aBxEeS1x836ZkvXDCe1AT9+Q/koJcQVpcJBC+CnpDCDE+j8V2DtXCvUCmS/+tSI0RypVEEHuSyd"
    "imeQ32CUTmVC7ntinjdgrQp76e5XsUIGKLkjbtxVaKXfk+ZK6ao3Eav8H02TrWm2QIgGPo5NrCrs5Ya+aKSAN4xHekkiv20RxFbo"
    "8ikZfYN+isr+9rPXC5mOddYOWqYtTulC7/HhKt4bAeVM7ziNdfHKEfwlm/2bP9z54/vWTq6ZHjoKgwrNa3uNBozIkA4narCWTe9k"
    "CzP88WAtaquegIfrQiQ1En+5vbrTb2SxheY+yclOBXUY+WnnLBU8foPtpWaMx36Uraw1Q3uF4aSi3Glie2wqK4LyRDa82gmzkh1v"
    "TCVyDFWJdPqCiHSLQwUTbntjbOxqHt3I8fwwuRn6bpaJcdCBTm+aYdmX3s4cxVjoRa8cITfV79lndcM+DdZbnPMHv7aROH7/eQvr"
    "kNBCKvxS3p/aihp6UEOli7iTEUI9RhWL/KKt/64ms3OCQT5yW0sRBKno38moQSB4fEOrs9qib+SDoGdWR8Qq2eeMJmM5NMjfvfCe"
    "dhzBCuv2BlWKqQ1HDoTbFybnOv1SdfbyutsMgkzN1f5txss/8m2rsI5RiSAIPO72Q1hW9qPb2x23dgYxsI8cPXp84duFkwvHv3uq"
    "sH5g65HOTuH2xZdI+fIX9PNDtRfl0vt/f1M4ufj44tKph7+3eOyYweePjdh/MC8TBjlCLRCAVLb7s4WWhYu/JpPRLQHxm8NOxN5V"
    "J511PYdGU9W+oFXO/EF2kp0jgY4B5UofWUx3RfFwVVSd1ChwDgMHhR/JVR1a2FqpaKUpNeEyNDvcxHBMctEA+Qrd4LCcyJMal1Be"
    "sapoAXGBRLmVCgbmYUW0QDEHIt7C986/uvfem3TDRtxcbkDtzIEtioIddKPt7dkS5VGpO74rwi1KiM+Fc43ZsMO60z3dCUU6xaK6"
    "gal98c2HvA23UZwrHbQoGesOvoNQjKexnEzceqJZ1O6WCKYL4VwF/iym5rM7lUiLiP2WDg+LoXaIDls+Cb2gELLH3GaRQbPC+MZs"
    "yabc6KnQs8B2UjcH1a7h096pHu6UvcbBjpl8ddvC1qKbXSqlskf1hIjThli9Vdhwy4OVkk0FjzmbwSBKZ2DuVCP5wvxUZ3vbhz0I"
    "Q9oPfJ+AI6ARIJjCU7o6OIdZ5dQXjJK2h8FASC9HJHvWP4VugvA1lKiDZuExFxHdjq+Gbn/d7R+2BpYZbD4kdEezFNfsT0+r5kxP"
    "G209XFVPajQ0lSkfi3y5zkm+e1gOuCHFTsnGpgzLsKGhuV3sNaal9lcyRgL7HZid61SH8GCodEYYnRlGRYvWQi/o2eU+pqYsO62W"
    "VdredoxInUZQH+BhkUaSArYFvg1CMWxE0URVuO92gnU3rzy0P4D2T3UTCZXSoRW4YEGAcZuwXWSoU69qcn2H5+x2tSMXAm6vIWyv"
    "pZ0qELIORlyeKMpljnmPzlkHh8tzKweLS5T9cIky2OOvDvnyHoTChFpZ43uMbIpl4EH3NEZJhfCI2FHpEaedkQV8RxRTmZ9Lk2Rb"
    "p3mw7N70NKLY9hw0i3V0kgsPkOTKUOGFSZJdN4KogP2dXclNbZAptOrcQDyEUM8UtrHAw5hfb0evt1czulMbcXRUZKkafHM01RaD"
    "i20A0TGeGk6BS/H20ER1X+a6tpHslTizUVPgDeqLqdSs5iSG5imabNyJx0wzUXuvvivizlDOlpCBU0AZp3rwcZ1It/m5InDymYhO"
    "XKgeXoiDWRf0sVW5m4f5LxUXzFN6e3tBHrMlVceSqkMCjS7Ya7DhFw4W1+IJQqTRnLGTC7yAhMbuqLXMxkXJ0QDL+wgitldmDcWI"
    "g2Qtzo9lZBDN8m8WmeWtyXdIsVOjBlWGNeZCKshjlPa5acLErlnOmP+ClRBaSStGfOmBrc4OCHWZ20JwpfvYbkupLWPTloklGLba"
    "ElFmFnBs1nVs9nCi0Eydcmvlm/YUAZJ0pT4kK88KPNaltd0nn+EhETwjC2HB9LSvKsn8fC/oZQT4Ce4n+7AYF6KKq7g3iizfLTke"
    "Eaw6mv7mCLpah5Ey5slb5mJJUtCR51uKpo6UAvXRx/bj6YrNF2fq6MnT9SGisJBSBPUuJSSW00n2OTmPbYJcTUiRjf5EK9kPWkGW"
    "e2inlRhPp78GUmm/Xvl+03Z8StHNni/3P2C3Xa/VjuBX7v71DZICUuzodLWWJpaS1GH/qBNHmzw6PT2EYajl8lX6Rr4Xu1KqGYrf"
    "0jX7qB2WKlXhapCpCXbL656rqYO71cPf6hS7JV0rzDG7KOWuH/P0gEsRw3ErFXRxSyXz4yOBYxwybX1S8zuBqoQJJ7Umbzv6q/qA"
    "kVv0Xzj0EVcv6Z5XA9JtUZe+wb9Fn3afuKbgG/auvUumx3dun/8LgnqSPyQGZf7hPJpsxWG3z+bXAz/cR/PlGL9KFhfhzZ6vHW+v"
    "Rl0jkH8K1uWUsgBlO2OHQy+qt9UwSJcU5RGYhLpTBnxlqOXwFQZRmfvqnavPke/5TdNmpSJr9+eBMHwIZDY9aZtbfuj4sWPHv2cs"
    "3NOwcBNW+ly6HfWd+lratTCjIBolRQ4r3VpnTRhnTwqiY0EiTzXqMIIW2kuqU+qn7UpMLjt/+cPChqPifWpCaoLHteWUq21jdIDF"
    "mD7g7y4xCJZ0p7mCXkwUhsYqobj9jdaI5sHC8kXznuR9J1y49jNUR3xNO9ca9SmaYqkGf4n36N6Lb8IRaglizKUPmLafhC6wmZgV"
    "hJEb9UGYQVoCSpCA2YqBsMc6K7KrIn320YGnJuDRmhHBwYhp5Avzzu0LpIlE49k7ZD8jIAZ2z0WvYBWjc/PzXz+LXDkysFoOYcKz"
    "uIvKuTba4D+WsSSqzhEVCv+BvGolGJzmea/GvtPK9sHsYeiJJXgPg/04oLMfw1aa/chJD2zBzLWdEJhI+BeYSJqUJVfNiVumv8bK"
    "6PgjV0bXlXvyGY6zv33xJqm1b3KMtGU03N0oxopeQvg6ySIxCKPIP2Qk1ooIt2cslEvQo+RiwtGpt+oYvJautws1CbXbkEl+gbOO"
    "GE8dc2bXgDkPOW/AJJqUALORh6i7G609IfKJGJgKp4WcFiR0AIeNcVwZkp8bV+R6eS0zMaWZs+/DTEzUcSbOyyCGhqR1OlEMTYWV"
    "Xw4j0ln55Q6VgL9KbxUKvVWo6a3CWG+F/9fG3q+NkU7oW7PKaCQWVruRyyuspVkFa0SA8IlixLBI29vQXdHRLHMTckCf/Nwipa8f"
    "HyljxN5wIh2TGFBblpaqe9TQjlM5WTINIJrAoDMxbJTQR87mNTboQfmYvYnxvq5LSNYryveXLcx///hlSfduYHk2op//QPCyFNzL"
    "EF3pWOZ4QWuZGGPwjklkVmNq9YboC8LIn9w76myeRL5Od09jJHiBQIhjFnNMjJ+q4/6boNFxsrmCl8qoSKO5Bf9W/J3SPCIDmGN1"
    "+9wVWNO4j57RcEs45col66DHa/GgVcgfKjoivhrn9Doe59vyEJDAU6APX0uAPvACIb1DOCoSIYyLhzs2Zk8iMW7VL5bki9rYiBW6"
    "tWN7VaAIwRquVqQNbgOEpQZp4wJ8AjRAPgLaR/cdvI8aLvkABFZ5aQ+qxu7Z3g6EVszZ3vbhs71N2Af4MwoaAf7FoZAKs3grQcco"
    "qWN1sr14Ro02oxMXDmx5O/cd2IJFgNmJoGU7B7Yc3qEGgjtFRsOmddgSF3CR2xeuoavPxY8xHRXZ3iY6M0DyyjsvxhDZyZU/g1yR"
    "S9trgjLmFe9k2dazCvYyIv0ankmVQ6mgIUVLyIoWOyo7wCusYz4Y49CW93mOat+BV8tNPwj6RfUE4Xe/Mjc7e59ZtlSZHTshFlk/"
    "slmcsOd1jSgoumE4dJDF2D4RN6Xv+hpwX7kX9BDkkWvdAAm5V49g45Xs0Lb+zUKa/sOBiwfUbOnwnLAo3ADK/BSeEPrTmbkSHwd4"
    "FhisVXcUa2XwVJzUEXOdIo603OEJlX1QPRzEKvvA0PMDBSAioRfVn+M3Hy0ljRySvcPEhhToMxJUQPPrucrgd7H3nRGxmMhazPjf"
    "r0vfv+fjU02L4bPGOjSMloekW2Hsy3c3UUYmJz2aa6YtYXUx25ynckDCQhh0w7bXjEaPn0fkG6bljIkCeAXIldjffDCNUPpfIiev"
    "d2lABRKBUnhkHlJnYjTOc9bYIUkNcmJAdv/rtd1XXicv6U9Rrr3wtBiKBg4FLFrCtwb2bOSgpMfEV0NyYOtEMZBq7UoBh4SVvWYn"
    "4HOB+BxmXo2NZh23lFzXY9dzDqbiKCAZGZH6T1/Qas3984eXUkUGQEHmEx6W1hLGSHnA+SD/4nULnGuqpt8u99x+xwvR64oSuTJ+"
    "vFUbT2xGK4Dk8P9u99mbX374H23a6YC557h2beArub3qem7DqhX1XmWguOT16eILqDsTlsxEnzBIYKHdDzpu4b7CYqPlFojIEo7J"
    "xUtyHV4tzB369/IsJmuh5+euiNopmEcOVzI4AIN5MErrGqvupF7+psDyNAAJxBKEtTBbqgg2HiS3Mb3+4oXff/7OVQlOJHSzcCzj"
    "Hrv09p3rN/devc5evKwoQ5QL0SUBOCFBiFS2BIY/klEaqWAHs6FjZ4WVRDgBvyH10AcUzj9qqq7v3vzr7qevxnGZ2qpLThKHU/14"
    "bBPH7oYxOK3/vSQJtUCn0c+nMdlBqDMSONTnrkjrxru3L758++JvBSOBxoU32cQAaxgDVVX864c6l8FRN0ZiHSnXUYavWCFZGBEn"
    "K71Av3nk1CJzD6YM/poKvElFJFEPkqevGHAtXhc/rn+lYLbY2I+pb1xjmBAYor3LMNnXf/DICQwP+t3zNBcvxagRGDH1fxlqhyF1"
    "jFQz569rxjGdQ7uhJnf3Y3jlmTsfvHT7/H8lAn9tEDHkgs3hfNLzzXyPk8X3OP8EvkdyKNzw+Pic8PR0xOnp6KenM+b09NURicdo"
    "BaRRYo5QAlWpS0WJYlSlzDTRdzC8ObAd9HGpLRvhWjb+PehAH1Yq5C2Xzna46nS7aNU2BFl5MxyhIg5rluO7/ciKQ/pHio2ruhAW"
    "kU6CtbCxnOP1itgWd8eUdmzUE5PEM0KPHBppgws+Qumwxjek5Dk+wwJ//VAJCkRed+DOY7pYkaC9CM/1DJu6+IN5niUPdAwqsvlW"
    "KjdBaaUcBv2oeDYqqdyZgUopu+yjeywmJA1QHjT9DWsn4PtSQYtA6aSLBW6rtFJSXjTd8uOLS99dnJ6eEskH/Ophf3l2haDv6VEJ"
    "VdT8NXHHFn9FHmB5hbGRG8eb5J97EJ2PkS4++9fdV68xfhCFoKJzrhkGY6jlXBOaQtd6i/MfAV7IQqbA4LhNSk8HHfhhB3puJi5J"
    "aT4Sui3L1B8K+1gcJ4JiN82XP0o7hqOmRamhX4uN90oU2mCuxyBej+QIIhfld31alN/2i11lnulONF56Fp69F9+W+RBEkobUkXxB"
    "AdCQylCmXNGThv2gUwzv1SAKPWzX0C+GeQrG5RNFoA2wmsJSzSKY16eoW5dZs43aRzuCVduFZVf3Bw03LEalWKOdk0zmBBS0M9fm"
    "TsZMRRuZPu8p3ZCKCkKS57tNEwIHI2QK4m5yDNMeSW0rDQiXKhW6Tr/eHql+4qdpLHVs3g9l6kKG6jFQd6TdKOWkcuG5vbdevfPH"
    "Nzk77kLQ6WF2iArHV0jnmB8a+YO24EbVzCAU2+uFccLuxpOWji0K0Psj1UWvx/2Q4VkS9lfc9lHZ/qVhD7r+5nd1Bwq6YXTvJK4z"
    "LhZl+FFYDKFOQJ+YPu0eQDHAx5aSbVrKbNPS6DapjAxGm5KRQpw7c8cIfNOsJ3gmxdOOV6lmcJFovySEs2WlPXqSC/KL15/Ulney"
    "Fky5aiIIyux1V1QOsfwaBl1Maa7XEM8nejMhotf4YDsOn+DpY1ZAd/aUThDhBmebMnSz4QjKk+ENbhKjng/Lh0+FLLfjK0l8dh3v"
    "AONdRTz8JwKSfgRqscAZnSikf0xot1xywEKd9H7kVubmyl+164GPRot1p1+cmWl4nZIRxJufB1bHV19RERlR9UQRKBJbTIduf8EJ"
    "UeMtkLXD6tRUMdreFjtd/lhC0/7yiu1VH8azOcCzWc9t71CGeo0l9KanPcEYzYIwojNFpalq1UGLhWIWUX81qAIHn8EmNoCPiYpY"
    "3m4QbwgSTUPkZres7e2NoOjwEzvA3OhwGhYH1YH2+gkun+ywdmCW0CWH+pt6uVHmHaCKLGUUgdox3NOanl50ig2sbsDsarFh10ui"
    "BLW3Nlepxxczc4Jq4KXYq7VincPRopCMFpgkKr7c3n6oy92xqZ6SVoHYqmj8qYtWw+e4Cu1yezv3C+lPxKE8I2dIH4LkbJkTZLer"
    "vazhlfELzWrcIaKB09MOSxeHq4fmSdYwNDFpb9m2Sa9yvN7n9hNz4JjmUba0mlZUMq3m+g72fcPN2ondxJt5bgjR6n5wKpLgdoL/"
    "FGohM1ajDnODlqlMJyp3A1rSsCZKAz3io1Izcy7ru7Mjvgs0z3d6oav5b432W+1nQI0fCe0t9His9Oxw0Gx6GxVLZFCPT7oDTVkG"
    "bo1xA6kn4HDUEViw7LZ59GWac3lUHE7EM9a26xi2XVjQ1kEilyV7aqASxvmGyjTtld/pRZvqSBGwRpU5PcrZmcjeH9asz3/ze8Ls"
    "RAHBqlhjjlFosSsbPC8pPCa7m2qWtgZKeIe9b3RhybO3+hXHblUadtsDFnxqbsd2pFjPtESvUIVZucPCd5yePcTTaam6tWMvqHtr"
    "8pd2UDXwoOpJjqJe/ZYrqVNpfgGd+4oyKyCGV4VuJK9tUZekhhvVhXIrflya3xBvh274bagNTibxOt+wgWLaG+IVUYYHoIEp5RLv"
    "rpnvJt4r2UvL8mIF6Ll2VSXvmjr57MCtCj1AfsocgQEd0vG5VNoaysYkx9gco05ijDr5Y9S5d2P0JbuMCqkO9iEsasqkeCGIphe5"
    "HDYBDiU4kPueG79RbNlngXwdceD7reXZlRX66NLyWfmbT0/5ENqhHsJvZAzksmmUavglecFyAX0IVY3FUgWf1lO37ZPVeFPgcdiQ"
    "PWhVp8Lp6UG3eLJkn61uyDP2ePXw8eQZuwiPSclFD2UIoX2q2oLTWj1x8ZNhG0Y4pFlT3z0uuILxh/HjRWudj2OomfL7WvYp/IUV"
    "t9HiTVnA6EHlpB5QaEYaWk7fc2b4OHKh6FRLUjZrZma9blWgo8xzlHaMc+aRqHgSqCYOCjCtXejL0WDYrUDvtorH5eJfRFBw4CTV"
    "jQIlboSR6bsYF32UTaIw+Hp1Ga72GcR/3atb2Yfc6gBuYk7onVyOYb1rcAwkvi7mRP70MJg1jr6MfWzik0+djhtw66w6+TJ1yk6j"
    "pYuhZ/OaCgL2+ojOirBFPtDWrYM4Ha1SgtBsVvsbRbkhtrfr9pImYSzDzlsBwlWX632xCrsMKAFtfsuinW/B6XOqukj77nh1japq"
    "QVVnca2e2t5epC0qKng43kktO3Ll9nm4ZDtu9bjcP8eqh48l948bwXPaJvRUbaATbjVyp6fPqmcjt9Ax3kJ2p1t9PCyeApk2qm6K"
    "5k62r0LeV/g9sbFOuPHOshECwQqjGetgNyqHkbnTHt7HTovc5IZ6mHbAw8aGOoYb6lhyQx0zN9SxzA2lqptsQ02yyHKC9kJ9Oy3T"
    "epiePtAtOqVywz9czdsLjUQ8+YkiLyfMbHlKZH+NvdYIC/eY/ViMhPujzCCvx3L3X+jqX7QKfzv3UQE38oniMdxKj5FSHdbjPSII"
    "x3dw8e+LIjiYlazTzZVeMhJ2uD17K6p0uqoN3Z5NWCuRLVvCMaRWaB3EtRa5Mbk4q7jIh0dykQ8LLnJW4yIfFlzkzs7wS/KhRvB1"
    "dvieryuxQN4B5khSnqgqLGPzRdcUqEWjQiArDjyDEy1k1YV84lcPE8BH0UdmoukTuxKtQN3xx4CKGh8ja0qIGhsK0PhGsxjZIZGZ"
    "SNlap3xl9hMss3Th1i1/ywGSYIU35FS7cIc0cQ56c8nKHNwXU9WqH2t4+IUBUjuHWKH5ASqIGLgcelgJ7KgyiKPaPcFvsbk1KAMR"
    "m3HwX6AZzaKn9XbJK8KEuTBhXZ6wSFk3w+q6jQ6aUL+2NW2Pb7EKxhXKhTkyr2SFi1zCNAqpxJNsgkHzySt//OzDp7Oe+svSyjwz"
    "t2IHyuYM3/KVamxmTlqo76PoD9upHhVTT61EP++pqbB8cvEYGiDhDyeTrlaxjLxFi4hslahm6SWAiOYzsWcGCGIhIW6SIDtYSj2s"
    "CfibR7pR8LjnDotbq34AB4LVdR3MpgKUZH6ozHdLVS3V9NB+YHYWYV2Me3Nasnt2VPahJvl8qWQb1wvooY/wReIDbX3+LKvSDTHy"
    "uFlF4zVmgq/3asoXf1g9jDeWhzBYKyKY5keODHIeivy9SHhUqR0b/7ABjP+1O9U2eZH1g54lKvke0i++Yxsp4b544won26FV8RyM"
    "TYVfDrpu4mW8o73Mzigc7aZe66Zf8zoJdbxSbWQGXTHzgNgOPdP5oIXoCMgn4Lax7LbkGNoIUk0cD54EygIwwOdorQkTXI0rqWNX"
    "aPyYC1HsfR/4c1zPfNWCCWNloGArYIoeb8Ki0Nf8BNo74yBvyxPrW006Rtq5TEDXiEGagiEI8s6vnon56OScjut02KZkE+qaQzDO"
    "p/xigO5LdJKv0FHu0SGuj/nEp698KY8tdwxEhK7U9daOAnWQFwR7lmvB6biRo0MQdJFBdkMyPUtMuNxo9o5dbAs19zrwhvS7BaMl"
    "ftJmoO0ba5JzVr3mzE5qKdXyx7r2VgvBGm3RuTWvC2SyPSX3kqy25dtbaxWtkKpiw7fliTIBHmPHbor3FgL56WRTRjraiVG0jSwv"
    "eXkGA/QzQeyzWGg8BeTM4bxm6l7Uo0/bXcqBaozEfnufMMf5G/sHv+NDKAunTgp+68DgYKg+0BSRNlacR9qDquaQ1AJpSTcp2Wer"
    "wDBtqlMVhDF50To4VyqJ33DYonfKYvUsKV8UCNoPB24fg+CgXUH/iO8XrX8lrIcCsirLSnJasVAPg4Gvp6qHT5XxPhxr2EIMgT0r"
    "yC9I54tBcZGwt5KYaaZ/BH2DUUOTThIMNaFsdj7Z7FZHGe08NNr5WUa7gLk/B7m/AHkJ4P6QpwIeAQ15ZHlrI4/H32niTxXRInhO"
    "kREJmYbe9HRPDXIvZdWjPOcGJ3G2CsIVEPTFKsxOhu2INFCG7QjrsI/HtqNNvoA2l+bb1TYin9SdCMZXfOFUhpL3OKo4F2NB/1uu"
    "rKbEmsj5U3RyPVza3j5FGsiHSfV4ikTwh4XO8XiJ1NaneL9twfg2BcNK2nWQLex+ZdPue5WWAgPcMRuBq+zUSKXjw1X+4HGeh8it"
    "Pjzvo8Mm6hHkCDkuWjAdN9eE6ZsmzFQF8HqGGdMotuiggaEI3weZX5oZpqebGo++qTSA1PH1ynF7nXIfnC2vo/BcO14RGd7t9bq6"
    "CXXznJYqw/5y69+GfYmlZYeDVVkMKX/Cb29TRhtbdhM2Foh0rbASgby5o/ZFp/qYX2yX7GG1I/vxkK9hoXXkz4XqEoe99TGVSnFI"
    "oW5LpcqsvRa/ulk9vKm0OfLNRuJ5QhdUrza1x1NFYXnxuoVN0vbCfsK5PYnRGbCagljiGpS23Eq8XDZ1C3p8u4W3ja0DtbRwMUxP"
    "gzBFK7vFa4M0zFvwpdn5VWjjWsHd2cn1zxpLfybhw1YTcAE5uheFI2JiB1scOy5dv9O4bMzfwvOhDVKSvZSLqwaMba+PoCmwwodA"
    "lpdqzFsgWBxIbD9y+0FGBKiMK1yAqhcwrjCJ0J3Rm0JYF5gJqws9M6m3GduY5dG+Nkn9Awn88d3uSPtjVuWNMTbTpp8H3pwESfbI"
    "TDgTYyUf2tlPzrJCc1X0ApFqCKQlbSW+kfazy7JXN/3ihmmvXs40WNtWnOfE3kcLFxBxdT9NJJQSSrgjVAdw82XpDoSr4A+U+YKC"
    "VM5fN6BL4v7MjoaOUYZw7JH4mDXOJP4lfCJX/3FOkas/NPMk4Z3qZp5bZMKhcVU4NJ5MCkjyoUjooalsk/lz//bkTwvsQpuGZ/ji"
    "3O8/f+OKAOpiECPGXVANkQ6Xq6bH5d36Ma4eH+NcuWk4V27+U5wrqVF53pWbhnfl5oTeleOW7KrvtvJOkVQXkjhkBZIrKU+zTECb"
    "HI/J62oJQFg9cS1UeJe1CSiGVNT7XVZHUqwxzHdZUcProydr3NE7r/wxBzQ/6Dl1D9je8tey8mKla5fNNNRaIx1tVe3/biPlOerW"
    "gz5FciJ2GZw+URs4oFbb8H5M6NnuYgiEbsvYSUjLX3j/zi/PGbnCMi1CCU2cPAGy0tFdEznKzl8z8s3LlGWG9sXZgM8Eflip28SH"
    "PUa4rF1nHX+EOUoaKk1Qgbbi71KwrokY4Wb8AxWmsL01FraWm+6DkiGyVg9/YgJYISEkVGDA98MzT2P9dyYIAFifKACgO+qc0wzs"
    "E5vXsQfSJc/Iy54GGvXCjPzCo/ywVDn8wCRuV3o5ym5gZmKoZCa9TvtiCYu7ax3kuZEwUR6uMBDhWHJB1zDPPnrk+ycrgX3qaGVg"
    "s2dNCJxQZWMHiDxZvcS76FeNzn4xnyFjb3Q/MX1fEG8QJ9W+8GMjm9mF53bfukwwj+kYXP2bd+fLfY9cuVN6MG+jCCPoaiPY5RGM"
    "cARDfQR9ZZDyqut2UHXLfdtBvQgpZEAAh/mVMmSreriVFDF7WWWSYmo7Qw1CsiO/K1twFnUhgZAY59ukBTkbu2O1SRkib9hbDjR/"
    "ecVe90L8g54WZ5Wb1Vl2s7LbpMNQlZThHdYZtHQXLNGWVlji8loz1JvwGflmrI8ql8ttU4MinLCUH0hbOE7Yp8TPsypo7IjDRnr7"
    "VOycxe4hp0hcRtu1GdtI7WzGw9XWvDJiC2dxCmTxs8LMCVJ3ws65iHbOs2znXMREE7EOpWVHlUVYSB2jLy0ycJ4lA6eywT3SxIwI"
    "S9JYXGQCDbMv20R9KpF66vCcvSB1DWu6prQxeffO0gRIB1N1g9u5aJ+CdtLwoTbulHBgWUJ3Fx6GNRiWtSqvj8ZY/5UGuTacZQcM"
    "+gMEEZEVowDZ/JIRqUbPt7ctwbdf+YnEHngRVb+pOkbhCDDnr0BRDrZQa0bTJCYz9i0KlGvQ/AL3RVM4TnXJU2ixZB+H/jrxzjyB"
    "ujo3uX8frp7C5mE5cgzCUl7Chqa+d8IVIxu58SJCj6ShXOVuVNXbTE6A492F3FC43pGv0MOaq5DjSsOf46ZchRb34Sp0ShwEJ4pF"
    "MSdTS+QMQGpAuqUF4LpR6eCZVO7eqwe2TtWk8F7RZN4dDBtPuiItku/QouGKhKO7VeRh1J2R4jvsjQTXWe5Iqsp77Y401hsJhKik"
    "/9AJ1+50x3kQdbp36UJ0wiWQ9i5hNibW5wmVwal0t75FxyexZEpkRU2MZc5Ga/PxtKMStRYBz9y7czxCLbLpeOS4tl7zCnlCwerF"
    "LYGLxvfWKRYFxqUeccYp2TvUHRrBGqgQRWUiF1ZuTEBugIhqXkxIXaWRZRFjYTQ/pGADzXBwRMJpYSvqsKg8mMQZiy7EkjDVSVPd"
    "beARIaiFOF/jHqBKOrdUF9U+6GbcQrND2yjghhm4bJvVBQ1Kc6EMW6q/WRx0S6Njg3NECNqkSQN6eb2+M4kqer1t7dtz4K4kBknn"
    "oGVo/yjpIoS8B3UM7tUOQBhCfZSnuhPgRtebRkzOGRNKIEObeWBrs5YKFzICiBQxPpPUYi7YU5vZ0TxQp1DLpgN7bNhdg9WcxCBm"
    "uBSVzs3CGOZEdGlqAzMSSFEVZpXTEULqfm9MmFCv9aVxEHtCU1av6Rbyljj+OSBvLKBzNxj6BdrvYzJFCfzV3AVvZJI4WazjBLQw"
    "b5hBBbMdbfqm2YJgGS274RepglIMzVvZyOzvxuT9HdvVvd++sZ9+buQ7Eptd2wygRyGldX6V8HAu3D5/jTpKRseOs4FOCcAYRp5f"
    "ItiFyxoucaVjYFuMmtCEv1h2J1/9LTPJye19/qZyLBN+YiuTazdQbpNNbEys6/CkoXmKf323hpa+3Z+/YWhoRbHvqmJLNZ0Y3kyK"
    "9gk9Q0owDzaKsf+K8oFdT/mjZHiG8pGGrtzoI0pehUE1Kjf6ztDtQ/umInbDjNJumFGGG6aT6ZHYFB6JzUyPxGbCI7HJHonNpEfi"
    "oOolvAPzs4iMdR00fZZsWLHoOoTeT17C9XGiDyX8IjM1taM/ts9e5ftR5ntn6R/P/WKWx9v0tIeOK0KRfncOa3G7nOyWTeTmdYhP"
    "jR4s15N2u3qi6DPcfPGEs+ytUHTCwaLoQe0MJ1AVlzu67xk/0bzMzlTEq2hfQbdBellY5A9sPe7Gj4zCPV+U1DCg6Zv4aGf3lV+p"
    "stIfkYrvvXoOJo5BKmT10kcxrl5Es4s3pC0caxfukKpk08f911RwX2f+5c4rN3afeb9SOHOQ7osteaLYJIwihRZ2nrH4DxZ75QHQ"
    "pfA0poZG7yeBqUgZm878C2oOEZfwekKMZe7pjJ5OMuX8FhgJSxeDOOGozLmZeiXS3OGY9MSOt0ZtxSjhOGcb9aeZKDQShAlwMtjC"
    "rBjwsj2CA+kRHN0bj+CRqgbmYNuK6WySy3DTcBmONQBNVAA0k/J/0xT/m2npf7Gr+91nyP/CudjL5SI6BstKsf3/MNfeqJUQEka4"
    "cKrDcZGyRbvj/PltdvkwHPwlNpdymgT+bNF38ec3Nh9pFIW1qWQAZyvIEVdLZouCHpyyro3ZRKCWb6BLFlDTBcq/+xglzYXTeeSH"
    "ECYDphTdHtfV4ezXPITSowy9M4SgH7qcy3dm7lAlLPcxpRv8pBN9xEfnAy522Kt1xRAdc5vRwSoxcXXX84uixIxXqqArVzP6ekh/"
    "Ds4dgkWlvzWjvaXKzPBLJT00CA0JaOxzY2NfVxr79FgWjT3GCBaxlak/eiplb3s7mVbYqXpGqmPPSHX8wPS0q5zu2EeNlhgmbStH"
    "Qavlu0XK4e2U7CnHrBnYkJEz2JtgBtvaDPbYQa8D9HfAo2xrU9rTp7RUkSWaKpTKy/Di5aWmdCwqk2RhyIHpmYtgKBbBgCftAdi0"
    "Q57q9gxeNCn+qqPcf+EbdL5imsusNqxT3KDRik7GCK97ILw2iXzGdbeCKKDKS6nK0Uf5BJAwqFlm7lDTjOvv69VDWa8skX4n+5WD"
    "npk021g1M4d25tPpw8ORKb61NcrrUq4cBqueVWuTz8Lt7WJQ7bvQ3jA60vU6ZPsHPqzjisOyOmuHRRhkoMuDahvuwN6K+j4QfTRb"
    "pTJmkwQDVIbWlLMaFtvlhutHzvdLh5O3/qNEWEWjNgjsa2OQqrImu506Q6BxvXTjHD8SvzCKQvwUTs9H+v1giPUC+2jefAxXoZXV"
    "OfLfITcJoM6OzYhk9r/KXbW9vV7uBA1Cfk430faLbXkUxh9HKKK5UpxM3MvIIi5BvIAR7cHq9dZdDK9EqNl02WHbRcZgoBWdg6KM"
    "P55Rvk8J3QkINSePOTSbs5L3OIv5lpedv1y1FBuXWUK2TzUps1RWqzILag3b0Zz2PbUbAo1iO9WgltyYTKnmAxlq943N4hbSnIr3"
    "laJTc0YRq/KQs9UfqtyPYXarbttZ9xAvLOyAdIpOfjtjlSercNYIfxH6lcwCPFbR2F3Xc9QRTVJ5MS8/o+kcP/z7x5f+9uRPb194"
    "jzGhTV9IH8MzRgACtd31Y1auPwYSWen2In5r6gt5vOFRhxy/PjGP+bC/yUaOM5PhRj6oBrEp3jNM8W00xprmvgnSyVl8JEj2F2g8"
    "akHSim+PFN9S2ewJxTJmPzr/4Z2rt3affj6RGjKOj5RrrVkF+sU29FHHowhpoWNJO9OAPnjCSwDOPCROvDJPBWJlapqtpjicie9p"
    "6xdzX8teldkeZBwOJ5XqeS7edYpHdKCRGJbIwWN6jB45ig9WDJ3tJFx3j6w13PHJcK/M1U/Hq9Lp//aN1Op/buTqz1v8aTXXAOOw"
    "KP7quy0VeusmdVzd5I3lyA5X+ObJyIncUQHC0v1iLAs3z8hO2tneUWc7hxFvHWHptNg5eBBWSsz5IBtlAffXaqHNBc/OJX6hU9XW"
    "VgepQgflt/hNpsH6ywj7tMYxSmvpIw+aZOe/b09RKzE5mEWI69d3//yOloj4auzejQkDf04OW7GLkGU/4N6vYoC+14JG4FY61Xe6"
    "YdPtl8pR2+0W17xSmbOQNaqH4UOYSuH8p+gGhYDwEpUea0ZM+EoB8Qb0RGUxMW9mHI7YGZ4Ue1iyR5XwXQfNAkujSqDebkGcrs3s"
    "wy75oZGF9G+NKMSfw/juLHUHzcn2tswf19+4L+o7m6ElxhME/RAEebpXkkNLLyKFWaa3V+LTeAKFonKNxkPQFZ7wqCWz7A4sJa/n"
    "I89DW72/8ZByc1ShEuybGztLN9VW6pAnU1PycqR5w3CeFRmmXtzCe5UhnL8YmI4kEJjd+abhIF+1LHvNK3ZKO2n3/T4JjnqTuZlH"
    "RzZz6K6ueRFrL4M+oejcg5ZzrY+5voPZvE44mOlnkv4gQikSE96ImVwLd0hELMVJMnPAATeSRgnDKud10e89bVDMNyRJ33bCGM8n"
    "C+SPrhESsg39lUARbyZydFPiIpPMxFkjf07/XY2VyBeeg1bcPv8zUqxfUTlosuNd9HPmaDAyHW3PH4TsCp2VNJW9I2XsSYQmj3QG"
    "zYwJaJMpSazADsy91z0V9Cpzh3bG2yYxYwolU/lw94m3tYwpmA9cjQWOKaaA+S1qsM9fRyOjyjJy4WnMeXz+BiXHUTtmYERFROxr"
    "07Q7saeN5XuZ62B0ojLRwbaLUlvl0NfsGMb3UPmrJirZIpAuMh8BXSSTkeFAIO7pdilWSrPrDuluKZ0FvN01I8cpLaoduFAHae/t"
    "qWbZ3YAJCHNYIKez6vYNU8W5c5nexZhSDhN9PJ3wMUYnopJC6lTAMUe7BBTspbtDZjZgth9yiugB2+4Cz8fpg3vIzhUHiUhh4E6B"
    "HEkFrifHrF0d1L7lFge2vJMDf3EXlINCYiaBkd1oT4Qj298wgbgTlrfMN0zv9CDtTMb9Moy1PbUd806606zL7obFXilhE+slfN+z"
    "GjbUPtiuLbfJ67MtUCDRizhcSabw0EwtpcSSJvSJSQHYJ8wWeI8InYBL2DCSwWc4WPY3mJlxUBzxZHJweXeSOFqvNfaYsuRJcF3f"
    "9RiQl0hwffGyyFV28UUrF5d9oCMLW989+Y1UlgxKnaHVJ2MbLxz/NuZuQnLMOX9+HieNuh4fTkSKRezLheekVZ9d7NEZH443pvCp"
    "PNsvsd99TsxY1A2tCSNRKXmWynDsqJWysTFizDmFNo0IDu9lSj32Ftr6OIaADNrEup/LPnQzPobL0o1Blep4c+QiJRaOs8NrUy0Z"
    "g319szvxNynQM/5qvKLir2Yh/QvqSmHXCRm2LjD9xQtNvLSZxRO32treKnboYiUp7NY10BE8V+aPlAe9WhH/Bba/W3f9KrDlR8ob"
    "7f70NP0pO6vot14qVdzpaU2A4NLILsOBU3H5GKbjoyKw2HaSkoRqRh1lbmBR8bNxSAde0TmXSq7rxVl1vZHpdDPOk8RAjqYZ/ty+"
    "/c1yvGXNEHa1mT/UOM2n2EnNK3ukYPGQAfn7xy9bpLaBRaYvjQno9KCu5zL48L299940AuFkVH5gGyqbfoHslbnEwTdgwYEl4slA"
    "6KX7mEeSU0JJcOCObf0baWW88rAdTFWrtEhFImuZhxRlcuwqlEi7wsa55uVSPQLH3CoJNS5isoSocUH9fn/QtTLSbCGSTmoRaamZ"
    "45zMNlpUEbYHtfj1oNPxIqtmcd7BLN7NoK7on13JoWzGbANnWz0KzS53g2GxdN+ce/8MNGPW9qvh4bkaDCO37z6lsZnDnEQHrftC"
    "dPP//8dijyjzrisWtastavcfuKi792BRu8lF7ZqLuisXtc8L2Trox6tU0bXGBojwlIULlip03zFRi7L8mbCU5hSAnrkdlamr1sXs"
    "ewZo3aqZQ4ZjYD/78BlO4VrRXZxgRuds7Bb8gWpgsa97DTeodMv0117HTH14BXVub8PTJvzA66a6IUvQD7zlYBFYtF53LUTUK/xr"
    "1wMPnewCD9NiEHIBulfBH7sb1Pnw7JbFT8yMgf5Ea14QrlEajZ1UjqymDo11hNRSdpfFoJTa1RKaUzcBEJWxQbCeCSJNo3a6UHrd"
    "bxizoPSPRBQwsHSHtN7cNFb1JJLruGUcU7Sj4N+E3yoL1oacgFkV9WVDb40UuNWrzbK/ri11vETCSUkQpSzLm5/zI2IGjXInbElZ"
    "tKKRVR/RsXBj9JA3CKO+10PfEZQ+t7enoJ+YtwOzT8JPyhncbYFwKrsvpBgQXKaOgDBd98lEjwpN9OQdVB341RjUXdmh5sEOCd/2"
    "LIqzjva+X5PS+GlqREVeakGcIAtzfHZpAtKZWBmjSWfUHusdbXLsrxnaFcUK3FCKFl2hEo5baMvmUhqhs5Cka+WeiIKKFfYUYXbC"
    "zW6d3ej6m1vO0PGigsYZsoZacoZdnTPsMmdoYzgsmbx5JUjfE7jsuyG72XG130dXBeYim2hTaCo9/lfd+1HdnX2QCSFPabNAYPrN"
    "Ryjtka7RFEmtCPunz6G8vxo0NvX7cvSF/K3UuqnlbA+rI9eovVAt4kMop3M+jAVnYNhyXTrg7lp1gVmk5JqO+sbcdURaHStjtUaN"
    "eCGQ0bty/+xOiuCNQjaRaCZTncTCYGV3A0alkUAyqYnhabiIZSNGqCJuoulKjNl6DFmjrUxq7kjI0YUM1Wlm4hg9CHYhHuMSMioM"
    "HrpmLIlGxnrIClr0eoX6jHWwWdZ4FbjQtT6pHgz0LsQ6xpxORxkajQYIeE30BDG9pdErWNlNiY+9LlIq//QZdiIwxGAj4h8VBVzm"
    "zuVLqP2I9RCfffrL3ff+r65vuPPJDWCE9559hRAHOB/xJfGpJ5/YvfEX1C5fuJzSRnCm48uGBk9zbTbRUzMW6wPpxTraptzvJNIp"
    "xfptYtHfwkTj/yAaB4s6xAMX/q4oSmfugjSRayCRa4wkckkaJ3ApuDa+tDMZC812f7e8xRjWgrgGwTTYQS3ntDVgdJcz00H2N74D"
    "w3sq0OwdG+RDVnngEFCrVHpZacC8++yyd67egqXAOcITtiNm5+xiG303MqA3pUodPRrZ70wsgZII+edBfKjLvtR2R2RmFsdIduO4"
    "qGHNSMTYJGwZdpOrzZKxctc3sqgR2etHjkHaHqdM9Jm7Y+zeAAkhgnbKb76osthb9v2w5NGDXLwXjTj+v5bYGdbupbfjZpNbD0OO"
    "afEoky/GEZrPAumW49EErteRvJjhP6TxMScDTWfGCoa8kSFm4TSw2JUMXhspyKDhUkojpicrWS5Ayt2lvnYIV26vZpBYIOG65dUy"
    "DbEWSbw5GhBgMp18BnQQB+bZogtJKDVFjxP68NfMj90Qp9aF56h9P7t9/mXk4s6dlyBQmMgbUfOyGipNnYQ9Z08M3iZZHDHqmXxO"
    "k+aYnlebCX5HZ2TQvniF9R8wDHT5TKKHek9Ei5lDHRck2w0i10T/HH3OYzysbX1264PC7fM3zbUgT2517mOkYOLcj6MsY6Vcb6O6"
    "FaxVLP2AF5GINjIhTh2GzFh38mlIzddZBctGybFiffbJp3d+cY2UZaiwsG5fuIZKtYsfw0trwEMrLdC80hW0TV0BbDtTHZDQCtaD"
    "QReIClBo/OJB0q/Av1g7RVEEawc5sgqbjw+greMESDJa9REXJKpZ3Rbsp2DNmgh6v90YoYmDilgc17dxVDtzYCvcgVnESbxx5bOP"
    "noSdcGArErfimcjygsqy7jM3F/N/CA1SOSOpQUyV//7xy/LLF57LIQ3ajsPXzui2FdNXYFmXpYq+7Y11GcgA5CiEwHqDFKU52fY2"
    "lvHGyvY2/skzvTbN8CJgzMIIWRcf+ZgcK7/OvFNZdnQkPOim77Q0WrePfsCK0ZkRCq2zJm8+fzrX1GwGUZ67EscOn6OdT59Edxhz"
    "Di2JL4AfOI375O46SCld776L1t/O/cKauHvmTngXmX2hjEmLPk+TzfU8egeNGhTYbYbXjO6xkTKxdXSCVDxSRrcdg13skh0R6ZAS"
    "411D/Zfn/jPW0+fnGhN0Q5hbfvf23nt/HOm24yoc+gcFWk4XuC6l3kCqSK3d3t7asf1qMQQiyVrcUFFKvE6SycTqoAjUKJQuN91y"
    "r04B4nzp0+mEKVFklTXENNKPD6BA6iGBGFGyOqLj29thrCgPJ/HNWSbnnFffZTIKx2NR1sQdg9rw54pQgNpdc29nO4RgnWLJ8KnP"
    "b/Gxzwco8rPs4ZPQebfMcwzfC6XSO6qulx/KONZYudzw+qXxKk6qkCFPJ/Gx8Vf3uVkZINjwTqvoeiUDPhC9t+Vmo512lb9w5xe3"
    "di8+m/CcgGUwO3ta7czy2V6rQJv6N7jCn7jIL6HXH/CBAtFMQIVqLn+kspA0TjCTFy7H/KFym3Rx7oP/CUOaXLOiZbpzWFgl/0GB"
    "oMACBd6I8RPoVy0qe5HbCY1oi87a9PRUu9ygf3txCgTSi/Gq9xUWYjGRWK2tubZDVRS4Ny9UoCU6fBFnj5yRfQIgaYpcEPCpkubb"
    "xiv9G7yHqwzRaQdVkk4LbeKyZQF0TJCs9TyKnfL7KfET38gVsijXQhuagRKl02ggtVEb98DWCXm3tIOrM3UmIo9E3Ks8H64QtM9V"
    "UjDr3NQlrosVvxzbSOhr92Parhy5Vu/0nH3aBVnCdrRBkT3noW2XcG5w7TYVriKUaHr9TtHsVlt1CBVfLyql37+M5ulw3xQObDFk"
    "4gkjrH+ngDVdfuqLl95SlRGXqQAabu59cEk+Eno/+NqZUmn8tHbS0zroTjSxYaVJM3smZmni3gpO+MBWRzjSN7I6lpqkDk5SZ+wk"
    "YUSlBJkEic/twGkVuea2C9b4lKULhsgtETJpVvEpKj8/IS36UmRogvZq6w43umz+BIFaICJhaoDm9DQFQFt9zI5WRmyCUpbylbCw"
    "ao76QiWAnxzLxIqDZu1M/pIVC74odoioh2mYNtNyP2jrdPwShu0v9xM3SlYyTglxRjfEmsbXenuNsQRlU4FVkLWXbNT3+Aq7VVse"
    "A56IkpqiPAVWc7WAt0aMt4PpXwTC2b7GdrJRPTNSSyU7Tl3GvTCRTWcEv8Ed6MU7jIZQb5zOA1LWSSbh11ga/vzdZz5HO8fzNGno"
    "Hs/sBSpQlNILOFWQiNMMjazLNLEgf3NdIjYrbGQJZv6JroVRWFZM6hVzeCIA5hBp45HyIFwtN/reuhtWiykKyQ9gAkQRQb3ckvni"
    "8or9CNAn08iQ+GQnxNdietxN0+PVfjAM3VrPidpV6+BJF14gf0L4EN3r0h9b3kG/SbpH8ZR8l7gSuEl/xb3QVfZg0f4uUt+u2V6l"
    "ZEu0e0O4FqbC0CZVaKcaYTQVhk7rIWYZpVHBCbL1MRZrBTiauelpLgMjqpdYnl2hStDwSUHmVQseWrH2UHVpPZkpjtlUegl9OfC1"
    "THUXfQ6kB3L0ZDV/upjAwxD1MQOmsofMm/5LPofABKFbCe2h16AYrvHI8g2/VehvwL8ZB1T7kCHATuQmrGmVeokvuWHd1IlKh0Py"
    "Q8uSmU8UoxGBFTI+hDw3sryzb+gKNd3dTzFW7JFNKlUMwRlpDM1N6dHo68i4y11zidXUNdI8Pz4CsqJ9GyR4O8gh8l90pexH4fe8"
    "qI250h1KVYZndGk/mYnMgAFY6KKqXJdwn2jzmNxNRpBJGVX1NvnfkTvHM2xu8MvNvuuSmsovu2fdejQe1DMOrL9xefeJazR/OHPS"
    "IpxtBpZSS4oU0lctxGiI2hXuPPGgHioIgfEXlWMmHN3WhZTM9oDFyp2OYldRm25Mhro6jZJ8qocEzzP5VI1CqX2dQpSjprEUbIsP"
    "l0b7PQCjqM7eHkhKiNpvPdDbKMwaaUVoM79x++KbBOiV2NXZUVBK50Nb/edIny9chpN275U/7r3wPpy0ZgBarl/TRAs2nuAx48Qt"
    "sO6y8nj1+OnV04OyDa9Pcfvzvtif6tAQ0yFm2McZ9kc6CCTDDVghwhZsTo7LtY8kNvVB3yQ2fF5PsqMSNEC+WjLSRv2sQCnAP7RG"
    "p2Y9IRZ8KT+Rrm/oQ/mVmtggCXfKiT285OsJUsruVf8YTyrax8TGS6KprIweAbMkvKm4PGWu5/KiBuFYIitx095UY5ypfNQk1vJo"
    "PTxHh999Uvs4FgbNLMSPo/pTXYzyupqiBuVYYpT3la97X/n78b7iPltWhY4RMx3wmFcfxzc6JYNiEiRsDqqrIXnjCZYIEbvKNHjS"
    "Kmgn3TDI6uj46dw0hkEQTaQ8GKfl5aWI44i2yvhKmA6hbXtP/eqzD987I88d5ujygvAwRO/87QtXGRHSGplVS8Xkx+kVH9zJQd+R"
    "azjUBlQD5k6QSu1FldAQLUEET/njOEg6ET547nw6BjDuuIzPS4DPhCRLZDqQeJ1e0FcOJJGuAhNcrI2NDplwY3oo4wxj1jXdpDGn"
    "mhnzNxVPaxZojk8oB1RmZf5edMU3+yDX9+sckE5BmhoXrjwodOOc9FnYcKtbffQvsyjxDnBRcNxhzOx8Qoo8SvCOUo5aL59kMMbt"
    "7Skz6ZcmX5rpka4qwSMnH1IsdEp0RzL3hFU8KzDLDwh36GPSbVk1txLVeJAq6wyevK7Ak7e3RatQpvQapEXdcDF2OENHAHdD6GJY"
    "I6MBye1hqURJCej+aD5DNhaqhkGshvYGRfUYJoiwliFNSfvijOHebFmx5AvHWS9L9N1MJUlf7tpRMgDEXg5t37jJLctOle7Lp3aE"
    "L+/Yy0L2tbljK3h4KuGaWpYhNnuUrD3AOAN+DePwcyRpDHBQ3KDwoKl2Rd5xWl09Wkz65sTMWrHx4Z3RDngSrirtiCf4Slo33E6b"
    "ubIKLxBlMOBLWECUQLwWbm+rOzhTZDHpAXuKSAPQzM8+eXXv0k91aQYj+nqE3gM7HmGdT4J4YnyYN7dwodxhjTkvNtpH7YRv32jd"
    "g7M/nYPBolkIi/m1Q7O9DXtudvbfStbOWJ1EXnB7TDjzNREipDAJJp9yBWPvNmXAT3wURl23Lo2K92YzS24AXAsm5FAWmoiRk9JL"
    "ZBKfCBBhVJ4IoIU60y/dfdndVSwRxfr2CHegN8qjVzYM+fTeKBfaHmIQa1JFT2YktPFJyRQvUo1OTBU2PX/LJDvGfszOSXQM4wbp"
    "m8roqj+6p+Kb+R01e5njI9wraRzq/tm7YHo6AEGjR1nlrVRmhBtjkglm5xy8ceeVPxKg/XV9eVt5U2PSyIwMzHrmZTEP2ENOq/xQ"
    "UB+EqLnk0euauZk/++vTlcLs3KHTe7/6AHh0mUImIx+zPoNRagZjGG14vNUzUbSnpweJ3MxJ+pFIuPy//vM/C/cVKoWvFGoFq/D1"
    "wuHCNrpyauYDcvY7d+F/3T2ff89Za0dnPRGt79eUHwdWzfVJOE4xcd8MtJBgXfqhIyjB5ynO4WyKc0hC+I2Ek2+2RLIJhQGvfivo"
    "xl511khrolIyYaMFpJ8eloyAOQV1X/OCXPfcIa4LBv1OKmawtkbbdRoTSWeRNUoRJN2Mrcli/giB8SgdtkpRqqdoXwzrBu7iN5u5"
    "cXj7SLgu8GaxAZxgj8HYtCRtMlFZcaDDXWjjhe+xXmdsqG8zHDq9VLkhI20A7wYMds1VbDYB8btxfpKKNWOV0g6AQ33lrdtdYhQR"
    "ZuAhttuwPmSxj4lQonFRy0nUNe11FV0MDULBRFbVcWu4viVrhBlfTVUtnvP/W9lKs9kbltRNU4qB4/j0F+devvPa26OSNKOpVW1w"
    "1mwi6M4vR5iVb2QndcYjROD0cHZnaZiVqDbJT2Rfjkg4LbXGJr6YwbJJDYvuNir8rLXIN6G4FkNz8dbu7361d+4q+V9iwnMejhPB"
    "0O2fgPM44i5SSnfyPD1/g+PHpe0IU72zmlsi+e17mWRHpMdOYykZzfZRkokEephXjV3IgLPxp6f9+NjHtN4ZS+YSwVwkhwv7UWE7"
    "Ox/y6afhsmSpZuZWCIXf8FVrVQ9PtchLrVXurDG0sAwUFzlfD2J2T3TXxFDxQeq5QtSAy3JHlutlfKglcveJrDSW/GgcVr61Mx8o"
    "J7gW4pMvt8royPrZrReslWrRuCRn0rmdOAdvtxygk5s19LpWzVrc6PlBHw6Eirzfcepw/yGviwrTih5cw0EQnepRR0ySHUn0tmEV"
    "5gedMZJQb9QhZjtU4aVqr2bVg94mdq8yrHXD4pAzMJC+3MIMNJbAtbQX4L0AnQeDHrnHm0PldkkfVEI1yhqU7LidAL9uNzJH1ikZ"
    "iXof6hZb5R5MCLCkdl29IRLzFrfWKo91qATMPSzISmunZFawio/XoII14f1CX/EwL2PW57VZPJnAYbE3q4/WftQqRqU00EqOoJPJ"
    "YE2WOLHeH3RWJ8iwh7ZpmUXd1sWw0NCpkNM2jwoshbMw3we6Rb9UXoerTo5TdD10R0KlCbDkHNvsuoB8TuSY7MsF2hkZmaanhzxR"
    "bPEJCs2v3IOmpqz7rZKoXWe223NmIS9fPe7UI8MSLbYTyX37AQlc0uO1GSNwaHJEyRWwrBDTrYJOOa0c0TVwi46ZNTOrYoszRLFZ"
    "s2DZj2PcHiGSIuBKfQ2VevSDslLlVSRyWFEV+jvZtXXlgtTj1Q02Q8tzZdnqNdvafeVXePZQs82vYWKrOOaQfZfHpZgUNFD/9N9e"
    "fLagZ5G8786bH+3eeHn3r0/cPv+GSClpw55SU8j5gXxbTeOj8smplr31UCXKW1XJRaXefUi92+UkWSiM6Lmzph6Ne6a4eOLZj8Nz"
    "S/Pi0w7kmLc7sNXciTNrGTr8b6SPl+w9h5I1QsUgUydqykbSo2YtwGCbRo4fDOBDZDRjBGrKQ43az5/dvvAXYirFNBgOEwynjeXi"
    "x8BnPZOOdkNohxHUAtvC6CDJb1EPjq+iLwecblHfc9G30jh1zi7Prcy04B9BdZfh9kopx+kmtlK2tAa1CCjrLNClVinXyI1DhBmk"
    "jGivSDePT0UKmTaTLGXo/hIRC5lmoZt3nv3r7qvX5Bq6PtJbg/2/gemluFNOOCfZ9Nd2n735+cVPgBkWKkmbGIp4+jjWPMlfC7dR"
    "I9gK32bELXttErxkkMizjuL2/RmWfF4YyL+IhYE+K0q2CDuO749TCAvlLXTlSdR0wLq6eAlGpxxtRIqVh4ZrJzWwJMD8jY74wubM"
    "YJHEVN2COYC1w68DUTyHTHWBP3RJSEkXnrvz6vk7z7/NBFE/WTM/MxHP0hkLfXQC+bXS6HMJmlwDog1/GKd2hfLfCl57ZMbWzmoh"
    "kQESz5tP34DxxuVneN1dgZPh9oVnWQSVEuOLsXctnA0tDqLhlLs5o5/86jKJVNmBtS/jdFC1Y5NfSmVf301+T/tWq4yay+3tfPFV"
    "D626pHkTaLLVDqcYjvqDbn10cuj0CH/x/J9p76F4+sW5X9DShm5f1YZUbc6XpAZOslgL9257GoQiZ0PyioD5F1HRjCRw4fLnP3l3"
    "9+nncaaSx4kyn1w3AqcTbpn5DkjueiK774KUQ4T652y1xVCVtUecZfFzJQdb26i7Xmi44yM+WywfQCvP6jCBeEyhQBmsgTwJ/6gb"
    "CB9Yo3/VLZz7Gv1bsQQSjGqHLIM4m5rcqCOnnF2eVas+E+EwFi4ZtJhRM02ab2ZyvVfI1cBktLKYjOTp89/Oc+zr9G/Fpz/sba8h"
    "A0rtxj3ceLG2qsDqqrzd9/Tzd35xi/x23iUF/034vXD8EfiXN+AX584jeYYCmqrwzo/f2H3qL5Zsutg5/JGTG8A4RiDz4/lQEnIE"
    "paIJ77aPyS6i+PP5pz9DJR2xLNZ+NrpqTCJyWt/6ME+khWCFjCx4/2xpAjgJ2P14pGBGpsFkSBJRBjh6sQXiyRqQCMS3Fbnme36O"
    "PgDLFdZmxolkXA/JY3deuRFLXBOCxBILQIHghaJlH23Kq5LFDMEQSrqnQ+hRz23kuP8NQ4MpOP/q3ntvMhOWmtEEPYkVvjv6oRsO"
    "Oh2nv8krsnhWrbTtbWhi97SYzdnSYZjEePUlcC3OMo+3aJ+KHT2OV4+2lheB812BxYAh7/jfiv1wFe+R3i9A0w9c+Y3T6FcluJMz"
    "lEA6vl3aKfztyecK4q5MK82/xCvxkwzQ4EnxGoJeIQCB5TgQfyFLHl8+tGJbTt9zZhjBh++ouo7DIWAEtB2nUyEX3UGHHJMDAb/R"
    "TLu9LW+wteO0uJ+fyvwEdJ0dUVG4mgy5FcaTCHMBw/UXy1EgfFMXJZGdrJ6HiRqfwvKptbJ/vAzYy5NDgsYigfnlmftnoVsIqrAS"
    "m0jNA+NLc2e6Qipub/KA0HRYhPGwQdAO3GxgwDhqDlb1hkR1EFbCesKLO0306mgzTTsDKXdvbbUh2EwWGiYbV7fSdWS7fLfNk49k"
    "Xo3QJJ7fuXbjizd+lXwuyBDy+Ed8rwXlKE+uETpx+8KfCLf0o9GVs+Zu78W39166kNOEpz7Ye4L8WRfSUICJsjFToquyvHr5YRgk"
    "oZMydnXKf76ewQEbDinS0GMvJp9wLptTxDLXvtMifpmZZfs43MSgnpMz+Pfrcw/Ozo4BQH28SCYji7zfWgR1YHXW+sEQr0wbT41+"
    "WZVT09PHa1bbR00NFMGE8xlbIMuD3rSuYrbGyoMHz37FdKWC9tSsv73wYYG4ZyAwJdGufESRgtpXxFofw3HprME5wky20PTpGxGd"
    "Bjlk7tJbey+8x6wp7zEKfD8eV2HtsFpGC3e+JoW7m3vPv6/bN/X4XUtWR9DuLQH/IBNaoL0J5nbSngmZgQCppUn6zksfgaiZQOs5"
    "dPv8W5/depvUUQZkKaqvUNt0hURSEAPfh/bu/vUKD4PAQH3ibRnAR17D7Gqv8w+yvCppJVN0mOEJNKEWKjXWarkhCpnh9hNgyrb0"
    "qIbWfqIaRNMCZLTCnLci8yVTO5Pd61M5OnVgXMMIKL+FzMMpZB7S9lQlQ+qb6xT6w+HWrlmYFgI5wnokskCMIFx66E0bzryTPadO"
    "mHjDvtPTKSnbjlkyfxi1bnVYmfjv8sNwFK6IqfuRY28RY1N5mAVq2NSVuBS2rxO29DtzcJjiL+Z9SwmCueAC2UKCaZMYwydvTx68"
    "OREemUfaaIN/IgbvkO6WlRdhkqHYMPOu3X9oJ+HWUq8Xt9Ypt0GMptfscEryboaDdFRdRuCobuSAANu3ZdIBTAzQ8AJYCV+89ofd"
    "X78PEy5u2Qi8l5HtSvgwIrhkiTD61mNFRjDTQGZU3CPtBd5EflreHHRRB4KgfDMwShZi2ug17D75zJ1fvCZFegz4Vzrr3beuJqv+"
    "/J3zn//mnd0nX0pUv/vJm7sfP/vZh8/s/d//QjxNqvT4t4HgPlw+9LUH7ryHWQlT/HiGTRVG1BS9qGKitBEQWURBE4hZujZIVaAF"
    "s/hkPxq2Nydz2h3nMhPqQT5QawINcm2jCkun7yoYymQMD5Fsog04C7CdOD8A6lUzs+HZYm5XbGc1xCOHjoTPzz0hAq9Rj4I+N5T7"
    "Ee9dRZi23MkklzVVLaxrYmGfIfTRS7cv3qQz8KY0meEHqDguJnTXRUWM/sbef71954OXUen46ROwLuKyGjrlal9uGnL9kolm3M6q"
    "27BKY5eDmVVseb0LdQgEtd3XYLzOs86Scq6ggAR/KPZKpCihXABSGBQzW6/b3KIVLevI2sYyJtXBU5xE1N23Xvji4jWlzom7Nv9l"
    "mjxizXbxpNAc3OQg8YhbNbfs0E4jImGh8YiaJULe/sBkBDWK5n3WSlmV1OuyV/GL8o54RcmDrnDpxZRDjD6DrtS/yBEuzb50SQjO"
    "GHixaRr1qls9TDi/sO8RsRv+lCk/R7Bm4VfNBTM9PUVF5JMp7QnOH17jJrRK8Qpc2ii6NgL6KTg/lykxuer4cNU9TddCgaCuK1LV"
    "RhTeF4t1WWj7MOc6MqCW0N3a+PKKio1Zqx5W7jeN6uEG96/B/YMOxc44QdUrEilGzy74SYQWvbjgN9JWdNRSVUG1a4mea75ZecWm"
    "p4trghkRlAfGV94BCoOYKaKiZnUZjqczGbSEaDGqX3bOYHrCM+o0gHsO3Bvga9pJALcHcLsNt+M1duknwKzCk/bOmVFn3e2LtyzM"
    "tQ1z1BbKemd7e7C93avx+Eh2eRj3uVFH5y59CKYa9eJaCdinqpzJr1fnZmsCcnXNbihg99U+Ls21Hbg1xnw1zH/ZXspSz7rAAvhh"
    "4qBDwFP0ZqhgUN0wBtE+FbRawIesoUv9mnSpx4IZeO5CYafzp7Km2pnd55/94o0rxOvT5NGyhXGXTdzZe/W3aEBURzXiB7KBCwGe"
    "ENDtL4iUHR/lyXcvn9nBHueOiEjlmtw8HfsMn4jQIH/nwFaT3Cqtg82DFntMWrBucmdiwfYPx6EoE9PjWFvkz8RpZHgoMo3H3APe"
    "1wsbSK8U/yexARWIqfSLLFKWJtR/dimwPSxhhCIiAoaECNgl4KhQIAJGEuGquyJ8KsTbZw5swfERIhzby4hyfOfqc2diKKdzVkk7"
    "aE9uFNFioNjTVJjg1Bwyj3AY2CJ/ea7s5eqyl4uyl+1V8UDokUNumErtleHe03WsCeLUTAhof0J9qaeOlSyLW0g5xVZkAqpQ2tj/"
    "BzY55i/LXhcmizj1tG9WWBb3dN8RsvWS3H5d2KjiWmL7lfRPejoG8JWYv/wWu3fB+hdhCqblmMvwppTJ1t5TeBrCPxshcccChpqj"
    "u/wPHt7MPHEJy+UY+zZIvMYUkIcDqY005jGoLgOLERKLscKrTQh44oeKlObyeEbxfXFSLVQPL6QP64XUYb2QdVjPB0xDloU0adlL"
    "4sAUJ2RMZmFTnKYPC0ZHXVfMhgI1XmIFderIXpIKaiDO8iVp2HtgVniELdhriZNgYQdulVYk1+fgeYx584gDG1SxIXStNYzz66k0"
    "C8gCBRGwdgT0KfqM/IA87VAseZb43p+hFKMx7slhGIw7WJwUHPSSvZDr4ZZm+Zdiln+pPOj7KztQBTqkPnhXR9Vg5sHYlGH3VAO/"
    "ei8aqHwKEjYYEngMUdwUiorYNwakYsslygxLgmOBDluBdXCBGYDK6OnJYKLlzkKGth54+pS34/leOP4IimVr9DbL1u27HY1lGI4V"
    "Hg8BXL1EHkgKuBpnD3vBH2UnEdXo0bDvZk5s9gjYvfSbO688deeVD3effYZcBmBv/Zp8Im5SJhAQwT+kQMGP77x3GaOFGDhxNFyU"
    "xIy++vnvP5aIzoLK777+x92fYkKLvbdeJYArg/oJB584OiOknJU03hJIFzYjHCenI68DRCisKWqj+zWoEYk3WVPxib96+cykA7Sw"
    "UWyiYg7DMbI/Q4vlDKNMZH4Lh4PcKgjAdtKJgTlH3T8uz9doYRJENqXiIPDKKyRZPx8HLGF7/iIF7csyAJj9Ym6qk/OLc7/X/ams"
    "8V3L3gcdpJAyeeiyOGMofWhJ1ZbhWGLzEWghupvWWms/wyL6cvFFwhf5mNQLT9IaFTHPeEygu+e7vILJnPKMnCB9uPQQORoZzZOQ"
    "V6Hrh24B+tZJHZgSUdhci4zIjKLu8uwKBuGgpNfR5b8lYr7h6JnPHacF5Z/FB2dyMXfSi3lCutKJdfe1fesgs0gyau7MTyxQWOFN"
    "w88ILTzvKv/F9PAzXktyEljUIWdKozZjISuM1tIOzVf+AsxZ1MMq5nLBk6zhhjiyeNX2Gg3075e/lCyLzOkvf8XyWYGlIlGkFLMk"
    "8/9TGNAxHgvDu0u+GdB6X5oIlE33adK+vKTp4zJsuetp/wDipZcMpd7S8iGsZGn5/hV2qcBaS8q0oyTSIxkB6BwJTGmd2X9M7Fa/"
    "eviHUdHnyAsRyVeSTmOlch9K90P4haF2YXVqqosRISY0R0oza0Sk+0ELI9DTIen+hDnDe+2C3x4P3yrc/+Egv/D+fmLNjwUtEW1u"
    "IEq5ZWgfxrQgwnoGKOPEseZjQs3NUYjkvoskDqAC/jzqJGdpIm8+C4pLZz6r4UTOjAeU1i8z4kncX18GcCCtAClosZv8nF30ul23"
    "T7kQv16dm3twdnt7PQEigJCh6/rISVylUnrsJvYlHOPVR2h4kWZsZt9DX/oe+l/C93DvlU8tUYHpa5jZKC+R14lcCjix0348CyXK"
    "24U36fh/V/MvvP75n/5MjORrwtEwyw1RyNb4Ubfv5jirDo1t5eU0a70RRBnhlmKFeJRv7pRfFJ/MX/wmCKLyfLQxzhvVtaOjBRpR"
    "KnEWvkCub34Zzhh2eCVRJLAdTRTJ2BrYxUDkK7WGJjg7OcuALEKaArS9VBDuV4RGBGX8kKVrcFBOcUDKDEe3ve8n2o4jd1pG2BKQ"
    "I7nHjdZ9JQPtl0d9yqsHVnbeVq+L+J+6N0cyhxNCRctAqptJEB0kctmRfeevw0u7V17QMltdU/gJJP9I2IQVeVr5Lgg+daARsSZ1"
    "MYU2Pgon5dHp6almHU1PJ+kfGaw4NXQRQGVKAKEBNcJPzNonQsbUTlUkFcqRyEZajEQeVWsxrDs99AcVSHElMqQq4lbayqRzEhrt"
    "m82ihiPWCOoDZDwRO3URj99jXhi5QEyLFnytEQxhLXbZ218V5Rwho0vvkD47b4H3gJZa66RSRiptqyMNFnzYDoZ09LjlRt8Zun30"
    "WKMfFnqTWGszSIkR8QR+9jfSDmnF0y3NaO/qgCjdDYOV7jie5AX4p67n4xsZoDTk9i5cZCKqUKxkn2svJoqiYZI7IB2ki2f1Rh2h"
    "i5gw/YCbrzxn1vg6xnhZ30jc2OQbbvmHAy8avdHxabA+Wpmdn0Xtzp8uyCiiOAueLcMkL7yDGgsUBS/T7+ek3tgA6EO/NBREnvzs"
    "w3O7H71DQE1P0oZ8Bjc1yhbiZAHm3t1whf3pT38m4fnFdG2W4XkZw91EgUOxCfqqE/cw6Sj8+A7mM0xgusePdmSxk+4PiSaoxS9/"
    "LPouXwPjEroRxtJ03OoBQqwIem7fiYI+RhA5/TUQH33yZZ0fWwuZtg+E8+st2LA5exNdiIDkw9MB9IiYQomIjBxjGAnULxtLOX3X"
    "sUq4DHt9YrGPuk1n4BPXODWb+x21q3UTF/psuJvk3QiDdAyNCgsOcuLz/ASH4KG5Q7Tw61Hf/zZmgXbLYdtrRvR72QJ+xDoL/6/D"
    "/9eslTjPVrdkvLUM3KFthekSHThfRb2On1XrwHwH2b90/9E1BBifE/2g57QcpPRIjGlQjjSLalxgXMVEfWPzkUbRwgMS1e2wZhow"
    "Srz6FmkTluY3cOq+fh9w0l4vOvwvhcLXiTkp9F0fgUvhZ9h23cgqAKsdhkHfa3ndw/d9ZaqADMMQ5r8ehoX1B8r3l+8vbBe+88ip"
    "wjEQeLogV28X2lHUCyv33acVLdeDTuEr9/0f39l0+4VeH9de5Lnh1v8JBz0Ekw0LxWJxZuiurnnRTHuz14a6KghlUioVHGAvi90g"
    "KhQZ124GkTcrHvmYAGNcCPrw8kwn+NEMtBPxMcUj7cV64Af9Sr+1Wmz2oSV9t1HoF1qFVXi9tPUVu7LqNjEkt+I0QaazK5VVp77W"
    "gFZuzcxEw5l+gHbImQ2o2Is8x5/X725m3v2ReTdcc4fJ9+le4u3VoA9zNcOMYhj4XoPv+65DXoJGYQyGgSEjpz+z5rYD+6EyW5gt"
    "/Oss/E+/O8NDkVF+xvF7baeC0Jp824PpjEZUpj/LqtJ4nqwYYXGzXqL7ed8b9aL2NPt1ekSlMr4YNJv4OoOMzvY20o/4k//abDbT"
    "z5If3NnZEcuciO1WhVj8CkrMsJpANKjjRJYPfRUYFKhNm0SYfb9R+Xdqs5jwmYhmdw6Kw00X6Bf0orLu9IvqqiQfBINIfwKXpfid"
    "xEO6oR6HPeyQ/pzvlFRXBpHne7RhYSf7vtML3a11L/RW8fZmRd7bAX5/w21s9YLQQzpVocsdIF8gJ2/Gt/l6p9yZmY2xKsudaOb+"
    "LbnFg14FONJ6kRslhq1U+Erh/hKUXJ2ZkyVXgygKOhWzHBV5IFEku74HuPCDExV+UHx8dqLSc7NY3J9B24R8wccYA7yxU14FpntN"
    "ITTSFQyg7/5/vX1pk+PKceB3/wrsTChiaIF4AHg0m5RebKzs3bUcdijCXu8qnuYDSIKHmpcBkNPzEPzvm5l1oE4QYI/stuYRqKys"
    "QlVmVV6V9S7f4cM9woSv8hU+3LkFUb7EhfIesWVPvmSP4vVQQ6y8A2TDiYgddn/HBD8D+r4bbkCBr+kng0eevmMml1MJC+ixlr/4"
    "fCiLZzgIzHffHe9+Vd+xZdN6A/XuoK7uj1hhk62Rnmv2TETH3vBK62sxTAUGyRkBTNzOQHK9mEiuFwXJ6BGSy1lFAE/eHnD2MuqT"
    "RZkIREHTvOzSlSLHmNGa/WfO3uEkDzG2vpa/5vjPnR1yHbLUlnWG55mG9GrOXgHlZRfgUEwaGrOHhB5MXsOSlErc9JNymFELzIjD"
    "jFtgxhxm2gIzBRjQ+4rNATYezibiec6eYZjOV5CJ1kOM2K/5nlvAgnst+bcVgwaIaF4HGkXjOJ2l+Wh2eW8A0SrrxoYDwApqbYeX"
    "ZK2+HSz4E9uQEmyCvyH+5r/ZnsQwsFfYyHa4zNbD5bZGCWZLPdMhqZRD+qE4BBsfNwyWNVBpG1jK4LbnqqVNVsogMfKhBZQXM9jz"
    "mw/s/CYgWnBRIYO77dsaZaUMEq1eLaC8GGCR5sUJDz/dX2ABboeaENT0ARTS/uUdWJGDDdky38KVAD3qBj1i0LDzdQKnre/yXekL"
    "7W9tXfkOe3AXYNyDUWEUCxf9ptVLrlskVB3PpzMdGIfV/bg/fOeTg68HHKSE3coBgq9FI3/5JQEO/MtXBkbLakIsKUrTv0QTEyDF"
    "VwqIVa6WjszSkVo6NkvHaqnVstbuq1n6qpSmZq9StVej2CjFF/dIiKUocNSaZpIsSKIQckEDShKsDstGWQMYaNVdAHzKUEauLfWH"
    "VTBl6cGiA8w9olNoSGD5kB1CY+fSiObyOXvFBwaXz822NlfUzVaQi1HYFODyZhSyVwKAFjUDgr8TIMdrBcK1CkBvRDEsZUZ9eiOK"
    "cQEzytkrAUDLlgHB3wEIzU+1g9Vuu2M8t85X54KkFNqY5ioEyPxM98sP+Q3EBlUv5aILFeBm964XGNrjIDReK2qeUmarZGah9Za/"
    "ACWHGyS+B5rEWpffT1X2Pv/0958W+9MuL/ZVCXLhAfQcd43vvWv82r0Gk4V7wvfokSqC+GstuPo85NcioInCxMT5tnvTCk/2+D6a"
    "vc49bfRzJx62f/dtnVk2ZK3fAQBuQdk2//lBd0hxMnCqVP/x77ItNN2/zrbe/KhvbCw4PXil4d4fNSzPdMNafT7emcYs1XM0VJNV"
    "MzU8oORRb9owPhgTAxVaxNqwPT1OZDSrmSQ2//RP7O6FT/+Wb8958H/+KfgPTGezPOTBv9M1IbIAfv7ruToH/wbVgj/+SXv8wx//"
    "mb363/si2+5P7DU8//ka/C9QlPcrhuBf8n3x/fwpLL+XoAsPr/sQOzEsodto/UPxcf7pj3n1P4oMZi74F3iGWn/IyhWsepl8Pp9g"
    "bcwQ/z/kf83+48o6wUqve0JD8kUofwHygkRD/JHOkykIXDQOv1DYCXPdkIvmK9uih+UK383p3QK1NpiQEfwl9JDOP+dL+JstmBZG"
    "s8VMmKSUwfML/KFhcYcaMjynmzTH8jI/QOUcnvGJ7QzwYgx/sXwBCNZT+MPWNtB0MoO/JT1AEfZjPF1wEWX+efoCf4htvT/OP7+M"
    "4W8FT9kKFxOlMntBCGV3yTr5eTqaTunTzm8AP81G42zB9TfoyWqzyl8WXOSB8sksHqHxHISs+WdQ1serl4VQMuFTYvi2fCFkMIAY"
    "TV8zRI4CD6B7fXmJpwupykFn8s2IUHCJaP45S6ZpjG9AAsQOpNN0uhAaNlbI0zxdCAFx/nn5mqwS/GaQumAEVqMsXy+EXgldWuev"
    "1CUmlMH3rtPZ+nXBpEDo4ew1WaYLqf3OP682m4xqcDERYPKX8SvOEMrn2EP4y/gj69QY/nDGKUXpkg0yEIl8g1SyzqezTLzRvlTa"
    "ukEDCoBSg2K7zL7EIf5F8XgQxsEUS2K7CKlsXSiTClIjSQ/6K5xbhUyr4eUC85dnMJ0r/uYt/67MKMGsN8oE4Bt2DLYZZHzHTox8"
    "jiev0+krf7c/wj4GI5nNsnjM3307I6+kk+mIxgVf5e8r5AhGdDZTovvU4El8xVkyXsZ5kgqWjGdxFq8lSyZJMk1WDUsmE5jktGHJ"
    "ZJbGaSZYEsqmo5HCkkmevowSlSXTbDQZp5wl8xHQVCxYcjVebdbLhiVnmywmiiKWnMWzzetGYUlZWWFJ+S2MJUez5Xoz4yyZLpez"
    "6UyyJM3/eBQms3GYxOMwSiaDhj8nm/XsdSr4U+Lh/El1J1Oo+xqm4xnUJQISzPqyXo82K8msm8lrHi8VZqXq6XgSwioQJomoLjl3"
    "s1xu0rHg3Hwzhv9rOJfVHr2G0xn+P++34OLN7CV5SQQXZy+z5SZruJjqJtOXMIH66SQWtQVPr8ZL+HLJ02m6HuW5wtNUfzQOU+h1"
    "OsLG04HK4NOXHGZJMrjsumBws+/xbKAye7JOsnijMvtkNc5oQiWzS/ZvZfaGoSUF+xk6HqdJrDE00GH2MlYZWs6pZOjNKptkE52h"
    "5fgpDD3N85fli87Q8iMahn4drZqqnKFn03yTraS0gab1ZA5jXi641X4eyd+jeTSSD+N5Go1L1fO2ui73q+Ey/3WfF1+iNA2B7EZA"
    "wYoPzoCZTGAgAWo8Mfx0OtgUwaLRREHF/XU6HFBNEgGbTccMEpai4/yFSRPD43r+yn4aEgaVvh/myYz/Rmv3/PWVQTMdXVjFmLos"
    "XqdIGUgWY3O1T2YSaARAaDkKZibQaOBbRx/in0w64J+iyXQ1/NOf/r3WzdFEgVT2z//4Z6sMaJHV+4f/addbb6iMnQS3iolECYAd"
    "aLQAiF4JgB18sgCIeAng/wLJWsVIx1T6j0i9VjHR9OD+9zVZVPa/IolwpR7e3HfV8RBiZH74mchd8eAtpA8WyxWrduMOWBhWLbKs"
    "kTHypySaBIrddCGiOJjt8HhG2Rq6kp1Q0t8D/a4XpkOGxZiHLBiI3cIoY4LIBjnnesNCOP/p6R6123hhX9NGCZ7RcXhc5oVl5Brc"
    "y9s22vOrRok1xAjh780e2AJX2UVZFee3fM5vlfsDouHvuMMmFY9oD1tllzkNpfoSz8Hzt5Qgmblvy4vmxcTHIImSMsAqWRHAJoDq"
    "EiiEQKSbIjvmZUB1qrPid2WGpS+jabzO0YE/n4v5YFHzy6wQ3xgr34jWXQcoMOb1uHRQBBM3pKuKu7sIJZdNkHVpPwioc+zq2oXq"
    "MTnsL3Np8D972sdLQtT2FWScbFxO7YXtzVygz1CZ1hGug8KfwpYa42tem49J5MeY32+ODLnFFkAdJZDXBU+xQ9O6cV+zSk/ieGGb"
    "mxf0mSxYomkiwK0pVP1/9IaPw5yJjKdz9WUubvwe2FNHUANRRwDWZ3SwVN/nsB2J3gOmYXYANs3XHDyCjcfGyORDfYmQMqMkEbt0"
    "oGB1d56dsZkvKcnmKS/LLwlJRL4uCIR0PsVDNXp/bHJilZ8ZzGiNV4oWpndAFu9XQKyS4haMC3H3Wvz1Wlb7zfchBUzCasf9WLxe"
    "eRSLdToV1CP9SAoJo3eHT+sG70kdUoTOIWfrqvGOrbLGy1+qbIk3mL1/1QtqEEvIxJ8afEBhDAteyq0+5LGmJn/BM9a/x4X8a6i8"
    "OF1xBf5qLfQqYz7JdzYDKxyOI42xKzzQ6242jFE5Cz24BWqIxRK2SYELZCWGjW2C5O1TtkHafRY8BuOGgY6r7KCOCKiIqzdY8bRR"
    "wT6fv9accRzcInoyUZZt/C03bzoM0Wc1ROlQX6lgd7xcFNHgtluosUi0XcE2WrATahj3dT2e7hEoAlrMkq9BlBfkKOIIBiR32my1"
    "LuRc8ggrNyUMmg1Um1qM1D936xLNY7MLY8UggjF949vkaKzsGfhbC9iyqx6qWl3fMZxP9d4irSwOeVWhr0UEA8ZpftT9p6A3coSU"
    "k7k2GpUIXwmf2uAUGjTxJzPAb0pCCyXUbsTiWM5V+Y3f2aAO50IG7hX5AaSTW86B9REWG6wDgYzIeWdcJp+/cxHQNT2NFMDQ0CzL"
    "fJlADzHvhkvG0UPjCkwP1Ic1ZgqhTpBOE1s8ICXJuRBJwchPtkawgEsGUEg7e+djME7JD0/fE0RV7RpkMaTMKSxe5geQt8p9yStj"
    "RDY0Bhgk7pT2IvHVY77IGfDUqKySjBWIbLutzeVElgQgXgvBU+Eo+u3yaOPEYkCdJL1sCeMIhQsZGoprcvDbAKZqsKCwynjx65C2"
    "L2AChfxAFqZlUnQaSr5M8F34Gt++PdhLWrYgXfQdE4G8N2YTsoJO8B/yacTxeC0Hdyr4DaMEo+JiMxKtSypx0tJbwoZVSSyvYh9y"
    "SOFmPInS2G+xQV4FB9NDo1qdIFqfKzU4V/+CstLiW2fOSV2YETCy+pEpeUmCrKDtoi2kEUQXUa2lEq10qDkPl7DVv83pXxRrFTy5"
    "K6DD7i3juT59VXcHxgkgIjkD+LK1Xl9GlYBIeDJChxaW7mpuAHeaLUbts4bZZhapTECqscifhkzpOeCKQHK14M5vA53i8W8kB0VE"
    "1mH15bV02BVY31tQNIF01AccO0sTzdatKGTAY5lvdS5zmDncCq1gt5EuKQDCgGugQjxvBhjWonb1gzcw8yx/DfJf6OoOJivn699X"
    "xTX/WvvUTsNIo42LMOPy1SgZewxwQe/GxZIIguCyOpWd5K6xMZjf9tVqZ8XQuXiKLzQFI3bkTFY5IGHa2Ph5EbtstFZULrH/zBz7"
    "umtbl8u+JQupujqIbaXSKBlP3DtYSmIgrJVpo2OY+2IHXhVG94HZi9a5H6/1QZuTRpKvfxtZ9hYllLalhvjWxg5Fvw5oisIla3D/"
    "vPzXvMKsNrUtTMoydv6qFmrwp08L9+AhZcj556P30gzeS7exY2a/6Hwpq2J/6US1qlg4k+pLJ0XFvdw0Mp4pItvhpLyjP2N6gR8s"
    "y84eqdxeKckVKsk7GkRvdbsUkLh0oWl+VFCcL1Ww1KJjtcFgAD0FCLVu647s2m3YbiJQsKXRts+oe3HT3BrUQ1M7NMqf/ZJ1D3FI"
    "EflRSO2sOCitfXDYItQ8XHGmLmuhzqdBBOpdGBXvl+K8pQeTF5iOzNdU1co9dZt43Uv9wPJSaD0I9lofgr2hoqvuFd/Ks8wwIUw/"
    "2Z9be6TxJIgNg4q9cYgjLU9yuMl76rbNvoCygNS+mXN/Pj9LweoDfTxBTKwyDH8l7pkUrxximaqeIB0Iuxw/OXCEKT7AB2FCBdUC"
    "wlHEC/X8ncOWNRbTQd4ih70ku1yi2xBTLQSsEUQ0hNm94CY5ZJa0EnVT4M4vI5RRwjEaIAcBfxeHyaYYBCMWic/wUdagLghZ5XvE"
    "zig9ofAOFp6TTXYAt3AUO8fPb0a0+Y1Zc5rjW2xftCeHLGXGoUltfNRiRrhYzHN4BFZth9RRNNIiqcyMy9iG38ggaFkgC034mqJl"
    "QZgjRrHDNDBVTQMxCEEik1ZLVx1A6lHO/37MMQbxi2agQRqq+9If1gpHM5v+dEp2Dywr9Y/v3ZgefpDnI6P+gl0NJzN11FNt1Ic0"
    "6LE27Gnu1YFcHWzD9qp9E0+lAmsTPsHglvJoU9EctDU6Hvw2YLKynEZpwoJpTMxpJFrQR//+eY2X4j0UZU1/Ezv8ssyrbzls/6ab"
    "I+gp6bZYK2yzyGUnXWIU7UH/zPRd5rKLDrsf9FGskXHXj8HGg10qT6kvzJNYZZ4Vq11n5UE4EqZdfFx+UwT3ZvmMz26LAnaUK8mP"
    "jBSq9MIX3MZxKZyBpLbYp53OSO32ci/PHQs/QWCJOXysdKe8ZuHsQXmW+WCj6Vu8o4YAPzJMpwyLspzSefeCmMyiqD499cwcxx1E"
    "RdKVpJoqB9vx5PfEtMv6TrWOt1MtbYk1VkpN6atZqNOp2t20g+DLP1W3O9uWWYbx4vCSddKGJPKx2xHTccwagaaoDgvlWCoKnfdo"
    "dapcx/9sffHWaQ03NftG+jeCT7oRpJGbg/bbxp+StioHqjJ7Y3Nx26/0k4arwUIX0ATgqf6xVEp4WfhGCCKIfPAGb0SrXX7Th9ui"
    "EcW4Jk1cATP24TXHPxOOkH4HDJ8VkTV8ZRFZrE+tC6Q/eCmwDFC47kz5vtkSduReDnlngqg81aYP+cfOimgnv8Ck5CX9csTmcbDq"
    "4PYsOwbGDs9gOh47zUz4orICiemW135Vcu3yD5u+9iS2nO24yEoGZDNhWh5d2zTPdbBwLQe2eXtbXGrN5Ydz/ip0zY9xu8uIrQWc"
    "ldR+tNujgK4O8GjM+/aIvbA67LI2QInhqlgcRKfuux2DP7pWDZOEP0Cv1MqlyL0GTN7MGNc8As62ZyNHgL2MKNIH1cH8cA9FJc7h"
    "D/bFib4vJj7vic4kYg6RRTDfGY2scbhbO9e9sHlWVMeUADKKcMreX08FMfTpaJv2W6x2/W35wD0Dzcbz4rfxwA7nNJ+r7qhqCHv5"
    "DR3baOersm2Ez7WVXqSkk/0qHDya2zyD49cgqbD8lSMYGStgV1RoSrrgWDMrbkpRYdkb87A/hzbwrk28UmUQRKHAYlI8qw9eR6Ly"
    "EXZYJJr9tnlXT4Y7RlLhf8xuIRUXPfRv2tHJR1SkzbF0rxms7ZS0ubb6Ed87s5gqWaSueFdBEqWljP9W2lIiwQmwBpwND6aTO4hD"
    "2Jsfymooymmb1MTPaptDVu5C9p+dml0LXwQglJSBOEGjfgwV1/AtftNxdfZFhd8jyvQst0w6P0J+DitTzIMgFXT461F5M448WBq6"
    "hut4hBbyp+eLo3WXYcKwYCU4KlWcwKkBxkHGShT72CZtxbjh3f81azb8WuWujQU4B02ugSdIy6/Eolukb1g+aWuwawcPXF8sp4lz"
    "0248QmygJmkzUJMP+n6e9PSwGBmjWYYt+jUvzs51l0rZKs0adPvjYbVa1V2HrUk2k/WaGpUcdQuUvVwYunniiEx1aNcWqarMHFV6"
    "gi8ta9fCmesGP7XuI3JjHebB8q02C3dKHMoH5NUq3PFcLNGPXUnkNFt48v/gRlt3t/ct2rLEVXRXg42NpzhbuFMEMQmvj8mRiQ+d"
    "qjAtu0XwZENAQk3Pfitylr2vjpt99U55rZ28oUoVrQZLt/73SIWElvFq9V5k/oaX3PWm2De8h6knxeLNHqfeBPuGxxZ6suHbM3S5"
    "6hXXPeohI3aZuodGfBdfrC5qNLSySTFz5upCa57NwLiZuGgBKhTXFge8mxagVrvf3h2f4XfmA8I2R74rxtZvkdkc/ss5Efenp8L5"
    "04HDsrY5PNpUes4XIHy0ADowotbnZhzAdzwXbs3Pe1zib7wSPnucwhkm/t7Zhq4YEVtMOM1UFO+RoQbLNaxoxM+ZEno0/pD46bDX"
    "qZHlPaRS9dgyqxnh7U3i3PNo8htH8EOzbSIsKaMtZ5JxEwXVjawwQ0CIqho9kPOMzC/HXJVbW6RW8tk9SRM29TXUSSGEZVnVD9T6"
    "B/RMOFrsJ1DoNTx7DA2s1gkkITd9idKoPJ/7S6zlt+H19Oij+yzUraM8ZamL9STCjmD4uRaowSPL1MC+Hk4S5gabKv1Ieeyz81gM"
    "NkPHV56Mp5WuF9dB+GfCrGSXQEhYelJxcojryYCQRMIANofqoXF51mpYlsnqHdHIvBMs/EE9uqtElt6j9W5/0rnMMkwr33Uwz2j4"
    "IgfG/azdGHIlj7NhK0HfGGp+zqA11NQQ5AySGDEMzI7sC7CPfLorKxV6jC+gFEDISCxIjCwC66zc5YLK6EoVAmyRJTiAU93jNudv"
    "3LTvPRlOplTjYPiQxNvlKbtpYUttVqFmAmMxfVA9Op+McD98G5DY4jmUaoXX84jRG4k6aqSoEb4kEHSxH3OfeLM1E3a5u/Y3B99W"
    "A4EkWnXcM8XuI6rZ+5PQGwgiuu1Ll8xOTTfha49jYjGeEId2SIILj+ls3rojDNE4O2ALd+qYJfuccJMwpDGkAuq6Q3yp1vf/ohhY"
    "y44IfQmi2+5D0UMSSw/H6aLlUPqEDyJHScqpRQqy/IdHbEjMq403aEjCiCin9oVfqVB2TwPQGmbk0eR7G1OdWrUVAwSIVRuBarag"
    "jQTG7tB56pXvMmWXV/dRII/EbQZeYS/00zmJfB2dfiyd2GPEmykeHzJisE/I4rKa1U7jGZT+ttmEV/AqBESUGLwrRkZZ38zsI7F+"
    "WHyNATM9BHdDAJJxvGPXkasxHrnCFqLqvM6+u4VKLGdyk3mWoo8fVSe2sUMry8tn5H4RJaEGR82cETmz9kApV9SoHiJIfXwU9cKC"
    "nE5/45BMasUXLfUgNCovOwRGVaoapkm7iFaI/S5ht7txQyUnfglFbz8bDyi4PEs6Vlxdsx/gxwSxS8EzQ6+es1O0xmIp0YbxrAzN"
    "0Kzlw+irZedoKcPx/QGqxDarbZfAJj+NEp8xRHPmz9fPmSwvPPbG62MQMK1KkwqoqE78fiamOnmC5NVqbIyNtG6uHWDpiJWaTOR7"
    "dJc179XXDyOzCPh5pYzF6PkqihRUrrqfMeq1NuRypqttGjk3JTPMtNdJEtgwCzxV/hxPLzokE+AtgOippofoJsmJun4xzREsx6os"
    "a/tgghUF3is6SnyzGow6czroVWMwZaw+7t+/7EHoL7bLUMr7QTL9TagQuzsBqKPDbuVhswt24sZGWl9j0xxHJy/MFFimpDKM4iQ/"
    "etK5bLJVVXY3HzkGsRPBUDOBN3TPPTZFz6gLJcdbqptBPIf3W7Q79inPbU53JfbR55325lNs4iG9buAHdR8u3Y8Q9HKY2dV9O4I3"
    "4NEdpymN6G7P6D3qRLmzhzHA7ETaJat2dFFgl0QC3vRIGl7kzWuJg8CyRhK/bfEzxXH0qVjdY+OkXdtBt2w98B1V7+WDsLNDlPmq"
    "2Xli2TcqCHajnpqztD46Tv8hOp6jz9AijDBx52KCWddrz/DwHO3eIbKGg6d5H1i9toxQCBlEx12HE1jLDOZ8ryTem3U7Pyl732ZF"
    "YTnnB02HhDFBWcnciz2vsGwOZtoHPBn9s9ycUz1HtSq1XoqcOM1uCV/Q4T95OlAbTdLYrfOPrGfAVyH99PnYHR6V/IamgTCqlGtJ"
    "+1kivTkcLArIbw2DkDVZndLWpHBQc77ZFyhY7/aHtZpILqbSaJ2X1TMy24wNAkMQNOuYoiMoi1LKoUFDOF8+0hxmNOyTcwV7eG3R"
    "OhDl9VDjXPJNg+dwVIQfxbPsJIRVcNjbzDkzvJqUO0YMz8wZ4Gwnm6FIM5c34EyxYc4QsDMFm7mddmcKD3MHgdHobpx2QDdbU4X3"
    "MHqvO6QP/FbW/eNJWh3kj73Z2Sn7sZyprtWpa62GFoNo95HzoO2i30MdjDrgnsRuazUheK87mNMJ8lhua8eh1gcZGhnnIIIKk3Wr"
    "i0YjdtEl9fK2el/95mj3rPvCaJ6AAFCOrlCXS8Sur5isyUgkp2MJix6cOnNHUktct4CivB2J8q7muQXj8LNbLW0mzT3Bt82xajkP"
    "4TDJq0ci5GJ+O78F5fUIr78beWQfJxM1fDd3IoJosz/k5XOkoCAIql1tnOa2ZqPL99ppWz/EmFoPDZrtnojAfXBHw13MD5mDfjni"
    "2OgI2qmcCoVhHrOqXY/qKBPVLjxXe7jcQ1YEpoG/OvouCnFNnoO79DFB1RLQhsbb41tx/oaD5FjeDNBLfmLD6T/jpFfYHXDvdlbh"
    "uVbtCrBv920DtnNnlebW9bJyOGFNSUNFzC8yOJ87X2TwKODWjZ5SDvWJnD5flvvGMNPEMVh5kZJotCmCZOP2FpOW22QJmbLYJ0Ie"
    "RNiCesOAnjPMcX4rddwIoWSAk8ES5pr01J0J6UDtqHoQTQlnYl4ZBWzpTUifTAzQ9vz1/tCt9ktSCsCqNhNtz3Xb4atWYjix8CsN"
    "G++3Ddf4e18mVh0YPbopSA+z1YC633QSvwwW7kCx/OZX3h6s92aC9vz2yIOU3x6oO09rYFOm7PRXwKDGvotn1adkBNG3XZcwEuuK"
    "BKxaHmtHhiAbbl31bcIvYSG+7NQt8oXBRt88+hoWG0E0Tk8F7BzZocnJttm/5+sF3VWsR099jjP4W72MFl4NRVm8PKe45Vnd244t"
    "iSLxTKKmccDl8x6tD2KJovxplMgfhbvBD4np4t4pJVlfc7+cncdferX4eEXQsTwwuvgayy5S74cuu1vqTfnJ6/y83t9knkt448tK"
    "RudLsRzNKCsBMuZmh4cHnjnuUa2bOoWeyuyogZqMjO2As25aUtdYrHtkBg4/yAfODCuGB2kK5F4Uj7L7j5rPI30zdpoHMaHFfp12"
    "Ehbo1gctbaISm/7Y+TRiWTmgNcr1PD9VOyZ9fzmvYa947Duk5NydPArMG2u2zepTXKU7lNLlj1Ap9rDUVhhCujmfDbNge8a+jpF6"
    "aWqS4rSjJbMAUT3EjBbfnpxUdjpe/6ctV5GeA4CFdWHrngZHjxoEhX/dtfs2HtlT81YPhjR9Dms76uNb1UUdJ0BVqR2xyDW61yFm"
    "peyySPrJc/ipKfrOF1AQaq+6b4E+0vEnD3X81DDOTpkcTLj1D1FKnD2HLfZ60TxrqsG4VW3wbHUU9+F1wpqMynsQAPfzTmiOPR6g"
    "E6ugUXaozCtltHMH1AOVS+24VEf2WtrcBzVxqo9LmFrGuDmILjCPBMjK58lPw6ShaC+KdkYUTaxbmmCbg7+Be3Qqj3ltpZGeOjRJ"
    "b65Sbao/fPEUCySGXmGi/oc51F2i5qns6adSTHUt7klAC4rSee3R5BlAy1FjAth1j/s2k6t1iX/mg7feBfwSWlv7eLxedE28LwaE"
    "2XX7pAngI+Wp2Hru/2R68azxeulhHrdt7Sd08p0MN5e6RKQcKjq/EaCDDKoIE2qdXMmlqDCzCplyw9reuaN3TLs0Ay5qO52brkN1"
    "0uRO5arI113ClNrOV1up/tuG3u8Dc00Kdo9nCdbueDuVqqTRs9/a3YyEiTdhsU2S8tZWu21txLY8vOngBy2MzVjstj6PhH0agaCv"
    "h9rt6G12TUNHecGq2bbIc+tzHW3Y9ys9FynECfuv52XduvvETeRzmyz9uXinmwVk3SnPuUV3NL6DPl0/e7LKrdNrDSWKn859Dgs7"
    "set3H6gyprrczvYwlaCL99aD5DPXjZxj40ZO5YTE4xxS5vFmlgb6XTUQpa4DIp578N6/dQtQKd43h2xbPr0IGK5ubwMB6I9PnHXR"
    "/J1jDd9m6T3iGU2chzu1yp7r73w5N3zeBh1jVAy7x0Z6ztU0aSfeWaql5u51Tfxuu7RStWU5Ikj8mcrfWVy66kHpmbyxYbhmQqau"
    "/EhKW60uCgGHju4OJL1Q9Zsg0VB0Xmk9l3dzRBGg0EL6WTFeELHdUjpQbeosOvK5+vjlQ7WxqD+pO7RIBOKSo0OfjPSyDtn2/6an"
    "ANWLoKxIMb4Lj7VOpV7ScPiGTZM7rfZF9t3arPvrQZbewzDjXXp/A92l9w0Ko+ZjsUtBt6AsXuEjQTgCRWM1mfY8Hi0wFHhNGSKS"
    "DDieKPh9oQo6CF4s4M4vJGE+FrqgoqpgbXM4OlUANbhnzi92bCaqOPovXninhFSewMTYjvB1TQ2iwOBELQ5x8TBbu2oclkhoKTe1"
    "LVlKGr5TM21A6IN8OZrMG+Ad6/ejK0iUVdS/DW7PIgJBcfWPUytcXD3F4Txl3d1fLc4nU+PR6VzlbeF1MuVX8V7kpWfl0pYmdzC1"
    "SQuALPJn5xQQ7UfvCKZXgGPLUZeR0rM+MbiiSsegW97n8pGMyrN+GFfditowTGHzgJkPgePdobkSqsyOuWcx4hB407KCNi8K5al8"
    "2198LEUgm+6hurzG0dOd3b6s3AqtQUQIqKjNU5fanMycl1cU7/rJ0NbNUhN1m72ks6zcqKQdfKi8Zz8rsqqS/CWdqTCqX5e/651e"
    "mqRN8vkWt4+ZB5h/IW4Q9s3jbHg6espFsfotpHbZ6yE/jNrAmazoDY3gFVbXotdqw5bBBxGDupFgpnzHgThBniKZxLedcYikt+yo"
    "4v6grNWgaeStSW95S8HSTxzqFnspWgDu0M51uapbKuwdYzWBdt+6XnumhenFi06XNv3ndV+dbx3iZcTlz+rtkPHDhOx9U9ePXanr"
    "WR97LC5pbGWuJ0myOmdA08a30kpNWawYJMmfrgvBhxMM1mm8fBTGo9yaqYe2zTqqsBvTj+E4GGhcio5cPdYDe5q7I91RIAs9CwEN"
    "hJqNjI1okzCz2p+CKJm5rzmAwlq5sCH2jlY4w2shvadOd+vCc6ert8rSm5a7pYqZJMG+q7fHUVkjeYK1u/vq8etm+lcUmbd6jhQ7"
    "uq4cVMfl1wfMgua06Di6GnS12cIqXdbaHhs0kUBlftioYXKuy10FEnG/nqJNOJ0FAIs2+V+YdeGrkT+jrPILnTP0+Vj0G4377VBO"
    "hWnJLhzj7WKImXoQRhc/1Hws4qAM1rRyNvrWS/dlGl1S7olUF7bE4Yob898D478TBz/Dqfs5gpLXeZXtD2VEp0iNeAm17MmDM0wI"
    "YJdCGxlYrf4f8CO/UnBj6C3E9xfTmqkerPcNixOrOFUvkRpdnLP4mb3LPO/KNI+qDosbwv0UOpTVQIt55RQvPb1h9T2FLWjJY40y"
    "T0j3e4QsD3KI10KChsZyNR5DFtzMTpWgREaTBQj2GfwXBKu82K/mUHo9ZAU+l9q1Odka2EDfU+4WwPXycNP58xe24aj3C5291cpV"
    "dsi/RK9jvUYJy0RO+tvjTS612mO1YapPHXo7nFrdxYWjPLO2za4mShD/ZHKfwQZbnS2oNJo2cPo4lrv9EaZCx61s2SzWV8PZlLJC"
    "67qj4Vn90ARruxsHAWVYPdd0+mo2TQLMsLMcgqvzIBAT/gK4+GbkvD6Q0T/fKtbXYpgM+IOQhgahulC0QzapsFrB+FdoQLyX82yF"
    "+bXMsxc2Jb9QArdt0LGavNEP2TdE2erp4ej2kZT4i/XK0fvZRIbvKzdusbVBQZtaaAOQ3He8Kgtib+pjDLpWfeSprhAXq9OBf+na"
    "80Dtv/OG+JBeatfKNx1slpsOnZRbilkfF5zHY9R8xfAM6u2ejvsG7JpfqRIoSgBnMi/i8lLAeiX6tim/ZRdz6q6XLlPHZT4iVSH4"
    "DZ6jgvymxJ0PT78dDVq75B1p3xVwZJC1ct9xeHZbpKhl3x1p31Hg1bTNVEFc9tufdrCXVgsuKA3zG6AueT5q/Z664Vn5zrHvO+ne"
    "Ya3D/Pph/SOEggkCLd7M5xgAeB3hl/X45sdSLYqXyu1HYncMUrwByfyg5kYk7AtalH9wb6xbDmV/kvb+UF7IkOeHDOn+CqJ1vMRi"
    "IPNs4x743/bHy7moQGwyJZX/94Xhv4TxYGBzMq0gwuriSsTYRvPalRpkEImVjmj3aAwrdpOGgmF/Mj9XS2Bo+Yu14vky37BUM/24"
    "hN3kAYoUzBfU+0LXVKup38Jiu8y+pJNJKP4XJbOBnhxOWUaZaATfNrNuCXEx2wP7gPFxH+x3PNX7fVfu6vZPc+qY5vLbvlrtQFQv"
    "oEdh87jDfIW98PG1P2yRE5wdyLeuxQOlFvwHV5nann9+QFGY6OiCS6LSrkmgB4YJjd+twQ1oybgfyzCCd67BzTrpVaTVT/Ukm03Z"
    "SEW7rEQwaTqxUq7K84Ye07DCxYYW2pS4mvoFVTeeNi1f/74qrvnX2lRJxcGHS5Fv8gJ9gevrKl8Pj2fqZMCeB7UimYXd5KNQCDoh"
    "kypCx7YeSpEF6hMf50O+vzcvCIV4UDQ7W7SIkrFkfNwZ1fGRspHXLNwqqYdOsZfbsxRqCB/tEyHxfdiVi5Fy2UcmoHBrG3RobJGh"
    "e93SbW/KHmHIQ+xm9fQ36qD5BSJZWelgNC2b1XhY7Y+4tW6uJ3Z8D41P5Zc0/Ov1eOF3gdx/9xPZa3/+u9/9hOIK/Hd5Xn+H/6z3"
    "t2C//v0nJKFPP//uJ3hGIF760646Hn7+u/8P2c9CgA=="
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
