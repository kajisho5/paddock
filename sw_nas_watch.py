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
VERSION = "1.16.3"
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
    "gBiQFvJD2gpjstUsuS+PuFLc7ieBDtPJHA+dw5QKw1k3DkdFfaP96qVQeJc5cWnoUkJbj/tz4/A8HNFOJl2Z6679NtAPjYgsnXUj"
    "q0INZDj6DEky1bPsvuX2qQfAuCVLrRbEi5OVCmGERaMUaJYrQPyudk+CHYnmK0B/+dK+9f3NUSTSHZNXvMJmnapiagzL6tMSW2xQ"
    "qD3DJqmOAwHdKvZ65pJfghuVPFWtwqeN8PsYux2JAksiW9DrpVgcBYkyHvaKnvJnNRcKlvR0KDG4UDoSIaHXivUPhBRDeBiMSFwu"
    "h/A7vqrEdLuFGw99hsqK6Bx9dc2XQRapp+wgdK9QWFYGMQAhMhIj9d4UC3V3QtGdUEjv8UkoporpMYXUJ5FYoJ28TgyDUHcMZy8V"
    "ow3V4JdXH2EtD1UfYfsPVl8d/StkCmj4evYQAtV8r9oKSrBwVlBM9AhClYaZUP5/sfuoIW/dcw8c3pZQWq+s/jdMrazeb9XV+wwZ"
    "YRF8bnQ2BbfGJfy4cUsp1gvVIt/0cJdpjw7FElr2OsWCXwfB8SM+q9hZ6KS77t3Yn5lb2nhCYt/cJNuFF4u4k5YAk//Vzf6AGzT2"
    "MXWyLXi/Y9/d8SxzWMe+5E4e1xUe++72xPKgx/5yK7e98rGbWGrCJNUjhHoFaphoRmaIj+NspZNJVO5E5zxH1T1HAwl37GWZGjcx"
    "40xeNDWMf3exn3TWXuLJEn+0xiZxt0lAfucG8Y/1tb4Jdp9k7PdMpMXpiJ3J8O7emvUwqvNQ7OvXr/HVJ3J3DBWsd5qN3zHD07Ps"
    "vu3ft4WLxzx4vsGmebDRebWx3t4wlWWFfcdRb3Ltk0w20FHOyOT3WsWByEZFb/FlVbmx81yqReoq1mUdz5Ui4NpLqSD47Ln0+NZR"
    "uoLtNZlprb0hc8EmLbO97LxS+Z6vv5QZ19dePJc5nz97ti6zdtY77Rcy89rztc6G8i23trH28qVqbOPlsxfPVXuvXnSe6T7zOoJu"
    "baMthy/gKLux/vLl87aq5PmLFy/WOrKW9fVnzzY21mXDz1902pB1w1TaWW+319ahXqWLubHWgeIamjpCzsLzlxvrzzaeaeDqCKmg"
    "uv785Yv2K60BaiKUoq70HKe7YGIqsgLHwfZvuXuGy4QP390w4YU6xmkv2m15gGvTW0fCKGvIh5SZnj3KoKj6ToOyrgbxrCftONqi"
    "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"
    "uTlhweutaNFdUXmv/Y/v3lyZr3gVvrdMxvspXsUNdh89ped/5+8/p+cP7q18zjL6mxvzRBVWcGP8myuzoMcKnlj5deGWOvya9Xnf"
    "Hvy4u+UFHwsUs0+axYC5bbB+huTtpMqFou/vbxdTwM8XZfXG7xdovJLurxKJ76tH7g2vT6h4iR8+37lvSXr3EN8yHj+71UL6ZvvL"
    "IIrsFua69ZKGb7/Z/ruf/MPHjOz/7uAW3umf6Ky9/39LAbxfvPv0G2nir45S7e9BgjvNPUUL7nj/pgB5Mj2ehUR0K8y8TPpmYT/x"
    "l9s0cXgrj9S8+6y90fh9CE+Rgk/evlx+5/7w4UY8Nz/sSXncZl/kj3nuTy7o44BWy3hufv+Ngby0aPxXJPpq6Ta95TV/uujO3aJi"
    "bs7cfcQPT0vo7x75bREHbRxMHz1jYxnhzyy6Yh/cEXS30vhbeP7BvH/eh/ihizj8qoPwKLbzZ7GdP5bxu4WUMv+mLZonV/gGp6X/"
    "l+dP1PzwcuNJayHQrRbNSytRHLRv71TRNn//a1nGq/Xy6jdneVssD+/lUG9TutH012b09OLLdruXjK3oXmZyAd2HO27DL9e3LOi7"
    "BPkQwAGAh8tN3rx7WFjzlXZs7mx8A9oTGxfh46rqfcNKc0Pg/eJ5Efzp68e/8HixmKd3yLX3uMITqh6T+hb58yozNHjC9KOxfQsV"
    "3yf17GV/ANXP9l8JRf38CvXh73//yVd4CSneZ/chGOV/iBo8NfzwM8+uwrvbr+9C8YN8vWO4vnPe482nwTxnI33/+1z+NTw9fOXI"
    "bzN4KaTxah7PVPWydv6NYS0C6SWm9xzX+mYc58MrH07a+hDPWWMfhO75LnTV+pZ3dZP1Q/Ed6MFqX69duneEvmmGn72N4nV05dXI"
    "P3nzP715Tl159yA+rax/5Obuow9yR/I9UnQT/a8Qu/9a9oV7y7j4uccs2EUV3tabnqtP32j7xis3unlaRIj9y5t3t6NS7/tLXxYl"
    "f8rb03cXUXN//6nhr7//IU1YrRci/Pa3X5HV/c7Pwz56P8Ty0Wa437vVLH72W8TgvsLyC28uN0375jGi/t3HL0UQpHHuv/nF1971"
    "bXS3I4KKZUDF01EI91a/86Hrnzs/KcNP71vL/Ifx4/yhdcOP24fmFkf4uHmo74ubD0OxiJwFhd9UxV74gKDQa8HWfUWwLcb4i/M/"
    "RH7t30B375Rf3IbHW+/u5fTucuyjpssyt57e3c/7bt04fXlff/t8692t7NsHEnhlfb282t4Xnm4Lr99aKKr96JbFevMUbr9589d/"
    "8C//8p//4//2Z3/8X3/w+29ukuftSzzpxeb/miB49zKMN7/wBtCfWPC7qXv206WXX7zlAj26At/7e997BQzvZlncaP/nns2LBeZP"
    "hcAez6F/ifx8//u3GN33v298nVmXwT08nsz9yhW+4ecpa+g5Y1u+fbnzw6NH/kSfd3J9K94OtRjvJPRMLw8/iZheqPkVNS0/fKSn"
    "d/faRG/UmzB92si2qLpvPVLF0vbrB4tLUGdxcwts39INwtpdBOflzVcn92HR+YPzGN903ePS7q2Ke/yyoSS9xyKaD/l99yjTM8bg"
    "Dzx23/n/aigvLwFv/tt//r/ef/4nP/5Xv/qXP/yPbx4+vW+3S1/8OeQxmlAsIqZY5nwnzk8WOn35ctvvc0/Iv63GL2Rwe9DG7Z3S"
    "vnWjtOIF7DcT4HGr4V/83m3t7+Pbu8/U/e4DrQAfpoB88r2/t5Dk9z6+r3YtfHiTjefHXZO1v5gttf+sfW7FOn7mZ/KPultUJPau"
    "00Oz0Putts3TzRt93GPDTxnutf+oAj/+GegWnlusIy+9LY8sc/20+Kis73YC+1j68baR45HRg0ed/ZB7b+8lOx8tpufcwM/S10j7"
    "9EOa5PjgfhMJC2zu1Uy/27RFWfqXT978wo8//1//8o//xQKdF5z84hNo38Y/DZAfP79R3HNIP3nz/gf/+Mf/6U/ef/7bf/nDv3j/"
    "+a+8AR4fAG9+/MN//lc//JP3P/gnH7D1iKsnvC+CqniE8yOl/Q+C+OnqA4RvJ6p8ditJ9gzjbgFO99+FcfHamvrk7aLni0c9Xzxr"
    "v3u3j03e7Y02uiui5WbRfLcob+cTSe7Xf/Xu4zvy3BfkffZKPNm3sPst3d5apONb654r9/ZpXFR3iYunrQWLbHq8Ofjna9y+fnQz"
    "3J7OS7iN6qXU8zI065bmu5C8/2E/6quI/0tJ3/u6zweAPknBZTz2PTJuvZSvfZGIVnvPcHkqknBTRcBH0PqWaf1UmfZDaK27vXff"
    "0aA1Xvy0++jdQ/lyW3AXRnz3c91jYa43zV0ydh8FN2rwc2962vOQPpQfhcurN8l0L35I3ft9u/J/9raXMn73/Py28/u2oTV2U9PN"
    "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"
    "ApGYny0="
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
