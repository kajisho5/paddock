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
VERSION = "1.16.4"
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
    "OadpcWKWzRLl8uPnL/l9iSvO72y2vHWPk953tN2/FOXbewNzr+jMu/5nb5u3OAI9QA/zcGYr7y1CIvPl/A++VyJp3pIEsTxdYcvT"
    "Fbwi52t0fvzkt2fNa799sd4XPGbNtzTYSzR6/sUH0+HOYDNUH43KhQK+4Th873s/z294jA28/Dhr3j0sA3noP14Npj+cSfrF3Lf/"
    "YfvJnfm/73/25o9/6+98509+89//6f/24+/cPfkPvsiiH958ai+rDQ/kB2PWDr7/0S7D5yWo7v6rH7RF66YvuXRv5x7ezhYt8Obd"
    "k6ji01exhmV8ny+wevuNgS29fitCJARPDPoYHfpIwd4ptGn1Fz37gc3unPNimH+jzeAJYc/I+nx6+5RR8v6rf/P+63/8/ut/9/7r"
    "P3z/1R8tn1//s/vnb7z/8l++//L33//4y/df/d/vv/7X77/6F8vNr/7z+6//5fLCl7/351/9mz//3X/4/st/+/7Lf/P+q99YPr/8"
    "6++/+vX3X/7an//4H//pT/+P91/+qz//6X+cG/nZ//L/zNL6/Zf/7/svf/L+q3/w5gH7sBt4iSLcB/8LjIzvfe8X2Bj3RKBH0TpL"
    "nkdoLcB7MO4Bp/+h9l5slo9iQx8pNX7WM995//Wv3aHy648TfbYr3rz/8h8sgHma/d/6s9/5m7N+ev/l79wB87fef/nv/+xf/e7P"
    "fu8fa/IduL/95kXnt/6SjfKibj4SkF8sIadnzXKnym/oEf+DpL9b/TN2PwzhX/2Hn/2d33//5T+6938fyDMa/uIPf/2OnlmT/tHP"
    "fu1v/+k//Olf/OFvvHlAZty8OgropVbLYxDw80XVzI7DXdV8mn/xcUDw/s6stsLnha6f4yo/r5pBj5HD+d/i+fIvzvDjt2cv+L6o"
    "8LgO2H+cVvQSZ1wCjI9hp88+uW/KX7K3ZwX280MRL+FW389nvH1jOu8+aSM/f/sD/znSeIf3F49S8Fosku0FNOXrGOK1ePZ67m89"
    "+N/kwUPwjejP89rwx6rufjr3s2OcP3nqdx/2vkmueQka//A+i0eIfHaH3f/8+W4J6N2Dtl987xGAT/ceDYMvfvhc3iR90cPc9ikm"
    "8aHXV2GIZR39w7LCU4bXazykn2R+07ih/4KOZ7b+72v8Hlfjv998E7nLse0LIKEPQu0VUTqLjHy1/vpz1pAWE+jzV4u30M95R3pa"
    "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"
    "+7c8nb12ux0f+TL+WXYcrwDM4vlUIkUXx8JOKV4Lj0p0dM55Yj1pO8vR8laQS0zAtHJnw01h5m6G4qFpgWvOdsdch6LbifZmKpGP"
    "JmNxcRK28XXRG6jxfrbWcInu/pzvVLJbdK/dnUpOjht6KIGrotOLpe1yI+fL7oFm0/bImSQ6zcLL2IL8bI+v9OrTYlGYt0dZP90q"
    "V4J7Ep2JhwrBdmgct+07y6zfHejFtythNhELVthpVcxOOnJG7PP9bgp4tXszMZNs+zVPE3Tk4LiyM+KCjZGNjSba1CTWjblifCla"
    "prpcEoy54Q47yHX3+t3NvuBlubk7F2pQk04/XxDzvW5mXsxtst4Al8p1k/1oMpup+tke5eqU42VbeK8zCvblWnOv5d/3pQeFTnhn"
    "Ond3i+VoMZoZxOJVbkL700Mp0Ekw491JIbEj5OVEb38rLzW6mV0fF26GMjawg8M8U/XIHLs99YadLnGSK6flqs2HZWt3MPLkm7EW"
    "SJjozl4USniBO9r2XFx0xO5kdyv5Hhcr8JlgKh8t9kEX7Y5CTinj9AQLrhJb5ZlkYejxp7xiL++ineVMOxAMxHtd0CZ74VQNbL4t"
    "ybefrRS2Ukw0WtsqNhi3FzSO/fwsU++0auGt7fh+I+aU2LDXO3V1arVkJVVM8kKnsOufDLldsdOOCXviJNqO1fc2892anObnFbbj"
    "anvpULabjW+y4f1dZljfyvUKiG+JRcZV5npeLtFla14qTcmDtjArddNZLpVNlOhNZzAjJZg08qfwVLrCb292t4bRYqMT2sls06lM"
    "O0qltvNRXyzqibHheWnQB+IqRuVCpbYrhm0Z385mJZ8sTiujuMcVy4b7brHnrPExKsRV2cw8m0nW6mFbvxGbh6lodC6HkrnaILVV"
    "iTeT9SCQdq5fCxYn2XTYw032bLGS2xNKFF31YMbWcZWrUXGaTLSLrnZqt5Rkc4xQBrBS6WoiUU+EPZ0dOlm35Sh+a68dqE2EjqvY"
    "TlDuWX3LE/dXcpnt3QaXcDJbzVorlWpUYj2wgmdbXEauJRI8y/olDxBOZ7o3S4tzuTff90ZjtkxJiNpsTqkSjbkKcVHcTzKxZC8z"
    "9cQG3saeu9satLcS1UByGmpVA3JdnJVs++HGZqpWdUVtpYZcT3UosdgQ3JPQ7jZdrbb4/Vw9xc3Dgd3AqLw5rHZFGFJi6OwKvhBf"
    "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"
    "v/j/x9x1uQ=="
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
