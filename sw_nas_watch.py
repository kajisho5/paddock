#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
SW NAS WATCH  v1.13.0  —  SEVENTHWELL

NAS上の「演者フォルダ」を読み取り専用で監視して、変化があったらデスクトップ通知する。
通知をクリックすると、そのフォルダの中身をアプリ内で表示する（Explorer / Finder でも開ける）。
PowerPoint は 動画 / ハイパーリンク / COI / 自動送り / クリック無効 を自動で解析する。
「会場ボード」表示では、全会場を横に並べて受付状況を一覧できる。
受付PC用の SW NAS RECEPTION（NASへ書き込む）、会場の発表PC用の SW NAS OPERATOR（発表PCへコピーする）は、
このファイルを部品として読み込む別アプリ。このファイル単体（SW NAS WATCH）はどこにも書き込まない。

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

APP_NAME = "SW NAS WATCH"
VERSION = "1.14.1"
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
# 設定に関係なく常に無視するもの：SW NAS RECEPTION（受付アプリ）がNASへ書き込む途中の一時ファイル
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


def pick_data_dir():
    # SW_NAS_WATCH.exe から起動したときは exe の横に保存する（ランチャーが場所を渡す）。
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
    """コピーをしないアプリ（SW NAS WATCH・SW NAS RECEPTION）用の空のコピー係。
    コピー（会場PCへの書き込み）は SW NAS OPERATOR だけが行う。"""
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
    COPIER_CLASS = None      # SW NAS OPERATOR だけが Copier を使う（WATCH・RECEPTION はコピーしない）
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
        for rc in self.cfg["roots"]:
            if rc["enabled"]:
                self._start_watcher(rc)

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
        want = {r["id"]: r for r in new["roots"] if r["enabled"]}
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
        print("※ 会場オペレーターモード（発表PCへのコピー）は SW NAS OPERATOR に分かれました。このアプリではコピーしません。")

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
    "wySZo9A5yqgwyLpJdFk2t7qvXgqFd5kTl4YuJbT1uL8wDs+jS9rJpCtz3bWLoX5oRGTpbZqzKtRABtFnRCdTfcvuW26fegCMW2ep"
    "9YJ4cbJWI4ywaJQCzWoFiF/V7kmwo6P5GtBfvrRvfd84ikS6Y/KKV9isU1VMjWFVffrEFhsUas+wSSpxIKRbxX7fXPJLcKOSp6pV"
    "+LQRfh8TtyNxaJ3IlvR6KRbHg0QZD3tFX/mzWggFS3o6lBhcKB2LkNBrxfqH4hRDeBiM6bhcDuFXfFWJ6XZLNx76DJWV8QX66lqs"
    "gixST9lB6F6psKwKEwBCbE6M1HtTLNLdiUR3InF6j09CMVVMjymiPonEEu3kdWIURrpjOHuZGG2kBr+6+hhreaj6GNt/sPr66F8h"
    "U0DD17OHEKjne9VVUIKFs4bHRI8gVGWYCeX/F7uPGvLWPffQ4W0JpfXKGpxgam31ntRX7zNkhEXwudHZFNwal/Djxi2lWC9Ui3zT"
    "w12mfRKKJbTsdYoFfxuGJ4/4rGI/R066696N7eduaeMJiV24SbYLLxZzJy0FJv+Jm/0BN2jsU+ZkW/J+x96641nlsI6dFE4e1xUe"
    "O3F7YnnQY5/dym2vfOwyEdvZOK2JEL+pV6DGqWZkxvg4zk42ncbVXnzBC1TdczSQyMHmikyty4RxJi+aWsa/u9hPehsvUbLEH62x"
    "SdxtGpLfuWHybXNjYILBrzl7m4u0JLtkn2X4/cGG6f+vzkOxr1+/xlefyN0xVLDZa7feYoann/P7rn/fpfbiIny+xbIi3Oq92trs"
    "bpnKhqV9x9Fsc+2TTDbQU87I5PdGzYHIVk1v8WVdubH3XKpF6io2ZR3PlSLgxkupIPjsufT41lO6gt0NmWmjuyVzwSYts73svVL5"
    "nm++lBk3N148lzmfP3u2KbP2NnvdFzLzxvON3pbyLbextfHypWps6+WzF89Ve69e9J7pPvMmgm5jqyuHL+Aou7H58uXzrqrk+YsX"
    "LzZ6spbNzWfPtrY2ZcPPX/S6kHXLVNrb7HY3NqFepYu5tdGD4hqaOkLOwvOXW5vPtp5p4OoIqaC6+fzli+4rrQFqIpSirvQcp7tg"
    "YmpnBY6D7d8KV4bLhQ/f91HKSyXGaS/aXSnAdemtI2GUNeIjykzPHuVQVH1nYdVUg3jWl3YcXdFSFGbNfyX9iJxIlyGgauQHrbgZ"
    "ZixeI52ZFsXGaHBHHCTW9q+EZaZE5gf1vEqmtDosqXRXXAmWzeZaK23K9w3LZhu7nTbbKUteh7EwEew9R8/6Cil86rQh8NhCcwvb"
    "vIce9Z4jf8Q7aG2Pr2zJoVOLvtpFVKKQEdIm8CzdbeBaqxCWdIlHxQDO3vY2sN33IR5lYh6AjlYe1JP1s3xhtGZT4HpYNA6A1tHF"
    "oFzDaumqBfv/u2Warj/jm//BJdru1RdmbR3Wlt3qVdauH8S1bS9Q/8iN6zV9SOKumrK2anBhuR4Z5cqy12V3O5bMSCZxKMbXKwGH"
    "MjYL0fCpP6Njz0FrrRU1K//+PmrKpx2ysxDQKMKzr2C2jbZ+Ldmi7MJ9GPkMluK/IvtUKq4dI9r9abY1XJ4R/9UFPg0ooAbWwIJb"
    "15JZhi11ehZri4642N4Oe2ytFRd6DeKCxH0OuDtT+qfEdSp4esZQa2ez97oS7gDVCZ4WUqyypTouc0dyH6a0ePW0E3TcKaOXGK0p"
    "C9HwCGcNjxvEhKVmZZOxfWVa/pI/TG+b/wIG0olBV33fbZ6589ekQtNZJbwARXasS6cwLq0TKEni7fFofriGmICHlRbuxIgrtBIE"
    "PEz66Wlyhq+84k8bvUCJ3woQK7YQ603mwsPtIcxHfyUZ7auGS9MwEdGynzTTe35anjUJtSFwj0p12K68IfoZsMSQVEeGaIZtznrb"
    "fLAF/3OzfQ2ApBhSsBUI99r/GLL9jH0Zsp+G7PchexOTWFcgJl5Ija0n8vdE/n4ohevsKGeHJviNsPenPPTQnpCj26EGhWZ5o8pm"
    "w4mQBUQY/a5QQLhaiWbzIR5tNkYXiQhIFyqyjPyiOmUYakVvW1gR/op6RkWWN/CRM+lkBFOtT5Hpmt9SRfBLHs0wALXRWST5LaF3"
    "AKBcftsYQiCPyoo3RLeGE3JGIo2I8H6uQYqVDalsafnWsIyLo1U7nvDMFaf63gS+slnlBRLs9mPMYqSVNvnA74RHeI77ZDk3QR19"
    "1ajbF/rGqk+WM0twWtlVDBb4UHaEqj6a7Yr4/ZFvl7/MKj1X9tFwkpVLCYcra7NfSints7sVduqoAEP67biu0V52AMvq7gIlNj46"
    "TIOUjbIpJdK7gxUjAnB0CzM43UOZJwDCZmoIYiauklCfA0RNXpQBrPEFs9UE8SYn9a2o/Qxt3BgI5i1JYawG7sOS6FG9XpYYj/76"
    "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"
    "xqwQaiXkypSolY+mEnrRVBbtbg8jYvema2/fHpWjVN2lII7iXlwpm2onYBSUTynwl7sdU98PqS9zVHra/mWJJXJlZSqBK43fbavV"
    "WplCa7+Vg9Z8rjwzHxpznu31J3maQv0vvVYhf6PQIpGK7Kle5IZziKmzytqCqNMTKMiIUcortptHvmsSAVC6bILKiMGKSlWrmkwK"
    "E4pg6VtfQV5h+G4FgpUSJpTOJ0nKcktIw1+DJbOGHOKeEpNkjMUylIuhB0KXFuWguA/LGY8LMWiFZXUERZXtK5tGUFSZvMJEl0De"
    "lgbRMCT52xlX6CoYmIr2VDTGaGPyAlOmiHrDMgSYKKKQVgaZr6dmtGOMESx1OqdiljLyLShmi3RT8tXQLUutpCBlmje68dj9b9Q1"
    "63FRR8ZviH+HkeC4xBjjNLOYqaOLpD6aaLivzJIte2Lku+rvVqjyqelMSvT3mpLManly6KRb2tRk5qmg5g0h2tEvOF/z9cTzg2pN"
    "Q6m69iGYKin4xrsn8N9d+DcjgWrFFkKmPVb2OtWXtdqKmHY08/rAaY38GHmvnoUJ4UI1/lpS3DXMzfLyksf0O37V+iYoWSSHYe6V"
    "6CqYKcQI85K5r2qLsxWK2Mu072wlMZSMTSWNKWsxCHARFeLNhkwEGmgzfLLZ/6wlvvW8KFQWo5rJeYWr3962GVvsdKSQrZLEitYa"
    "vQ0dwyA1JePv5VLN6jgX+4PsAPVL+w+KA8yzE1lRCXFsmkgeJHGaH7ZCQD/9OOsLQD9ApeJTmsNrJCYZQE2Gk3gkWnS6tW2pfBCA"
    "UwfUDPqhVr87SQYiVzXj6SDJpRQrBciV3hgUOq1QurLif+kNiv30oNKAdESm9smZuDaw0aFqPhnFh3qEADKO3W+CBQMcCATYBVUu"
    "88PDtD51yU18gQGhE2onyYATSGpNaV6iWHt7OkEOT0URPT+Ni8dA7yfjVIRLS8naSD3ML2jMMhOvGjuWFH/iaymmRgFE5SVIQyZ1"
    "Qk+T7wlQdN28kXaKI0M79Yo1HIUihBT1mqwtIn2gwlJ7eXk48Zzvgph0MdG+7SuIgbxm/Sm6bHm52iGQZb+1PrEt6LZOnBH9q4mz"
    "fDFxBmvezGdOJqhCf0nbhIZuzdsoa92OveZDIy/WmLi7sJFNTBYwgoXDCKLnrEv2FSyquUPTKcv11CQNhLlf76Uh8KPoxnpXJQoM"
    "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"
    "jCU="
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
<title>SW NAS WATCH</title>
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
  <div class="logo"><span class="mark"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round"><circle cx="12" cy="12" r="8"/><circle cx="12" cy="12" r="2.5" fill="currentColor" stroke="none"/></svg></span><span>SW NAS WATCH<small>SEVENTHWELL · READ ONLY</small></span></div>
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
function setTitle(ret){const u=S?S.unread_total:0;const t=(u?"("+u+") ":"")+"SW NAS WATCH";if(ret)return t;document.title=t}
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
  if(S.op_moved&&APPKIND==="watch"){h=`このPCでは「会場オペレーターモード」（発表PCへのコピー）を使っていました。コピーは <b>SW NAS OPERATOR</b> に分かれたため、このアプリではコピーしません。発表PCでは SW NAS OPERATOR を使ってください（このアプリと同じ場所にZIPを展開すれば、はじめて起動したときに会場・コピー先の設定を引き継ぎます）。`+(h?"<br>"+h:"");warn=true}
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
  if("Notification" in window&&Notification.permission==="granted"){const n=new Notification("SW NAS WATCH テスト通知",{body:"この通知が見えていれば設定OKです",tag:"sw-test",silent:!!S.ui.sound});n.onclick=()=>{window.focus();n.close()}}
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
  <div class="foot"><span class="hint" style="margin:0">SW NAS WATCH v__VERSION__ · © SEVENTHWELL</span><span style="display:flex;gap:8px"><button id="bCancel">キャンセル</button><button class="pri" id="bSave">保存</button></span></div>
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
  // コピーするのは SW NAS OPERATOR だけ。コピー先が1つ以上あれば有効
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
