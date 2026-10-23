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
VERSION = "1.14.2"
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
        for rc in self.watch_roots(self.cfg):
            self._start_watcher(rc)

    def watch_roots(self, cfg):
        """監視する（NASを見に行く）フォルダ。SW NAS OPERATOR は自分の会場の監視フォルダだけ（OpManager で差し替え）"""
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
    "aZ+ba/wk8K5lOMUEdL9JsVMMQBSh8XZluYrFGYXWvdcqAkalw3gL5jOdN1ZuZR8uoT3P2uUEMj1YRiCgz4yqs+rUoY6B/OaDujVn"
    "aQyQYrMRwotOMSH4qBgsHCHa43PPRAEX5KMw21XHhpD5YEsyaLA8no2gYD59Z0T1jpjyDlSsL8u47zaRomMa4+WY4p7wg+SL7cqK"
    "5tLDH0WyStDUxxyOAlnF5NnIqZiIqRErsM5oFEBPPBtwMKujWmxsYch5La2UmJCLeGfoED0ZaUvPcBZ44Vkm7Da3hV2ksNOEn09J"
    "eKt+D8UT9cp2EjWSlekkXlwbE0tUvKQ/76Q5J93ZidBNLNI/oN4ihT5eybQDY/Q5mkmny8JAk0/zKuajBk+j4javKDTCv+inpzHO"
    "QAKgWx/pzk4af0qFZDQIfSstRD8pC9GjvIHv3tEfTvoDMojXsSP1KXqEto+1BqbKJZ8Iocc9EfoI7YoAjmoqvOxJm1PSX26g5jL9"
    "wTfoc1WtbRf71rKLpZplGOtWQaxdhrH+IhvTyFCrWcJMGLIKTeaG0GGmH2wWkANftpFmrg1pzd3Ak8wjUhIW1rzblonvO2XiK2Ai"
    "FJllU2KHbwh9V5GL+n0dAsZBc0LXdakx7VfpDX0yIsM/euPrhh6rRReU2tgnRh4k3gpnmguJtb1PHISz4yo+Ya8nQRnXSPouxh13"
    "T2qejiGfUNzs+QPowusJblbe2u7En8NnNMJPl3RjtpEbbxFoTD13UyUpxhSje89q/iBFsjoNw9QdUqG24jM6WszSN6h9TfE5NVSj"
    "4YMjOi2zHDiyY6PizCz15hMnL63DH+eV+K9rtnShmaMHXS+h63+sxE215PRZ0hkJnIYChlzcltn3LG/Uz/gsXFO1a0ZDV2SbfSvj"
    "c9WaW/2iCfxPNPiGFOjFJROMv3brwcylDbNuo5i84zFAsS42qVjNHl6P5gE7eHPRt6SLVuUCXdmCbcG/rQFBWNwWhEXCv9oErv5R"
    "qTYv2KRyuVnhbyU3K7WTRD+zk4gtYGR2g6m9Gwh4LKPiNvmNNPl9lPAaiiuBYJuGKMppj5edTWjLPgAy6akNmvZgtc/RhubQYrs8"
    "HsJEYdUalb5Ff2c1IUmc6NzfK23bNjHf3oDXFLUr9jpvlVBSOiNDBZ0lutyGLZ+O1LNnrbS5SS6MLFvOhZeNVHdQzEzwBIKUnPAs"
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
