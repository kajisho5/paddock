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
VERSION = "1.14.3"
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
    "V4rb/TTQYTqZ46FzlFFhOOsm4bhsbnVfPBcK7zInLg1dSmjrcX9hHJ6HY9rJpCtzc7cW6YdGRJbeppFVoQYyHH1GJJkaWHbfcvvU"
    "A2DckqXWC+LFyVqNMMKiUQo0qxUgTtXuSbAj0XwN6M+f27e+bx1FIt0xecUrbNapKqbGsKo+LbHFBoXaM2yS6jgQ0K3iYGAu+SW4"
    "UclT1Sp82gi/j4nbkTiwJLIlvV6KxVGQKONhrxgof1YLoWBJT4cSgwulYxESeq1YfySkGMLDYEzicjmEU3xViel2Szce+gyVlfEZ"
    "+uparIIsUk/ZQeheqbCsChIAQmwkRuq9KRbq7oSiO6GQ3uOTUEwV02MKqU8isUQ7eZ0YBqHuGM5eJkYbqsGvrj7GWu6rPsb2762+"
    "PvoXyBTQ8PXsIQTq+V50FZRg4ayhmOgBhKoMM6H8/2L3UUPeugaMHN6WUFqvrOFvmFpbvb/VV+8TZIRF8KnR2RTcGpfw48YtpVgv"
    "VIt808NdpgM6FEto2esUC36JgrMHfFaxb6GT7rp3Y2e5W9p4QmK/ukm2Cy8WcyctBSb/Nzf7PW7Q2KfMybbk/Y797o5nlcM69mvh"
    "5HFd4bEvbk8sD3rs1K3c9srHrhOpCZPWjxDqFahRqhmZET6Os51Np3G1F5/xAlX3HA0k3LFXZWpdJ4wzedHUMv7dxX7S23iOJ0v8"
    "0RqbxN2mAfmdi5LvmxtDE+z/go9TiLQkG7NvMvz+YMP0/xfnodhXr17hq0/k7hgq2Oy1W6eY4fG3/K7r33WpvawInm7Bjhxs9V5s"
    "bXa3TGVRad9xNNtc+ySTDfSUMzL5vVFzILJV01t8Xldu7D2VapG6ik1Zx1OlCLjxXCoIPnkqPb71lK5gd0Nm2uhuyVywSctsz3sv"
    "VL6nm89lxs2NZ09lzqdPnmzKrL3NXveZzLzxdKO3pXzLbWxtPH+uGtt6/uTZU9Xei2e9J7rPvImg29jqyuELOMpubD5//rSrKnn6"
    "7NmzjZ6sZXPzyZOtrU3Z8NNnvS5k3TKV9ja73Y1NqFfpYm5t9KC4hqaOkLPw9PnW5pOtJxq4OkIqqG4+ff6s+0JrgJoIpagrPcfp"
    "LpiYmqzAcbD9W+Ge4XLhw/d9mPJSHeO0F+2uPMB16a0jYZQ14iPKTM8e5VBUfWdB1VSDeDKQdhxd0VIYZM1/JYOQnEiXAaBq6Pdb"
    "cTPIWLxGOjMtio3R4I44SKztXwnLTInM79fzqjOl1WFJpbviSrBsNtdaaVO+b1g229jttNlOWfIqiIWJYO8petZXSOFTpw2Bxxaa"
    "W9jmHfSo9xT5I95Ba3t8ZUsOnVr01S6iEsUZIW0Cz9J9CVxrFcCSLlFUDODsvXwJbPddgKJMzAPQ0cqDerL+IV8YrdkUuB4WjQOg"
    "dXQxKNewWrpqwf7/bpmm60/45n9wibZ79YVZW4e1Zbd6lbXrgri27QXqa25cr2khibtqytqqwYXlemSUK8tel92XsWRGMolDMb5e"
    "CTiUsVmAhk+DGYk9h621Vtis/Lu7sCmfdshOAkCjEGVf/dlLtPVryRZlF+6C0GewFP8V2rKxuCZGtPvTbGu4PCH+qwt8GlBADayh"
    "BbeupbQdtZT0LNMWHVnx8mXQY2utrNBrEF+zwH0OuDtrMSSuU8HjE4ZaO5u9V5VwB6gkePqQYpUtlbjMHcldkNLi1dNO0HGnjF5i"
    "tKYsQMMjnDUUN4gJS83KJmP7yrT8R34/vW3+CxhIJwZd9f2weebOX5MKTWeV8AIU2rEuncK4tE6gJIm3x6P54RpiAh5W+nAnRlyh"
    "lSDgYTJIj5MTfOUVf9roBUr8VoBYsS3uzFx4uD2E+RisJKMD1XBpGiYiWg6SZnrHj8uTJqE2BO5QqQ7blTdE3wBLDMvlnCGaQZuz"
    "3ks+3IJ/3GxfQyAphhRs9YV77X9E7HPGvkbsj4j9GbFPKE1iswIx8bPU2Horf8/k74dSuM4Oc7Zjgm8Ie//MAw/tCTm6HWpQaJY3"
    "qmwWTcRZQITR7woFhKuVcHYdoWizMTpLREC6UJFl5BfVKcNQK3rbworwV9QzKrK8gY+cSScjmGp9ikyX/IYqgl/yaIYBqI1kkeS3"
    "hN4BgHL5TSOCQB6WFW+IbkUTckYijYjwfq5BipUNqWxp+dawpidcteMJz1xxqu9N4CubVV5fgt1+jFmMtNImH/id8BDluG+XcxPU"
    "0VeNun2hb6z6bDmzBKeVXcVggQ9lR6jqo9muiH838u3y46zSc2WLhpOsXErYWVmb/VJKacvuVtipowIM6bfjukZ72SEsq9szPLHx"
    "EZqosVE2pUR6d7BiRAAOb2AGp3t45ukDYTM19GMmrpJQnwOOmrwo+7DGF8xWE8SbnNS3oj5naOPG4GDekhTGauAuKIke1etlifHo"
    "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"
    "7/xu/DR/ed58+3zp3ZT67YMIvEJfL482942naeP1O1Cimk+mKNaJKUy/efNn//yf/sk/+tv/7Q9/77/++HffTJrn7Ys/6QXzf0MR"
    "vHtpxptffYOYT0vwB7l/iHJYy69NsUCPVOCHf+mHrwajgqrt80n2f/kZXsAxf0oG9vgu+hfPz49+NPnofvQj65uLFTbu4fHt3K+o"
    "8DQ/T1FDzxHbt+nLfT08MvIn+byL61therHFcBehZ3l5+HnC9CLNr6QJ/vBRnt7d8xO90Sdl+nSQDZq67zxKBSz79Q1ICapzWk+O"
    "7SncIKl8qDjDNx937sOm8wfymE627nFrd8rknr4cKMnvvoj6Q3zf3cv0PGOLD2vsnrL1VVNeHkLe/Lf//H+9//L3f/bPfvNPfvIf"
    "3jx8fj9ul7/wOfzRm1BCFVPCPt+F8zMopy9fpvM+94D8aTceisF0o0mbu6R9Z5K08mXYJwjweNTwj//xtPf36fTss3S/+yAryIcu"
    "4J/98C9Bkfzhp/fdLrgOJ914eDw5WUUQtlTRs/WZEnZ897vFJ+3kFUmDbHyoobxP+W2eLk7ycfcNP0W4V9GjCfz0u9jknoPoKMin"
    "7RHY18/LTy7VHSdwj+kfp7Otjws9frTZD/v27T1t5yNieo4N/CJ/PWmffwiTHB78b08CHJt7RtMf1E15uUThZ29+9Wdf/m9/8nv/"
    "BI7Oy5z82tPQvk1/0UB++vxEeY8h/ezN+x//7Z/9p99//+Vv/8lP/vj9l7/xBnm8gbz52U/+0Z/+5Pff//jvfJitx7l6mneoqMrH"
    "cX6UtP/JIX769GGEp7eqfDGlJXse4xYOTvvfHePyNZr67C208+WjnS+frd+92sci73ijOd4NEbxY1j8oL9M7ijT/m7969+l98vyX"
    "yfvilXqSJrf7FG4vQ+34Vr7Hyr19ahdow7R8OloAddPjxT46ZGnz+hZUCfLTOxOmVr2ke4ZNk6cwXyjy0YfzqK88/i9pfe/7Ph8G"
    "9EkLwvZId8+4/JLC9kUjys09wuUpUcJkipBPsPkUaf2UnfaDa62dnrufaDDqIH06ffTu4fhyWfThQnz3y+1jcq439V0ztp/EkzRE"
    "RTA+nXnIH46fJPDRSTPdEyCCe71vZ9Ffns5Spu+e70+nv6cDramf2/754pSvn/5kPp8ehq2dzf/HfvFcPlJO72qaSMx0WOI4/fj5"
    "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"
    "z7SsxLJUdfRspzxS51StMKOqwDuQiKQIHl5CeVau8fkBn5Y7TWmxTLaa5ZE8xxq55LhozReVkpVGBWGGRlsV3yYcoq0A3ziejw6N"
    "7KgzaGvFMavxZcQXOk2t44z1ajnrOnZuGE1VZArPFyaLuFRbpuwl7ajLVMDfXjVvTtVCTTKlKSbUaSypdtuU0m814m1jpuUTrBfF"
    "xGGuaxRZtRdtp3OLpZQbJpecOu1oJWSWtJR0px/H9Ok0ynG5HlGUlonshC9OxbY4WzKdUqVb86YdkSFkRkqWJtURAuarWJAKlKxR"
    "6bS+4OI1oWnIZj9eydLKeFIcNeat6tLOlH0ircvLUpkrcF2LyrWKDqAbssxTUaDwlnltjuFjS+fUaHXmtwHmTJL0dDS0lp1Ua55y"
    "hCZvYMhcdvRp3KxYRqk5aqpyUeov84NiQ2+5lUmC6TTEnhuvL5G+Hp+TBZma8saMK86RmuhJ+cnEWQKbgFSrpR7QQ62aJStKYxnX"
    "p5zoz+KV+UAlWtFCbbwkKV2hceBZlz2+MEWSi1QZGM1SZ16o682+ma/Ee+MFaiOUZJBqalrtFS06pfcSWm0qID02WvFZ1Sjmrcyc"
    "iNrm0NIMrDFDBmVEbPT5+HIs2E27jaM6P8ry9LBjlF1+oiHJomknJTuv5vQRTKZgCwtCt+VsRmQbk8mgM0oRBNeP1itmQbSibqVq"
    "Wr5X9qEhK0eZqdkka6iCEHOAoVNULefwtt0oqQBzm13TZRb1DqZXRvQo0wdWpd/oYEaWLRi1TK3OajN6Uu7aEhN3e0qu1JlhtfEg"
    "SLtps91Gq5IiB6XSeSRmWqIN31P735XVU3D3XnCDU4l+ep4CT+gMrXY03ubtftOb9yoLKpEjVVXESFPtIgVeG+PVSmNGkkqWL6BC"
    "E5XZAtXRKxVsWvGnFaw0HWszq5Bv0hYB9CuClBqJdn+ajAKl2e42KnK16dcWmjLzJpkMQKuTzJIRsqnUcMEphKaXPanRnzdcZOQl"
    "0OIk0Zw7CeDgWBRTByCaTTU600xhPuCmvlrO5oYWJRSsulNpjM15oyLgHW1GVCtLHqXTfQuXRkmAzvmq1fHGjl1ZNHXcnA3AaCoi"
    "vXQMoS+6TbZbaLFa2+kgjU67os+Hlaji5ltVe8mLumS3PapusspymJPGSQ93itGZkc7SwLvr6dVSdTCrjofTPMuNAUpQ6lG8khIH"
    "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"
    "U68Na4r4jHSRLuP7y+o4MElf+D3E6SAujQs6DfkuOWbozOt1yqfvnLu8R073jQ2ef5uM98CbwPatTz7//ZsiZUHYLGnT2oJufp05"
    "EorC4Il34+MXKAj8Jd1MdZqFGAHbxxw3Z5DjBl2kg0huzlQUyVdu6xhIuf71DOU61eKNPNXDMK8E6Ow9zh4a0xMQzmUXvr7oQYlJ"
    "Vw+I2EEZzWyx3YVplMlyMzYv9BjwAfTInMG7pTYxYoL6QS17Zd93o6AP02mfemefeqBo+hAXzhwRNg3zB6wVUzxtVmbXhCdAb5nh"
    "B1jDFbc2HrXTwuih2b+bsXlUPyXgnCoci2DEWBgHye3bZJTS+M54g46ruE3qxcIGaky1gUgINAR5biXZ8akeXGhlZUVJoMGQWkz+"
    "C9CVCxRftb3J9chxN5QvsGaznA7dJNVOOmSoaQaTU5C3HSRjkDulbE67ohw6d5ntLbBJOaUCJj/aqQi9+Z0iQ9Bl2JR2bv6ZEo5u"
    "yKy0S0WJMMVEO/TtB6gBmghhJmRdYYEW/sjTHg1ITJqenjnF1RULE7TJK0wVP4iV8O7Lt7+4/Ac62bIpPFzL/TXBO5+p3diV4gpZ"
    "kr3q3Dkud6ZWyjLOmh8YWVy2voqSA0aXQyvYnrz9/nnMi8Oz5R3yM/9FJAwJL9dzpE38MvvA1jVJrMEz/jmZe7T1+bu/2fn588Sy"
    "ew1DF9Lwji2ZYnWTHTzbN19XmV6WEKC52ssgOTdqIeb3JPr1R/j6QKGadQVrDB/4GO5uIVugYvLFiz//4pVffDlWT0weYE7PGYLP"
    "/tq0SekZUnrBqdhrGFvmenrdmVorlFqt0t1rV62hmaMkyHHe2s7L56E5X64tqBcTWptiKAV9O9scfqioQemd3TZpNKPwYBgDS88/"
    "3L52ieQTjLCAHrmLts1rwpfJlGQMyEVuiVTSxWhvie+KcdPoPth56W0ogexXpHRfu7rzwvsgMRMMCUPFXqH/UzQHXIEFKBP+BBcV"
    "5+flmL4Q7Z8027t//unOr14jsPzn+SRcGAbeYM1M57m77yuKQ2811lNX4ZSMeskpitLEfIduV1dheNCLnnHWBukzOmIeRgIT9R7n"
    "Z8LsZZUEPY0g+8KW8+e/guJPg3BDjlUWnCG3V2j549zJ/2fwMNzQ1XsSfgZnf+RlO09cHtxfgqcBuWivkH7wM5znitDgwm1kGrhw"
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
