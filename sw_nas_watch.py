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
VERSION = "1.14.0"
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


COI_MATCH_REV = "2"   # 照合のしかたを変えたら上げる（解析結果を作り直す）


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
                # COI などの短い略語は、字の間の空白・点・ハイフンも許す（「ＣＯ　Ｉ」「C.O.I」のように打たれていることがある）
                pat = r"[\s.\-・]*".join(re.escape(c) for c in w)
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
            paras.append("".join((" " if el.tag == br else (el.text or "")) for el in p.iter() if el.tag in (T_A_T, br)))
        paras = [x for x in paras if x.strip()]
        out += paras
        if len(paras) > 1:
            out.append(" ".join(paras))
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
                    texts += sa + [" ".join(x for x in sa if x.strip())]
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
        if lab in names:
            raise ValueError("日の名前が重なっています: %s" % lab)
        names.add(lab)
        out["days"].append({"label": lab, "venue": v})
    if out["days"]:
        cur = next((x for x in out["days"] if x["label"] == str(op.get("day") or "")), out["days"][0])
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
        try:
            with open(long_path(src), "rb") as fi, open(long_path(dst), "xb") as fo:
                while True:
                    b = fi.read(COPY_CHUNK)
                    if not b:
                        break
                    fo.write(b)
            os.utime(long_path(dst), ns=(st.st_atime_ns, st.st_mtime_ns))
        except OSError:
            try:
                os.remove(long_path(dst))
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
        srv.clients = getattr(srv, "clients", 0) + 1
        srv.last_client = time.time()
        try:
            self._stream(M, last, tlast)
        finally:
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
    """enabled=False：画面を閉じても止めない（OPERATOR はコピーを、RECEPTION は書き込みを裏で続けるため）"""
    srv.clients = 0
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
            if srv.clients <= 0 and now - t0 > grace and now - srv.last_client > idle:
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
    if not port_free(host, a.port):
        try:
            with urlopen(url + "api/ping", timeout=2) as r:
                if json.loads(r.read().decode("utf-8")).get("app") == APP_NAME:
                    print("%s はすでに起動しています。画面を開きます: %s" % (APP_NAME, url))
                    if not a.no_browser:
                        open_ui(url, data_dir, a.browser)
                    return
        except Exception:
            pass
        raise SystemExit("ポート %d が使用中です。--port で別の番号を指定してください" % a.port)
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
    print(" " + STOP_HINT)
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
    "eOgc5VQYzrppdFGtbvZevRQK7zInLg1dSmjrcX9uHJ5HF7STSVfm5m4t1g+NiCz9DSOrQg1kOPqMSDI1sOy+5fapB8C4JUttFsSL"
    "k5UGYYRFoxRolitAvFW7J8GORPMNoL98ad/6vnEUiXTH5BWvsFmnqpgaw7L6tMQWGxRqz7BJquNASLeKg4G55JfgRiVPVavwaSP8"
    "PqZuR5LQkshW9HopFkdBooyHvWKg/FnNhYIlPR1KDC6UTkRI6LVi/bGQYggPgwmJy+UQ3uKrSky3W7nx0GeorErO0VfXfBlkkXrK"
    "DkL3KoVldZgCEBIjMVLvTbFIdycS3YmE9B6fhGKqmB5TRH0SiRXayevEKIx0x3D2cjHaSA1+efUJ1vJQ9Qm2/2D1zdG/QqaAhq9n"
    "DyHQzPeqp6AEC2cFxUSPIFRtmAnl/xe7jxry1jVg7PC2hNJ6ZQ3PMbWxes+bq/cZMsIi+NzobApujUv4ceOWUqwXqkW+6eEu0wEd"
    "iiW07HVKzobi8PgRn1Xsc+Sku+7d2G7hljaekNgTN8l24cUS7qRlwOSfu9kfcIPGDnIn24L3O/a7O55lDuvgoO3kcV3hsWO3J5YH"
    "PfbWrdz2ysemqdjOxlnzCKFegRpnRskdH8fZzqfTpN5JznmJqnuOBhI52FySqT1NGWfyoqlt/LuL/aS//hJPlvijNTaJu81C8jsX"
    "p9821ocmGPxasLeFSEvzC/ZZhj/srZv+/+o8FPv69Wt89YncHUMFG/1O+y1mePq5uO/59z1qLynD55ssL8PN/qvNjd6m9epsZd9x"
    "rHa49kkmG+grZ2Tye73hQGSzobf4sqnc2H8u1SJ1FRuyjudKEXD9pVQQfPZcenzrK13B3rrMtN7blLlgk5bZXvZfqXzPN17KjBvr"
    "L57LnM+fPduQWfsb/d4LmXn9+Xp/U/mWW99cf/lSNbb58tmL56q9Vy/6z3Sf+SqCbn2zJ4cv4Ci7sfHy5fOequT5ixcv1vuylo2N"
    "Z882Nzdkw89f9HuQddNU2t/o9dY3oF6li7m53ofiGpo6Qs7C85ebG882n2ng6gipoLrx/OWL3iutAWoilKKu9Bynu2BiGrICx8H2"
    "ceme4Qrhw/dDlPFKHeO0F+2ePMD16K0jYZQ14iPKTM8eFVBUfedhvaoG8Wwg7Th6oqUozFf/Ox1E5ES6CgFVIz9oJ6thzpIV0plp"
    "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"
    "3994DVNcvv0iZlrWI/HicXb0sOEuBGhNwUz6Tec9TQsv2XaNHlxi1w/yIFtcQ5+PiA8X07mQ+y3coocXY4TdrBVYb4OQlbFSkh12"
    "HPbVqWi+OnUZFTXo264RYFKJiUZBn648ZYOWpdrR499Hj/9J9PgnXy1nKDdqu8nRVKONICpyCRMWVvxOxk89Jniwqd0c1dmW7bCy"
    "OsK46+JZnF1CVxJPSkOEL3z6dTvE+vItov6fo5MQKsebGBEAKnlhdJpsasPZbiTV3mAoQTiBORzTStV6OEqxOrkjGzTRpmBRcEEC"
    "zFyfny/HmKQ9zFqqufZPNomipAWX+5HA5YciKYKpN1IHjyaTcuzKG9EK8esmh40HG3N5BY8J7+Lle1aKM69Psp9j0OH6woLsZDUW"
    "U3CH4qmY/vzxMqaE7+xUX/W+8Vl5WXsYM++i3M04Y7UpgyqcqkTqSMljhx3emsgpy2+RDgR28Jfry++x5aUFluP4+YfQCYDdAybR"
    "PWDSyALY8AgTBEGuGJXZiPXJ1YTIRcMzVcRwTpRUuVutJjAV4MAatRipWZ2fnxMFbykOCdOZYuI3rH6HX8gzNTs4ZE/kZ4YnRqo+"
    "EiYnKJyrxRjJa7nBOWJG8TgJhyN0Iq2PYX/qXdBN0CzsiRTbfijFLx4uTuSofDu+MD9rhDWFStgIt8u67WOB5XQZHVf/w+ryUwex"
    "sIYobkv1VlU1C3WZShGpX7nKYA+lWtBQ/4wWGtkUC3tVEQ61rU/SXaJliySQ6C7TwQ7S9a1eO+I4qR4pn6UudLHWcWGRZeqNj2+h"
    "WvzKyyE1DqsE2ddTeamwuyd6f4q737QWt9vyC2XpAFVy6Pgom2FWVxC6P2+l9DEjbehNW9e+Ankp6hKHWpY4h7cYYZ9VhMo0ArP9"
    "4bu/bXz8V5ittY3vVt6th+IN/kddW2U6hcCM+8OXL1Poj/RZbcMZSlIbIjSnMAQMA8lNE0V8UBUNZnunWlKrxQrrgRwrMNbjk5Ha"
    "p1pVYPTMSc3P7/7vwcPdz+S7nx/K7k5jMnRAaP14L2vttoJ6QpLV3z347LO7h7p27baRnNS7KsAglzlEL4HlokxKSpjP5yTZnYiF"
    "clbXaQerjYmaoL79uEhsjuixXPM5E4k/OZKdA9RYwzhQLT5+CvjDAhJjyhiuzcqr2r5CU+je/xgWpU4mz9oDMP3kWYWtBrhsNuEk"
    "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"
    "JwRshPH5DNoTLtvIhG+zJ/j1zzSatOa7UeB9GjM+O7Vw6PYj+r1bBlakvA//34X/PyjvxTm1xlWt1i4whlY5TJcYwdHK27U9U6tT"
    "vQ5yfunvR1QI8DzXA39iD2wk8kiHaVD2+xU5LjCufI6eOvlkr1LGsxE17bBcejBKbOENaP9Vt6cDGIgnnwAm2p1Elz5SKj1JfEkp"
    "cDwMUgo/w6HjROUScNlh6AfuwB1famGTs9XV0B6HrfInWfSr8rPOwHdKn/tk6a/swEVpsPQcBWqTD+DnVT/yS89CtdKnrmuXlz/1"
    "aXbrE25gwzvYbbj+/LT0cT8aul3WwGcdNzjB/OEnMOmj1alrYSdWQydw+9urqyN/7LfKn3KipwIghmHps3ANtWDCu3bPteU1rA0f"
    "Nhr8fNrZt/9qyjrBnk5daiZEJKIlf0HjQavRnBzjj2arsTk5ntM47JIcwPYS7Zk9WHqeH6yGXbzXontQqTNoPdZfg/8adNFsPeZ0"
    "4L8tuEKsIDyk//FLeNy/AP9twPUQjq4Arpv9poPPQ8eDyg5c41XHDzDA3WPOOvxXlzeggd4m/Idv68OrG1vwX4cu4BH2Y30TB2wa"
    "OfDuCw34z4brnjtqPWY34D+8srsY20ypzG5Qg7K7GMi29djm2uYmfZp/AOU37bV1my7ou3vdfte5wK6pMxtb9bUeXA98aL3e3Frv"
    "XmBXVNypw7c5/AaWr69tXrSxceQwobmLFy7UN/klG1inv0ZN0B2sYjc2m3W807F72IHmZnOTXfEKTtNp8htYvnOx0W104cah68N4"
    "dNdsp8euWJd6zkXqEt7A8pu95lbvItxAwwz0cOtio9Pkl1Sj2+/bVIPu0Fc4F9Yv4gxhyB1llPGSdWod/sMZJ4fwDhtkWCTyDq6S"
    "nrO5ZYs72peGQxvIX6teakyOS7BSS8GgY1fqFv5Xq69XrXppE5/U049wlfUCManphY1nQmJd4y2+rOudutNoimVd36rb9Z5c1o1G"
    "Y5MGli/rxgYMVDNe1o2tZr1pi2UNzzbX1pRl3XCaF9Ya6rJu2msb602+rJ01mJe6WNbd9W6/14mX9VbfrtOs0LLe6Gx2LnSUZS0r"
    "K8tafgtb1mtbnV5/iy/rZrO7seHIZU1juLZuNS5esC6uW7UGjSNf4ut2z9mqiyUum+FLnKpubFqNrYtWc31L1BXr/UKvt9bvyvXe"
    "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"
    "8v8A54yK7g=="
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
