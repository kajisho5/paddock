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
VERSION = "1.16.5"
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
MARK_ROLES = ("recv", "got", "done", "drop", "direct", "warn", "op", "info")   # op=会場のオペが対応すること（発表者ツール・演台上げなど）
DEFAULT_MARKS = [
    {"w": "受付済", "role": "recv"}, {"w": "受付完了", "role": "recv"},
    {"w": "動画有", "role": "info"}, {"w": "音声有", "role": "info"}, {"w": "動画のみ音声不要", "role": "info"},
    {"w": "PC持込", "role": "op"}, {"w": "Win持込", "role": "op"}, {"w": "Mac持込", "role": "op"}, {"w": "持込", "role": "op"},
    {"w": "Backup", "role": "info"},
    {"w": "持込リモプレ", "role": "op"}, {"w": "OP卓PC 発表者ツール", "role": "op"}, {"w": "発表者ツール", "role": "op"},
    {"w": "ミラーリング", "role": "op"}, {"w": "Mac PPT", "role": "op"}, {"w": "Mac Keynote", "role": "op"},
    {"w": "演台上げ", "role": "op"},
    {"w": "変更有", "role": "warn"}, {"w": "演者変更", "role": "warn"},
    {"w": "演題取り下げ", "role": "drop"}, {"w": "取り下げ", "role": "drop"}, {"w": "取下げ", "role": "drop"},
    {"w": "会場直", "role": "direct"},
    {"w": "会場取得", "role": "got"}, {"w": "取得済", "role": "got"}, {"w": "受取済", "role": "got"},
    {"w": "受け取り済", "role": "got"}, {"w": "DL済", "role": "got"}, {"w": "ダウンロード済", "role": "got"},
    {"w": "発表終了", "role": "done"}, {"w": "発表済", "role": "done"},
]
MARKS_V = 3                       # 目印の既定を増やしたら上げる（保存済みの設定にも新しい既定を足す）
MARKS_ADDED = {2: ["PC持込", "持込"], 3: ["演台上げ"]}
# 既定の役割を変えたもの：前の版のまま（＝利用者が変えていない）なら新しい役割にする
MARKS_ROLE_CHANGED = {3: (("PC持込", "Win持込", "Mac持込", "持込", "持込リモプレ", "OP卓PC 発表者ツール", "発表者ツール",
                           "ミラーリング", "Mac PPT", "Mac Keynote"), "info", "op")}
MARK_STATUS_ROLES = ("recv", "got", "done", "drop", "direct")   # 演者の状態を決める目印
MARK_CHIP_ROLES = ("direct", "warn", "op", "info")              # 演者の行にチップで出す目印
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
        rc = MARKS_ROLE_CHANGED.get(v)
        if rc:
            ws = {mark_norm(w) for w in rc[0]}
            for m in marks:
                if mark_norm(m["w"]) in ws and m["role"] == rc[1]:
                    m["role"] = rc[2]
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
            lab = sorted({(m[2], m[1]) for m in mk_add if m[0] in ("warn", "op", "info")})
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
    "nxaW/p3vfFteKMR8+IgT765ucc5fccavOPz0RP1na+i9/TCen4sLyrffXnYtWgbG8BX+0SzrJ77CKoaZVQw/j1UssvvoKT//u7/8"
    "nJ8/uPUyK/TuYaExzwlW5TLw9ceIUlM+DeXXO7ew4dfQ53198OPylpf+mKWYfdLMAGZZYf0syeVVlbNG3+/fzlDAz2dn9cbvZ2m8"
    "su6vMonv80fu0q9PXfESP3w+c1+TNDOZJefxs2UzpG+WPzeiyJYw11LLNnz7zfLf/ewfPqZk/42Nm8fO9KRn7f3/by+qtxy8+/Qb"
    "eeKv3qU63YMEd517ihbc+/2bBuQJejwbiVnF6uWhF4T9NL7cponDZX+k+t1n7aLj9yY8RQo+efty+N37xYdFeRYe9uQ8lqcv8sdE"
    "9ycK+tig1dyehfcvA8hLi8Z/paKvJm+3dwQ2+87d7GIWMndv8cPTJPq7x/E2m4M2DqaPnntjbuG3Z18xw5Glg+4orV4A7UN6/7w3"
    "8VXCcvhVgvBotvNns50/7uO3hJQyf/EW9RMVXuQ01/9y/UmbH15OPHktBFo2o3kpJYqDZQOJ+RHa5pe/lme8Ws+3fvMp56F+Du/7"
    "oS6PtOj0157o6caX9XYvOVvRfZ/JWXQfzrgNPx8vedB3C/IhgAMAD9Zib2YBla+94z2Z+C6056mV8HFe9b5ipVk68H7wPA3+9PXj"
    "X3k8mOHpXXLtPa7w1FWPaX2z/fkw9O/P8+m3n8H2Eiq+P9Qzy/4gqr81fSUU9Usr1Id/8IMnrvASUrw/3YdglP8havBU8MO3n6nC"
    "u+XXd6P4wb7ee7i+j7zHk0+Nec5H+sEPHP9r/fTwlXd+33vmcSeNV8/xrFUvs+ffaNZskF5ies9xrW/GcT7c8uFVWx/iOWvsg9GN"
    "70ZXrpfMq8XWi8V3oQenfT17Sd879E0z/K2lFa+jK69a/smb/+nNc/LKu4fiaW79Izd3HznIvZPvkaLF9L/qWPdr+Rf0knPxi495"
    "sLMrXOabnrefXnR7GSuL3jxNIsT+5c27e7A0fX5h6rd+/t3T92ZTc7//qeCv3/8hUViuZyX8zndeqdX9zC/BPro05wkz3M8tmxY/"
    "85aivM+w/Mqby+Jp3zxG1L/3+KUIgjTO/Te/+ppdL61b3hFUzA0qnt6FcC/1ux+q/sX4yRl+el9b5j+MH+cPrRt+3D40Sxxh2b3u"
    "Prn5IBazyZm78JuuWAkfEBR6bdikrxi2GYy/kP8h8mt/Ed290iZ++3Tq3X0/vbsd+6jpssytp3f3F363bpy+3M+8fT71btn37YMK"
    "vEJfL7e294mnZeL1W7NGtR8teawLU1h+8+Yvf+9f/fm/+If/7U/+8M9++LtvFsvz9iWe9IL5v2YI3r00482vvAGYpyH4vdQ9++lc"
    "y68u2UCPVOD7v/D9V8JQFmSx6P4vPsOLWeZPO4E9voj+JfLzgx8sMbof/MD4+mCdG/fw+GruV1R46Z+nvKHnnG2vXF6pvIyHR0b+"
    "pJ93dX07K1D80XhXoWd9efhZyvSiza+0af7hoz69u29O9EZdjOnTSrbZ1X3rUSvmsl9fmClBncXNEtheEg7C2p0N5+XNVx/uw6Tz"
    "B/IYL77ucWp32cY9fllSkt5jEfWHDL97lOm5x+APY2wp83VTXm4C3vy3//J/vf/8j376r3/jz3/0n948fHpfb5e+8DnkMZpQzCam"
    "mJ/5rpwz5PvwZVnxc0/JX2bjZzVYLrRxe9e0by2aVryIfYEAj2sN//R3lrm/j5d7n7X73QddAT48AvLJ939hVsnvf3yf7ZrH4WIb"
    "z4/LJmt/hi21/+x9lt06vv3t/KNuiYrE3nV6aGZ9Xza3eTq56Mc9Nvy8bsF/dIEffxtawnMzOvLSZXpkftZPi4/K+o4T2Me9H2dM"
    "9DTQg0ef/aB2b+97dj4ipufswM/S15326YdEyfHB/WYnzLK5b2f6vaYtytK/fPLmV376+f/653/4L2fpvPTJrz6J9m388wT58fMd"
    "xT2L9JM373/4D3/6n//o/ee/9ec/+tP3n//6G+DxAvDmpz/6F3/xoz96/8N/9KG3Hvvqqd9nQ1U8yvlR0/4HRfx09EHCyytVPlv2"
    "JHuWsbcI52+UcfEaTX3ydvbzxaOfL569373axyLveKON7o5oPlk03yvK5QVFuff1X737+N557kvnffbKPLkLAV0S7p3ZOr517tly"
    "b5/aRXWXuHhaXPCDHzydHPzzNW5fX5pNgvP0woSlVS97Pc9Nc5ZE31nl/Q8LUl+tc3gGKt++z/t8EOiTFZzbs7Tu4dvOy/61LxbR"
    "ae8ZLk+7JCyuCPgIWi+51k9b034IrXnLffc1DVrjxU/rj949BC+nBXceiLOJedyZ601zt4zeR8GiDX7uTU+rHtKH4KNwvnWxTPfd"
    "D6l7vW9X/t9aVlPG756vL0u/lxWtsZuablZaxeu7P1qvl5vn1q7W/32/eC4fKJYXNS0kZlkuESw/fv6S36e44vw+zJa77nHS+5q2"
    "+5fZ9N8LmGtF57Hrf/K2fosj0AP0MDdnRvRvERKZD+d/8H0rkvotSRDL1RW2XF3BK3I+RufLT7xda17z9gW9L/2oNd/wYC/R6PkX"
    "H6DDfYDNUn0ElYsGfI04fOc7P4s3PMYGXn6sNTNHXrYOn746G7xEHZ7t01y3/2EByn3wf9f/5M2f/dY/+Naf/+a//4v/7YffujP5"
    "D1xk8Q9vPu6W2YYH8gOY7R4ncF8H2e5TUN39V99ri9ZNX7Lp3s41vJ0RLfDm3ZOpyuNXsYalfZ8usnr7tYYttX4jQnQpnwboY3To"
    "Kw72rqFNq7/42Q/D7D5yXoD51xe3P3XYc2d9en77lFHy/ovff//lP3//5b97/+VP3n/xp8vnl//y/vkb7z//vfef//H7H37+/ov/"
    "+/2X//b9F/96OfnFf37/5e8tN3z+R3/1xe//1R/+0/ef/8H7z3///Re/sXx+/rfff/Hr7z//tb/64T//ix//H+8//zd/9eP/OBfy"
    "0//l/5mt9fvP/9/3n//o/Rf/5M0D9mE98P2d5Uvjfw7I+M53fg7GuCcCPZrW2fI8SmsR3oN3Dzj9D5X3glm+Ehv6ilPL49nxv//y"
    "1+5S+fXHB33GFW/ef/5PFsE8Pf3f+8vf/buzf3r/+e/eBfP33n/+7//y3/zhT//on2vyXbi//ebF57f+ko3y4m6+YiA/W0JOz57l"
    "rpVf8yP+B0t/R/1z735owr/5Dz/9B3/8/vN/dq//3pDnbvjrn/z6vXtmT/qnP/21v/8X//THf/2T33jzgMx982rl8stLzx+DgJ8u"
    "rmYmDndX83H+2VcDgvd73j08xcIffiZVfp41gx4jh/O/hfnyL2T48dszC75PKjzOA05fTSt6iTMuAcbHsNMnH91X5S/527MD+9mh"
    "iJdwq+/nc7997XHefdRGfv62yZ8jjXd5f/ZoBffFYtk+vA7jdQxxXzyznvtdD/7Xx2BQfi368zw3/FVXd3899zMxzp+Y+p3DPm5U"
    "+RI0/v79KR4l8slddv/zp9wS0LsHbT/7zqMAn849AoPPvv+8v0n64oe57VNM4kOtr8IQyzz6h2mFpwyv1/2QfpT5TeOG/kt3PA/r"
    "/77C73E1/rv11zt3eW/7Ikjog1F7pZTlYiNfzb/+rHnd7n7Ly+Qt9DPumaHTPWDwrBILoPqgErWf3hXiUWIz1Ty/bV+eFvWfXaNc"
    "vI5w8I8x5/mk/8oDiOHLLm5y8W6++rjQ4UlSL7P+TxHB9lGL71b6/ZfzwP2377/8g/df/vD9F//4r35zNij/4D5k//gvfvSv/vJ3"
    "f1Nn7qZkGcP3g79/H96//TiMX5nYudQPqPGp6B++//I3l6K/+OP3X85u4MvlYC7jZ1f5B4/O4K9/8l8ebdhf/+S//tmv/eP3P/x7"
    "3FimRe3X3wK/xS9JGPW35kKefvXDvz+XcPcx//Fewm/dTdBc2v++WKTP//Zsgp6SKz//T+8//5OFFPzX//BXP/7Tpd7lgf7R+y/m"
    "cn78/ovP56pnm/bTP/mTpRlLgf/s0YTeTRb+6lmfOvXh5wjvb78ygr+9RAMeVsTi9peutJ/eFfTSb1H5bPyeyatdP2bI35coffr0"
    "gwfHv6+ufSXuetlBdVk2nS8Hy/627VdCQPVH7S8hKPSd79wnA9xzs2zZf9+29DhfG9/9EvEzLjnzpWm+9KHiWbFeVzyf/rT+OH9Y"
    "4jntxx+qexg/fin+YXo5dj57bvnXjVVWPgIGb9lGtM7eGp98//0XMy74rUVRvvjHj3mrzy79t99//nf/+ic//oWXxNf3X3wxk7zl"
    "2hd/5/GOuZ9fp8Uu+rr0ze/cQcWiWX/+735nVpC//D//80//7j+7l/vjGTzctXlWz9l3/p2/+NF/eqlv7vP3P/zi+/etff7GZr35"
    "+L+j6Y9jacErz37zaw+w1PfuNS57thnL1MI9BfPJsj7t1fg2/1b8tLFnEXxr2Q7oaUu4eeTlL1bkNQz6bHpKT/xgqb4Rjl2qf/L9"
    "zx7/mWU93COxrxbsLc7pa77OTdN7MODrPs5fbJv/3KrXhtYuvhpSfZrZfMo+WKZEX4J995mj/v7xy9An8+fH0KtkmKU1v/Lmvl28"
    "X8/tX7ZCmn/9dDRE/owefvUltjA36MV5f2NKy394Ck1/JU30g7J/9vBpucwl9f6yz4TnlnPz/Ptzv3v4+aV+tW1u/ELWv3nnHXa9"
    "eWnFN6jIK84w+/g7nnmFTD5gonsi0eIgnyYHvo5N/J8LRu6a8VVSNd1zX1+la372APvIu4fnIsv7W+weC/Tv97/Kj33Zyu2+TvPD"
    "nNpXq3346gTsp19x2c9D98UFLQhzCcX630AIL0tndt13P73vEfbxm2UW8uM4m28Dyzz8xWVDEAx5iA+0Zg6QLIQFNf9Rd/uI24fz"
    "kbR8Zea/zvw/y+qZuF3OUEd1Z0ISVTeIhxkUtbmuNibH7/3Nrc0NnzqoNjriBH4+9sFpd90yUHNwD/KVHzjTh1olEdMq2YrcWpeV"
    "Itxd6S2dxNZRqJirS4xbPizkkJQwRuKinFn1Dlyd9d4Hwdxqbhqu4B1xa27NZN8kAm3RAfcIAoVBD0RPyE2Dkr1VT8BxvF54yE6c"
    "3NrLq9OWG6l0p7IWJ2makzXtSQbGa3QwwyQkT/51dVLoKJtCmFvZjqcx7IqO41YIvZYWzpZ6woTxGO43dCFxKsNrWXNJtva6C0WT"
    "yhS2LaOm1U5+2LcdrF1Jah0PV1yiAybHUWvrqAa6PxQuxfhaVatmr/LCzpPMW8MM+1vS9YPoGEis7vxDQkvYdnVQV/0Gr6QNSvKh"
    "d4lusA1mFdfSZc+MKc0P7BFXRsePaa1Epr7Zp2TcdQeMVg+mcKlil10zIkYdSh7bmOzKms6VGPsnDjzIx3p1WadpXGo+Cx8kzjSo"
    "PsBICF8L4QZQVxchBeqTPHZjqNWExjOckBxuN7PTUK43tSuUFHhwQK/lPui0A8CUl1bIBmtAMjwNr2JJCu5pb2YkvcqjLEIiUmS3"
    "HsfB08k4WYivp63Yksja6q8HqFrHB2qbCCSSxcFq56RSb6NT3QXJOEtKGAdsbBhf2WB+QzDgulF3K2agNghw61PkHBanQKgcqIRO"
    "njWKjrx3ZbmmoXq25D0EyFBSyp6BWh7N+BRoouYqIqqDfel1mY23kCo4a66LCzvfAV0j7HB1xKILwNjsiY0PN1uuJofcj51NjvpO"
    "ii98jI0wXxdsSjac7CoiwBwkueCTLKfUBB1IbQ+ahJ9a6lZq8J4XTIZWPQ0qDU/eXIT82nDoaFE9AkqbG0Juugvn5ngeph0jD6fK"
    "ShHQVpWgJOBdEbK+NsW9fVTlPFV3IpDftEk7eebmAl2BG9mcouzaDlipZnTAVsfGZ+nzUfbgbisReH+TbuU25e2wt84dcSkOszAY"
    "C+EJfaA3lq5tSpIhRoCFhvgiigZb5hVZtgQ7oJ1Gw4OMyDBJtnYgol5fn8Vww8n5ZlLtoszJUiF7ActwVr74Ki1STQXLiqQLns1e"
    "ZDPNuXMhN2BbTkxZRwQQbGmYq05NRvWJpYIn9YhORkm62AGQkgu137GceQPWzRpcV9A5KjX4GG7CDYhuTh3pc1qXbBXp6ECn9anE"
    "TBes8dsVRhibSuGTeyTHi6l79mp/EMB0bYo9t0v8lt7O6gznVGCFB5/Ko6i8HeErpsriOAqYvPG0fSJ3MEBIZidStUel2TTmAjHt"
    "hgvMEwUSk/RBuFws4yaaU83we2w2FuuMpTb46ZS3nYmIhCMfTsMh4+prKbecYTWJUYtodQWnlaYbu2E81wkx6pNPz3VqG2+dAjcC"
    "48oovCJnmqVA0ba7DuKV0jGk3FxtsvkBy0BNilosdhVlkmenbI8nVFqL07QlQZhgUexQyzzWZwF+3QSlaoTMVl2Fvn6I4y1D3My+"
    "BsHhvFOsPbHlVQzXudN+13EUfSJPxxVp43jClg27mZuki0ULuZa/Tjz7ZlmePLfZ265SEDt54xB6Zh/2zqFak3WTNthGYEKRwNfl"
    "DbogcWc1mjYKPnzaF2bSG1ywNbTmDEG0AfqrFGJRse5W7in1tFQ8QhQj6Al6GZAWRbNx5P3bFZIMr5CplIHlcF0iYdij2Jn1UkyI"
    "UgzX0mqHp2gqZhMkW4BXdzVFRZRwwGlrx2/3gVIgp8SQrtczczCg8lrtXPHYNpwkbaCr5q6lgkQRfXYPGE1neRwd9WtMEUhwFvtM"
    "N9VVyjTHqFhofUKgdrrp8+QaYiglGURz4szZ3+W2e6qja2AVotGOZgPx8sGqaHy7yo4rpV8Nqyt+JsbVtamVxBFDbWQ4x9PLSm+T"
    "MTgpaZaIlLGFdu3JMEzbHHfCbpoaU9+f+6kWd6HJOCcjjAC92IibyBWUTIIO0FUPBJckDzEK7oiVaM8+WTlnATBC+2iAqsLXzvUQ"
    "CuFJZAONPhzOhbWxWbhN6zKVEpbBo2DPjXq/pXxHTDa+lWS9lrhipYXG6MKg37ZTud93XajC/rlS3FgyczRkdibrGJrJyFlE+Ve3"
    "wmy8hx1A2W52nQ0IYSOvY57SC4v2DTCfBgy7HIYm8fodghbbo64y6g7tCay4kIpkS+jVs9vQU440lUGUb/LotYNZYDRUE71AIRx2"
    "VxqOz/SN7/TMTkVjr3lxaIReuA3rxAVjU9iddpZUQwU82zVAn0alT4EdEiBrGHJ45ZSFUzvM5h8yQlKLsQDSZM/iLkSssMz5QrQl"
    "g6/hG1K79MgXwFbx1mOBiFghNaN08LPRljqZEsE0lAto4l1u5QvrPPMHmWi2o8hXlxygzHKnuJmMosY8lg1Al43pOFFIVJ/W9F7Y"
    "uGc7OSMMa6EtMqmFGZKJdNjemjUaOuJtH7R2LRMJ1JUDE/KDS8FSTMT6MJsmC1knw2UVqr5l6ijdz059HRllLerW7hBpJ/Ey7CQG"
    "lKSbI+Feb1gKfIM6GFRcBA9UZ2SAoGWkQR6GMhnAzGrAAwQ6UVHRluCGe7uDJj1ITzwfHi9RczoRg7TWNE8E9hvgtO0OeU1gkbuF"
    "aq/T+eBaGut+QFInWR0KPAkTDcNOly0IxyBQwuJufRgBgcgdxnTsJAooT7A93bgN+IQLl/M4AkAtbxktiQP6wlTnkEaNXusLDdTj"
    "DV8Sl/E6bvc+mfiwJZOdshIO/GF1oEeWLqibeu5ygZzrQXl3vQI9St9Mepa4ZY2gnRCtt8DWvXniPk1P+QnwQ2EdxxQcpsV+h3bZ"
    "QDlkfgFKq5TUS3nZGjyjoYJVtVAJ+lHfXhrZRXcbjSJAb3tzb2pZ+qLXwscyOit6wrubcxToCQmPxq6UgLiQIko5ZMXp0k8c5bmC"
    "BpwpjI+z9upn2A2y1XDSr1v9BlmlD+9UH9yfG+W610OeUnzczZG13AbkHtA3haSMmeq4mce1fTwPYK87V9d8J9jsWaJCykFovIyP"
    "JnC6OnvcGM/DtEVYKqtbnIMQHtlnHN3QLMMyLtte2yPoHtbuOiOVMM8RT08DCtGEaQ2oUr5zMoGTdJEZ4wIL672aGIjmDJyEwJJE"
    "K0jSUxA9ic5sYM8eEMBWcTFmLUEyoJON6/GcOeTJiCX2Nk48cVLMzRqztnBVlVVCVTsr1LkbVbFKr8/CaGBrX+Yzvkkar6ZcbMU4"
    "6TpPzpaGtxUi+h14LDhGamtb6ChDPdiD5DZ2l9nMqM7ejSz6gjX41BRzQphBd4Mnx4gZxIhCN3qiOTtxRSdyCpyBau+WTOdBCt0e"
    "GIXWOFxdkVtlvF25AGkrwaQ7LfOjwCft7Ijp6boA3NE58+3lTAN7o6bPouzKGSKDyZgxO1exaOEoNOQkgVjRqSmbl6M392hTDu3B"
    "7vl1WO0UE2puR4w0q6u6vhkDq1RadOV5CCZRLt1JRu2ZytoZYXLl74Jm1npzhsEqSs2ATUBV1h4ZxvTo65WuGpUp6jjD/IzbmnXh"
    "1uzBPMeq46uZuFb68WIYchZi9qle7evLIZk5VtvseCHBRWOL9oFIJqdhI0lWQig2caZ16lSbq5t/2FupjcTW3s+PBg0p8bApERrx"
    "1yE30q06ppXD846iOaYr4SV2sA7Rduc5AgwUh2MaG9Wg36jpulrZKhsHnDacTbvNCeNsU0wfXRvqzJnrvlB2LCu1+aYvjo7CTM7W"
    "CtVb0OPr1VG0CUakADcS6VgR2p0X4qZC1dehtGnVtikeYoZqbUHoLaEKBgaklbiKR2dIUXDFjXWSMU0YDFvuGAPS3pCow42jwkjk"
    "CWYlIsIZbHthJCW+v/BiN4SQf4kydLpa/VlruSuaj5MWolWnRaDAYPlwnBiTk5SaMnJmTdNjl51MBgHb6CgxMC2ZIt+QeydDQ2lV"
    "0NH+qJz2lKQEokd7I1Lu60j1bwbV6LQr424PTHJZkNZIgC7GA/guvq531wZOuC4Sm9zTg7kt0DXpzw17mxlgHiWlu5qxju8OkGPO"
    "Tt7hBg4nnEiQ0pCirSGUxUjt85AyUTYUWxYpqnq7o/GmnuxohJhZTliax3mAelSPcYXueFuH8S4DY4kEys6ARN17l5mWTY45qZiv"
    "XmYEEAXAaZcbtkDvVWxseXIejlHF5KLiCBPRNLtVkHVZCIoVgei1J3qxLoX1kHRzm/xAZ2OLrikZcQBfs+t9UjohPZNzWq5Lez8P"
    "DiU5g9Lii5TVzb42chhR2WAIt4qj5DPZ7IsxSg2qm40JK51iajeBcpSq7FCJLusVKIZZbWAdxcNxHgdHeecAcQScMr8mRFuejVwQ"
    "X83NSrwg+HoAUIJfDRlDUXw40A7Nu/LKyyBSKZU4kUIdRUIXb7VVKwaXlSvbHnt1KaidFcnWi7be9pRfkAcaB5DJmXE0j+wGzrse"
    "javRzNpQVdQxVGlj6/AFKAarotV1nb2tLZNOty4w7SMgG60B3EMekZf8FjxnYSrUcH7z1odWJ5UBU3y1psyEgZSVgSDTcO4RzJYd"
    "YdfL25nFhHXsqRDfNEE6TTMyoS643OUadlkRaQGe0jWQtjPOynWFKXbrs1wwR/mqNJToAuv+FqiTZgJVcENkYCb6E38+1uR+K/DH"
    "NjWS+nq5JHgXmsXOnSUR7RuOYyOYtjYcoTUn19pBHUak58PFz9CTbrrb2E4asjmfXNw4c8V0kwVGnvvMJShKXEIeho3wYy4poNpM"
    "txV2MVPeYcPbQb2t9y6PoXAshggQ8IeNvQVg/ogffC9p6fLIxCi3q6DZO1Fmxxc02JMgn4Lq0UzkhGgVBO9wJIEjczVD9SI5qmlg"
    "xUdpI12pLU9saUcegBW1CakhYddCVCXl7NvpdT92syBh1uyn6wCt2nOVsMOslbgbngLEp/odve/54EJL6A3mbt1IzGQvIRq+OKon"
    "36sRMss3qlzmKg+OAsrFU72/raAtuBY0juJpm0/y2Cg4Y9CsXIakgmLDmamwxzhpsg3JDmJfUayyGaAT6dlQjR4ut6ogCaXVMtHB"
    "aXpQT+hWupIIWeD4dOziHbtm9XOHwBrl41un2/Vh5M6U+WxCIDLuL0MNDFU+qkgV2AeAba4Sda45MR8cOhIMJRS7aW9TRh3Z2y0E"
    "0j0LuMFq2ERbfSXwaYIyYFmEcg3uw7MA3PZ6QNI0hBfXSjTTjd0U3sCJwWE22jC1PlSnXcvCacaC1hlTrU4dEx1kaJRk9uWghW0M"
    "0+qWBs3WpYym7ZnKUsKNh3anfZVwYwswFhNvzGOEN148iQizFShNC6oVi2RYT0cIRBeQQsE6CBKOo7RXkKrZlWehhFdJwS33YFCz"
    "G5BrhJmDDsk64EvP3F6irS3ukDO3172rMAOyXUK74OAkhAGL261VRptDo/TljOKETVxebsjY7K+qsqdy2sHOpekdLVPSLpY10ANx"
    "Qt0Dkq7YythSjlmJCht0m7OgH7SOUKgEE0NHmvwDpmOnyYnYQKKI1nWVW2uExe02UmtFwm5mzTJGCHV7MiZImgBmA7M75uNBIvIa"
    "YsOdn14yoUVOGrtpS4KqVDzmGIiORnfHA1IeEVvFEvfySoiiidyY8EwBdCcI0lYUZtS9OpzDXN70oltQeYillEBJs+wyklQj0YTY"
    "gWJKc6Uja+mS7wMNJWN1sGw6AahtOYv14iZrT6H5Uk+oOgvKHNkII+ccDmpf42RYYPtCXtkshShI2WVlJOsn7dz3l31mwDWbnTAH"
    "60y3T1oph5DilomSuIJVhLYdPVvBu1DzAIxuOm0fBRi6Aow9ta0qtN3UFMk14ZaLuIE6UyEvdAKvbDlYI4KDB7MbfmXJLSBtjgBA"
    "E44ROjDqRYg48JeTcXR35gQJkIUkFJwj4cnEJ5DzSGK/H8H1SlDLaL8SesIBExMkO8+6JhS7NqERzum60W0uvuD+7GrEHZxf8gTY"
    "+jf/yE8Yvh/YG3rdOPm1F4JcDiHuBMJpIVIu20xMs44pqKtCxpfDLqLUnUvoyoawTK3WIXGci6pZmlFPk37DtiiPuBR2XoUh3nnJ"
    "eJ65XbtzgyKEkWayYNI3ddA5ODo+MJxkpAwleucL7QfwaZz1oyM63BGdshuAs7uFyday0lIvuJ4+wdOGCkrquCKTPEW1nSsYNhER"
    "4Uj0Dan4vTtRFEOT6Gi447DfS46+s2acMQRjI4XZVhyoxOMJ7JxBEskNSj+ojnVKduzFT8DOPCOYDph0cpLGQczXgEiom2K93ga3"
    "mBSbI3gmGCfesF5FJ35FzBCFJUeq9ke2wcIA28NeAM+emiZ6AwfWPMPhYX8ZIG/uPHLkQgvYAEfRqY+7RgjTsGJLmmE5NzhKmr3r"
    "dsdpxBDQQ/mUQRoqZc6DibWcwoAkedyVmWprEsRTgooLnnCis6qPxJ3fJ9ihDGEIP96yxFinJHXK1sqOVDa6RI4yq3WUq27LjMiR"
    "1eYkdr2SwG68u23ICxdAB7jRFIjOMoRdY5xNoRrAI42s3uqwRbAuOlx2GLNHehFmUfKgMiAgMRTnKZx1gpQrRcf0imijiAuyMrny"
    "oRiDVz8EzzPf3trhdXZ7bjZzMlKq6us6t2fVCtoRBzFqasEUvexECQYJuaD0Syy5osr32eVaaXlqBeuxOGa2E4gQeA1mG4Q7F3XY"
    "zoYXycfRvclQhJ67bLNVrkYCSOGV3uq9ogYoLZRjMFK+1czWwLERmqtDKgzECKwLm55V8rZHZtvfxRPkXaXtBs1TEj/0VoBVrHzZ"
    "AUfjBKMn14/GU9HQG4YHtDOKb1vXriXXssyqRH1HUH1SkiizP1pQjGSbmBoUvmGnlR3S2haIeIWVUNs7aMDgHDeDQJo05RIOtYYA"
    "F3PUPmHpaRq2MzY6+fn1dEyECqgOK7iSHHt5paVtaGzXgalShbceplzkgMM3Lo6zyU+lFoFzAKtn7qqt82tHHQZiIxWdSKITBuy2"
    "DXyIuIbiZ7Ay5MNm0FHP3Mt6l59SWTOvhcloWn4+GoQt3cg9ppYZf7JMwmLH86mhoj016TgfMkSNObSBK5JYA5OwggA5PI6WlW2N"
    "y9FyobLEoEy5JTxCwJKLV7bMGLJRn61KhaFCIUVY0plbcLIhgNaPsGTcjtMKoizCFyDfmpkrsZZiljbPcn1jrVDDTZu9FHbvEl7o"
    "t0fKo2OWm60NS0SzDy8gKaPo6GB2a47SE9NNx2BFOzrWTA6q5+FGqTijm+H9CvYzsLr6ZkO2kJzxOFZFIkQmPsWIgATN8HzF25S5"
    "FkIabYHe5RzORsAD5LXBYaV2vEUgagRxRMZO6uilMy7NAB0nSpgFoAIYt42gmSDTgebkITxWUfIIQch+o7LncweMKGqdMLRWCXKn"
    "Sj54VbVTXKIbRfBpPNzCIXeouwaiBgYwyLE8iFsj5ihEELgK5ApV0IzLBBXV8WzE62areDmzmxAZtmZ7MsAtZkMFWGSH8kTaqkBw"
    "AkWcVRNCbpPNTVDAQYh68wmmsNMbfIraGRaUoG5DuOvspSu76cIdBODrxAaOh2ylOH3csj2Cinv0GJrzM0oJER8ZcjBU4Eg0ehj0"
    "u4nv4uMAjLVU46w1NcQ29mDNtUjI3oHy7npEdTWaqWHd4xjK++m4DjYYz2c7juLOQLGzuBmwmIAwkKC5a0PGywC5d135mK/QIVUg"
    "N4oxsLb2mYp2bVupo+7E7jCEBstI+u2yJxNqDM/59eL6rJaPyEnM6sHrQMbd0rXT+9ebz6Q2WCOgg8lsdHArhS2LPeuzvlRLhCo2"
    "4tSsoZOsMy190XxKWYm3awgFgJsiRr+56Y2uoFt00OXbahVYwbjGJ59Qyeig7srTHtAgcgs6nVSypTLl+Q0671atruIKxUaLGVSi"
    "gUVipKSj4UhRHl7QFxA8X5HKnGTkKhkS1kDTaDPdkZ0tK3wAIsiqkzIpGgBUM3FHS5dQsmZ0fGS2oW52fuTQEBAka8zPIWjISz3t"
    "2LSb8RuIaUpe3pwxJ1hdQEVFFKUQVFHkuLVO0R5p7DCa0O4ooML22FymCK8bYNjp5/WaKtpQ0zaQeb6aYTH6jECXFWVRUcOETKnU"
    "TaMyMgy404mT8pylj9YOGFMvrVWutmmhIfpozUpSf6WR2Q+Ko21Mg0I1tNRRgYePjUlvyRO1zSRUJjs0Fwg9gEE8S3L+NA+s9Yq/"
    "4prtKynca0h4UcU+h9AcEjE3Qhtyo4ze0Yx0CNMJ0nFuBAH3MW6GAHCU+PQqblS7OBQKF0pOWxlIRG0M1uNJxNOOZaa0YrjfMFKu"
    "XIqDD5xLtzbghhU4ia1RStvvsJ4LXI5hYPoqSUg6ZdDlOhqhQSrqHucYdUCj2DelYjh4Nw0c3FswVzR5rImL81jlFC65apioYAf9"
    "aonbCzO5pDag82jwZhTBCzxB6lZ+8qW5UQMt2avGY2wk4h3qKISz3V/57YVX7Q10zj1IMOGBkqQW6tRIm7ulHXztrBNnCgzEOPH6"
    "UuR2YMJCIucTLHlBK06ECDIaOV3f0lsgEFRgRjjJhdMn0zLxi25eADGgdoIpzmwJyMj8EENI5yz8Kp9ZIocwEqeI5ni1N+LGuAIy"
    "G54joQnoq0JI8Lk+bZAdexoqheS22FSNYgdUV3tQ2HhNtVvONGzI1BQKRaIRz8WKXs+OU8i7q2QXRA4rxjitaWGS1G1MlGpd9pew"
    "TDeAAtQ+29aHg8OcjzO74nEqo6FA66J4KNkNxVL0lbvdRMKS1KZtNSnX3cQ0VKJf6y6vGlULbiW3AmFvA0iZqF31iVLWDMWKIAdQ"
    "zgR4JKKfmz1nOBoB6KE/wwHKznrw5q/rsr1eWwuCYJpweVILRdOPyE4nRWZiMPEG3jiGXoatv10Z3o41rp20ZjyDdsMDqe4IMWb0"
    "anVI6eQa0N6RU8X5cTKYO0cIAyIij2uW0Yd5HqIqjDE+vDnNfhRs9r0ls/CwPoB0sZNq0E4t3qkkk5QMsgeUNCPI06yT9I5Swhty"
    "jDKOZpULd1uvrOvI6simDCrpkAur3XlzqMaulGZSp8hDQkm1exqBaxzODvHEBSHOHHUtxvjtrfPHpOgFzNqJWY+eM6wZGWJmnyiu"
    "9nDRrqmQZnnE2IUcJUgOP3DrJJy73rxcVvyNnN2QrHuHW2/uASbgT/HZj0vVD+VRABvPuLp17S1zSqYZ7bR9Ju39ztqdqKnjNFAA"
    "b9vJAp0euBJjLoHZrKYEa0gSu0fonMpGasY7XCgPSH4l8sz1UbCOowQUnIPBKsGIG3o/nQPL1CN9w5Q+ZRD6qpHkybjATnEcCyC6"
    "+JlToDNRJJDtLJsNiAKzH9Eua+VcSjynyRNjcAqQryXao4VQFhDeZ8XBji/56XRJkRSh24Awkz23xhTBGuxzgqblsOLqUxiZcXfK"
    "0L20mULzUKxG53DdWgEANBt5rIrmNLUKTSJUQKgIN20P6IEpRJaYucHqUuvzWDeE1KBvFLCaWYayOSHCUYapSTLtlpIVN5zWu2m9"
    "ReT4pEZ4Yprr/UyUAobyCnaoLUS/nape5R/ruFR5TTL4ASCPK5jY2x24G5jIGKIQ0ScGojqKdTYZ1O7lUaYOtkivNlGOoAB1rsVT"
    "l1PnaGsEQHw+sDZ7Jgm+79iIZVe3TKowjvL9IyHlzO2GaIC/9vI97Mi5TPoHj1/1EA8AfnBNMaQagoISNaADz7Q6KVUkhZYBkhxj"
    "GkjYY5BAZ1rSHSp6hzgptBmjOnXDS0DdtPF8m4TdAeOzhl9FqRpFcnSMAM260BR1ZuLbxaPDbKWP2TbhbzduWHtRnThu6/iqKrsh"
    "iq3E9THkBAmatvU+WKEAb1c6Rl6bSKElZYPVvM/0x2Q1nWzXao8bfdfNHE/11I1tcV3Penv7CrUl0Q/7CJFSVkJaOgTqnZ2UDgLR"
    "NeXL0WnGmUePVGRNAR3COJWVgsIQP0gXsgplVb7RQepKoOsprXQEiKJULyilo5hjRvmYKWgb1dqKzevpOko7GL5KDrDKFbW7yOAB"
    "V0WCnZL9BcV4UaD5w6E2GDWqDWtPwsfTTmZw9BSONrrFiZqf5mF6ueVg5YFJfmPBxtlpaNpw9Roo9oXCq5kBinuL92/jPucCVdpY"
    "VCblahuNeZuPSn/syx7b2Ouy8VAibzL1crqg+Abky57y4U5LiMO2jC+6aiHyzBj3IsGs8ybYHtcuypEB6ygDO5zLI34b4pBqw/DM"
    "y2tKS9qiWPfipuWvIgnmp1Hbzx4RIWslVipl9mZ+0225Pq9FdNdrA24Xo7uK9qjL9EHCmtNBvoboJg6RFgnxsqQ8JOnJmMe2sgGv"
    "r2wBZAzOJBXqBZ4etmGwQi7BmSH3tanMHm5bxN2Z85gjDbTFzeA7oM3Ruq11wFcMP2Ps5LANYIijeAahKTrkmYbpil2P3E6DgpWd"
    "BlaEeepFljcKkjhyEWxNrQAcrqq40j0olEB5vz22CnjIdkl/TDO5irisiI71sG00tnc0j9uE4KTi0Uo14Lp094yQ9KHIB2seJvIA"
    "YFPTqbY6uTpa+lGZiCDLhiS9nKr9bNlWrauX/M0L8IhiGWq1dRlKvJ73zFgCCmExEVIccXqSsU7inBxaq8fTaYvlt23URe1mzelc"
    "TMGJnoVCILEjHHHCOp0t5MV2TtTgKrY7EKQ/neR5KByrndmPa5EEzuSUFsiMyEajhZsOY09Xxm98W/WFgB2LlONrs5huYLa3ADvr"
    "eKL1UzFMR+dIEcedkCUrimipTVVhVqhLQ+lzklgwMcVcqNm9Ojv8hF2sduNJV27fH3URQHT+lBAaRXC1hgGGp3K4QR6um/o0A0gM"
    "qQtiU12EtiCL420gb1BH0jJ0dUuQUNFqPWhdWOeIsWdCPYgC2ZMgens90XWBp/kyb4FTFdDVGGNtzjcHAXgiyI0DFYa9vdURm65n"
    "IIvG8Wrlx7o+DNOGOhBsQl380BNGbctDt801J6D95hjWnUfClz3k8cSV1NEZJvX+KKfQNJl0gnktYcV72h22hKRznc1FRnRlqTCi"
    "wjg64bKNl7jFmjln4wUFquDU1/V6Sx/jybVowJ8ZyDoUbVE17SwrVZH2B3Omr2cuJFWdvnkcgyhUjGxOFG6gWOknxTZCrHhznRUp"
    "CkqMim7ocaXU61tzumkIlXLBFtAzeN1nDRGBOgU1nNAfd4WaHQPMLzUVrECSVliqsRFTYtSCDuJzG9ySCb74sLTGNphoXzhZrtYw"
    "BJR+etqaW4INZGmm/RPSU0kXGHpNUUWmFmliQc1lPJlh1zZrjingFQ2kSGxwHTUIsqPcZP6U6S1Fe6YWKrva0z2wrcmDW1ucZ/or"
    "cXbphu5DKD7M/sFxZrWDehrtrMzx2DbiTkqHG/AkcTvKhKyOTSKKZiZuKxobFQL1gZ2Hq9rRyJnMA/GSyDv3ggu4WABr8XbrNAK9"
    "Fv3edIou7L1kOyCHKYWLjbua+JCyWTFB4ngzc3eHcvQdRjRRck32WVJd+VDhuKOtDQMxpSRebJC1CJ9tvxeOpkhhYZasR1fxL12V"
    "wU7O4tpuLHF5Ntj50KsTIVS6JyDehcYNZq2xqWTspFDzVCeEZMtce7uNJo6CGO/oXQT7bIlVEDjovOg2sXSy8/GokVCfUwQNu5jb"
    "FZqxlptND0ocmZKmjAn6qcLL86jlxY1lQ2drUDDBg+uKYSippaxZymbs2qx85Qw3NzWxngfdxh73QnTE0Mwgz0FGiw4hqboQT7Yv"
    "NqDKJ3vf1zSmKVDOrskU87jjmt8IN+5MgOC+PCXHEba3iMMlrMTzaDwQqIiw0HYWZJREh6tQOgcL0/Fxvd2sImY6FHwNEByjjLCm"
    "rtWAxsl4O7vyE+LfKPWWb6sgQS8jJOtRzcr5uI72Yrr2wOiqxftA2eJVXLT4qjMt0Pb2ok/Q0lnbjjRDj87sEFlOHIBa9GZT1vim"
    "tbLIQ0SPmnoUZuOKKpIsoFDVZpRtwXtMW40t3OanXgjECm6bUelQ7MQOHERXuY5rgddNcMSgvUCbcJu4dp7C24C87AtfpB2WGtSc"
    "ME3RH8C+Eq+CNJjQHiv3vhXc2EmHpoI4oEmv9WHU3po2VHooharGVDattVbWx6o7Uk3Y9huRM6wbLGrYMASXNSt2UCytUpoJs7PX"
    "Ij2Gi2J+6WIC1urJvnoxmzSiJxszCZadub9Iepy2ujF75sNaMirGr/BkbSUqovH0So2IpJPAQ39kMGIMzzTDaNpwKZlL5RoQeY0x"
    "gu5yhfR7rLwNTYWerwguGEjuJ+WBvt10Ek3Cmcr7BIGQGHprQc3zYUFDtmIe4DeRDmfUT7gr/DZeSzsGAOF06qF2XG9YXAnUG4oe"
    "9xp/guZnoLojmx39G0dnjJ7ihdk0tHbeNEyJFQKyg5hjg6gDjdznAUtEx0Fi5HBXxdP1HgwvmnAtxpPdymDfzOZgO2gUdu1CUjdv"
    "JSwOVjpkjY0St6QgZYt3p2un2GcKDu3TBmar43kzMhAKBni916OdeDzdskij0yRGN/BwuxSX1RZAMd1A+GO8I71Uvzj7c9oKRzLf"
    "XrdHaZid6Q3ekboKb/3qJsoesx145bjZBbPjm/IJq7ye3dmI0ZkFeT3bKyaR8Z682uQM26tZTykFTk089PIbWQLw9iqGI+cOiAbm"
    "Ao4F69UlFSHWaiGIW3iiwa82fTcqo+2cEdA4+fGhqnREUFfUSscTTTxaJsUqqRLc4GQEVn293TG9ofrM6jrjlQGdq9DQmwZhJMHM"
    "Cu81Wyirq7PraykZxg7CdYNEK4G9ivMtHgCNP00z+Y72BK2oio225P4o9KS9zlRqPdvpuDnFh7rKMxYBXCftA0CDJgeSBzoDSpnQ"
    "R6JuWzTDWTbgi8JgtrwpRLUDB6w9FgcyKFIrx42CEs4Ykmp4Eh3PI3TgoG1q5C547gNxnD123PK5JjvUVjExqb11azHGILbApELU"
    "qVsC9CXAS/kewf2TrwctYHlDRTkmd9XoMRBZNBEv7dgngzuYAXHyZq4e5euVUK08AkwDxempc+yQTuD16FC25Mq1hVy0Z3hsNsRe"
    "DA4yhAMk2AennmDK44zpKGuGXD4O2tpaOyCIvfa3qAZL5roEEJeCVzjm1goQQz2IV4Q/gVIzQ+TIoZS1ajrHag/3TpMWaH+Lu1ts"
    "kl5Mz+59dggWXvkpnAS1e7PAmdzHuQIDzqqcKZ9n8SnkpAxx7C9787xKNnXFR3KNTZuR1jQWdKlanftttlFurZU9iezWWyAi+Yvc"
    "FteBnus40Se8P0q7Bqzd6MYyVdUUXXAsroZOb+LZqs9uUjx2Dlmply3O1z1QGuutX56jfdlIM2QnupnZTB4nJD6S7U5Cvkrra2Pt"
    "s80Zm26xCETYbT07p/2t4H15xRFAb+99BkrHa7RiDoKrO9V1bU8H/AiC/lXUuPOQupR5oaT1qfMTaCOpvrJCZopMCtf4xDIsrKj1"
    "VQwA2E22Aju51ZoXx+ZCo/DFllShD3qxMZAETGuM5DHL5LzjZNRT6vKq7DdqnueH2VaeG/1sFK4bwy5lD/XGLBTFL2eE6Ntbbnc0"
    "3NuRjU8mB+ZAjhGT36+KkLzIIe+ZdAT5dmVEqSaprHGcoEOlH5pqnQply+oFVYT+zIKFbLU2D7wF+ezxPFvHgKDX2YStN5O23+/v"
    "S2Z2+4NmyijjSNJ372+28Mv7Rij/fy3JSdpXS3Iu4YE/2iMBnE+MQ0rGNY1O80PREjYjT542Dt4aKk2YP5grHt52zUZud4NdVfiq"
    "QfoOxYPd3uAO8oxMdhvRZ3YQt79mwe6UnW7KDdbhwL8Ju53kpcppZhVBe8OnPO3hGoZzHcDnP3A004LEs86R1WPRGDJA6JTplqOv"
    "/QbLqF2k5/jlsNn0hVo6x5S/yjMK2FDRrlKrekMTB77r+ZVT7KbrYW3O/S4JFXvkSWhTaN0ox3h4PdCZBIDy1YpwrLkdToYt4Lvc"
    "MeV9Fpj4rrhhl+1BX/tCWTtOEMk5TZxDCm7gk39szjnGnkHaBo6OSh5EeC5sPYxVuEUm9noozV3dcF7CTo0Hs4CwZkxzJ93q45qR"
    "tiOFMpR8qGLZyG+ESlcsnjNo42+9w17flDUAi0GRXHrFOUcelZO5OdZsHubrfQhzwoWYSSfY5a5M7rIKM3bFCsM1IVVD6bDrqsK9"
    "2psggwozSt0kQq6WrRs4sdrzWziZ6QKzNTZOrV6Pq4OQH2krRm7gukjc/mYTaQqEE9XhfHDcUZKASNjVvICM3FchnArkZg+U11sY"
    "XlLnoJHVxqP4yuxx0rtV+jFfH0sVJCHJv9bo4RCT/qbkwNts2rc0aztDRaq7zbW9iadmRoLU7rabe4Bi8QQBTWAHKtUuA2fvEe7r"
    "FkgbsSxdRhovdUjWbK8HeBauWDzcFWDYUhQwtQgpEaZIepUcxjoAXHBKHa6xJFn40Hf7alhjwQ0/nZsozrRK2Q8bJ80vw0QK023D"
    "4auZCaGVXSrWcE3yQjR1gpDPW1CWb3ZsFRuHw9dpfiaDQ9/bJx4sWVUgzzTiunVYF2IXA7Hl11RMgjWK70/psDKS1qiokCT1lX+W"
    "iHZkcUsmB5uwTU7hSDzoUnglXfCDft7JxcGgt8SAeUd0hgEKcgY1h4/XtHeSiS0LGVqsBJXqpibFgxmurucRxV7PFzxUIdKhRV8g"
    "yQTaqT1d4GJ1FRoZkdfK+aCPpIa1/anc2rq+O9JXD5ayQL5iZz7XrfUqbqPC9JJj5m79FRODUFf0jT7I1fEUIh21PvLFpei2g3kU"
    "BwLhFVrMrBY88u3gZFNUGGN9LAscPxmRyjiN62kWtFf7EZtBj2EMG6DHTyxA4jin0u5dvqnCuoS2zg78Gc5McjWKcmtXYR6GyBhc"
    "4PHoieNcEOe5K9RlKg4Ac1P3dbm3CE8REPQgww6TbTSyLdcxzF5qD+BOtZiWrjNW6cGMiQqQchLszl3rDBxCMRMIgirqX/w6gPID"
    "v8gBKqJDdBHDq4L3N6AYiDRrmG7gGi2Z0mtbEwUKjbJ85JtqHrpoqdw6BStMPjzsKWUCWmyV+oUFALPjPfRb05tluN7kZHAK5NjK"
    "/csglyolA+n5ONYnUkSrC3rsGegc5HtCZW4AfvKwpMSE1b5gdnNfnlYw0Hi8Q6pbptt18YrEjloBAGLRrKn9gPeQeyuAiOFol2xF"
    "RogI+9DTe3AbxdtTyBH5eZP5Ujae9X68XqfGt/NyQ134PUrFjmKIsa+uGUpUtJpckxGvAv1U+yFsz22H1nHMVntywDcTTxy9nqNk"
    "Z4YlZwtG2q5nuFtmUVnp28m1ngqbj7wT0eF9LfbEbH81XLoNh9zPdHOCiY1EaFYS451/JQLJYcA8xfxuT5KyUW1vhmc14dGMr24o"
    "XyzaNFz+8v/Rdt7KDSNbEP0gBPAuhPceIExGeG8J+/ULvexVbbpKVCWJ4mDm3u7TBGdorMRuHjT01b88jmL36FEqY+q+29YpL13P"
    "fjp/+/7ur6Vsrci+Sgan3FmZYehViD4tOGZ7udbOeNaJxc+cbyDAMz1zeZlF8PPscSYpvJTShc4bslO/1fZhjeHX2MqJxT63u7jy"
    "2S7xQ3Tyg29T5kg/7ePMeWIMI7guz37ddDptkS8bvnMhhv4Y/FYIqmap6ks8s0Wygeu/IEkD9kp0UHjMS4+bKu298HHUVimUgdg5"
    "A8e3FIAxV2TjEUNZpXqBErnAvl8uGEuxKrj4z8BVwmSF2ei+YACflYPP+my4MiqSdn4pPbcEyDHIKBfQ5bAmuG70yOcthMRnUcVj"
    "Jnq8zv3NimBgE1Bl/0iaZU3MtXpDjLxRnynQy3sRqd3ZqulcvLaUqPilErpqCOqqOtUWyIVjJetaBd6MlfvOJ9xWT/yJck8m/pSK"
    "GVkLGEX4s2DFqcOMQBfleouTGPBDn8QfbbEPg5M+hVjJ23jTE36hfKWsQdL3uLUCj2oMXZlTr6txPkpfU2VjvR31Ubm6jUOWdlgC"
    "0xuU5WiGI44QulNOwWvhaJXe1CmkX9Fh/IaRx/JmncJKiCptIJ4j01xOAZUB8C0tFUSfob9LgoT7is1um4+GUFYuK5N3wfd0w7t6"
    "Nv3EbZwYJvAU6mdc9ecHhANkAwN5Sy1PkFoqsDfnOi0x6VUOe/DUFyR6IrzHa4jqW8grV7MP05xUhCJtE30ENXKDabg+39eWyFcA"
    "tk3wW/eoGFkMpAEArwjsGWOpLhE1eUx+L541pJUCXRoKQrsVZNwBmDQAjL1ikvCEjl2gXOLnuZC92St9fJAAC9l5K+y5xmooICM3"
    "3KBGOPzwKtCAG1GvP6Mula6u6D7CYVm0VrQRguHr1sVNGUkViWpPlw4YA+ie5qpbbJy3aDbV+RzBtd8BGUh2AL26+miiEysOI5Bm"
    "w+BsUsjA3Bhuq8986V4olm90If5+H2m2WXTJroC/+NJOCaXprvRzBl93SwXXcwgL+AwECXJe+c31jSD5Yn+j1uDKCmqfReKA9QI8"
    "vEQ9Pn4yUfchgMJDcy1sGqOSj5hZn+57RVwGAPRBsD+bG3ezfg2Pyhwl0FVV+IYfnLZIcbzHMuTeqOObyNfzCDZIaf0HP5hl0CI1"
    "Pyxi0Vgoluc2bl+GBDalEobfdWnKyZhzwcZEVoZQj4OMGRzVsmUNxeyPVRWqoZqo8dltkqxzOyOP4mTcX8bKUVMiPYYeugTESGdk"
    "A7qgt/pt3ude00TDUBos0RJaP6LzXjZlcHWpoD1ml+Lr2e0YJ3WmqLt4JASTZQB1HOMs8s1ng0ym5RcNaHXiwlvmSQOGdvWaevt2"
    "/TrijOYOP6lpmLGnicWXvYhkkkgkehw/6MqVs2Ke3XlGlD3QLAC7JUHlwiowxW6J5oDg32Cq9viiPQ/vjhezIc8lIfs9h1q7Ng5C"
    "F2bXFc0nRp9QJCiVPkO6SRLXOrD+YyZO0scD/UA4sivpZuJnpjJ4HLOi6CXfnr+KQzMREfv5ZcNnSDWxHk9yJ9XGGHNPMl36tUmo"
    "bMym6ry4AJPFaGZ/uAqmR3SI813Aq2AM2ucNuBz7AwMV7BCyAAiQi0RYlcw4ZadfC5XRA5bhk32t6UPUVLKJ3Yt2PdvMOB/vIJ4g"
    "veoWSEe4AiV2DF30DR4tN2PXViysGadPtVGJSKqbzQ9W+NfJKx3Uf1hczAjQLE5sLGdT3WbrOGsSsT3xqXeagsSiSin1YLbeUBMQ"
    "MNd09XAB5xGv9sp88MpEC+cSHziSWBOSEtfajkRIgxuJ9fDrN330rUBE1g64QhVlV+ogGdxXLmn1q5BJiXD06u40pz5u6H4RejFS"
    "XpycCshBSC8wZPTMq4GT7D4Y9psNWCp7C/ZlMMpoZAxbrmamY7kxA+ozi2Jlnu+Ch2OuIyoztkbQURr/jaAYSFykJ2Jo5yJmJA6l"
    "R8AvIakRwkCczHWWvbkgN+Q1rVefQzg/VZoS05N4eKlTwMB31zZ/MHoXFSkyrGm07fsaO1ihY21NtA6tpd1jsWiy93GWF1uUIOFB"
    "RHwkuf3zmfD0xD1zZgN7XTmToCGGtQ+i810MxzRJcHiyvhDVIIZPewE0PFhcYVwr82wV7IyJkx7XYwOPQVIVYaVMc2NlmDy4Mhhj"
    "TvEwtk5tgxPMdt/ChZv73Eg/gRR4zILhutjGEwN0EwiyuaCfdpZVpWI6n7ZOZmMSlT2V60HdwnFM3qINM1Zz2VPIZCz3sJyoy1Wp"
    "hPGKHd1RlqY4+CxhEUGrX1W5A0ep7R3eHKudDMUONe16I7XFAodbSMwWjozPtZ5gUiMxzkv1NHkyCNefMr+bD0iKd2JWG1f0lrK/"
    "C/Zjq28bjJcmBd3FqNptYb4Jck5WVg96TUrB80ShkrNBt4Xj7iwSN8bOoiwWmi9XzGfl3jzCMo9+Sna7bs8+izoOrOb2E9kjlvo4"
    "LdozRWQf1jTUTte6mBhBZKTiggBuu57JmoGtwRCxi1lTMeUIFQk/HM6iRTODhHiaQOOuv9FYF2b487JtEyPHrzoBuUktKYORudwb"
    "4gRg9nc4Asph4RlfRQ6bnMf6RyWeSZNjOOUY+UPuQvJVlANhv7Zd1bo4Ih3OX+Jqd1oDYcCDJBAX18lQfrFT5RjGQp/HvmC8o9g1"
    "c59aaUsScdF9IptYv8aalhJm88isw90PkKExJldQukj1LG7oUXLo0ZcR91tN3m0FU19ir/zbmiDLz4O88Ldq+xOwBWu/ugCk1XMB"
    "kpCvghIyLNvNSkijOwPK1wfRXhw1//bKusdPAGwCRQRtagvJdk6SSzru0j4YF7nilaOdXZVhHbOKPGiK7Uu8xzB8i325psyF35CT"
    "+++04+dze9gxC8eSijMJOKzpr1WSwAq02gnV61rC199umGz71ZX1LN4LnK86BtmLADeui3qPBdyWY2XlCFiwlZDC18+PBEAumdn+"
    "/Q2i/Gf7aJCRKUs/m828OJDM1oW5E5zz62jmkcFslYQcBfzmJZ4sgRYpTSX2qkGPE5JpQ5xPNYPehvvUEZmjNAUtLDJipfEmQxIh"
    "Knk9qU9jGCCbgbiwnwgHbYV+2+Paw/KUifeP8rjCuqkCQhuVYw0akaFDLfRRxJ2xc6juWegBYXTGbXwNLkpfu9MQ4wWGISx5+bvl"
    "KzD6BFK/de41nl+2omIPhZ8UptB9qjwA+RYAlpzlX7ty0O+VckTKykhYqRz7xIylhg8+VgZ82taH9wWo9CdU5uPUu7CfWrywU1R6"
    "T6USNrIGC/JIzYJnXl1kqoUMnsAhxiLoR5JTGExbK9dTRMs3naED/mYVAdDqlFkuLKgM6DKhYIC+jgWabVSUcTRqph2scQXoZEPy"
    "OQqWjBbMaL3vvDlRA3N+Vi+Up+6lA0aDbRQyb58AWEg2wQbQF06d1td+nyFaOG7sFqIv509Bsx8T/fvf0gGNCQ7ySsWa7LFgmXgK"
    "pIyUNATDcqCSTtsa5AOs4qEJSNoCPDkwdreK1sJKNfF7ZOhrlrVhznEXTwXGVwJm/KwcFqvt1+BH8E5H6b06kbcVaHXYNlbM4UrT"
    "glrNT1ATRqKwumNPNh9miqkJNo7olSiVg8dgccQsMD7kD75b4FGLci3M/OzPHukLSS2/VSJuttJwAEMqTaRlQsfc6tvJaKkQTDRg"
    "b/+u8FXnGMk1vfYtQi8h0HBWIIUp09QwkyC1S35EzaretcC3HS6jsh5uKdNhc2I0KuwLhLbkfGYSf2EWs/TkQRk8r5TYwQ3fpdgp"
    "pkPRdhmmmHjCEpEg9nWUaeoxnkrW5DXCfJKASY/47dgM8ApQjOjFP9uiT9egcpjQsbWwh1CKd0M0oLokKtEUsu2ckhh5Qb4b94SM"
    "2FhvXjvNKI8/mPWgWQ4lkXpP7dOdEPmm3zhm4F/iM+rl8r/V6DHBWkaW2PIMQyQG9ZGZ1Wvu6T85At0APlMwyhCEclTES1J8cp4a"
    "o2BJ/fINc12/+sewZJtU6fJ8A6i0SfC2rXIW89xxogsMXQY0qPRnZFzBfmxJguwe7bKZy9zZ41tZjVOJskDeEgHGrZiXxNaqTyv/"
    "ePyf7f1MuMPeKkN2/MvZrNv93Ad6O110GBKLRctBaoEAsNPass9hzTRZVOg70D0HKQPA0VU5f5VV+WdmKookIZs9UcUpQpyj7zgO"
    "WMiBVeMbbaNrjMbMFHrgaLPP2stOF2L2QErUqVbqa2+00ESY72BTsxuMTsxiOvzq8+cTifXYlKHaVaW16nfMo4/YK4Gq0q7MKoEI"
    "WSbCnnrcXGQVoh6uMXYCShgroQ33kXJjFAWLPpUYAE8xf0D6bHe/0stP3V9vKPnyaEs8wmt9qsPDTvypco/mGB56Yznf4LS51+6m"
    "1fC+7x7Vt4QZgyiDNL2zTgvkgfGKMjDYlr92JkgA5rnrdHpk0xHytHetL4/SuTSc30xUog/P//FRq8qI7HjZuxzqSEVxE1tu0n6Z"
    "SeRaLV5F86sAbCw6hznNgUYoRuOrJwJuX5brCUY4UjQ+QY7gSPUMKguQxXEOhEDKunDscRF8KeRuQ4QEvqPE0Cb7dVjxlHWZuhJm"
    "Mlvr5BwaTUa0cOUfQl/i3Q0McwmXvT6c8PKsk2N7edjBrUrUR8L1qQnS795YcRFiIWLdPaA+jI5pGT7WOUOtUKAQBH9oLyTqzkL6"
    "mYKp/sbqXjFGzC9gsTKan59nK4KB29haPnb94NYrjq5h+tbwVY1ieMbk9oFk0mDfOHHKnzyx5XC2qf2I0R26x2qyFO8v76RdsWsu"
    "P2BscpG5HmV5RWmTuo9szD2nGLCrjm/ixGPPBcFczNg3ENXdakKEasZbKTN0RVfJJWNQorglIXWfVjqjeXtqt4OSchs5HQudk1D7"
    "Ccf+uIoHHoqzky+zqXDl8BjftVRLlFhID0ok5h3jvizLCB3ot+nHknf0LLtfNY0Ow55ntTmOdoEqu7sENgs7qtqQruoFdaNOG2iM"
    "FNQ3/ygvAdklW2+02D0cbDGkJ2JCGtVr2wVTdTOTPy+lO5iRX5SwXNUnYjD4i3P1WzWEfeSybVRdWkYf9u/d7rlIf79kfBaXkA47"
    "xYVVJ2I48et1xqalynTp84Vi9PycIRb4D6PF8A5ZTQVY1U96gVU1rH6P/RrhQtg+GgMP+q8pLqU/7190Ygr+HCqPwew/3c2yGqBz"
    "RrHMY/mNSEvIQOOJrimPCg50ghrSnOkRxrhuOAZOLT/rrNgwZn0Wx1np5jEDxvVjnQjBRIRxLUYrDbLMvTctoAHLy/nJyRRsz9n+"
    "jYR5EoNdnfLg8L9Db5WOFHU4HjF8DjEmFlaMfcUo83dWQcunWKruF3H+1gmJrUHg8or+NXeQLKFD0EWpki94ttm0+Uuv4bp47XxH"
    "x9zfdTS/MWxBXRkEVxU0w0MIuIk53kaixyVb+K7fS6CkT/saO9boW/y1j6Ufm3fG+r97ncgtgv1vA/bsZ+Yq2ot9NXwSk29OYjtr"
    "lQHdsgSkBo72bhorkyrGWEcmkoBFN7Q/jMqUT8U4wtm/DnAcKJzLZmBM74pvx01YKP+lQlvr+vPsLTolimL157rBIO5wp6Pqv98U"
    "CzBNIbLY0oyt5yzBYOkG4U4oykRW4R5PvX8HCy4Xp8SVvnFiJfOnDzBBSin2qkw1un1k066pT8WUwlPwVGcJSE6Jg94C65MVzw1T"
    "yNtiGAIJVUtifB5UCYKTqSG1mmE5ZdrgNwCATQ7XdyuHTYYqp+fQhrG158IcD4uXoRsBoz0KKc/qvblAveCmYwTk4dvqRQ+bFkiw"
    "b170Lw65NY622ssZoncMRZB4A2w5uvbi9kjv+q+vYWqN7dNUDjHhq6scYQndn8muFHGKiom1yjauypJPVrHks7K9TzZonKtNyubJ"
    "fgdOIZRdKj72QwcxCt7YrtkZVWkQGP2W2VmaoUSlgOQ5Hv51mXAWjATy2cWR8sab3Nv3ZQv6YJSxPL+9kiTYtaR9BN8j4Yuuf0ou"
    "TqYUNQTAIU/P1PNOaeXmrNmGtQxbtxnYLBPOCF6raBPL0/QmryZ9s8wbvyOmg8cefR2IZS0tFOI6tVCZ8o7jZXIWraliDV49Ms3V"
    "ZIbm+HbhU/wwPUY/AoLKM/fxCQt5Xso/Be9XjhONTTcskWjMelVojO+4+e2PMZ7qBB97ytwmr/A947xss2wslyIhtGRHaDqW5dj4"
    "vtseAxElTsVbrtgO3+2GElQ+li/L3bLXEBRsNeb4R7/cw3dvYD/jFExKexEDBpUwlU7GAAjirzALwvSyygZQT+CQ0Qv075gYxzFU"
    "4jmHN+cHpw7GiQvLTRizT8/uMG29CQDotHTasrYyHZ6/dr0oK9XeHnr0wySaTwArm5IGtAdeWRYXhLM5h2RtC4KLKolfoZgNWF3b"
    "axbg29Cn18mIaBC62YJpe13te8D3D0KdNfzLOM+AS+LGQj/T8JmdMRKqHqHNvExAvFJG/3AjsAf9D6fSiuh9jPxdwfFdeand2e2t"
    "tTHrGcl6IeEdX3GakBFK6cxELJK1iLNqTDGKg2EHakN8KTVGuI3l05SMKJPew2IqgTdBW0GcooBCdqkS81iem250UtopVQFMmwUo"
    "eBuBQGe4M/m3U3cjjMV6UAkA8NGPUssbpdSp4HiUJGEyG3/RFcsXU+F3dWOnqmQwZVwDvzsjhjZ2FvNeGvcL+mJHx/5uwSjtI2Pq"
    "TNY0MuTL3k87wU8Ze4fMgJXGfC8abQ0u5qtzZ4mb4SusOTPQO8gIUNB82FifYW5l/WmpimLVdOpyjOXnb2JuxJYzDj0BagGDHwJF"
    "konaWHLrhdi+tIkauLQ/bOp9DDprLddt2osSJ9AKhnuerh921EblKJ+rD4S0f5Xd3U4OAM6sYAtjox335KRs4s2e8W/PNN/syLnZ"
    "dC1oFfzOaIST8QSFc3tx9uUh6WmnW7I5Z74gGt1/oVQzH5eSFka6N/u5vjbOwtXf2tad3ZCaCuiZrCdZy3ahbnWcYts1ybxSnn68"
    "2uBXm0veJIo/yZeNE5bjNcw62ZKXpK7QgLFIWCbipBhlw41hiR8wc+1dvH4r4jubTUad+l+oAFUPSkiDMnpOJN4UchVdFmZk3MLO"
    "9tYDbta65VzJ8xLOhbD750TyB24xcnbIXB5w6tgNddQ+x/S1RJFlKc4Rh4bnXBuTO9awzsxSUtuvie7wyVNx1vbCiRO+eoTZuehT"
    "hZLyO9v1Nnk82Fjx6DFlZxTWBMcMYjZ6XNkLKP/2bpCCcYuK4Et5iwHGml1B3QsbulvCSceszkeSex+cAsoR/YBiOoM8z610qxQO"
    "01TUk/tBVNrcxDxcLXC7ZtN55Ka5CBaVdRpJVwTDtk6BKYjhbCM7eq3X1fmZXxuCXAU1FBaGWrW741gaRJ0YxbZ8JVau57pskynt"
    "BgIfdC1dRA7R5+HYpXC+sh3GnxkEoqxmpOO0ok0ZsdhlpExgA7I5Q67ygk5nW9JwB3c0nKKGtGaQ/W78hgeifVeEvXqn77hiSMU0"
    "c3R8UK5+ixR85BiMLdUHLWlm/N5t2YoXt8Cujxq2vpieF9O+gMk1OqW6cyiBU3E53D5j+Ho8yZ1Y8wVNlDkyJBIc1JsJ5pOdDfG3"
    "G68pMkwFbn8xx4qXawjeFuYx0kXW4uBDWppocs1lkxEhc/yLP0mFPUVijDY8A4D3yJQ8jkuyFPRthA63Sm++Hg2IwwwxUbhxHk9j"
    "6BKgu5j4FUg7NoOP1LoVvJID1J4Xx0qX6B6KogmqsXOQckweiRMdbZX1D/HWbV0YmCiGD/O0JBdmYPXawSnBLNW4HMPCkY3tyC4m"
    "1wwwN8Y7IZNTbqtAuSeZDYBY/ILXYiDo/S5n+wRFMjwbRQX5qxoLo/dmt4+b+apskB7zYOMWJjIy09U5kA14B+XMILMFoG15pph1"
    "jSJX88TaLiQWTUymnWQ/xjbKFYn3MG8V48ydeD03ZdJ1+6uHdCuEb9OsaK9Z/oypkn6vr8ZLwAm5sNx7BeJo6Q2FskWs6rD1PLKj"
    "0fUAQwx3EWc5fGlKi9FHShNajLwrdxQuctLAlCAje8lQhNW0Snue9TI7UBn9QDDzDMZaNAH1sSADyLq4snsuHIIDlJ6twBE4Jvur"
    "DzNdonEKMczokTUOYiEJh9TPd5A7R6H4nqJ/kPtQ/CJJVULSHUywskZoph8STQye03dUartZu6QIpOITvOZoVHo8pZ5VsnFb0bOH"
    "GwS/GAqcRrb4IAR1DWDZrVhjcWE7onO6np+DjctRvOzkCZP/3TdgYgq4hmAX4eU5ldNMHMbSTX7LeJv1OI76wPskyb9ulVl5TNnP"
    "ByqOSK6sex1BErNeQrxoWU7tNOFDJvbEwmKDIMHtAVUtIR1Nf+TSXVHihnASOqoix40dVklyF3Jhxzi2XZuOiCIlti0wtgX2tOSL"
    "MJ+AfMi/mqamw1o2ADljfcVIBJVNLOC+zNccP8orNU9i1IIhP/rWDAWieE67mdjpMFxmlJrAmYyPifqZGjSpcQQEzLl0Y0+/aGEh"
    "Hjcw1OReNofIkoX8ceJSfOq/85wY7LQM3vcloZvmR/PpoiinbBgAkJcLrmV5//X6GJKYNaiz45RcKneeg0dFNohaq6YMhXrbGGGu"
    "Oy6rwZ1oqBwaDXTaYnmtgobNKSXCLNZMjqyDIyobC7Wj9rFApSDJ5VQOx+F1heFm5W2rh7WyMEl053UdzwORAfIBu5m3DSvzKoXz"
    "ugVtghc9TQmr5vB6bMu+QAZ2eDh+PsozghbEnZsbbXilfHxO1CDzHGHV92Hj6Vvt+ITgDn0wsBYFUK/LAdMMGdOt0sbGIBB4bGe8"
    "in2YuPWsEx25+A0cjMBIFycz+NeiSi+jOhToHZaDVP4gQVmk7Q+1PoLc4qRVVhQ+2LDKYxrrp3OMrWM/rOa1Hue48tWvSd2Y0y1s"
    "Y+xAjjqxJpY9KzdBkmhEGinz+gC2DU8p3lNAjuuHUUfDUAZEqcMoZNn71xTkS1o+3NY90w7S22oNtnjD9VG8ATCv2ZKbHKVjCtj7"
    "OmC+EiwoP9TGWG/2vLntwpGU7L8V/g3HH21doHJg29viqiyOfPEw7AvtWl32/vIr7OQzfuVGfXnG4INz6moj44YzqkhHoBzJ/fH+"
    "HeUsq6Y6k8awR90s/NVTEOAxq5uO+8lk+dNDAH6mWlnFjKprF5jBS/wWHH8a1dq5gi6LLKP97ZDDzZbzxklRHsngEHXrhfozmaXf"
    "Ewk1HYl3AJ+QawEkewM/wHOn0Ol8QwKmxtvrp/Vixt2c6IXkaqsqrkx8KDGAtwe+lZnGqP3oWrYPrQDsE6yxR7CJY8gwb2pc3GDX"
    "7q9n6n46/cA3ageBnF2OwwmcNpl8laFR56BuqqPk+8BPV0HfFGJI/xJ+5I8CIZrZwMS2eD6Zscr0vhjYW8zMTr36JRKpLwY4AUeb"
    "bDPi1dh401Q2Y7mYFarfCWizMeZXrYPwiPtqTefgStspwaxqGu8jBWJz7VL1QTn5xJVGjwdztt8JhFLn8lErtdE5V9EnbXKu0SPa"
    "KRHVxAJ1jDKHiuxFf/3mVlClAQUGLXoO6s63Ve8FN6/AGLX742rbjGuGdpJJM+HkGdtAp3CZNDW8c3iKdLdVHZ8pFWETAcxPyOYw"
    "Y4JqlOrDhcyQ1En57Xa3u/pdn7eYT4LYTeJpXgx+OkQxpKjCU8tH925afp/flXp58VnN9lNv4VRV8aT/HVmBsFtDyVp7TpdwHWHN"
    "ILejXbed1YvLzITAW682WjCG9e7kFvw4jRqqe5LGwaan0MxR5OUC/LCvthyfDChveS8i0Qe0n2J+v5KmagPHqWjFJWzIqzrjFTSV"
    "6sMp/94gCJjMF20bHICIKrxb0bJmovSa8gn2fkLHzk2k/cTDB21DqVD4AKbY2GGqOs9sDTCBQiGOz9cALPXgdfh9kqLSg4HblZ/a"
    "1Q7jKqEgNy4efq4lY28Se3PFsH2cR2a7qJFlLLB3A8dzN+m/tj45gyDJGQJWCtPcTAUdXBNe7o1bjl8wOwlqvlLhHChfDQp8ROcp"
    "8sGovEjafiCewPvXVppr4Nhrk/tdDKx+z/sBbTLkx6ES7y0ah+1s5dXF2Jd9KQrSPNaf5pXLWsaJzME4zi1rVc8kyZCQx4CQ0mBu"
    "/HzrBcvBtkkUIeJzKhh0Gt5XBEETWNOzbAwmcd7kRqMoI6OcLytCKvcoSKpuA2IcY1tJaMfGRawZXKLTI295g2xJUcyIs5VwXxBw"
    "sN9bI3VSfkk13ClQI9x97y03AkrQeBzHDYT7zTch/xS7MUgSh7N8zQfvz2TNIQOfbdhu8AzEpTvBtS8kAYwk1s3lC0kg/Ih9osaB"
    "PhwONnGEgimLmntx2L2JKlKaVmh0peXP56EiwaoN3TOg5DhwmU3Dbxm21DR94p//GU89O67l0GErP6WM/XKQLoTBsy3hcheLchuc"
    "BqsmTwdQzXhmxpfomf8e8TP88gPPTr+n3ahAeNc79z6AmrTDskHfF9WNpZxhvq8yQeP2uGBUD0U69nPh+NUS9lBsODpwZ9ug0J8q"
    "gZh6uTMJFl/cuL/hZ3KqPjj0+JlOmYUHiZ5wGvJxIGk/ITMyUqosbbfqlz/6JgPT+6/WEUKMQFCq0yT/RQcHKn38+6gmY6PRsy+L"
    "nkv534kkzebq3M0gmqJTVe+oLPAiAUOsn2VSK3a4gSl6I2U++KWMMA3El4P9VVP/1/3QFn8Q6eNvr1XwjkkabetGUoNk+kZebeUm"
    "jLNs0y9TIyiMysM57k1aZOcUTpPACSyg8CSLwNvr1nNeIrxb04rnO4gHj6Hljy9xhRg+cbGQUO9XrzlB0oIqOJe6B1pMiQWY0YL9"
    "i0/I4RvS4iBTwPAmRQcHGVTTs4KWNsldXf2oBTiyHIOptDY/a7Bsfy8DO4ntp/l3rbxZjVgD4vmRRCk7Gb3a/0oXnNP3z19OJhY7"
    "qfLK0Sfeun57kMj6hjLFkOttMtD9ayiJoZNhM6XUjuAynrv5z3OQd3MnexZ8NMb0aLNNmiqTplK2x2OkSrN0vDUPVC6f5vSzktRk"
    "JgEVim82is8SKi0PsPkEhakvv5sj4JOw+VVXECt9OZK+zt/8ISUCL30Anqv/JnJNQHKPJiIXg/iDfmbJ1L7KAXNHswT3kn5eLzma"
    "buM2noWA/BFiHhSx47yfN7MXihgsHMLCrw19iyByeRHbXOP16+szPZGFyCOIsl4cfV8YXXnGjlVvBZsUCj3KJumswxv1LV1Q97GD"
    "nGzwGgRoPQQX3ISZ64Yr0ijoWMHfsw44IjoHymnM/bspag26PtcxlRo6iYldnnvC3omjSSorlH7QWwWGbyyfI6rXBxr83TSmP2w4"
    "OSWPDrffrs9CY/uvVFccYtcd49NMn7gFXeW1ZufIK0m2mxpM6wYyIIy9ve8DgsJAGsv6+CTpxSBPc+EHIAE8mct0qSapAaMiELp2"
    "daJmn6y8Z9OmMvfQ0HjkQlsf8gcRMX39EOqqir9jfXd57Bto8JxZmrqKx1Fm8R1rXBHsZ4jSdErBSxBuD240YDjTIlaadsGWyzK8"
    "rX6FVZ4aPtYhvj5BIHU1tSmDSDSSSlBbdYPngYGSd9iUH725KcDsExxkkvHHZLrR7V+23kxzsf59Vu1/tfNG2ef/23kjmn87byjJ"
    "MylBqBqhVmeOv9g31QnTE+b4u07vBSuNrS9Vbo2ehTVKVX0ESCtKrls+wuKizsQ4HBd8nGMeOgjNSRTcSe3r7PORq4X/S5F0P4rS"
    "IF8mftr+mQFoMMZZWsWGvD7Z/kN+bYrYbTKYI3J2S/W1+EMb+vn7+WWjqn2Gv709xjuAp7hW+PsLl1BTv/pg1lhxKB2/RBysrb3P"
    "YfD4YRYZH5LBHbRedxSRiT5yEYZ8RSIf37iNXvO7OmIDZvR6rR8DWveUOtDw/DN3UF7W29pJPMR8FhD8Lqy+JjO9fu+fXciCuY2q"
    "d2zBnGvuWDKdOUnFZXxaDdLwwsgDs22d79Bxa/J9BGqCa4MsnoZUz0zY2Ux8zA/S7/XxqHbquLgBIEpptkrKMhhnp3wewSf4IyWU"
    "6mbNI6BcsNPYOmpY4yml0fwX6T57rDlwGl6/JTQBc2jTS7EL4vcJrbbC63v2oAyXXajYDPujxCrDhqtZBxcZAgSqyAX4VqP9q38l"
    "BpSxzJ2LdV7TXS8icOhjdECTQEm/D9jNd4OwVC62MI2s7tWS3BKpzsqw8Y7mHJJE9rHGVHGBS2GNllp1Jjf5nzZVZ6KAmfEgkzld"
    "3r7G1L2e7uxNj434bWFnof4utThCmZYBvcHQ44dGhRDvhjfxn/Y7TARMcBELxnVyF2N8Cfb5I4MEehvSYZD0hwG+R6BRyj/Xg4ZZ"
    "KQ4XnAmjCi+QztQrUQXNz8UFKjai83XzXJgZOd2AIzwWTECB69QtxlZ9IWx7lB6/u+2DRpum4POwcd3/7UQ0pCPEfssPWR1iB63R"
    "dqB2Qp0iye5Y0AsiD9v4gGk8s9GFDnC93y6AF0O1ZyeGlO/y15LR8QPpEEAVQtRXAzbYTLZ+fkiZZQFfmBox8BKIzrdjNxuRI0gF"
    "gT2yr1l01Txp50mvP+uLldHheGAhHc+ovL5+9WzFhCSZ5K9yHnFJuvNgg1bh7XWlRiOKX4HVoijSypTz1krM9AuZ2PxIxYX3hYDM"
    "AHZebZVxxvZcp90F85Pude7r2yjBZLyIoH/waCe+PGiTyJiCscP7z/g6MaJxECK54nSHj42exvayHbvx0pODPwAc0dIxPAE36iEa"
    "i+VjkeKBtCUO0gL1pYyLbRhnEk+jeMS1gH6rRjwdiD2iUwDKUGstQsPfqd8wo8J7ZWLMZEfGtYFpysq3nPxC9aBVu8WPOoEjBw3O"
    "GJUOjt3oXcAprLpbBbqtLJZb7MlwztPHMKCD1WrQDi7vx2O7uxNnfU+lmilBRL4/Tq20yrebR61e91RDI/hL5hc9napwCxpXpQw1"
    "QXYJPn0LTtOwDB3PjlBL8gl0Z5AjSo50cv5801uXfAeunWG8UTrjjQzrjL6UiJh5tsM3UBaVWkWMbETrZ36w3RPvIokONUjLMcqm"
    "13N+zjGW/CnGB8aEso3AD0qCHwYKqBHH741/XgQziMBvxu6tSVkbVbdVKfI7hc3Q/azVvcv+akOdFKWAGXhotzpaNNagMrgqFt55"
    "azdAT3YPNciwpPYB93KBEe5kC9sBDje03xyqiT/dvOrtS1PDLxzz+Pf9JpEVNhUX2xIK9BMHPhiq3UYjJNr3jpE+acubBFAEz7eI"
    "gjyFsecTAem1VlCQnKR2KDEnAlDHjvS8KYfNZSzAHtyZpo+nt5rmC7hAHUBl6dIbsqLOhyl5iZLl5dTYVOOhY9EFqs1fg4EVF1gY"
    "0G6QFPqSvwHx7h9NpDDnzJbfYbSJ8wu33d9e5/FWS3jpoxD13XXbqa+YETakXxSWDzv0JrvN9zkVDQ6VLOAwR2uFsmXHmidMNqC3"
    "r8J5oGwrZCKA0MTui9ZI7llXEJXb3Arrd2LSo55mo3TPU6AF67UAWiVRIgRawINVxXSwCHINqjLLxIk9cH3o2AH0Nl0M2DnNVyAV"
    "Q7B0d3s90pXbq8GmM6XGzZ2h2qn7+EDJWMz+MkLfXQ8Bgg8SbaXPdm7JldBAeV2iVavUL61ARmgaoMfhW4FsuTfB7D7fFIIb+F6/"
    "AMAMFfYIcTx/rQYgKqDOXZ0p+ecNuq/R4l0SdmYZCoHmvX/FlH69wWWAqI3QEjJ/LZuMfdt9Mfgi6vGDm8kC8Do6Knd03uNe9K6j"
    "YhopwG40b10S5iJ/h927M7/aK8lnV45gnNc/yRfdXm8ayU8EmS13baolGS7knj/dpxTp3WQlFsLzWXkbiWhJ69qm70+x+FW7s/2h"
    "nDQZbltayR9MUFj3iV5PYAOWCNt2FOnsUbGrCRcSllx3MjpNyW69fsMSadczcqS53utjLB0K7mg59u1rMFqgwhIhjeGW63N2+xep"
    "BbaIHPvSlzVID8IzWu4yP5B/P7qEbIs6POkT3tiXssPkh9lhKkNqpORMkYZo+lu0a4K+zi8NPr1Yu5+DT9gT5L8ZQeGF2sos3zul"
    "IwPxNQtELVJ34jhctQISSxTNV3RfL2t+YZrJSKONOcgrvb0A6ZooltyW5ApMaGXPXGllerwJwEHO6Px8Jf5Wlnw9y3kZna+NBOHy"
    "cZKpJWsuRZnNAWSKjoDf21JQAjQPuPddIr2hVLp8pE2WDhVmetGEyvuFrUMrxzF2qjymZyjnCk/5pkCMBHi/vnsUKvmp4f7pAV5p"
    "MH0NvD5aGXASIACOwtVdhuiZTKbMj5XfZPa7oZh+ZcHIHX0CEfdMn1Fyvk73hqQD7AzwNihjLU0y338CSWIkr643RcvBnkygowQO"
    "ZqxwZe9iz65VPoBuNXdTf4K7e1V7MBc7qFx/nMaVc1opB5e9lc2c36xVavpttMuIOeuRoyf9aTrYyou8yuwVV20ht1KYsAlmKaZq"
    "aoxNqHucCQCI0Yc9eRUouV0isl3ix3u0Qlainw9Mqtvr1cWaQWm40eA6E1YrP0DKmEyMaKbL4NOVf3V2lEH6auAsl6GhNTaf+/Ev"
    "syagrPm+XS92hsSPZmw2C8nO89mhLDeQu5WFMV6KXV9Du7GfEhTLGeSrmfl10Km18S8TF7w0/07VemBmi9LBSn8EwZC/hmU5RIy7"
    "YlLASRUpwRzAwfWtUdrxl4xj5O8TP+wXaH2ciujiKF0QmQPyCL+fIYoWari2VLICBdGiK6A83B785luKC+oY3TnyFzyuZAbUUJae"
    "Unq37KOBKw8GHmfFudRGt7yP0Y/T4JpjAFvUbAa7iwsviNH+eQvhnjsFHEDXTmx7X2bjM0u7kPtu1SQKMVGZ3fVJlTNwgYCG3XPk"
    "MmJoTLz10EdRHOYZVTakGgZTZofFN8JneQjeoqxMYBmzCeCl3b1VRl4VmjvXmYWAkiSXSUIdp+1nI3sZXH2o9yE8fVvZ1PsvpSmH"
    "wVHD+lCbZbnNfEf5WB1GsdI52JJ0zkUt5QuuuZI4JBDiyHzz5EA+FlP9XpNOiRz4jgQbe2tc6bcOoj1o2R1NR1cpg5UIKV8zpBy8"
    "d1GLu37uXUEyfe3zLffXUvSGcBfGfLxw8Xuf52Go/XPfWYvM0DGyfSiTkau+sycwZQDFjHRShzIs+pL3I0XKFFAvHxa33oXUQzLZ"
    "e+yW3MLngKxxpOs7k7BmMXVquRiV+T1C5opalLR6WWQLYpz8paishqWBCDK+YzJGwmAopSjhfZjYWrgTS6I5JjIPSJ935mLuCTxj"
    "B/iaZ9Jukhi0YAlfsbIfu26piOXbGxoJP1nC3bMh8zqtRvU2dJCdQGBk59opMQ9eTXn1MP5a851KBEPA+e64txMScm0qtg1eym9N"
    "Q9r8nkrhD5/jce6NBJsJpOaLfEPgfB4sxeGSzlWEYl9Cy7xEAL3a5dI2aslUoCs5GaI5lCPteWNlS9cnkeas98aC7Imcv3eVNZFd"
    "8yNYYZMY+tysDS8cNqfyEXRb5hLgELovs/lVxyb7cH2YImvFtBO0iZMQ0mbM6XJ5ZSV2L5gvzKkGfmxjUEfoibvfLBCVXRoxk+ko"
    "o3rniwIv51SyDLjbX1686cTh9wlyfU5npDaf0vzbFKV3VYHULZdI0NmmRjv+QqVoRcaXBDkQ8QbAtuQZSurhwTEpDWQPovVpAoay"
    "0eiSc8z6dC6h2leXYz36Q17W8oHy2za5TzCRYgCT5e9nD0mfHIwQPmksOalZenxbpRa8ZVL5aJ8xQQQ2EUwCTEkyrSO8C8ZgdOGF"
    "/LYDxL6pXUxdGEG/hD4S9eUG6bYA4pZajxlAzCZLTjCDBXj4kgTS0u5zttwizWYfKJFnNACMOU1jQ3pTx5fZ729uhPv44Np+c9MF"
    "WFd1CcqPQzC0XKKvR71S+yb2eSkpyQWPetBp6B0wZ30MSOYdh5SJXsm2NvqdiCk92ReY9BNsUQHc0Yz2LVMCqfK7q3lhA9jnyo5o"
    "cX4RCo1yLT92PfmCwwBytCRv3sU+RELbrMjPfK6tgtU46V6O1sfHEZInTouvhva3d9B0EggVCwr7fT5VjONLvlx2+0nRulHsmjk+"
    "hze04Vw83/KH2rBCPGuJMWpCjTdl/22SttEhAS0Bo4YxEYZwY+h5z5bE5VJ/lQoICT6S+w6cNVpd/AaM4Gg/xM4jyv+s7RkkbLPY"
    "LUWBUaeHvZnNjk29OEWsuavtpbkbfrNFa5R1U6aDCoXwvAIFDKz9HdgaMCf8S7UwCuhposf8giP9PO+tQ1CpqdIEfIa2lVe4RbTQ"
    "Dz3+yZv+W8oArhVDTKwfELXiKNudzHz9v+9SDv4VAkPx+c4YTGXb0YK4cERDRt2Qo0FZeLnLXvJ6DsBV37tStJwnPnF3ZqlcdXiO"
    "eiOw/AgHNiCA9/DaWKYgZD/IKsImRZC2vdYbzUU8cPYfzBIqFKL8ygLS/MeE6BdjyetQISCfBwAlKeW1bHqok3dFc967GanKs1vI"
    "XNoZ6BiITO/9PbVPJH9yZsO9sZxXZOqb+ocl5/eELnMBsZ7NM7vNLhBHFiOxApkbi5lpXEtV+kKd0mswEIk1Vk2fjkwktxflqNQe"
    "xtY3VFLOEyoWkw6DkdhWMQJ3i/TZGWVyundbpkpnFajwZJm/Y7oM192FNiaEkV+Irty0Eqk1lvy4r11+Flk6xRKFaA8IOpUTtJpR"
    "IGvXf/XLsLQuUtQozu4X2mdJ6FGT+lE23clJpDKJzAr8Y/7QQOsDwuVspq7ZhB9QMpuNiaCmsryICkXJkoNsRlJrp9LjM9zMh9Gr"
    "H3mKJlLwX53n4MO7R0qG0CvYkqOOevpwuNJlfGqReBDqjsOuuF5fWd2jX1EUDp3V6YpjoHrLwh+x32qL53B5muLXYBSQF2gw8meI"
    "kJwxC/GKBHf1G62i0KUy0+GK6zsm2qNf3uUdYh96QanNn/WzLD0qNH24buwQYnQzikZ7+uDAMfIp4Y4dPWIDD3kExolyrYkTFBWA"
    "oWJm2AnOPhPjcVnVoidJE2a9QjArRbknCtPX1gIpr0EOkYStSpgxDAkW40KtrkzAnJnCWzR6h3Bf7LFMsaTtm25f++CclEUeX6EA"
    "VeWXa3ut9m7kqILaYXUOifz1V5B+kc1nGS78YbE51yTwar3bBg1FzAiYad3JCNTkiBuErMmiMOyiAxDXlvgZnuQl/vz+Vx00aAUH"
    "9stoUriK4E4d/hHq8aFHdu1r9ZXyBS52aI+Po3tTtx4KoIfZSsVRIRojxfu9vXNy9Ge4fudMr7Y2FQxVrwVEEAb3a+4LlBNmpCZI"
    "vaQUprn8E+u/u/yHuDftbuO6EkX/CljPTw1cFDGPVENcmAiAmAGCAMnwOQWgABRQqAKqCiPFtUQqdmRbbjuO227H7jhOHEuOO3K6"
    "Mzm2E6/1fkpoStan/IW7z6kBVSBIUUnuunFEAKfOuM+ez96nvOnE2O2Z+KyV/n58kNxK+fzJWS+6PQSbhS7X/aLLAWqjn47VpeRQ"
    "auacPSkcnRSLEY9EMz3vqLUz5aPNiTgO0DuF7XHV26SSxa4HvXRR2JrnJpPwrrfERBKeZHR3d1zzNocZuhfvVrfCvu2tXL9dc45H"
    "uwna37LujFujji++L21V0uOwIznZjkXsvlStZm3nulX/xBUoeBnfjjtC1aSR37tXdUrTcKG9ny9GZlTOF3DV+K1JHswGwAtxPyeG"
    "GxMWhq0Xe5ldl79fCrgyzZJ3XC6GO0xuO7IzizS5QLw+E7rtWdmT8U8c4yTQzMTKNXq5jDBN5/em8/3+PF6QpDZV67WajVq8GKXn"
    "e45d0MPCg2gqvM9uNQvFTHsQdNhTxZg1w4lhPusejrkaYHo8yYYdBbqXyI+sBX423t/pxQeJIMoT9I37uWQdNNOOw+Ngs7Gkq5yY"
    "RIp8whnjJ/1wt7dXaGfYeb4Ya/C5fI5z233MnqdR2NsKope8saniJJ8TeuE0Y53F2pFJtiyNHMP0xJXkY55imYtmfG3frlSdBqhc"
    "ja+g9XTidHhUHJe67Uo1HR/wZWcQ1LK2wwfa80wcRqlEdxbux/LcNgf7upfnqr5GvhNv1wZWJtFhOvvhbKrtymWmfmrkzTB8oTEE"
    "4czW8iDKx2XB1+70U4N4J97yxxy+oLVW48bSVhXWZ092wTbzbvniTc+kGmb3QX6Ft5HKFs7FdqjwVmzHmQr0ex66FnEXt0Yl5yxi"
    "be3kgzth974z4Bp3whVvLDwMtnhm5qxXSjlXzb8dFWthfznbK6U8sViYtVZie02qX9mdUr5g0SexyT7nnYSTEbqQTtmrOW8AzAqn"
    "PwimEJ+K19quXmcaL9Ex92iXLrnDU39j7LBn2GGg6q+GE6lunC+1PWE3F8iHu9VcouCpwopc7dleoVRPRwc9X7M7yMS7oHkPE8lu"
    "Z1BuRewtMNwGuz5rpOrPeHudaqbTHETLbV9AmNG0u9TsTQaFqZXzbrs6e+12OzrypLyz9DhaAphFs4lYopEf87uFaCU4KjTCc9YV"
    "6Yk7abYhbfvZ2ARMK2c62ORnzmYgGpjm2OasOmY7VKMda28lYtlwPBIVJkErVxPcvgrnZSp1h+Dsz7lOKb3d6LW7U9HOskMXxbNl"
    "dHuxuFOsZzzpPdBs2i4pFUe3Wbhpq5+b7XGlXm2az/Pz9ijtbbSKJf+e2EhFAzl/OzCOWvftRcbr9PWiO6UgE4v4S8y0LKQnHSkl"
    "9Ll+NwG82rkVm4nW/YqrCTqyf1zaHbH++sjKhGNtahLpRhwRrhAuUl02DsbccJcZZLp7/e5Wn3cz7NyZCdSpSaefzQnZXjc1z2e2"
    "GLePTWS68X44nk6VvUyPcnSK0aI1uNcZ+ftSpbnX8u57koNcJ7g7nTu7+WI4H04NItEyO2l4k0PR14nR4+okF9vls1Kst7+dFevd"
    "VNXDBpuBlBXs4CBHl10Sy+xM3UG7Q5hkikmpbPVg2dodjFzZZqQFEia8uxeGGm7gjtY9BxseMbvpainbYyM5LuVPZMP5Puii3VHA"
    "LqbsLn/OUWDKHB3PDV3ehFvoZR0NezHV9vl90V4XtMleMFEBm29b9OynS7ntBB0OV7bzddrpBo1jPztL1TqtSnB7J7pfj9hFJuh2"
    "Tx2dSiVeSuTjHN/JVb2TIVsVOu0IvydMwu1IbW8r261ISW5eYjqOtrsRSHfT0S0muF+lh7XtTC+H+JaQpx1FtudmY12m4qaSlDRo"
    "87NCN5lmE+lYobFl96fEGJ1E/hSOSpa4na3u9jCcr3cCu6mdRiLVDlOJnWzYEwm7IkxwXhj0gbjyYSlXqlSFoDXl2d0qZeP5aWkU"
    "dTki6WDfKfTsFS5CBdgyk5qnU/FKLWjt1yPzIBUOz6VAPFMZJLZL0Wa85gfSzvQr/vwknQy62MmeNVJwugKxvKPmT1k7jmI5LEzj"
    "sXbe0U5UC3EmQ/NFACuVLMditVjQ1dltxGvWDMVt77V9lQnfceTbMco5q227ot5SJrVTrbMxO73drLQSiXop0gMreLbNpqRKLMYx"
    "jFd0AeF0pnuzpDCXevN9dzhiTRX4sNVqF0vhiCMXFYT9OB2J91JTV2Tgru85u61BeztW9sWngVbZJ9WEWcG6H6xvJSplR9haqEu1"
    "RIcS8nXeOQlUdxrlcovbz9QS7Dzoq/pGxa1huSvAlGJDe5f3BLjKMBHvUskdbuazuhhJCvc6PXc4PagKleEswnqlbiQA5vqco4KU"
    "tD2Shuwg4mx7HMV4jWqxwyDVdY0ie729iDMb2OlOIrv7XWqL78aGzugU3eyT3y9N/Z3ooF2LTwKNSarEpIsNPtzaq5Wsra1uyeeM"
    "dlOjYSE9T4cHSbcvbucirdGWtZGYNAbh2LQ+9IPImMWpaKDHF5KzQnJnRFWFPd5q73kLDnabae0Eg/PxYHccbpbj1XCJY4YOcVaq"
    "5xu74/Y4NY5EMtR+IMn4Eq1ecZIJz/Jb7fROoLEdme/WCtw8ulfbmjb5Zr6V6JZjVLDQqzoT+UApEKGGLDVot2OTAJjT4TiTKO5l"
    "kmPKOd2PTYMJMepLMX2PxzqbTAttTgrHxrNYoewAtbFe87db7M5Wu0rZR5MmcC//cHff3k21A5HJtr3D1HKJWa9UbsHe7+Y69uKW"
    "3Td1iONiK+6obgV6kea4FRjtVgvRPZd9HCv0Y3vhvXAsz8689SLvyccGUWcgIzDpBAP0NREZLtDAvsJpsuUG05YbjbmduHt3CgyZ"
    "be3n2YijWPT27B1Pr+1JOFh6tp0cduLZTq7kypQbwEh33TmWYzxDvl3d6ol0y5kq9/yJSmBr3xcRBEfcWkpMAqVwoUJJzu3MtFvs"
    "9/i4J7zlDQarYJP56bEj30/sh2dsdtAb1fyDeMFunUWCjZg7EdzOOGJBnqWAeWeqe11nf6eY7qakRCVWzFFFsDD9Pro1Z5rJ0owu"
    "t7dS3H5yxxOIJn3+Oh0chkfBEucSs7P93Z1IA8zAZj1aoaZSPbnVsMfYdCwvpmejcrbZ9kRbW4V0NNxupzwNq1PaEab17UQpQ7XH"
    "+/NyrMQWAxkpMLeW+4VMp5QQ9mbhLJVpCq6ZJ511cFtUf57jMsNqf1Ac7G9ztb1hoh3l07vb4Xa0GmfqnYa9LAj+aTTjGZSKkUDP"
    "Y485i/FYuLEzGRc8/VIq3PLZ02F2Ht7ulLzxPS4253Z86UR3x7UVizqq7h024IvEguN+oxBsO2otb6RUTGw3SuGoJzffLoXDUald"
    "a6O4OOD+oL1UCtXYxBfdj01a0TCfHmzb7XVHoOSc7CQi2US2VgEqzAq9mI+N7E3sqUq+s00Lw7QX5OF+MN3lpvGIJ0dNRnVhEq8W"
    "e3vRois+lQRPKlobFoJAC7FBbCoCbrJZao/vVYX9WbJaY4RyvVZ37hSb81J23t0dOtLFQdKbAg2G2mUnObt/2Axa7cG4VAtb9yPl"
    "YiISyEQ9E5efd1Lb+Qzf2CuJcanrLccr1oS9lZF2nY1UqQlLzCWDeZerbo/68im3Lzadplqcr8lHndkmt9cflLPF8djeKU2G1laR"
    "5iKJfDYiTTlnWODGsfKkYK+JYFcXKoyrkwnMvA1XazDJeIO76XwiO3E0c3ypQUnViNRv01NrdAQKPlMpB4dO2PIJlU5PK/l9ypPr"
    "T+fxuDWedcXqUdA3OY5jvXQu6WdK4c5WwNqiC7Viyuuo02zXOvfUc7lyapSIUc1UeRh1sNEdKpjdrSL6mE2dgWgnIG07U81azG6f"
    "ckk+4bIWGzNHzZcS+3GHfTbg/I54I9G3RkslsBODvvquPVZJD6iYvy6mkiO3mIxlmsVxLWVv7GbbYia8nU1OouGu29dLdewOKxMb"
    "epqBTKOX3PNkkiVPvcQ4dwfl4W4pCgauL7fLUtX+lhRoRVyzIltIx/hhH+zf5n4p6g86kxVXOxMP7gPbHe9tdbPDoiNTcfgDfqk6"
    "5kDpyCV62WGi6AtT3lbeQfmb9kAtxcazQdpO9ZwTKtgFAypfb4/r1k5yzys0miCQh1v5sa+WFIUd6/5WphPrVuY9asA74uVgvlAo"
    "tIq9Pl9hs5PxUOJnze3dXGHejJfa035vu56TmL1hmdtmt9ONYqY5BY3C49tJb5Uc5XRQKE9Ge9Vsfd/a56rBeoBuDQsZF9XLOGPN"
    "ajcdEWihnBqytLsZ9WXtwY6rG53G2a3W2G9170aosSshuSK+FvDI7KgK9Ag2Ddj2yYQdVLwS4xiO9rLNya5L6pY4NzebSQKV4JmI"
    "mMrHewU6Wci6p710J16cVViY35BKj33T3a1pg4t1dkfAK1PAK33V9IhuO7gGlx5V6TlYeVPeNZuN3PMZk9nlJ8kpPRnWJ9O5I9zb"
    "blekSKDbaISFMO+K2GfRPc7piKXczXlz2toNVypbxX41xgXcPXuWSUWTg2hDaDv2Kp5cclJkwh3RaZ8HhGwrXJtlHfF0uN9zBLLb"
    "k7zLz9BZZpd1OOqFYdbfRP7DUsyT2C6m557y0EkJUq/ec9eFeDsFKmpmVOI6+VIgvUvv1HzNfDAabOTosb9g54fpUQ/UgNbIHe9H"
    "nL5Sa6vH5QHJAtXq1mC/zhZ3RWt3WknFJ5GJyy7kY9xeMOtNDGaCky5Me9a9aqIfbW+77a7GXm4rEqd7tOSot3yiJxqJh6PzKLJR"
    "ovPsLDva7+3bC7Geq7Gdn1qBv9JjoLHudm/SptC1jNveVnyU2vHlR1LNudWjo2Ux1q6UYT9T3m0u0vXEpUwpHu7uj32x+GB3yHmt"
    "wXYyXM76OS7RqOddYnxSKQ99Vj7vbuWSu8livN5IlzjffoVqTZvZ/TlYOrE9167g7tUANkEpOazM/ekAcKLJvNrd246EU71ELNJJ"
    "tVpioZ33ez3NaMReL9ntc58nIfoT83CvMJpWtpIFRyMctafGWxIwvNmwHObYYDC+G617qr14OMVn57UIDUrcJDly+ndbozSzN822"
    "ko55qz4WM94CO+82tnxFhststVvB7YHP3XD3wDrht7iyr2Cf1qLBdj7PZuPh4T4/SdiLLcZR2yrUIlJFCEvx3f1hOjZK84WpdxKL"
    "+pLVna15ql9hhF1YX5MrT/xSpCIGAuOkO9obpHaDu1GxnY1JjYwnHh10JFhJauwWxz7JP3cVG9G83T9u57OVRj61Nx/vDhoxqlIZ"
    "ZqYjR3uYTHnygXGs2MvGfDzXzFWFoj9RatTc09oW0x4x4Ywn2e8UZwVHxuUPJjIurjXhp0Oq5O/320P7KOP0eLan80LXvTPvjJk0"
    "HdzhpkEOv6cm4aV9zK7HFbByE7o6Fd0RZqe1sxWvWyMBqrhfnnX6yU7PnsmBecRPg146OUyP3fbk3vZuJB7fi9pjBRefR2+ILPhy"
    "RT47aWebO7FpJprqzVPbqTTjqW5FmruzoZB07EtRtkqlOaEpeLp7w1w5yES9k0SRa7faAXY+ptpCio9XI6VYxEMn2XJtp+GOxHci"
    "kmde3hIr3dh2GpY46mxFKvtlasvtbw+5bCCz249We21uJ8z4dqITdyOc23cK3QzgZnNW48WG5HLvi5xvu1hjw3ygIDhHxcyITezl"
    "+uz2aLtT88TETMI12AsUYpOOZx8mOpEGe5XM2N1LpAuF4mhAseXpfiWQms7zVGxbKlIl76yWj9US3kKQS/tjva3anLVn/bX+jnfk"
    "Ku+NckxyNxLY4RP+7Zod3TTBFGOg+6aCjdK8APZsYHserJVqnaKTq4p9t9/rLdcmuWyyMW4lJ36/x5pi8sPCHlMJxwb1/h7TGe1Q"
    "Hm+UiTroBiCuX/K7i/kIG7Cmtl0jLx0su2r1xn536rFX0ZXdW5OkLyUkfPtDsZpMST12xO9udTv2LSvXHLj2d2e+Zi28N63P7HWJ"
    "HjN8pZMbAf1vTVrbO4kqOxCy81nVKRWiwWa+40hny4Ew6L/NkeT1WKNR0ZuxjvbylHfQS8asXXpc63Z3w73dSLsY4d0B1r7LliqA"
    "htak4Nuf8Y1cbeiuCbTos1oz++1opRgpVqJ8EvT+nnc7vdsr8MN811uK5XZj243armO3O97fTXg93sZsj+aHkXA4Fm2OxjWrr+kL"
    "Wj3Zebab6vSpnhiIWIV6buZx1OwFrjv31T2MdyvMh90BT7DQzO2wtQaT8mXbqO4ow+1ul6V63mfP7Hv8rc5+J8MXI+081xLEecWR"
    "K5SCgVmnmKejY1e3OXQmY/X+fi5ZkrZ3tiK9cLI1djQa3tIgZ7XH3UKhFXUWo63YjErPJr0t0Znn7L1yZB4Pd4r74fi8luRciWlj"
    "J97q2OfecK+XDQSEjLA77O1JmXm9med2mFncleowbUd4KgQLY5ejI1mt1uncymbHhcBeVRLKQW+ukAnk88nMpLXX2ar0U+FszOkL"
    "zsVWnEu72/NeimOs8YDfEcx4Jx5aCHenidQgV4x5aDGaHw5cvq3SvDyNTOLzSUu0J/Zz42pASNdzQoVuBe3bRSqcmqTCA45t07F2"
    "r7CfHpRSVHZa2bWPxr2dfclXc5aHWfuw5uVm/Z1woj2oWO2s37cdTQUa8VItGN1O7zO9/aZzLvRqol1yzbJJu3tS2xv0i3vNxLZb"
    "cPvH+y6612K9s21gT0M+HWRHUbuz5hkWmrwzBoadkKFc6Rwgky88FOd8MhzJzr2esdNfnvUoV57xiK1kZ6+60++hc8n+TsqRS45j"
    "FcFpLYytCX+hvJXP07WAtZlO2tOtUnoSdTTz4+o0OKaLgBQFJmHNOTyZgLgTLyW6ucT2GOTzeN5IByfD0RaY+Lv7Wdrdm5WznUpe"
    "2hoVt8PMvMhU4/PUXOxRiY615Yu4QIsvbxX5uHO/PduqRf1Jl3/i8+ZLlQJVTpeataav2vMmPIGWezrK7NK1aCoMvA22C2gENP4K"
    "PWD2ncFpeYvnXLOUWLGmyokSqDnl2XbX3h/uzSYte3ra9NNcHyz/uCffGIsV2s8FeH7aa/mk8u7OCGxvaZLwinuxFKiouYLDD9yN"
    "8VWd3X2ryAxnpU5jxlCeQdlHDdIVPzdrFnOzWiyYqs39ncZIsM8izVI94RQbnL28389KbIsNdLtzyi16Rvke3Ww4hk2h7mvxFR4U"
    "0R2ebxb25on2XqEYTbcdDXRkuC+5qk6KZ3JDBraf6pSFCi/09yYNUcjPnDtMzlvwVsrV/Y5nby/c6FWnIBOSpaE0bzDbpa1EzCMN"
    "O2Vpb5AVqHrPn52LPmd4W5R29ztIRwnWhjvJaorfs4viOGOP9friZL9tTw/3LkbDH5NSI1QeHYyFw9u3yyPbhJIanZutEddAL6cw"
    "Vdtmy1GD50TJRIeafGPUpznJ1hBoSqLjLI1+mQmW4XqE5SZtE2g2RDBQnSBpmzQb0PBLja5HRR2BboWkBql11KGppo0aDGiuGe0w"
    "bNNMW47l0Yrt0JFIU0Kjs/Ev/9pghAZLmxrTEOF0EqbGTP4UQoSfsN/61wEldUzNENF3OUwux7rb5kX/4Mm/kGD9sNCBWiPrMwUo"
    "n8lncsB/TpPTZXI0HCa/yW0Kon9Jt+hed5nc60F9t1mnw+Y2uZyU0xb0mPAfB/7PbYNveJhGh270XPqBnAEYxW9y+tl177rXOEuX"
    "yelY99u8JviXcbpNTp/cCd/W9wCL8XeWZwLj+5O4Oz1M/ApM/Bgm7qXHytPFQzQUK8JYAt2QTBOmKXWgcYAwdWim3ZHk71NU1zTD"
    "fwX44TJMBMA1hlqGuXnVsn8hWUaU9GsBYHScbkP1AEB/RVlgucwNTW0O51IZtF1RGFAK/4UUOzytTqDFsICWQLkCoFyUZ3mBMImS"
    "wPcAPTmeowlcY10YsVBAj2mObzYJeUk+WyBg8tgCjnDQ5jKhfxhtYOMAdXC5E/6Y8B8ZpYI2hxseB7xhr81nQv9QKfzz2IJ++cFy"
    "k8Uo+4A2NjcsxGFz+CmHzQfj4T9yFzYX4NuF4nW5HNr6bf4g6s3teO62eHZ/b1PP3zljvFN9hhuJelzxYsTw4IfAGAxE5QL67iyR"
    "hA+o0G3zUS6b04T+yUB1m9wZWFGQXfcgEK975NHECTUw9OgzuVmPyQO1PIZuEfUlPUvY6XJCd+u4uuEJosqOQsWUIPATYfWCFjwA"
    "qB6xId86/MPNWjzbpIUl+nc5KFixwm1c667dwOL3OvzuABcJakVOgKsvuG4LZoKAdm5bMLxoDPUAIkmPvr3JNXa69QOYXDKQQNQa"
    "YASE3fGNfUs8EVAaAGIyUiuwPad77NPNCb4lvfrfhmU40bI6Kv8bzFSmBAwngLkP/FUZlEfHoDyrmBJsg68BQHBi6NiCeCxPw4GK"
    "0C88ltPRwDVgArYgWrPKwMe6NfeBjgJod9B/WoWMvgZAxRlYxxuoVKFYWtADru9y2vyIK60H1p16yIPcCJgc7DrAyqPbIwROwCLd"
    "jqD260sABjY09iwXAfqpnI/hWvySyHQp4sGFJYDTcaG1b7x+ocuArsc6PzVgpgth9LqPRbKys+6Bz3V30rgXXpvHC+zPCRsMlcc+"
    "I54ZlwnbMka9AVy868AM9YgL5O33mTxJP7AMHQidmNVB93OZehiWXkJZV9K3jOwXJuFaIi///rK0dY09S40UxsRexrQMQPSOFUY2"
    "vaAb+ExG+dnHRQhYsuIyAnWI4dpG5cUF+LxEOwZaQqsMGBeBOr1A98uQcC0TcbDjWuo3aKTpzrprmR/4Op4LLMKxosyzoiygwLXJ"
    "T/QcH4ASVBklfs73ngO3ERWjSbsUhv0vpMQ3n0kcim6w3qTEDjBzCqlAIPhlxUkcMAaJ5EJKJBWEWWJJDtjrcq0HbF6fwkgHFNfU"
    "rwdEEpAF+m9JKfRDF1CGnqgaGksNRNrYGGTCopL+gUfXKWJWvSVJguC40EWBYFjKgFrAOr0iCBCAlBM6AvLHUMO/d93iOhah8M8L"
    "pB6Afx7593yJ/7qAkP0y/lLc8+wU6B8m9A/UJBf+I2MDg4TBBVnkWUZ5zzJuLglbKPcj4Cyr4qg7oA55azvNCzzu/yJPMxDwRQ0Y"
    "LcmncegBS82MjMLDAvNCYscUkDkkR0s62Qq6ChKu6EORrr6FcPXJshUPqDZwPWf9IK7velZ1Pf8EIeSmnCZVgQNkRAxaV2Byji/I"
    "QicoE7IaSfd5A6KAUgi8W22OO1jmO0BPzqR/STfxLvFXP+tFbNxpRLH5kjXkdHd8y0V+VVbwE6Nm58RIuySGA6DG+kCNXfASp8vm"
    "99sccicNlm/0nlOug84Gui0mpeOFSR8zH3EbNHRIiWKO6tMb3LHlSKClkcCZRFtXnJoJcQzm+tGiBsEQVjO3SZgIK7dBEBZyzNCT"
    "CCgFBEZ1GMNDkAQlMNR6h2k2aY7YICRhRBNkk+LatMCPRHZWpqUUx9FCcieb2Th68cWO1Gc3iu0D+vD2bYI4PlYt/0Q7ZLbZbLQl"
    "dIu2gWCXaMEc4XmWpjiLrcsznBnmYVmsR2yYjxiJ7ouwqDHFjmBBJM9FO2jkDYlkqTrNbgi69bLHqkuDCeVtI5Eu0S0zN2JZC3nA"
    "k9ShXFiWKImWi28q0MHlGWrGj6R4qwWYbjbDJJW+GiHGptiYm7bhiBZgwSzU4QUzUR9JEs8dYACJuJRuhhCADmEhjRs3KPPRdKNh"
    "41stkZYydEsiJ9rPKiIgAA55wJG0jaW5ttQ5tJDPmAtHT0wlWmTmdL4u0sIYYKh73vp759pS5toyzrW1NFcNYtowN27AeuSZmLVC"
    "C4nm1LA1GRHmxaFFoHXC6jAeimaiyYwBEQW6tcHoNjDRBhSlAUX5GzeIDiWuM1yTIGH7BMASwDyqjvwPKkZiBCAQBiAPE4y7cQDt"
    "VEwHAW1EdehY7k+UZtDbEWZgG7xtQkoCxYktXuhvfB9/ZQFBauYXjnjb9HgwtXz/eCUJHFtg2/rUwNwI3VIGlUEMwyIX2Yb2U5s9"
    "QTJN2H+mSUqMBGUNG/5Uulc3hdjgQqFQwzZG2M4ywB0QNCUzlFgWa23Y8PqPSVRsOYTN0QgnwpmPBiBeDbwgRNQpgdAoRAplgaHA"
    "/KdmByl/BQJ0Ohwkffu2w2Kxw9ebS8xjGaScsrKBwLcFWhTRAMpaML1Cj8SGw1BCTYkNNIiujOMnxAaeAbATrmmW/hdU0C1UGZ2B"
    "oZWdI9bXB8SGhDiLbtVZFtgFLG6DDhHIS0QoQOYWXUnK3gtLjFFDSB260P2BNDNRHNMHbFhvUU0asEdFHj3OKfO70AHMhVheRYxE"
    "LBrNm+Q0VK2jdmo94NmkdKjxzN126IjhGnwfWQwHxPkb7377zUfffvFrgHOfbxKHinvhRWAL8PjxO7/57pM3zu7++9npp2d3Pzu7"
    "ewftR6MB9ahmEyp8982fz1/9GSpsosbQBWr1/u+godYjzALNHwZ78/XzV14///gVqABPoRyeNoHnwqNXXn363sdQCD8Xk9Ba6meA"
    "ejF2odSWezJUNfYKrIdlONTf43/75ZM//OTxO79ePOOUR+d/+fT8i99oK2rwA4ZGizo7/e3Z3bfP7n59/uj+t1++rK8we5EWBH2V"
    "7z45efLzL7/71etq98dkexA6kkGGDEKlNanCT4XcANYjg41UoaiDH3JJKYsmjcBUwYhdZMqgpArUQ6Qdv7hicD2otImguqs6WwHX"
    "i/tkmOHqTZMhBnVl99diMirwELRSXOgIDDgdSB9/ce/s5Buox/egC2yd6ffkLy+dnXyE5sr0lRFk/NZqyCgujBC+TChG0nBf3s6l"
    "DkShUR+JaJa5cPn85HdnJw++/fM3T95+KHczoQTUj1Ll/I+Pzk7effz+N2cn97R+lCp0ExQOI/q8BAt5IAPj7OT07PRVXW0FjR6e"
    "3f0UQYIEFtuUEVdDWmh8dvL62clfzk7ePzv9sVrnmNwDygaleryBQES2eWmDgD+gWPGA1wT6C98FfgDf4S+hmkyE/EmQaA4b8kxk"
    "1xCGxTFZ0/pFAPvqP2AnlO6//fon5z/73fkb75z/5V1cKg/15L0vv/vo4ZPfn2IykYd8/PXbTz+6D1Vhvd9+8drZyVuLCcjdPEEE"
    "Lc/h8W8fPv7BG+osUF8ff3l28rOzkx/BdPbbKiFdk/dcxnjQUdJFJPnrnU/UxjpNOGE+wtJPY6qKKJB0AlG4qBwvy7ctMwht0EYI"
    "aZ2w0qRgWXSjY9cLCTQSzEc9xN4VGcuFdmUt+IBW2PCzJCrRAw3F1IPhuAPnoW6YA4dBwgugGsv6Lw0SCdbXF9sgENWBhVCKO+DQ"
    "wJxCIjeXxN3FkRsDU2MAAwtoYHmdtJXYMKESx6HVLIGV8Nc7b8NvCVsKCwGItBWExJs6GUc0Oj1QNrAmQyj0bayAHC4EqdfPUAFq"
    "Apo5SS9E4HQQosFiQB0hAtkk5DM5YgMXIVSHMhhe/q2NJfcnF2Jq2iSQb0QtQTS1CbSoVZHJalP9AvoaMC1igVPjgRn0D7y7z9pE"
    "UWJU5WObUsyglZrAdGCmLToYrFwBmFAGPWe2eiIrN1UA/DUh3F1WV55veFJbhgELWcBCSjeRNVAd12gbt4m2cEOZlWjbEqg2OhTW"
    "aTkHtA3tyb9CZVUNSoDWLPOwxWSJ7x784vFP30RcHCaxBn0DyzU2QNx0RYPXz9/4XG0zZpq0ahhcNh9cD7GzK3s///idp3cfnr/2"
    "70/e/krW/8ctqLJ5oYm8+QqrPDt5VAWy5ieiqRBFwuTl15+8/aEqGH51dvIDmOx3d//8+A6U3H/62X+gkj///PzrN6ClPBiUy8IH"
    "C5L3DHPCFeT6uQQiIDQrtBTDtGRBocxL611We6D3829eAi0IZrNyvL99fe+7Tz85f/m9x//28PyXD//29SsXZwDN5ToaDS9AuqYA"
    "Svl2Ec5IdFzsUpG3x8i6wTtJ4T4ug/bZ3V+d3f3t2ennZyegycACPnz64W/Pf/EbrNh8dHb6MdJtTu5/9wnIs4/PTl47O31FBv/Z"
    "nRO8TtiTz2Vp+N2dl9BWPYLde/zKnbPTtx7f/yEoDWcnn6DqF/ZAHUcZX0U8FD4hXr1Q3ZyVtZIyaQApYuKQf91SMN9M2xo8Y9hY"
    "pD0s+ovmUwj+F3feUAUv+12oqIB1JPHGaS63+e6HCDGeApzkOaJWHN9AxumVBIMWhlZ4F748+cFH56/+Sd5NhbVHR6EjrEM4SNA6"
    "nKqK4ZJVCbdeooNJ2wZhBwYkdmupRiwApMWCnDu0YFPczJIM2MoHLIgskkWSjIEnIi9I6iNzdHSAHhxubnos6+gXo/66fZs9cB2u"
    "M/DHcpNpmdckxStjUfgswuqbqoSFvVGf3+I2JZsIwKDBlubWnZYNaUnermY6gjznAxbNUnMiXOTiLdbUYkE0MyqmP3n/0fnrv/nb"
    "1z8hrFEzq5PF6NcxycK+Csrc/lWdpMYALx2gzwua0ayuR+1GBi8bugUjAGwtqsMOSMegCxBW6EFps642Pjw2+ieKPN7MZbkh0APW"
    "IDpklELF6rS+L+u0538B6v7shSO5zfH5+z9VFXSZ8BdUqtZ5URI3CWBjjz+4A5ouiMQ8bdaeWKzqd3HUR9UArosCpO1YCcTzkCz8"
    "vn6xYEqAHWFCEVCotmGRVRFUNBQtAxraqNVijHjLMkj0CiEVViQLXxWf6FS0qKVMSNjUuUZY5BqxC5YNxzP1OdBdkVuGIIFrsMBM"
    "hE1ZC9pgNwlYyJwWeMJihKrphSP22P7CkWBYpIyVEY7ELiUGiJ8lCTv0S3IXFILuQF0zLBVR0NrazFbehNnzkghk2KfNDJAgY2vD"
    "egaiTLe4mA/d4m393oug4d2+jb+h2VosK0jvauB12yrwrgMiGK6xANGNGzKMLEb5rVlMgD9nd+5rP8/uvI5EKKZFmX0bBSMyWVFV"
    "wA8FZAZgDdugxzFcg15YDAckZ3BSO4we6ov+YCk0wZqFTUQ+eFj/mGLxc84shG4JVqeFdNJutRfslGVpStCqSnq37Gou9ULLHIO5"
    "ALufmC126M0KW5qOV9dpg1a6w5qPBMD1tgHNoSrsU4c2W5AkY5oAZcnGDzBCIP4JXyloP6YNP1C4oU2UKEESq4zUMXO2Hj2zAgQt"
    "m7paWMlQVrbG2RT7EFQM4Rr655q+xaU+QGGqKRe5cPns5AvY78fvw9/Xv/vL12cn34BiCjhx/tLDb//8Y3h0dvp7pGWcgvX7Oa7/"
    "6Nsv7nz3yQNV1/j8/N7LBr0DNI7TE2ChsmtD9pnoOnn49M6H519+AuqHbFQvodel8kKoU4IJu7pXOVGx9/Eqk2EJhTWPowaxW075"
    "xEj9bSW+/eoPiDuiKvWZRIv4+Qtm9acFPavyZoQCJGeBp///H3GFRRmwWLuo9oH3fvPKDZS7UBB32CYVUlIbY4mzgdkTUh6R6qQj"
    "GzYk2CReoliZubZYnhdA1CHilzms/BT4LHBgM8a5Ji1KCsNSOA2wLNRmUQ4TYEfw28zDkiyyxMR8DVvqmsS8+xVhufks77MwNSGn"
    "j4x8URgHSMKykisv7TtBIjbNPscWMySBMFt1qsjc6v+VwauMbBMHLCOZEQXaBvzAjM8bEDOzmI2SvTfAnpeFaUpvXj4NMJP7tH4m"
    "dQ6wQUQaML0WQjS8Sfz1zo8JKy6nYTvP7nyAdhRT/mLQiWIQy8GpnCJ66JWig1N3b0hpQlYATVuUkO3LAlshbt82q785eirBb+0x"
    "8EGBwKxsxEkM+68htwPJnhs3hKuWOVkfLUyvp++8dv7gtfNXXgc8eHrnf7776D7QFmYHj0ClefzBr2RZjBjN12+DGYItsYsmxwGh"
    "VYVtklSgqHilzlh2fFxJSJd7MQBgshtyoc8rXkKkBBxiS1MHt2sMI142Du5AvzoNNLJu1VfxAaHl40evITPEGmGx2tZX6Nw4Jbx1"
    "f+eUQDFAk8JdkLq9Bv1A5HnOqPA+/q+P0KSQAnDykCBhUrqDNaUxphd5fqxi+my3wXYBvhe6la93QarbYHICA8wDLDwKcRTg0yqu"
    "mg8kZB+swTOKo0BUogUWCjuERbVtJFKACsh1ty7BH8vCGtGdp+cGsg11ISxgJXi223h+iokCA2gmymr3YYcZmBpgpOico6iVIisE"
    "vEekZDEoDWWYEdM0eExh1qB+AZ2WZRPs9m2kPay0wA4Ob7aAbyss3cS3TJKsaWIGwAJrHoD947JABYnhRvTNA5vNhs7PyzQyBw1K"
    "6IKn80jZ0Jg3DUYPKRdZlmMWLIcy9DMSPOKFONXooCaCbTASO2DVgRSwErcJK0+alYmp9qJzE8woRSxYCZPdRGAjI2rmLWBaHauL"
    "te3Gc5U40mhkJRnML2R8we4rj4AVqaMpJaTyqSCA+guUAXqab5lhOhZQCpE5c+/JG385/+Ch7ApAmsXhwmhccDN8JA07jXZJ87Oc"
    "IGVH9W0hP7/i80cc7SdPPvwloYZrKHPSgjZgAZM2rBwkdJuWbLjWRalG8AOEHTCq3A1h8CicvHd28ids4ilTQNxIUM3T1T1gd4DW"
    "BzL/wUjGZuxFacI0FjgJmHdTRcyxiBFzJpg5TXxz14KXeiLy3tnpa4/f/SWyQt/95dnJ28AvENfXHbupbrfX8KPXsb4nr0BaABEU"
    "e2kAcvmfBESYC4IghyEoLEh8qb3+xBu0Ags5EuEvtqm//epVvCxsIANkBQsACrCWW2hEkmWhZS91LBk6lizkStw8XrFTL+pTmDDf"
    "4ECSly/YfXRDGRA2hWDplmQ4dgBORpuU0mee6Q86yzr1KuVNTm8iVjvd1aeqhgZKOTcYKThDDEGY49gRCQufAUs16I6cQUAoCsHd"
    "r85Ov8IutT+e3X2AvYdvPf74gye/+zlBIk9elO8PWFqCPvhWS8Uf2jbUxU6BIgwFYIrpcQipXX0GReooup0WorBqjRIwQfHCEqGm"
    "HJWzQsNQlymvDx/i1PkpDokheI6dVQg524oG0rHhAsOM0wh15GravJX6aK5IH1K92Y/Q0fOhTgX+u+eUW55TbuWccpfPSVPnDHPS"
    "JKgS0dJi6emG81ivtes4CYHEzGIn0a8L05CrSM/LFVAggJ4zKFz9Ao49/dnLOoxd7kWgG6A86Pt5/M5vsL/8B1c3HHECbfQYL7bx"
    "9K1vv3gVdGLZY6wD3UV6awg8y8q7Jgt1XY/aScMLbdn2NRgsL1zCQ5DuwRmEtsXIVrIsYI3qjf3Fd5+8s4qPv6o799epjH/7+qvv"
    "Hv76/NFP/vb1n2V/wPmvP0GQf/N1Qy9g9+Mzc/Xk4Q0sbf8dn1icqrYvURewUU9eqsj3eY7Xot5aoAyVmTm94XTavCgYHb0uaUwJ"
    "5vX1JtO3EMd6ZPjLaxum78H/nEGXzekL2Bw2p+N730PR8/T3vqfNWd4gzcSKgpo6tIAFnUHhsVFKBKjaQLftm5HPbm3NLCGLCpOy"
    "+iUHyjGoc2BsMwzU4pGUteiUOwopd5xOuWNu3GA0HZcxqDeWtVCIQga4pvYBMzQ1QmZqlcLXB4EnmVF9so+1vBs3zPgLUrHB9Kuz"
    "Zkp+QvIWi+UmyDVzI9TQNY/K9ZcXrBN9FmTR4vVeaNy3yRSgVcmtqAK9r6HZ3LgxpMx91F1DUfv75Mii1MDz3XRujBY/1p0Ks1DO"
    "yRGJbppHoHeK0ovIxHBY1mHyup+3b79Ay8shcT8WXQcKqSJHykiZNQwnd6H7CdbzVSNcHEJFnNblO6QHwfJuGTeIbIZaq8CrmvqD"
    "0GJBmPXduEHJdsKtkOsmthqwOn25X6Zj5FcHl9d0XstX1+QlMI9gTXJEG0xsDSwmJLk31DL4ic7hUfgSYbmK0AWW0B8FUYqFAU0G"
    "V53+SPUVM9VCWXUV2x0exVbjNHDNFlA0yafvgNL6BmEIWQ2PYG/WnJaVsQ+EnENDHOuW9LyD4iPbD89O76wa13HJuGoCDqEIA72i"
    "cHEXXRdhUxVJ+ZSjpZ7sECZZzC8kXXeg1oGi5i3HVfBvcNKyZ0cWgSaCbBpF38XGmpOQsqEMgQse33qT0Ss+CCtQPYu8eBIQmrBi"
    "dmkh1xqqqDvSk8FlsbGaSBlQTRyZ5QzohMcSQq8OhtsQNonvPv2fc+Q9xyfSG8QzxCjMmFYnfFPl8MdIWg9AjmtmONC+YQlJhjwS"
    "NiiyvdEnOwwo02vOY5JSDXSZl+g7lFlSB0fbZ6kB2UXSaRI6OibLWllO/aYTVH0kqFqqRjEKVWiVO1lulm0dSgTmOKZhBOCDZXRo"
    "o/4mlb5UbjgOlW3txWPLzbHSWqTFNPR2+/ZYaS4X4FOcsdJEqSMDoG8hc8ttc8a2S+0s5ORA/XEI/Fz3K3TUpGYgY+AvCUUb+AHS"
    "p4wQaGAhvZBLlqOuOpllGBth1FmCUedqGHX+eTD6B5eMXEsdtAbRrHMLLRBBmbpZroem0LdoLj+1hblN9pAbj4Hx2weOw0M86OSg"
    "p36Xpaf6EOahPYTvSDFQ0aZv2UQjqT9kcwAP1GIpMPE20NPRhWIyHFoQBRKHfXUF7dCacONGhzOHLWQvNFZlbCp0K7UsY+PwGLur"
    "8EPliMhC7oTaN24snqC4DUrsAIRFvGvauClFK3i2MN4yE2NZHEPPBIptJsgd9A113CHA/kKvAV3HDzbCpETVU0hP3HAoaQuqtJFz"
    "EWRxhLIv1trkItFg3CA2uoKic1iODXJmVzKHyTUMFFBaOVhLDGW5wuqOzCkV+ePorBU0Sa3AhE4Q4PlAQFdSSDG6RY1YBHx9d5bj"
    "6ygPY6axOrCQULOMDeJ1RQecQWPoo8rxK3JoBk0UoqyKYX2wtjaKJh3HUNTTJN+q3upUs623PntXTRXl6V+yWJRbTKgCbUxY0Xa0"
    "LUuMZhqip2aVIG7fHpETnYVxAJR3CIxrpOJ7PARUBpwAEz9BYMonQPrshOKY7lKhHO6qDV31EK7u3L4dxySqdFBZUBKgE62ST8VC"
    "juhQSnMlh25FlumnIcFzTCb4qUZAMTok0jdu9LRnl5JQRCYhssuF4pJ5B4aUQlNlutejK1GmKzSeQlgxekFZ0B86CkFR0SPJJkpG"
    "Sqs8B6WJ9DJBVTAFVAwEFUEEFVkmqIiRoCIrCUrr7noEdR0ku+JgVdST0wHGBzAwwGKx2JrsrdBVtNBEBygGYpTRCcZDuAUyVH8I"
    "iw9lImRpcSSTX3nEVbqS/kRaPyIK7/7ShAg5ao4gUirJx1YN6Z/EEFLHCPmfiyMA9SI0vtJ6YS9q6L0BihzrctocJgPkatsYSaQ6"
    "k0OZW4iEFeGaSC/YRU/TIiuXapEVRYt06LTIiqJFHh93/0E99PjZp3Os3okF9g46qtOibpQzrptm2mhQK5MSQrdeoOS4C0F2XahP"
    "2NAtyQbavJlFykSKxeqKdAh9LwYDLmoYDJ+LCMhjIyEvTo3Ch5GIzSwiD9dY7QBPUZnVNF39Gd4Bj1gwrXZNhTgowZ446vbtRWcU"
    "oou1UIhdeHjU5Ng4cg4gVQjl3jIy4I9ghRs8KW00jjXAMoq+xZOUBZ34ARNbp9BfC7lPmRndapOMFtYkb5g+yWIG68WxSTrSJBm5"
    "SHbB0IpzwSkHHyoOfL2L7x7OsHlVPQhSwpTlwxR0EPL+73D+zcWn7AGrxlk6D0k+xC4OF1nNNbbuVMNOYGpIjlGhF5Wtx7ME6g6t"
    "rQm2cjyDjhLhAzvZcPAx01SLMBLhU0fkZmkt5VbfvBCbhrascfv2WkvLB5bhruxTN4RqtRaJyrL/NsVJ/C5DT8xHdZwST3A0JdCi"
    "BJzkZlc7iJuAEJR2mD7NjyRzl/SgVNGysczpdTj0IW9HOOZNfT5BGQ+632UgWPKgcagO0NTvH0FstEUzZyEHShAbZ2sMNvMgXDAL"
    "7oZuoYKDLgDrUInKFhqkkprTlf0vOEFHq3VMog/5KEuJk++EmouUFEMyBE780vnGL2ZlHVs2mkuBHmrj5dANfZqX2oy72MyYgKGd"
    "YBBLESYXE7lbpDG0UkCuCZTHDWRDkE1VY0CYJ2s8SBIsTgDQc3RIIyxpNbTKHTnF4ydrIZp6LxAbGJ/lX21iQ8ZSVa2ALerARpEG"
    "nH+2984gyLWcg7EsRppXKgGcHoAHawAC/ir5NRAMkS/UFdJxjIXtBdsEL42y4NMjxswDYGRJfohFOYOFuB7m15a+aqOr1HKqzRta"
    "KL7ezT3KrP2w4CSiq05w+rRE6bpZw2FatIgPkRUF+OpYng5pbmrpYLdvN9VsMeWrHNaLyFfnSb4c68/u/hC0mLPTb7RECWXmCY48"
    "whGupLI4lK9340ZzTaUltduRQB71NnSVtC52WHIRKHuo5mpcvq6B0q7Iq0MvT2UZtxaJeTIUldReRXisOIRcxPrCnqGrJRY2Iwvc"
    "jIJ1UBylleUGeGSS23AvA+J5F790GtcAaYsIlxdpY/rmhGmiSAGmqU/bvCQmmg0xSAZp5oLYoAZoY4B/H6vcS7unFJSdODIaMqAW"
    "0hxYZAQ0w6o+unYC9apVFeg+P6Yvrw1ShD68AsX5JsWaeJQyLidTojXhuB+8LFDxcQ3kyc7ysDBs+YBCdqSGy8BiWFVm7uASeU3G"
    "ZFQZBkl0a0CLl+ULujQKf8EJ0GtOssvX5QIUgCmAlYbvvpDrCnRz4+hYl3kTHehOSJM21O1NfXzlETBp1OmyDXD+Eo6Xv/umnP1z"
    "dvpz9OXuuyivCojqU1BilIBq2TV8+pZ6fP8uysfSYez5S//9+INXoAJ2Az9EIdMnn8gHqPhkFIdGHmuBOigmsMELTVJCh40cDudE"
    "y1K0YFlLwqU4P0tfqmoNeE2Smgqz+X054gnN/DMUxS3P5+SReoh774UjDvEWANkm/mvFUb6I6yk3F9x96fxn/41P1eXz9K/P7oLi"
    "9xmGyD0MifsoqvHkF/rclbM7pxgA76EYD6h/ch+k99npG7jahyiKHOWt/Rj/Hx0i/+3rr85fuouiSO99hZP2/owiQ179+uLx8ff/"
    "L+7TcRHYxEJdw4Qro9Xt23PQU6kBY+cHdo6WwM6VOjRnpnU1zPKXEE3OlGgV4CEoYhKsF9wVulDHg1IeKHHGNUwLGwmhsSTMlJ5C"
    "FLpVwLQ8ICk/BZ25DrInKX+a8Wdo8QhVw0/wB8pUkORc5BHHIZ/bjRtzFghTnhXYM8qQR7Qg8MD9bH1aFKk2fXysruF4abIjxiwH"
    "MSdtiGZRD+gztObQln1TXgvQ9sql2HEYihztr5sHqn5xGmrvTq334wVPRksxatBJG+YbCAr4iy4HRa2C14P3A01T5R4rJwoQJCw3"
    "ZRDT6K883yN0qHM1mC1H6nRJNEmFdo/lUdB+X7JNTUVQL6Y7YsgA2AzHOFlmsfQmmLYwBubLKKIYlK8kspX7OBiZlMGJv2oTQcPK"
    "WItWj/ZRu/2Kx2aP1p+hnY7fxkfmI9EQEkvb+B46RnMoae7KT7ApAQgohId4ZjoB6gg06Ou4wDhmtQNMy/LHqf3yT5wmPiWUtFaD"
    "c0yZwmWati4RHBtJz0jPXnVTjtISxVmd3bmD1RrAabGtZKWhW8kZTroihI0zhOgRf335LZzJh1rJ7QVqgmL94WMNGcTQt6Y8X+xM"
    "MMlxNrr5QUP1hHmBVIWRWdNgUMCRjA5YgQQE06UumRsMqWlDCV7WgYADoCgnqMpfdFRyUznCaTEYNzUbwlhVCY7Cy3GkU1N2luJ4"
    "cxCYmuwUQphoSBbJUAE5Ai6SH3nAkLwhX02mDnhAkY2lRDa928Bxic+AQaSKpqd+atPTHaSR49ARjkB6Ueow+DhO+7GGqEK9cHlk"
    "k7/gyxdwHbUuLoHhUR30gX8PYCcnsHIoU7/K5TQtoFHwJy7heJGl6QGUKd/kYYGdvKh1sraGjgkXBbB5LQaXoi8kcmsITEPCJeoP"
    "kmoLNI08gjcVLjMmefMY23WXqLqj0Bi+jy+ouuYxbBc/SPX7dJMB+BcEfkC1KYQSwKMSPOJKz6MKj3A0xXNow7gBTi3UvCoMoJhu"
    "39Yc6kZp28Mtb49+W7St0O0A9GGEulOBs1MHYecCruQgNNJgB2hks9maJDoIXYY42VHi1J5DdSS7oeYFXJygBHVGccCiIPRyCEsN"
    "MhdaJSJHq0UkLHI0QMGiC/Dph1IB2VQwXgGnUkUGZRNj+gKcTQ3LFbA2ZQzXYNtUsdsI4uYKtG4uIXVTQ+ljVbCPMDMZmI+0vbCQ"
    "BuGtKCkjy1HdPFI1E9KPxPEx2dcBC/gE9a+LhFRgDLr0VKsXGhjdewsfJKl9XaGw4NRYxKa8zoXz8BiV3Hzm9oygM6xpGRZ77eU9"
    "U3g32bYJxoGPawWeQb31zuU1jRHHFzWCjksvZMGQeV22Us7ufo59Ior5g20GWfH/LZgKYNqssiCQxfMNrgS1PytETZpNoQsKHizN"
    "nxYbxjsknsdS+Qzf7fErFDqE0iheQ0G0v/oGh4upNtWigpaH+xCHJX2+2qA5+Uy7HUWxZpZMnI/un53c0/onjCFll8a0yfHKnIgF"
    "/CKADST96ryBKQIZ8fQdmNB/wNrU1FZ8Mwiv3YqzDE14aNBJcOWrIt440ZiUeaVCt/IKK2OmiWo5P5Jv9dLte31VmLJuqg2+PxhJ"
    "WD6ja75WRuo953RSBYw1r5zd/a+z0z8Rz46a1prq+Lh29cUdwoLn9rYyN5zSjpwA/zyYYQy8Nszw6MdyCg1KBsARgfjqimsHi/eI"
    "K53bRkfpAcz1K0RkynSNt+YhX4m8lrO7PwJwI+JFKfG/Xsp6QnSLb9gxOArIyTNsAtiAUxmnzk4erLjURyVqNUtcvMYuHxAo3B3G"
    "Jgn0Icki9FDV4nXu2v8De/ssaBMYMj/TeVQ0X5EcG7kczdpxG2ZI/PVHPzMZt2jh1yGeHYMr9lWWVUJ3EzIiVWfp5obsPdD4F9jS"
    "2pDyo01C9hgp1/Uhjg5M+OVvv7hz/uUnysWb8sTLm2WZQW1eh5mVVWYG33AavpqNp/7EURIjcrxQmMMgnEFZHYi2FqgA5njoVly1"
    "pi3kNBS+cSNs42ganxkgxQ906ZENLZ5sh9bC6IfcGofg4NY9OZRcJFBcXBJriwdyExQ9hHUvTrUyMDLpdFpOb2rID5+pDWyZAf5N"
    "ggxv4ruWNtr4Opc2zzeJ6x1sic3OqnBvPaaMNMv6utxxhFnNVQ3wRYpafZi9Tgzr4nvRehb+xUUxkU8rOKJuAd7cOLmjXZwUH4Fy"
    "sxE/hiLYS1UeSmATo93YUPaR4Rhpo0eKo8GAF9Bdn+gqK+0XDgoBA2BB5ksYiJwD2hFcnxLaDLfDDzYcxwamaKCx+0ayXbqhCC0P"
    "GKM+JeivL791due+jlOoqbYPDR3fQfmhqxKBdEzmPkGu2mBilRKF2LPavzLN09fOT36nKGsE2i3sc5YDEkx//dFHoM49gJlr44Gu"
    "pawS5brqHNDvyXnCUD2fxkHgWFHS2OklYL6EjyxdxAY8BUuWZa0O3dzzJpR/7sTXrsAsP8Wi6jWsGP4Yy4elW+5Q0IUszlWwGVko"
    "gde8QkNcHAVgNRmg+AFSfO/+VgGeHseu1NSuxCxlYx9/+uF3d/+MJJt6raAG3W///M2SKrqkMMn8ewtsXX0SbBczETD4ZAZ1DTaC"
    "3cuiqcGzS3OW3xzgGUyJ478/OVSgmgywF07hWFm+Savpj4RzkZLZXWRBIvsNXQOidzCsDNa7kvHpxfNSJp660wixCUXFuoYBhA0T"
    "ZFZcoCx4iGyR/8Ts4Kf47wPn+fs/XaQ7k/9EqDkWUFu7GmzOfwhs2uHYuzIRaqAymIELsOjUx9O35BwiBZnvnD559NGTN1/Gd6Bo"
    "F1V+fv7DL3V8UwXVlTk8bYFpulaQltOlR9Hu9VzQywAh9IhhuHn96iARUeAnK+SwcUflJHCVZpFvx5C6LgtheYc1548SFUNTzRk6"
    "K1A9qCg5jxQHNMtGER4gv5iGBSOMBJrfVJ9CfK3sLHWKBQYdOamK4HUcXAPc4gipa5hgb8qKxI0b+vnIqsVqF4pX9hDptuON0ycv"
    "PdDsxSuCHYDpyXuHUlhRFu8Xj195TdPL5bzWf+oOlmXuqu6X7J3TsHKK37Gx4XIBx79yn1Rf9oVt6l4VZrRsuKHTDoPxplxRZiKu"
    "NDXllVQ4g4cG20xWs8FiV1kCujsRP1UWrGQCQ40FnC0Kk9BKsOH4qTKxB2AunL95H3k9kEn57kJYX72/ygBP3n6IGPLpZ2enn8gH"
    "6f/sfa2IiC7VbcV+1uVddXqftavKecRltHdhcbJJrTjl7r6y4jqJixMtwCIXE9WcuM8/Wd1hybMmfIUxe8kGKxL2qp2VBYVGsYBl"
    "Vw28vKPPhhPyhF/BaWVPueFuDpwqnw2ncuuFKGmKhKPpSmEd69Sqi+I1o+8J5Nt3H//w8b//BuE6igQBzPzp+f0vz+/9UL1I8uot"
    "UM6lluF/ARBXIvsKc2bJljl/6ZfyXcpYKTKEsyAvqBYX8+S9r57e/x85KORSo+OHaOHoSuB7soKE9ntVRIxsb9y5D+ArRAGAAA5g"
    "Vo8IsqkdES24B6qJb4v48weaKo9DZzSNSzUXsNJ1cv+7N0F5/gjnDj9Ur+D+FE3lzgnGpwcYvX6AGi360BJXsV6NeC3x5NMvH//X"
    "DxT8NRoCmIEZmyjMqnvFgfSlSvVFbeUfutkERBE62VmohIvDniUsW5x1Gm83wXhGPH3/q8dfvqnzuWNgYEA/fefHij99YRtifvUr"
    "vNXv4jik9+VGWD1cPMIOws91xC3LJtW0WVycqYgA8h+FBS0VJnpYGE64loWv/jBsNVRkVqaS/aMl4YNtzvcwnD7T3/Wknj4YuLp6"
    "B8qj85dfOn/0J3QS8fErCArIuL630I+R8fHrs9PfyNaI4mFdHvdznXGo057/UfCVlLM+PQS1I+0l6GlHhKshp2MnCts5xakPgDrI"
    "64CTJO7cv8D88T28svoim8GfPX3vTRlESzz35D6C3+kbKtSXXAZvYBeHnoVcYrT82GixoK/AAR6idwMo7NIQbvdPgnSVaTF6KONT"
    "1yUI4wPZ1dCtMutbjMnIrmQ3DeDEqxgp38MHWgu/G7ZQf4/h9DIgENKm/viTTDinmWi6FxxA5ys5wbdffqnszukp9tLfw9CRB3nZ"
    "QMl6/ngdz9sGERhM0asbDbfWLNMQuuLs57JzBgsPfEyIiE05Sjv5EN029rPfwbrO3/yR7EdRTwoV/Rit4VQ7OHzz4pkobiKzu8XN"
    "avLLHu79UjsA0c3ps9V3+ujNWFqiGHTFllGVaXTQ6/HQ69PXHCvCuUZ9AM3sEuNce40R2naZpaARu9p51YhdGbPFMsZzBMXttHCE"
    "IVbzCbZ8v8bvWPjsciVAh0OP0M3Hst538ZD55ZcMdon8NiHFl3Dn/gXpoGLk62jwuydnpw8UXwwC84cGFnvynxfaYUfqiqNfGKyc"
    "jaCnd7/CighCJnzVGhQMGK5twi7P/z5/43MZqN998sb5Kz/UXdykEhjwZuQVQPINdXPnfrlqyoXLpnwhXgrv5Eto5oBwKxDr0ZOH"
    "j55+9FPkEQYkuvuO9j6Fv339BhKkdz9Vg4SxCnUHO0lkKbGS0y9vJ7HSn4luoUYd/lg+tyvjN03Coqu80EORYCi4bHHqDuvFL4hA"
    "B3G//yP+gt0hp/cwiS+U+kumcJmlpmp1Rmkn0xrmMo/fe/T0zk9WSLs7p24HvmXxgU5vMPB3vCuLcyjVTf3w/Ks/nJ38Fo/5CuYB"
    "emENyPobGYFwJ3/Bnb+Md24hf5+8/dXT//w51m1P1bsfZa+/arheCghdJuDC9YhAgCPDF741FY0vCPnPvvsVCP9v5EvKkfWBKR6z"
    "vEePH36KBeNb+EK6H125I1fpapeR151TWSFUjIT3TjXiunyci8L8opGhk7jam3SQpv3bHz7+2ddKNaMBcn1LQ49hMvBVBf6+jpW/"
    "jLfuDSzWfqFfsHzLu0osb2JL4TP8Fhl1MnoaNB4gj1aqAP/H4aNwpOed+aXMYxWk75wYZ6wgruFqny/w8FdtyRWjLp+iYw34EmmE"
    "YpCWqEQ2+JbZ5FKEyXX0D99F/QNf77ech3HyAH9/X2M9Kk1/uBoEd7/S7cOHxg0/ffyHe5obDLMePVgf6nLXPtfVVNU5UITRjaHf"
    "KCrt59998zZ0g02Vz1bmiqiHjMjilbmJbNc8efUPj196TYYiVioeYcL4LeJBD/9Dh0NojiBFnXiPltSgX+FKjxYhZaf/gyvIOTGy"
    "xfID/fyf/P7+05N/kyX5qvOBR/I93MgGkA8TECb8Au/7K+j7JUxZZ6BfUNIXKMDWWRMn4hDGZzoIl5X3sNpK1d5xN8vquxweuVp/"
    "N1qCD4xkrwWm6VU84vDqQK+6xInXvPptIDCawYdus9eiP/Qnm7dvs7dvr+mWhs8Bcrqbl1EgOYVD01HYhBzXukmcP/pQvuwdh4d0"
    "N4lLD5Tvrdrz++qZkHKCayAXdGj+LCbTWbyK99LgF/l95wsHOAr5vAwI2tL7ly4dx4yiAwiNTyyfaRMb1K1FZOsmsVpZMbTHcVMb"
    "+k7Ry9iUsLRBk1ocPl/riAC9g/P9n2rItWEiyDKY71zbrHVnwe89ohq0mdghSHQTy+I8Trgq9UJEaT+k4VVYuuwKI+vV5R7ggB/i"
    "9m1dUYPiGjRsAkATnaBfK0QDj4ZuVhHkYBLdC8TkcCF9RMkIRYSgK8YvJBBdJSj0S+N7m4SSuqdon1hrAp6DNL47T+8+NKoYixvy"
    "sOqJKgPq//UDYMePnv7spSfvPzJk4a3m1xcJDWEgQGoMq9g0Bu7pPPCqyq6TBa/JYR84euzkEYr3uBC/Jcu4pdBbeIQbn6wwdLVX"
    "sxhyY6SpWQ7WoeU4HU4Xp6NdvHEgkKwhuYRbkYmC4rmoUEML/GrhaH8BRfs3ULQ/jtOiD0MtkjW3LMfXSKDC4WDK6Sr6jg8+N2jy"
    "8vdJ6CMV7xMkLTuqLyjtetNs1ZmE3kE8Ug8hBCWeX38GcXb3Eyz5/4AChJBj/JIDBIAKpRw4NS49v3nWTAauxVQWqQTG6RhPqK6e"
    "juZUbTzX+TOWS4tNQRuy4MrS7dvMiuNo3rxmCOtvXJJBiTdcxUcMLmEpi2Kx9GPLzbrZrM5di0QklnR1o3aNCBu9YHfRTPeKIPxG"
    "COgRs7xFh2d37qidPFjJKeQOlVYr+hN7zGCABIH2Vd83aqsW6xpbCRO2uWWe8eBS5XTx/gLk1lP16+Vgt0tslLs/xf4PwOAvzu7+"
    "Qj51uYLLybnzQRQAIIcGNFBoQEMLDfChJzzmBIsEV5SRebwyHldnQJ4YolKV/E1xivM30TUw+EZpWgwRutcDC/haJHzXJTzh0HXO"
    "6LJhfnD79hHNKQjpJNHtOiiFCd9Yib7gSNWNg0P0ZssX+/WBiAQVrb1xSp9zpJaFDpQLZhaH7CSKkUDdaUM5jg8tJL5BQ9cZDlsV"
    "QrcUMS7g0Ar5cjH5WN6CXzGq1j9wHOIaIRq/lAmKX2z2UWaUXIWaGTKgtAvAaeXedCxPgVmjKy1tDIpx/X8IK2u5aZanhCqBuigt"
    "rsrWihfzwLcRSTARPEvdq4en5guvP77AtPmBkjn1zPClz7HoO5FtV6xoI6H39GdIEppA8J3d+eCvP/q5CceBKQ5+kIPffvOf57/+"
    "Dyz7nuXMXZ4axUrPntaKgDIlEhNZMaZCOBbLR9OmRHgnbpjawq+qSvPFGvCJNHomu+4V750hpNywCmOEmhxUCv1j9wGCEXL8ofDK"
    "R6s8Aei45rv/eh/dewWE/s57WP59YTyZVQxi1PGneLLvLt12pXq9Pv/2i9dxFs4DWdNf2GwKhcZG6iuVjhaoqCEXikKx3L5t//8O"
    "wuv71Pr8cMNukwDLzTQo1/Bsg7ATi9dnqWqt/eB737MfWl+wk4h9SlbumKwwcjqaiQ7dMhslB6ZqcRMj7Q1MOYQ1TpvReyzlO2pF"
    "cjt0pPKAJiOI8q0b4qi+cQRkL6CcR10ueJoxHzWQ8BmAKjSgBMlw/RgikJvKr5yR6tSL4VWqG1lu5hagEGQiA6YifwvlFAIDpRFP"
    "E7GxY/U2FbVjFDGPr3U0m3NkH71KN6f1Dz9DIaVbkgmhuw43lXYH7KG8SD7EbDI2lVFdSBHGF2KRB2RrOXG4KV8XZs6FbuWszktS"
    "h/nbtyWUQ42nT6j3jSE+nQutaW9LXbVPeIeYTXkpSNLpNo63KMn8fRgmByJTeb1pX91Necdkrs4fL66iWKoP7B3V7GuyadEAZ9Ue"
    "wSSd6Boy/nBFri9an4BYL3DLa63TbEiX3Mb7AI14YKryjxBPbtsQ+sm3EGyD9VpHl1tvI70BbT65Jj+3IC1JqSqjegXdMKUI3L7l"
    "SG6xWBgsurm4igHNHL0jcUlSqCjcD8ldq7ehjkK3Zpx5ZIH2uE0IvTtA1k36G0pV9WY7j/KCRWhjVsThSJGqI/Sq0GOLRbkJoiDw"
    "fUakbRTLmg2TQc1lSu7rMqqVvdVd6QfEgW68GYEsxZA6GB0qcJF/LCATG5l5oDwVPmPLog66dWNjvLhzA717G20rTAe21TAvLKXx"
    "2wvwujBloatAkVDE30L66jC7Tbkixl+0A+Ymeo8JvhrFvIRgGI/AVlLzsgchIKsjXBrKobb4zRrym9M80JPyPaR8Wp1k3Uzgg5Xl"
    "F1c5Hz/6/fnP35WjE7Q3m656Nwo+xP/Jv53/98dy4A4orGr3SM38TK8eE1iNw6tBWdmLdZNdJSlY5kXa9nUOcofkODS6sIsK5ugv"
    "RMS7qgAZOKbC+/oIfci+ttt9/W73l3e7r+321LKog3d7uthtNftIrXBzfONGWBComY0R8ac5bEG5RxqLHqPNNszIOlagMAmtWvNN"
    "tfJoFf7iDvpoUR3tss+xLitqvKoROVXmG4b5Av8AAggDVFbUdR4uL2cK858ultO34EsJ5BmG5dngN0yhBZVDFLrVU7l4kt+k5IsG"
    "0Q2iyHlBNceE5TqvU1+dsqHTNh7J79MlrhEs/uy4b+XdvCih8dWn771JXCNo3mhTc6N+XfUo8oNsHb21qI/i7/BL7p20m0S+qQ2n"
    "ZmarFsLt246F9SyTr/oopHv3pDVnsKTR21cwvJEGacpG7E8evAV6l8MUMp3f+wM6GFx62xp5Tf+WAcKP/xu7YlEE473zR6+cv/RQ"
    "ORiQgzwupiqh05kLSaOgg8uBJcr1qPIRuuGFVH/7+o2L16nK2qys3z5+8Nrje2/iA2BDXODKOVwSrIC13M+w6nnn/N4P9a9+1p8a"
    "4agEdPB6ekcXT3CqvTp58TJXAx/8XAe4989OfiKr1dj6kEMQX1ukiim5BYpKrBxjPPhEPcBQTkeuAd8Hlyz16gGR5x3fH6q+rPZT"
    "5YDmi1dloBiy9eTozVM1Vf0VtVdkL2gvBnvyCtrt8z8Cdrz7+H1j2tKqZRhrfvj43Qe4h8+Ny0Oy5UV9VXRYdcf4Wq2Tz/Bda++u"
    "GG8151B61m/A6Vv4bO09NZHs8wsvKpGxAjb0/OR36PwPVce+kNNT/fCX5vBd2Lgnf3z49P2XFd+xARk+lzEHD3T/8fu/wzCWD7fQ"
    "mT0+9H915VYtbCiN3WLLn7BodoWg+QJuPgcTvs7hKUoUczqMmWIKyanvPn6kO828j+3bVy+/A++LVUSG3rKpBadctDwRmd77z8cf"
    "fHh+5+OlgNXrm7SGAWXr9N6TH3yEYyxQxIg2vp4VKeElK5PGjHFKn2kx2Esm/8l91frWr+w9JWpycUT4Y31ApXqXxTLG6j0W+mzB"
    "JrJgCP3ZiS65WrYzL7+KBAfey+5ZhgAF/VpZFXL9HljkyhmsLAAVddjoZJbDbNGBOgrA1xLysKzRZCTSdFRlemx856UiEK81G2QX"
    "Gl8dKnVM+syAvnzhgn6CIyApx+aKMInvfU+PRdB7bMNYZDLZTfjle3IEYSEK37AnZKnl8jKx9XrlKq/I47oqd2v8rNytsZK7ZdYm"
    "gcGBDRHNIKqbx9dL3vr7o2UXO6Z4QxfH7n2bUrQMNaV4ATilhaYxoWSDV/+kP6t59lmx/tUWRyrdILUZ7JAR6VTUX93yXwFN8mPs"
    "dcZW5PPEolzIQhcMDmRkzF3zRpp6LNxsXjJ5+UZ9xfu80uu8vCjDFTYDdiTK2oFetKnRkkDFlXJkcUMQvt1GvHEDrNIcRiV0C5/4"
    "7LN6dRkxurW0jJzqzl6G/LPo03Cefl045mgp2mobp4CulLwEOOj6P5w/oNC70VP6nu6t0PeUq1hBKVICZ15BNLM4UH32+yNow7tN"
    "N69vDtFLbzL/e7Nm8ctDV+bLXqytFutficsPSjwvLc4g0ayWrSLZt2lkhQsPJ6k4mQ4ODc4wI2YYvKqy2b36VbY6X+iidU51zMiI"
    "d4y9BZarc9uWfCVYvP/o8Tt/ujprUZ869M9Ju+cHsf7K9HHFhWRMIV9zyrkveFtNKLlUtuDw1yXTDZfJuhrxj6a5G2apuxpg7ZJp"
    "OpanKb+QPRbeQ/Fp8OHC10m8srwE+ZIJ3XvbP8MbYzCYdKYzHnzz76IM/bvhFy+4f5ZrYaGvAUQAq3VYgF20m5dmRy6Z87j2sUVx"
    "t2qMQUIMfvl0DQpXeEok+d1RRxfeky4Jq2aOdKrl5T+6hDEs1ZVVZLmFdg61BDOlkfpKc7WszjcNWRIdPYVrjrXcSrfYeEX5Cu8i"
    "qbr7RsiTZpYBqnh4cWXLTeRS1nnJRthphmXsSHXQtkPLfsLNsNp+40CzycbQU9voPmzLPY0XyIM3QNPG+yu2buW+aXx3oVhp75Uf"
    "LSisF7rVBYOg97yvINcnBQONPUWRwX9Qgo6neFt6lzHdnv59WT3g2z3L0j5fd0FjdUFjw4Im/+wFtQ0LEq9a0QFaEnnRS7ymcxP3"
    "LPjFQiiB6YOHujvQXjVEb+NgKwQbEvlvL/a4vI5FBI0uxSgsM4Zngfe59eKOqhH3r9KIsU7cV4XnxnW5GSGnQ8guOyXA9NjyTwjy"
    "vrYuTc1WatNY8UDvAiUX2rQaE3J8eC0dGvE9VXXGchTF7zgxBjxSUl8UJ+pbMgoimaK7cgXX+UyL/NMSVtWcvvtaxovmv5A9MIaQ"
    "6eeC5P+m7t2726jO/fH/z6uQ5+T4q6knih1oD1WqaEES2hyCE3AC7XF9ElkaSROPNOpobMu19VtxAjSQ5KSlXA6XA4UCSUlJ6D0l"
    "UNb6vpQG2/BX38L3uey9Z++Z0cUh7Tm/tSCWRjN79vW5P5/noSEzeU9JkcTsDnthzPhpbk8DqWUA3oREKH6LhcKkmpcwRqe5kRAW"
    "jOSnOEGHhDUZeW0lMivHgKyQgVK4OOOw/YRIDJMRS8TkWbSsjClIysTmbmtKdyw63EUJcaJas4NlX7bMJOXeviOfHwoMkTyzsI2V"
    "IUfmUt0U0e+3b6lkUkZKEAZhYWTmEhMJqMbdyV+DBYnx1JKnyDOvVoErFyfWgFWQoaswN5b0OAbrEaGBZugcYi0W0LA3YmF1/joL"
    "3ZulQGjqPnAS0YQWV8KFmGNTQ6I9OR06j5MPOWMwMsKIRD40Js+aUzyrmD3AVIfEBTg4AziHubnGInsGhBvTlRwHU19Lq8Fa7mg6"
    "5vGinlYqyTkbeBPE/s+Gd4E6LqoquiUEMYi8dqNbjCMTpykQkaKSFoEZYd0oy2kt+5GHholVKsPHt6CSrJer6MSBeFoALWYo75Pv"
    "0Qu5VNyCvFyKPzoVlyxMJf4T18VI1nZJFEpZcjHiy8GKkxQms1aYKxf8oFrx0dJoSUCxm7ppnyztr2J24/kXia1dSiKEXKMnPtcR"
    "PCwuKiPiWmKjqJ+OHaYSTw5HebkO1U4stp0QeHxE9LgZrGIVK4wX9gurzQp5XRjsyipbib0QQ5HI1BCE9p3yaZqmLK4EqVrpQtvY"
    "BoZdc1rw83H2i45rIhvDYGG/gKr0lJVu2NrlA/YUjKjVbZTP/NOZKfpEIbp87V/dB4oPxMG6tEC+MgU/RKbgJyYn87ihnEcbeRnK"
    "R/U/450iLbW0vjhHmBF9gyx3H8qc1Gty3YVvLA2uGfuXjKmSCHQUlnL3/IcYoJ+Vqm8RdLvcDWITYnVNrZ9wjmD7SjXO65Vg92eM"
    "AwuMBB3+FysYd8vqU4EPXlEPMw56+fVHuTpMXNWjXdIadqKSOEyifxNt+a6NjQlREZY+YWzyRKRVHMmOoV30MnHnsyRfuDWH9QB1"
    "aRdnh61z4t04UbxTbVk0jH3LCQfr0F18JU7i1vx1sbmU62E9bw0UokFS2j3MYVaPjGZaFd+UYSMhGlnp7mVAFw6Y03EmlCj28AlN"
    "TNyJYNUNTwTAsDRU/gHzRa3ver4G9+KqLlYlJ61dIMZDwMrMesrWfhAIvrjzPkmBCEO79ZfLPIuokoicbNBrngOilbw1YUvKSDuq"
    "xIfqfp+nETkrQYDGFIHsKCvoMchr7AE3GELCQy23FNFisdmIGPPs5I70On4QumEucXDG2lLcr0H+CvEzByukmdZVgUEv9r8Q34QU"
    "Uu2V5q1CpxOhuw7+dsXfqCW+i7+R+GotOMeWS+vfcyu1jKXSFic3hMS2Y2tm08zP0jrcTnSY5R3nkOv79GYH09L6cflr+foBbErb"
    "GKoEtghuaxfgV9jrS0ZwmzCq9CVtD0tYO5gLDwM1wTrD8cf56QUU2fxSKIpzbWzQJ7fmRej29Erwlg7I+Mhx9/2wMP8fBQpmtzc2"
    "5i2LYkcLUXAMCcGhShcYihOUqppB0sMkOp/AgWmD5Y+258MFfDjWk/8Cm/QdbmvKMnHXZL1CklVpjn8W5+kmU+5o2EJwXm1C/+c6"
    "lSqGyQWrYaVj9cfLU2ZDExwr44CRNBtrCL551BK8Q5GoqYo6JJRISDWVzFJK6YMD8y2JsS72x1QvGFXWIDcMih8LK8dDFFxUGypd"
    "yRzqMG76dcbKfTCcqQPYpCC7fQpXf4LdbbFks9yjXAeV5QlSvZEJgHQKHsI0Tu2coa+F6r3yaQno9zameXr9A3B74EQYrw5HRMtr"
    "YiO8sHLAwx7VOhdJUV46KSo7O5TV/eMg7c+5Wck8iTjU4SJnohzOYAVyODzBLmEJguB4OzadtdPBETA5YV5piV4mLoEYGLCmTGn8"
    "wh2+QVlyKIE4Y4eAcA4/SVL8GccvDRYhfpYBMLSQVYJwDCDo6f44Ab8CUELQiVGGoW7SMhQcRlFGGIbarOcmJpoUbC+RALs7hwPb"
    "ahNycSL83iioRMYgn+xA3kC3BJ4QrR9ezCSBZXpanZmFvoP3JtwwGU7uTMUtBhP6h3u7g8OLKtJMMIz4XIAuR0o6XTZcyrhoymDC"
    "52GI1DtI6v7aXnCj98wDUr3ny5m9p5+G9H4480iO6qaMU7nfA5OCcnphxA/ZSyPlVI1YDZBXpbQ8hqU+Y542L+uqRwzt+Y/fy4+j"
    "/qSmTShR2rSRfjUxZOISlj8OmhigcukTqEdeU3j25fip37wgkFtpUhDsDbNLf4VQvIjDdwlTB85vSku+WZfNjPG/D9vKnKH0xlIa"
    "6IgZMjbXoG2Fo8TY2xcFXNzmJYTwgOOjPMNpU8CopIuEaXNQCHuGgCvSLNJiOq+ptqNFsrFAw5S5CTcTweeaWiny+9kUTeHoN7/4"
    "7M3t9z+6e/4ZTEq++ipBz6F91Qznv7H12W++evtztMj+hICZTJhfXa3ADAQ9Np70D0V0ZH8uYT7F5o2dt9+nzfXGsNyCrFhEjK0T"
    "SEpJAMmsxG/hklKoKHJ1riu82ni+CaNSQRZpWcwJ23atJ4qAP9GVeZ4DC2mb5nYHnjgwnqFdiOFOohQmGWGpJDa/8kRpfcldQ0kj"
    "CitrnM97NljkD53A94vTlKRMTYHUTLVZ3V7VLwIJyYF87DRFHmzoipxn2NvRv0ETFmU9uZj/rPwSdAMqNVz2tV2bc32+WPcr8nf8"
    "+Mhydw1hFXrNkC8udxeL6zIstVPBap/8AyiULcJZ6Lpxp2qht+Li1X7fOdkuqWzbE1hR19DX5czTL6Ag19ze8Xre2rCkcsD2fv5Z"
    "5qi6tjD/65fdqRkMeg6q9LqJifyJAtqPTnCp8hOpUucYSMRdU6Xf1RapU3ln0bW1wtyRY1jUGe0d9F6Rgj0F3ZwSl9CY3AbKTz2a"
    "nMzT31LbOVHAheW9cKKAK1eSk3QC4ZzlL7iMGDFJ/RQBk5hwGsJ+qVRBV0pv41Dr40lQJMlU4ppbus0dikFZ5iMnlKmWegLv/I/z"
    "Z2jTh7192GPO4d6zfkQqp3Z/kgYqr9EXu3/GdrQncRRBuIuHF6jX1EeYvLbsvJi1SE5MWKBthvqlcHNE9voJUZ65TdNND6yjuEi7"
    "cbUSAjVf91eKVM7NQZ9JpPJGF5woiCpwuIA6PIz+4cTc4oyvG+VuTxTwNMblvkdNOKriEWviOPdRSSEaqMmChR5/ojD+bZHHvt7P"
    "mjJp1Rq833mmcXtFDF1mnoZ1nAiHx5lRyLdSdR7UKvhiVpPRhsDuQvMZHQNBhiYnQ1wp8a2EPztRYQmaJ4yxoAUnjx6DswCcn5YS"
    "j4W8AB1CKjbfXijFoG3Jk9TFVAholsF5sDUD3GdycjGvLkka8oCMKMztywEpQL+Tw0uEB0sOM5yczNofTwXkRdOSOLQFxl9ouQ7I"
    "2Y7HD8STphk3WLyTsXtm7eLE+06gMxhfdqJAhDrBqGAz0WVLtuna6s71mkdQCnB+Oj7MYFeAJgRh0Y3zqGmQInOdPGquNOO0NdSP"
    "Nl50yUspbfb7/iP/w0KtexrPvbsRNZdbi124sLgBXHApCjo/BJru2Xv2eYwJEmGcHe2aMOo+7UXNvFU4baUv/n97sHhNTJCbvdgf"
    "LdkHLL6gYPk88CFbM1bhb99//Nj3oqjzpPujZbQjnygALysFTlBAnp63ThyfO2k56jAug4JSqY17HhnKgq5FRAMDPCriVWhMx6Lt"
    "39879/Tek8ESeq1P1/EefkkhaHfCoAH7G9YRZd5KAS+7NbwlaONn5phIQyql9T5RkErp3+aOY7h7COMN8HR0YLDuSbcX2ZIuBHQc"
    "l7twtPZPT5f9fMUuenmcjCO44PAiWviNDet7J0+eyFlT8gHgLvRu+plerj9mfYV11i6nIbEsm7tcWQzCKP0YSJTbH71roA7YPFXt"
    "Wr5tpyWzpz3cubGggK5oES8mbWGZkTeWTpYC5Jb05FV45c+2rr6C0S4X7phJxje/OvcS5dyiEB4/L4l4B/Yb0/e2wtYwm0zkDV9O"
    "5qkmmoyIYzjodQjd2jKQoHzVqWNx9Kk6n6qu92PXAQKLYktp3QPBDz12/HIHqStcYa4VOtVlOtOrzYBFIIfBGrHInC5W4KkmTuSX"
    "pqW/HISMA3VYHZYGoA8LQT2HFkqQLt0uTh2xieVOgdu0F0O3skS9Knil6tSMwz8uh6U6vEm8hHYo0SQ4qZHDQ3L4hhpsZXoGB1Hy"
    "p2r0iCo8VhvwRo/DrKkN9Ly9bk3VJMGy+/5USZ83rf2+JAJ0DabIqZS01nl+WXSVWTqL+TN71uW3/hd3/oj6UrzUl7NgI1/HJ7KZ"
    "ST9u7OADZUuUA8No4f4ZwlUrVpAlZZ0PByM5HCnZBOWYIxWz+FALt6ny2GHcq8uS0oJhhZfslt0n0iTpFVbdxSUv+q4bPdw9Auu/"
    "Vk5fyrOjDriraJ4kLFA3cB/p5wNdbgSwAi1PeLYU8iMFi4GWWJHnhm0UPQrd8YibIGhLeCAxOD/vOQFtDq/gdR+FZ+RQK4L/GSyA"
    "j5NHHaQviHajva9C7wum5Bv7rt91c6L1w17oVlF0jV/hIZYlMMwnmZzzQaoeqAXr1azX150avL5SwAKBR8Rhwmt2fNpy9RyctarN"
    "T/vws+wNAnfY/dUmdV0SnH4/ftLDJ9vqSQ9Rs6T3JOz3QDXJa8JAVnzYiUyt9UQBtUFUWuEPRvAmA8McFD2cEw1qQ260tPpzQIlp"
    "k5OxnLZXXf3OzEPug5OTcRjZ5KTsb9fVwrrYD8YalWi6LwbRbSdj1mxnDfNAutXQW2Q/1nqsTgrtNltGf0zx9wOoPbT5TTpMUFQ6"
    "GIlTKLk+yaai2Uzl/gdJR54N9By7OW/VwkojWEF7F+Zud6wFdSxgXoWwXanVjqwAHT4GGo8LrJhwDw+2MWQJLx/mgpOoCvJebEUJ"
    "T19Daa3z8GjKyQf3r0MXvPoaGhGWXLdzmpYCv3Wqp9mCZ5H6f1oIjZXlKDgNJ2MF74HjH2+ijY11jOsG1UzNuk8+QhfvC/sH4G2Y"
    "8+cPwoBF103YG8vDx+atoegy98XYa/rwwt5TNFmx9dIt8PTFNksYfJSXkxpmevEId+F2LHwgE/mFAFM/t8nBsDvCHPaBACE//+LO"
    "s9eoxnJGHaH7UvQo7D1mFCpzC/F+SA5P2ynZQ4xZpbB0KmgJHKJhkDx/SYDcP3/RLHMn0TteS1ZNQgvlhyhraZbIJA6JbI9aeFlY"
    "KD+De65sX31DAaBkIPDcZ08mb1Qun0BZH2NUjwx7J6rSXu4WxDnMqIHIbc9YydWRJzdMwfvuxurNrW/95v3tj36vFRowgPzZOAvy"
    "eDGOpBhZwJ4ZjEjaAErieitu7W+f/vfAPXNuc7FSXVru4D1Zy5zc/vd5CXfeuLl15eOdl+5sXbg6KF8ydjeJl9S8LgY+Fq2678IB"
    "a1Q6xW+h8ZXLfma9d/BueBTILyXeyC0h6XHGnkAUi5lv7y/MfOuhwnRhZvqHP6RCXD/8IY9CTQJ2qzhj9CixixTRD++lSjGPQt4w"
    "DOsiTFsuEO6i5rHT4EAooC7MLhmFikPUxMLBWBfs/MkqVDz8EFhcrUxWNvqlilznyaRqGhd4YyC81/RpPjPbty8WznYaubvn3szN"
    "PHSa3Zc7fzj/xSfP8XUtn0nhzSQcWtuXf6JqMQiiyR4dLEx1hfRLdISIjqg6Q+jFeWHrvVeEKwW1T6M0ptzFt/TKSpkgsXHo/uZl"
    "8ZSs4zAIiEllQJjINuNW3fzWsNCb3XGyh0FI0TmZEloSmWq802ORZiAzo+nV6y8BF7qsVpux5g06ASuYgZB0W0EDUXEn/Scup5gA"
    "4VZF/Sh3UL1ukyCaRFK8FpmjldCKb75wR/gIr76y9ZdXqdxNvB9Vt/UcRLknzWygTMdZTzrOWtFwx5mugjgoFLYiJWG2IsnkRBRY"
    "LHDCT/Kz+C2GC/4PUDb27Gug3tNHG0mWMiMEYlJZ+ighPynldPH3cAehxROjanfzmTkuquAsQ21q+SvSgallsWRksCQnBa7WvQbc"
    "Cb3STHn0sUshciBEUq1vvA8U4q5fisvMY99jLY3yXZ6YnAx7+Sd9J74LPVTycyHonEZXJKOXrhVaQa3il6wqIqeoNCBlLl7MuwmS"
    "GiOw+zBB8nmax/hxBjDqlebnLTxTljw/tHFV9BgoQA3EFLH0zZm6hTwIMlBG7ljjBtSc8A2vMHjh3U0EWqRSzwrK60NZFhTvJ6Ve"
    "vXYH67Vd3H7zQ3nEOQFFfwK9RnD/9u+ubz+DVP6rO898+fxvSQ7YZPgaeSf1hCRTLGm2desvW5+/qcD8iBQ8o8pkAXHYuvox+fhf"
    "1GKToBWvXcdwU9U61vkTNZSYF1B5xoUFZ42m2GtXA2DiDTHNn7/z1SuXtq4xiKPmxedJ2/xp7KQXGBrwRo6rON12ET9MYQamyRfd"
    "XMEMa6OOocyKhh9hPyR+ZIS8RLSKfDHQczjziSdQSqbDxOuF1N/8ndPUtY6bzYjOms2IO7XW5G1xa0G97nu03UA/E5UWXvmIf2rH"
    "v2z95Vdbtz+GBYiV7OPLoPAVMfOUwtXNEHMVmCiEt5j5RKDJ56eiBOSBiCHO4h43GclXR90iKF9dbJ9x9jsPOA8633S+tUBWvWhg"
    "oGFkxLhQ0yDFRwt9JyLoHDW+xeU47xBTofjcY0wTUo6NjYknfS0TI1/1nHUU+IIuMFjfWfVqrpEpyned7TlksIlfcza2VThuEpm8"
    "XQKqxg4FV8KTO6nyNOsditGn3MriA/2MYjXtgtdoB6HLxtkz/3QGqGoKHx3uqgbe6SV3DeuNCBuQ/kDdqRkPIDmd7zjNVF2c+bPO"
    "qnnnYqWLyUNzJQM4HARaGQHNHo73t154QxSX5toum7cwtU6Ad32G8oVZNYhVsaz8uQe/aTpp5RSUPAGqgoOSycmzshvSWvxIEPhu"
    "pQ0rYMxJqbLLh0HOW+pijgR9iFHBZxFUfLU4W1iVzD+EZ+A7/unHTVHzq7YDZ9iN3By3Q1Jb4hKwFXhd0FE4c09gRodZl4MaUykr"
    "Ihp9Nh2N7shnT9daMUxnvm3W5Igh1ZclCNWyzLRulWa13yeWswCd2as0q7xKtXwGMhGs+IwKeRzt8mrprRn5yuK5Z0RVV3yR7qmi"
    "tNOWxHtXA7IkJJOh/wLnhCa3X3iLUlJlFZtzm5YK5O+jO4BnCwjFLE9/3DDGaoifCXNdfqEyCQLQoN9ELCmnhqeMvEqwKMIJAhTD"
    "QUs3f0Vh9IBcpMHyVBs6h9mvs2Jhy7NyOUv52RErOzmZvYIpfHwRtS1Q8vkZ2M3F+F3zC3Ljyo7YziwlT6n9qCq34JbUfeH/jP7x"
    "+AYsI3BA4vxnipjOLCwICG1Oq4ACDcrGk5Px59jrpV1LxkIU0T8VUxnlv9Vt3t228wCFspEQOYu7bzb20DUJu2xkAbCa38jFykLa"
    "dpv1wN7mkDtTxuT9JgwFifXWQKsAEI6q1voTZQtRE85fEnVddR4tMwZZ6COzn8R4uW4EP57b/PLaL7ff+inaEC69THq1XhpGhisW"
    "e25ZWuIIGRnfab5Qiq6yHdUyaHrSOpDVsiXqBZBYmTmU7ffepNjJm2iEQ+Hrbapn+jHWcz/3OoqSm9fHGsXozNsEJmroD0iE7FGc"
    "rES7viSNt7qnZ7Y0BIsxBeEWJiB32yZYY1vHJOw5jWEIvKGJwNv4Wgi8vSwEXlYEQLSVILyMaUEXdBDeJZgM0UDJhNRyovsJwtvj"
    "bJTEeykQZthrjy+DCAoPk/CKUjM/x9Uvlox77zMmbS+ddsXvlrLCUhKsKNo9Jq3KLv7izgtx8d7zL269/cn2J68IHRNO15sf7rz7"
    "CR2Vm6CqbF1+BYW6K9cJtxwVOHnGNIXUxLZCqaGHGUDrijJTCsANWYfdtEMoU4yLMihrNOxjxUakTxVbxrojv35HK/t6bdhQxGuk"
    "K3YJn19SRN/EGOPnEA/kDheHte4Z5Jc4W9jKn7l77vIeud03Nnj/9RlXgkkcqOJf/uYdkRohbKNEmjZhmt9m5PiscHuqRvDZyxRs"
    "btToPsOiCpMGAanWQEg1dMUOQhlu2HZxkF10IGb7QwnIdurFL9IA+GSobJVG4xhlFkirMXj42C6J9okkZdCpAugy8fHqlQ76ea4H"
    "2oF9lki3M6gbui6YDx09IQG4gbTBR0nlCKf734vJK/ueCvxl2G/71DP71A1Z+4vQ4k4QpPYwx0QvG4S7bx/oCZeEPjLDIdHDI9kb"
    "D3x7qOeKl2b/btbmmM5GwoKfuRb+iLUwOM2dO2T60krTMwUPC0hH9WaBwhppoUPLWy+m0frkxMfqcKa5l/SlnoClIe2YHCmgMmfo"
    "v4r+yQPLAUCUuNBzWFyHaZLaJ3EhGpqBtO2nbQvRGMCBMWSgkFSWh5/RWaeFd62MlGHGqRWjlX4q5bKqQ1FRQQQA+yDL3HQZaN/2"
    "zT9Q/tQNmWR3KSuvJ7vKCb37AZoGTVIx88uuytKIV9M1ZwbkWU1Pz5zm7orjDarpVcYMznyJKgWbWRSHe7m/KACIE70bu1MCYlkg"
    "Q8J/3O5MMQnInHjByOaS/VVFTrA2BkWKsO176+PzmOaHLCyuTMxMUFTCkGUujBs2rwl8c3FuXpCpVJtffvje9s+vENwilqzWolU2"
    "ZcbYTfZXbd18WyWuibTwh0v3UD2K1Y37UzFKCi6o23z1ys+/ev2lr1c0CjMguGTUDJWM+ta0WTGqTTkSp7tu1SC36/H10lQvUyS2"
    "cjvXXrSGpr+SlMjJd9uvnYfhfL2xoGpNkHOqABao7Mnh8E1ZA4p/2e2QRgNTDgHz05Mot65dIuEHw0RgRnbQPHpNOGS5ChSjipHL"
    "IxajMWT9Dyjcnf+Egr/RNbH96vvQApnASG+/9uL2yx9jMWXEUnmedvpV+lfVwLmsshZF+R9OMkwVV0IIQVKOd/7w0+233iSUxSvM"
    "RReGIVBYWKcnCd16X6EowtWunn8LHDYIo9MUaopJG1iQOrnoWfeUeoOUJR32D8OZRVl6TDKF3cv6DrpLQbAGQvOHP21depkW4YZc"
    "qyTCRIpWaEnwPMn/M6AelXZFn0n46q/92E1Onrg8eL5g/Dsv3cFUW4wceI9iPD4lrIbfMazHoeNH4V/Gm6DMixcoLzfGc9h55h1Q"
    "T9H6Iuwx6RkcEeqiDDmcCZwjxCiQrgkxSoSsEDbsR19+QjgFJv+hUyC2vZlWcSuhPAGXeMxdaweRi0fo1Wtbn7279enVPL7PxkA+"
    "UtZITbumzEfO2AigqbAuC+cO7eif0xhe237lJ1sfvQq9nPnyncsE4Yzpx9f48tbHV/kDqBLXv7z24taVF+Bf7NXlT6hWiNDFMdLi"
    "3OVDoIGC7Bp1MRL7aDtyQ7cbcSzIl+/9BOnIZ+/iGF/6M7xKW92XaV0FFrTWt7hMmQ6pD5J9JXQrQm+pBiA9dzuu7x/CTYQJuUyy"
    "K8auq+ZN0jz2Phi/bhEK7NV8vuuX0TGU8pFpyk5c9Cuu7DLwZKvQqkRNvGR0FcznzL+e1qMHzNgqa5d42Rna9ny2F1YFfNFyvU2Y"
    "Cc/dPf8RIXegc9u0ItyUaN+CxfAGQ0DamItxqA/G3iCTioNlr9HxQR40QFAUUX0MHnCdpbjt53+jMESx5pq+k7P2OhqKf/XJzmuf"
    "EXLA5dNUZu3O9qVfb316DUd57qd3z/0sjlm7cIcp0Bd3cGTolZaIuduXgc6/w+cea0Ze3oTPOb2GoTxGogTj1rMXv/oF+jh3Xv5w"
    "6+qfeJX1B8gxxROERhier2f0Omo6DMiNrc9+TnN5i4LaLsUwBS//CV1dYuJvKiwNspM9k4GxnlmEo7UkVGz6kDwxqTIXaVdnwoA8"
    "oEZHFs5/lrJv9Gw1Nsmuokh3jMzXxQenE7TCUPITYRcyZOaSIpFsYybmxKWPUjbm1WxDb6JsgYSao0jT/Q+m2LEWJWGMKoxHhd7g"
    "5MvxWtb749ZXuKhFfn7JObJgj1Ha4gjVbvgadRd6Oa+Kvxiod0j+z78ojIGmxUNskqQVMTVDsftDFGho6N0cbQ3YhfPF6BcbS1a5"
    "8jqOiOKTxrV+0Lj1sglDAfeGdWSIPxc5UHzSkj3LZj/YmSfK96CksoS6S+ZihHtbSWhsrKuahfmECkwcBhp7FK9JaBtR93tQlVmW"
    "pc+f/+ptkjbQk/dqqmiqgoqTQWYYXibrmpp1U3eB9J85aSyUsqtjdJCwtnnX5CkG+rmgEdBde4ZiSR3ET9g6872FREDwEu049etA"
    "f1ADTmDPHizFyBELt+g/OlGp267po132Ct1guZ3S6uT1wZoJj4N20Itf/e73pBIb0eE7l34NaglKAXDPufPH5yiPWj4ErFc89LIW"
    "Vfl1M5W60VJydBHQi7Ws4dEPo8aHRErWXaHiwaq3F03QPI7A/AveJjKT7sNwgu5xgrE3RhR0TyMoQcaQxC/pMem/bmzk6WsVCWnJ"
    "qnQ6lh2r5+cuK6zifblHEWEnBi2+Ko2GIjkrgfvIfsmt27eJbGEW1vZ/Xt96//qgmRCEsFOp1YBcH3PrUXH/AyOzXwwEsaqfXG4a"
    "FcYfLgbohzLwwtaT406tdbygomKe2Mpbzz2LErcp7Ct9l+kjOwvRxUpVymVZ8GFb++83AyU1AzEIbfbmSU0MP7aLmeHh5/726aVc"
    "5t5BPsPoqrsEV/vruTuZLd5KscmbOzff2fnpc7ppgHslI05u0F79pVABzv/h7oVfYK4MybeIjXYxNm/gzSbuIhszMNENhBZh7UOj"
    "+UnCLynUFmHpn6as3C5l7jyTKxyeOz2HGCfwy+OVKufziN0hqhRxBs5rWs6MEWqHGXQxftttZBcKm+3mZVDc6NixCfI1xe8T5y9O"
    "48kqn5AJw4ZzLsOSbu784S3okLTWIIoa00IhEKA54xZLCRh4eOE61Yf/gBSua0ZdoHSVAM5puSkLQmhSBEXtcbcaPd0ynLQGPPOO"
    "ilFKqCvKhIMewM/JYAYcaPMbsHeu58o58l99bmR6DjSqYIBclk3FM8hvMMimMqb0PbbMG7BVhaN0d2tYIQeUPBE37ylB83BHuitl"
    "qN5YonK3aoo19QYo0SDHiaJrqk/6ppEK3tl4plclftw6AXV1XeaS0SP0UTSGNX0yA+usPnqmLS4MQ88xcxXPDQCEpmcqtRXxyMP4"
    "SXb7V7/b+f3HVn+omx4GCpMK3Wt6tRrMyFliTtTheJYmYI5UBUBf2/UEX1wVKqnWKrpkqpWwliUWmudkfuDSYhtt3c47Y6kU9JsZ"
    "lYEXdmNsZasZ+iuMIBUVThP7Y1O1FVQkshHVTsiXHHhjGpFjwEuk0+dFvlyccNjOrLE8yMeu1tGNKp7fTR6G0M1yMS63YNBrZnI3"
    "lY8eUlgKu9YSetPyfXut7tinyXqPKwfh21YS7Pcft7H2CyukQkEVRd3iHfWYBy0U24heGSFgZFS0KC7a+p/q8gOpAunDe0sZBKkc"
    "4vGoQSBkfMOqs9yjdwyHUs9sjohVcswZXcb70CF/78p7OnAEG1x2VqjRvp0fPBFuKFzOVfqk2qwPG26dao2nV3n3PuP5tudYuRXM"
    "bQRF4Ck37MK2cp7Y2Oi55TOIpP3w4cPHDz2Wmzt0/NTJ3Mqe9Uqjn7t74TUyvvwZ4/zQ7GXl/u+fcv/3V7m5I08dmT35vaePHDtm"
    "yPkj8/4fGlZPgwKhDhEMVXb4s4WehQu/JJfRHQEUPESciKOr5ioreiWOjmp9Tmuc5YPsUj0/CHQkKVfGyGLRLMqHK6HppEyJc5g4"
    "KOJIrukAxdZCUbsbc8Tg/sXl7homdVKIhij3h/chjg5oSPEdKipW3ZpDdCFx30IRE/OwIdqg8KuFl/C5zTe3P3qXLjiIvssdKJ/Z"
    "s065tMvtaGNj2qZqLNWK74p0CxtRvnCt96y7hW610j7d6k5wn/Pqwr4Z9wF88lGv59byM/aU1SUQL3wGAR1P431l2jLWVOTltas2"
    "gX0hKKxAscUCf06rGGl5tUs6yCym2iHGbGEORkEpZE+69TxDb4XxhWnbmfcdL516FjiV1MVqqW3EtDdLB5sFrzbVlMVHOeljw8Le"
    "YpgdPX+kXgeazEH2HrUTItobIv6W4MDNVxdsh248VlkLliP9dh5MsxTJBw5MNDc2/I2NJkxpGPg+wU9AJ0AxhV/p29TM5GQ+foNx"
    "p+NhMhDSy1TP0q/CMEF4G2rUQT33pIu4cMcXu2644oYHrWXLTFk/SxiR5l3csj85qbozOWn09WBJ/VKmqSlO+HjL1xuclLvPFgLu"
    "SL5pO9iVswU40NDdNo7ahqn3FzJmAscdmINrls7CD2eVzQizM7tR3qK90Ak6TiEEqtApVBoNy97YqBiZOrWguozMIo1HBWILvBuU"
    "YjiIoovq5tBtBSvusPuh/wH0f6KdKMuUTq3ADWs5oVuH4yJTneolU+o7OOPUSk25EfB4nYXjtdovASFrYsblobzc5lg96Zw1dXZ+"
    "ZmEqv0o1FNHFYU/hpybF8k7BzYR9WeZrjI+K98AP7dOYJdWFn0gclRFxGo/M4TPitikLKAuSiVR1mxRPezRv0TpYTn1yErFwOxV0"
    "izV1kgs/IMmVqcJzzhiiTy2Icjje6YWhBRIylVZdGoinENqZwD7meBqHt9vS262XjeGUB7COoryrDO8cTLXF5GIfQHWMl4ZoMGft"
    "QxfVdarPjv4zJHs210fqCNRCfTPZndLg4YglGm/eScZMC1Hbb34o8s5Qz5bAgxNAGSfq8HKdSNf4d0Xg5G8iO3GudHBOS2bV59aW"
    "YKFnhz+UnzO59MbGnGSztmpjVbUh4UrnnFk48HNT+dl4gRCvdMjcyQ2eQ0LjNNVeZueilGhA5D2KuO/FacMwUkGyFlfZMuqQZsU3"
    "3/zi9rkvP7hmjX9C8s0ydah4tsxSSBFlDHuXh6abODXzGeufsxJKK56gJsmle9abfVDqMo+FkEp3cdxWU0fGoSMTazDstSWizCLg"
    "qARN6vbqWKmZOuXW7u84EwRr0lbVpTOqtcDPura29dwVnhJVInqBa7z5qpHM13eCTkaCn5B+spnFqBRV3MWdQWT5XsnxgGTVwfR3"
    "iKKrDRgp4zB9y9wsSQo6kL+laOpALVCffew/clfsvuCpgxdPt4eIm4WWIqi3wCRCGv5IVNo7E0NyHOtkCtKguwDVQ4mEMM8Rvlwm"
    "es7Lj3tnFqDx4vSBR6LvTCN6zhzQR2g+sh2Q5oMG2hPlFQWxr37Z2MDHytPFtqS0fumgDw0efCSSlDS5u4aYhUmTOxYgvEsl9Cp7"
    "3R4sds2tWUX1RkkPRUztBVivj/WcNqFFoRn+v2QWhBFhoVoqTcSN4vBgvALUZ0CgB+XODtuIi0aIKfcNHwgPTg85+IuVWsOVI2Y3"
    "WjEkPk/hcwKgRsC7aPXkD37722Xr29+esophQpVdzdCrEhpVZGpUSWQR4KVy2YZqOh7WENXUD88UwwNR+KRAw0WxGKlgVPHasA+k"
    "uGeXPVPFiGLlwycdwzP0Cy+lX6gHSsadjs/6xYFAASVUspSeQI21ohQQj6X7iqmAxHSlSZjImFEKpL7tGLSyWYMfQk2gtcdhHbAV"
    "g6x47FYjQcAq4ZLldMNqMao6FT8iGHQKNXvgQafpeo1mBJ+GMkzf4OFtb0iVaUuzA5Ga71QbcXrXE6D7wfYqD1VkdM55P9igtOvl"
    "l9ipQCRrIi/6YqsiqBl5p103I+R9rsN2KWmcFefbq/Jlv0YFvWOSj44f6S0RUUSZTh63sOK5q0YhxtkGbizN4cPp+PT2Y56eSy3S"
    "s+6k8qnuqGqfLO1x+lKmG186dcawgo5J4PxFk8B9yEHAQo4it9JiQGZrGtIj/FlS7GevK2SW7esfUlTBB3c3/4yovxTqjPnWv9vE"
    "aAwhx+6y+9XA7+6i+3KO3yRnqkhUGe74ai5GbQOjYwJ23YRy7mbnWXRXvajaVNMgo81UsG8SC1PF5qgYDM5MY3ykmW/uXHuR0kpu"
    "me5olTS/u+Ci1UeBXOpVHd3Co8ePHTv+tLFx57B6rRmAM1Qki8JKdSkdNZxxI8YbWH17fLaqu+uNc3msQ+QgtSSj5I2TrnbwMBod"
    "E2xB2brIiHQytu0yhhRSTijbZ2Ox4seNAQIDbAV/VwLDc3yeVNTlmDginF6MlFvF4b7GB2v71Xcp0kOCCKo+nxrUZ1rd/bvptfku"
    "S3EGfn7W9PwmPAEIxSj6LMwDhrCGyJSD+glS4i42jcS8WWCGoTD4R0Y4c3wz9faJZU9tlCfKRtoXgzVSAN0Hd8+T+wI97h+Q053Q"
    "WzimH1MJVGLfrS9/eRVVedR6tfLlBIJzD41za0Q6npEJaKrNAQ2KoKNhzUocSi1dR61Rq5MduN3BfDVLKCyGaDqri6aHOnl7DO1A"
    "Via3YOWalS4IVvAvCFW0KLOuWhO3QH+NHVQbvIPa7u6k+SsM4XH3wi3ymN1i+AUrMcC5eIBtkr0Lc2xv29iYIPkkXfsvIlCwkThR"
    "QYfqH4ooys5iRfcxzutSeaiZv9o1WYcc1PaISz44fiksg+YfcmmTccy0QScimTYcYpol0owwvQoEiiKiJC4J56Ry0iqS05uX5b56"
    "O7N2rllW9HYmbPOo+Innrak8m7QP5UPTGu4XuhEZxP1Ci+6Av8ooHgqjeKgZxcPYKI7/a3Pvl0eYPuhd08ojLTZgszZ0/y2lhRVr"
    "APrAIVCBSHzd2IDhioFm+bJRBvvs5xZ5lPyYRY6wqYVjGbDFhDrybukXRPfPKHu2JSuVon8dBhNj0glnx/SwzgYdlNGVgBWDCd6Q"
    "qNGXVWIBh6/87dPXJX28ifdzhM7mH4U0TcgBjP+XBkqIN7RWLDZGBhrHILZkMtC4I/qGMEq8dw5X1uZQstRjX7lYhYA3xTmLZTaG"
    "eNZLk5i49nE9TNDhk0VfaTbX4d+i37cPIOyIOVd3z12GPY3n6IoGisRVoS5aUx7vxSkrN3yqiJV8My47GHgKj9lDtBNPIcp8K4Eo"
    "wxuEjJrhoDSnUDOV9J3QFvUgJjJ21+TkCrCJ5FYbstMSTC+hKqK3NsrbsnvaCohzsN53vBLQnWAJzwRSILcGSmGNHAoB/gKURv4E"
    "FJauV/A6GunlD92wKr861ZJxRjc2AmHYr2xs+PDazhqcNvwYBbUA/+KES5t/fGBh+qgATmm8E39GrSnDtOf2rHv9fXvWYathmTbo"
    "WX/PeoXpgFHKgsAdgDRUOJgg4Fvunr+O0YoXPsW6fBQ+MBZnAg1zGFcaQcrHt19Xh6qWumWO6e+w21tZ4UFZN3YykpVrnkn7Q2lj"
    "JltxyLZiJypUQCJZwcJYhmggr/MalR+HRwt1PwjCvPoFcci/MTM9vc+81y5Oj1wQixy42QJXt+O1jUROumDEpFHQi3Mo7kro+hr2"
    "aKETdBCnllt9pO2sd6oRmj+d0LH+xULO8aNlF9ngtH1wRjhFbwL9fwH5kP7r3hmbmQ5yHEOAOzRIgDMkN65ui1WnEVBfnvCE1zEo"
    "HQxir2NguCqBAhCR0G/Vf8d3PmEn/bRSiMQKr5SrOBAXRQtNvMb4nXEAsZF0nSjfzoUQfiHDl1+OeaeWhmyNjMkarMXJyOg4HPle"
    "EiVNuX64dO5YbSy76SlqDxthud1tevVo8Px5RL5hWc6YQKaXgVyJ883sb4Df8iLFqX5IEyrAVJRhJ5MVnokBhc9ZI6ckNcmJCdn6"
    "z7e33vgFJXp8juo56P48FTWcCti0BPQPQuDASUnPia+mZM/6oXwgPXPFHE4J+6vMQcDrAvE6LEEd+/17rp3c1yP38xBY2EFYWDKp"
    "/h++odWe+8dPL9XMDYCCHEgEiVuzmObpgXyFUpLXznHRvbJ+udBxw5bXxcBRqmjNhTSs8mhiM9hsJqf/N1tXb3396a91nHTO74vc"
    "ujbxxaGjantuzSrn9VFlAFENG9OFV9C7J4IxEmPCPKdDzTBoubl9uSO1hpsjIktQTBcuyn14LTez/18L01i1in4/d1m0TvmIcrqS"
    "+U2Yj4iJptfZuSj9D7cEHLGBqSK2IOyFabsolAXQD0eM+qtXfvvlB9ckvpqwQQNbxjN28f2dG7e237zBiQjCtnjhjhySwMyROGqq"
    "bAwjuMlEs1S+ltnRkavCJitcgF+RseqPhEgyaKlucGGSOLVc23XJReKM0GdGdnHkaRgBNf0/S5LQ1nQaQxVr4zFCXZDAqT53WXpx"
    "qPTLhV8LQQKdKO+yKwX2sKoEg8/d1qUMThw0KoxJ7ZFKHcbm0dyAVH8ZyP7dh08eYenB1PTfVrmDqaRKGkGS+4oJ1yAH8OX6W3Jm"
    "j43zmHrHdUY6ginafh4W+8a/Hz2BGY6/eZnW4rUY+AaTPv+L0cIYFcyoubV5Q3MC6hLaTbW4W5/CI1d2/vja3c3/TGAXOKBiyA07"
    "RPJJrzfLPZUsuafyD5B7pITCHY/Z55jcsyK4Z0XnnpUR3NNXLBLZaBG0URKOUANVNZzFHfmoRCW6oscRoSFwKhgjUJ43Mk4d/DtV"
    "gTEsFCngN132dbHSbmP0gKHIyovhAIN1WLYqvhtGVoxKMp7tOiLLB9t6Yz3n4XsIvqcLmXHyEsp2rVAnf+Jj7pqArRUBIdoPJc32"
    "3Sj1CpgD3Ttepzh8Z6m0p5LvqbriDduRXxpTM7YtPoP6Nj+94BwpLZWxKLcKwgb9LkQ7GZWyftj389Y/k0M6V+i63XlCSsfiSAuW"
    "vcC28ZOlgyepqFjXxULdPlrJl4RZ/Mjk5PeD/BGK/U3GbMdZW7Se+A7OWtKJNFzIsT9cRXH7pUN5t7D4I7aErrrhIXhzXlZgAaVw"
    "YiIPXJqyONZOyQ+zeCDQRuVUSmsYsOJUS9+v0P5z6iXPE7W5a1iSnN/TwY9KHRWVlgUiEwbM1ycn62qS68YS2BOlEuGsG6E8S6VK"
    "lO/ZMOWwOnqxaKHAHi0dPIrlojFby5qc7MLN0IZD10BdXfTh5fQF+mwfqJVqGAgC8hnMr3jDSYrNgYOl1Qs/ilhzR+Q+PVU65cpm"
    "bDYyHjiJLqH8KXtj4yRideZPOdAp52ShgZ9t5tRHbawRMwE3eD927XWY345A+nFbnYiKQYfFnhN6xYZKRuibncBddhLfC4uwUOgG"
    "YZQ/Ftlxx/iFR3kdum7p1AEfqC186LqqrIpbOngI/uXem8vvtav+cs3t5n3bRgclrX5WA/D4chsrrKvbZpO3/Qgm2IFdNDk5ARdF"
    "fPfkpBwyvJ0Q8Kl4+VEa+ErxqLNC2AtLhRX/YGm6fFRVZFipqotnQ7GmdvFUON/4l1OhjOV1usuL8jYsIWTmKZR70iFhOXUsnHXK"
    "aXSLXaytqs5Fs+R7+ZrtnC015Th6XS0Wuyk/zpVW2WYVIpRL/izZqVbt4rQzqz1aOthTEd3yyVbidzGP8uflUkf7eSJv0d5ARaln"
    "I0Q1nCdc24dRtYLdFCjWNFG1191ivF16VKme58COLzfwsnF0oJUGbobJySOwV3FnN3hvAK2CrQVvmj6wCH1cyrn9ZJDyLunPOAFo"
    "iwmP4mAbXxw6ESSKKJN7Scpt6bhw1uHh97OOtc9yVofGdQNL7IQYC7o6OXkWyPJqmQskYrA68MAfu2GQYb6VRsE5aHoOjYLJDOGM"
    "0eS6VeFWXTzUMUHFTcNkljg6O077yzKG4FTbaJ+rYnz54ZUBjbdGAObX/WHJo8kkTY/si3vjXM39/d1gpuXqi2IUGDObGW9CkrAZ"
    "saZ0EENfOernVxxK0cs0FXPgr6h+I3FWnF30kOrx7aaLosQORluxMxouvv4LoTfiLvgdIW+Qhrl5IxVWzOOZHhyt4vuVTtfNrucz"
    "cHm7biWsNgfa0/nXdH0bmoEfyarUjJ9oQCFKf/ud9Exsv/fmzu/ftRysEnwoaHWwZFeRk15lWOPij0ycJrxSSmBjq1hqPUJL+skW"
    "2U/mPJz0tMkfBaCI5oFJ4vf+9bmf5r648wL7aBMe3K/O/fbLdy6LaEKO22LXrOqIDPlcNGM+7xXSavE4sms9hI74tzFLj2FFSr6t"
    "lxFJF1MCrrD79XG2qFOzyU7NZnZqdnCnVL0t0alRW3bRdxvDuEhqCMlgyRyV0Y0LUbNrMTMFaHRbDZGQlii7e4+tCT9qymV1j821"
    "kZsZ03yPDYkyv/FAd974/ZCk/aBTqXog9ha+lYXLlW5ddlOvS5yBd59s/V8dpDyH3WoQkhkW44uB+0RNkIAaTcssEBMXNLbuaQpY"
    "mLOMk4S0/JWPd/77nIFVlung9XSHrKU4QBYc3nWBkSaLwQm8ewmZZoSkHkbAi8DvFpcdksOepLywdmUFP4RDkojobopndpR8l0or"
    "Sxj4O/EHNIXA8dZE2PJQuBECY+RCYvgRAWiFhiDxJqy9e1eqFsr98Junif4ZWyg1mpWmlUakT93VHsTnFpfhqjh3A5dwpW3kXeEI"
    "ZOaYgQufzrswK+INzM6iqYzvwxeMEyOh30foCiYSRHbp48tZJa/QqOdaU7w2MpLsCEGq9BzWXGCSip5z+OEfzBUD5+ThYtUBVeIx"
    "UFpBEiqu9IHIo34hn33cBy5YDWJJQsXx/eq3hC2NIO3GuSDZIAb1Pv+MgaZ2/kWsJIGx6GkDuv5O8ZasFNbUwLW3I3SSgFb7TFQ3"
    "G1AAR5SsyESHk1l0yg52pJeHGXS1GWzzDEY4g6E+g37fVjFTa05QcguhU0G7CBlkQAGH9ZU6ZKN0sJFUMetZ9yTV1FqGGYR0R35W"
    "9mAJbSGB0BgP1MgKslTgztobGzUyhsgLznoFuj+/4Kx4lAmIoV1LFDAGvxfpLjghNbJhqEYK8AzbDBp2P9WXRtfm+7VuqCfhNfLJ"
    "2B6FdjrTgpJvOEux8fBIiRts2M5J8XFJhQeHXv4IdfgkFc/d2NjjwgV4n3OS1GVMsEQVPdHPTjxdsnFU3qPYID4RbmzQVEyUSqFt"
    "Y3qah3Yl2acjYkZsNAc2NRtKw4mKR2AjNY2xNApRobt3Cf+1FdDGv1cQkWGVFnYOOsEEGlZf9okLApN56uCMMydtDbO6pbQ1/vCW"
    "aAFkRWR1gft5xDkJ/aTpQ2vcSSYJqGTLaUCL0myJ90fL9HVlZAbXui7ozHS3aAIIIma/RQGK+bpGdCi/xJWRLSG3X/6JdBy+iqbf"
    "VBuDnIAs+auIhqkGWs1omcRi2mpPBdLU1Tgwx2PRDI4TbVjTNlxxjsJ4K/HJPOyWDh52k+f3VOkkdg/vo8LOeJeH7oBuE0kEnUH1"
    "vsOumNmuG28iZ9ktnZW7vBqV9D4foDrWo6Yb7rcc6IaFxmrLOYWfsANAvZdd+NKN9lpTWLA5sgVHpxuLR3SUARN+IJlrO3FSMIJD"
    "+bxYkwnYHpVCjcyAdGmKKiVTvHQ1sqfOpLCDr+1ZP1mWyntR03n76PMxdOenItiUE7QONvwAU3k4WG0XcXbX8zyN6Lc/giVHrI2N"
    "+EqO6kLD905IWc6HOV4hbzt6kxn5vFl5h013xcrOZhBQAUNT0HXpoxrpIWuE5X3Ydc62Yyzv45m5bGfbQ2NP6ZzFZyD313Of5FAk"
    "OgSt40GAF2AfE/vzsEKQsoe03UHkjhhqQlNtoMWj46Qvy+BrTY0VZd3iPh9VU/h011lHwatIvcXL7rAA7ygjbXMJdPiIrMiizdUO"
    "6iDFZdfRW6YqhNA4HQncNL634lr0vVONGPFKjg5th/pbySCKxkS+mclNl8gNEFHJKvpMXaWT5UjpoH6K8ydAQgtBHGtgtQVFHY4w"
    "cbD7fcFjgTvOScK0TJbqdg1ZhKAWgr/GI0CT9NC72mj2wdp0DXQ71Iwb3G5GUGWvNKeFQBNwQLiWb7bTMD7jqBB0SBPag1tYqfbH"
    "MUWvNMeyWH99jUHSOegZ+j9sXYWQ16CN6v06ARhDrM/yRHuMFLRq3aiycYYjDhSicdqGt2e9V44NnooGa1cUMT6TtGLOORM9O5MO"
    "QpvCLGvYM2VOXXd5cQgwiW+ZUwt3D0WB7I5T9lAYTdJUhUVldf1sJ3m9PjyhpNppfO0g5rosgVrWPeQNwf6XWW4flfPVDlb9HJ33"
    "EUhVIkVj6IY3Eusfzi/jAjQQt8yggpkT0g5NtwXFVFvOI36eGrDj7J3iSuZ4V8Yf78ihbv/6nd2Mc2U4npE5tMU2jKhLsNJvUjDL"
    "+bub12mg5HRsVXoYlACCYeT5NtUUeV5LXSo2DUjeQQtKFrV0XL85yDd/zUJy8nhv3hIWOEJCwIVbGN+6gXqb7GJrbFuHJx3NE/zp"
    "VBk9fVs/f8ew0IrbTqnbZss6MbyVVO0TdoaUYn4CFPMQFPMGIsauy1TJtVQ8ioNx97C7UiwN9AzL8UqNbr6N8RNRoRZWVl1QKyYm"
    "osLckWMYVQR/yIoGHNMF3iwvkZcW0cE4YqGEQffo2K52yiq1p1M6iBfmO/DcgljwUGFDdIT/HGEv1V19p0O2G+o3/etUSx5xa9wS"
    "48COfxelnpTBUhmQ1Vb4LsgyaMqggqeMhksvqoVBZzcvCg04qWxL7eCX7XJU5rkwDc7qZU8E9LJhLx/6xgnCKnK7yH2lbDw56WHg"
    "ijCkSz6WOdda6oTYt6l+VbJ7Jq76sEcqXD5TXZvt8J3t4n7mGnXYrnNOrXQo73NGav7fKvPeAm5peyovRlA+wwCu4mtfLxnAv+yB"
    "WynohaBY6Ul0r5yOxLPCIb9n/bgb/2Tc3PHFnVr+Fr0Sf+pvvfGWupegX2XD22+eg3Vj0CLZvLhBa571a/mEdIVj6/xLfGfdx+NX"
    "V6F6Z/6JawEWc2em6Lo4kYfynfnpBTuO9NvkbN2pfF0rFYLBTyIemvBrzvwTGg4xpvhGQotl4emMjmaZin0LDLzU7wcx3qmE/Ew9"
    "EmnRcEx5SCtocziI1lo+SsTNOUb7aRkKfQRhIrAQTjDbBTxHzizKP5ZwmiConEXQOFHCmGF2zJa2BkuaFkKU6b2a+NawikwvB1oa"
    "WICtKZkTFqwJy+ZQI/wOzQDQQf2/k1T/O6b230kr/z9w81qDGer/CmuK3lAhomVIrIRAp0/eKG1A89KIvTwMLqWR0BH4zpO+E3NA"
    "gzd+n8CqXYF2dbQdBU957mp+fRF29RJCG1RCQjXhiI/4goq3apdUzCSIZ0d8Fz8+sna0lhfOJttIelNIBa6GpYt6HjBZ10G8AWjl"
    "EYzIAmJ6iOC5niTILGDOA19UdWlJMepxTfFmv+xhGCwBeO2l7Neuy1Bfe2f2F8NCiABX8JEY+oCXHgj4toNeuS2mCAsRTZVIhqu6"
    "np8Xd+z17CJGctWj74T0Z2pmP2wq/am92lPqnr38kK0tyWH0I6Cvz419fW3p64uUBBOWsuHTaDwGlNrGRhLVuFIahoT2IKL3yZg7"
    "DlGLYdeioNHw3TxBiFdsZ6JitgxSyMAVrI+xgjVtBescn9cC+lvlWXa0Ja3rS2oX5R0daRw/4GUE8fJWUyYWBWSZw3DBQZvgrNgE"
    "VV60B+HQnuWlru3FLx3Ed843VfQvvIPYK6JsZvVhhWBwjV40M2Z4xQPdtUPkM267EUQBNW6nGscQ5RNAwqBlmduvlhn333dK+7Me"
    "mSXzTvYjUwlAPWPX7N3fP5DG9AsHIowPhPjjRLNptTeZF25s5INS6EJ/u9HDba9Frn8Qw1quYJYlYAoIpYd0uVSDK7VCNQp9IPro"
    "tUoBdpMCA1SG9lRlsZuvFWquH1V+YB9MXvo+8IMhBwTOtTFJJdmSU0vxEOhcPd25ih+JTy03qoiPIub54TAMVrFdkB7Ni0/iLrSy"
    "BkfhO46szuQw4oPzz/JUbWysFVpBjbK20l10/HxNssL45eW9M8UZO8Yy9zJAzHkOgA446x3Yvd6KW5yY7mOaSPre1aZLmHnarTNw"
    "K+cOZtwfErQiJTEMgVGHbjMoep1hFte9bPh01VPsXOYdsn+qS5l3ZfUq80atY30tZt9TpyHQKHalFJSTB5Mp1QH4gfv+yFp+HWlO"
    "0ftGvlKuDCJWhVUGs9xffGB62nYW3WZlxUOAgm4rwNp1/XhFB0deAa8R4SL0KQlCPNLO2F7R0a6IJinsPqzorUyOt//26cW/PvdT"
    "KtXxaSoU0sfsjGxPCjpZjllDwzGQyMqoF/FZs15I9oasDiV+fWF8D843uchxZTKiyKulIPbEe4Ynvoa+WNPbNw5sLbMEKf4CjUcj"
    "SNru7ZHdW9qaPWFXRnyUzds71+5sXXo5gVHLQ6ppe61Tqk1Osgt9EHsUGS3EljSeBvTBE0ECwPOQOPHOPBmInakZtjqCOZPcU9O/"
    "zHwre1dmB5CRV0qOc2iEdxWWd3KyAp2EP2wA0D3GFYoTry4YJttxpO46OWt44Pp+G3f3E3tVJv1fv5Pa/S8O3P3DNn/aynWM0rAw"
    "/areUzC1btLElcLvnY+c0EDs5dSsATy8M1qEI97e0Xl7U/H2s8zbT7B2mm9OTcFOiSUfFKMskP4aDXS5IO9c5QeaJW1vNZEqNFF/"
    "i59kGqw/3HfmSrOcojSbZnnQJWf4884E9RLhgyzKlryx9acPNLDUa3F0tyzJpkcIWc6D7gMqBajVg07gUToZVtrduhvahajptvNP"
    "e3aBcYpapYPwIi6miVFQmMwpM0qxZcznLOasqZYBZRQT804Gc8TB8KI4Z21n0B2+SwWPVgfdgWa7OcFdO9nMLvmigTfp7xpwE7+u"
    "36fsq9QupDXZ2JAIU2FvXxRW1rqWmE9Q9ENQ5OmaLaeWHkQKM09PL8TceJyqXjIyGpmgKwLh0UhmOS3YSl7HR5mHjnrYe1RFOapM"
    "CQ7NjWOlO1rBHaTCHSnLkeENs3kWiB+dLR3Mr+O14lngv37xbAFJIAi7BzpGfHzJspynvXyTCtJmdLltdJm7eXhgN1fdxSUvYuNl"
    "EK5hntV96Dm3+qTrVxCJ50QFUTrGGQ8W+EBiwgcxU2rhAYmEpRhGb7A7MOwlfRKGU85rY9j7LosLWDK0HeN6R5AFCkfXCAm5hv5C"
    "ydq3EjjCBDpikpkYV+7n9N+12IZ8/kXoxd3Nn5Fd/bLCj8hOd9H5zI+CgcCWHX+5y5HQWbCKolSj8E5G6PFIY+xlLECTPElG+bmT"
    "Qac4s78/2jWJaAcEhHB769n3NbQDLrMg5gLnFOEbfo0G7M0bVHL8lwq3D9FTN2+adW2XjaSIiENtOk4zDrSxfC9zHwwGGRIDFEDq"
    "+7/l1IN2NAfaA4y08M2+wet/4ALVQu8R0EXyGBnxA+Ka7pZiozRH7pDtllLR4ek2fEoY7y1nDzRBxntnolNwezD/3SESUKW16IaG"
    "o+LcuczYYkSDwhz9S4kIY6wzYSvI1gNS+z/ZzqP3zEuPhpxsKGtXcSuWHnNB5GN80TpKc/lqIk8YhFOgRtJ+68kpq5Wq5VNuvurI"
    "K5mgpPdMOCghZpzSLb3mWNiNYS8yHWKm3y3zCTM2PUiHkvG4DFdtXZ3GYYxujU3ZjW6+bic8YvVE5HtWx3Rs/lp5vkYxnzVOrXYw"
    "hri7IFWkR4IA5IC2rXla7MSORsSEAVkhmHNYnOmPh2f9d6Bz/NyPTTDqrDo3PZZlKqiNeBJlWF4dJ4vWa4zkUpZkBGZV9gt3kgi4"
    "F54XMEMXXh1ac6a7bCDbn5p7JIU5Q4CoWnsys/H88ccQdgWpMcN1/DzGe7kR8yaixCLzRVaolAH2GIoP3I0JfAqI9zVRs3jwjCUw"
    "9YdtEMK9URCoFbVTnuwNmHPG2KUZwel9XpbDfkVkEJA7myT3c9k8N+NluC1dVQYRTYzVpYGblCQ4WnN9qaVcsKt3tsd+J6V5xm81"
    "61DzW7OK+grqSknXCRX2OJ0c9cAj+NVhCU9celwvbH+SviTBvx9Z1iBHkK8cOFFY7pTz+C9I/VgVtgRS+YlCrxlOTtKfQmURo9Zt"
    "u+hOTmr6Q1XUkF1HhlN0mQsT+8AYF/zbTyoSqhvHUeUGCRVfGyd04DficylcTC8GxPQGImFm8JPERA4p/TKz62izMeuzaeBNtzVB"
    "8wUOUfMKHtlXPJQ//vbp6xZZbWCT6VtjDDr9yLKOVH37o+2P3jXS4GROfuAYFpswR+7KocTB368PZ49YC8R82kcSklwQ7P9F6JFj"
    "/QuZZLzCajOYKJVoiwoEWgkgiAo5DhTuSIfBxlDUcqOeACa3SBqNi3gsXTS3oHE/XG5bGWjuiKKT2kIapmoMpkrVepdALEITfjVo"
    "tbzIKota9VmSm0FbMTa7OISuGWttOWHpMHS70A5W8zZW9d0L3ZhGHPiDM+U9onv7lLVmBvGSp6x9VO33/x87PSLETFfsaFfb0e7f"
    "cUe3v/6OdhM72jV3dFvuaF/iqfvxFlUkbbEHynsRFHOkazD4iglXlBXIhHdp4QAYktuSS41Vk90wLOtPIzaWjjBHya9f3L7CwItF"
    "PbYJ1nPGwVHBH2gGdvqKV3ODYrtAf50VxNfCb9Dmxgb8WocP+L2uLsg76ANequAtsGO99lIX0Qzxr1MNPIyuC7zyDPyGkAUYVwV/"
    "nHZQZb7ZLoiPDJvdhgMXdJfwfrRVJDCxHtExsU6QQcppswaUMrhawmbqjqzm28N2xkgxjZrjVMzpGaugLI9EEWSBLGGBcdnIIzPB"
    "RD/dAs4pelDwbyJgddlPqQiIhaZvG3pqoKqtHu0U/BW9BCZ8RapJ0GVSjeWjz6hmfbQutroNqYYWNZrqIywWHowOigVUBgOjRlDx"
    "3NiYgHEikDlixsFHQvpsN0AvlcMXCgzoLBMnQI+u+uScR1MmhvBWSxVV4ZUH1Jlqkt7tTKMmW9Ge98tSET9NnSjKr1r25mMUSYdq"
    "8BiEM7EzBhPOqDkyLNoU1t827CpKCripTCy6KaU7aqPNm1sp21ohKdfCfVEClRDsKapMRQ04fi5cWzerFoBMyKZpKRO2dZmwzTKh"
    "g2mw5OvmjSCDTuBr6HY5vo6brYWqFkEHnQkdZcD/ZqIWgcHFhHqnzFigKv3qk7j8kil0Rzg+fQnl9cWgtqZfl5MvNG9lz03tZuds"
    "aeAWdeZKefwxgajOGHAzUpOHS0VuS7vJmS3NsXiU3NJRaKydLCdsZWzWqBZvBFGvcLqfoneDEE0kislEM7Ex2MrdgllpJRBMymJ6"
    "ai5i2IgZKoqL6LMSc7YWQ9VoO5O6OygecH5urLokhsXgUH4unmMbpZQFcpPOGluilrEfspIVvU6uuteaArUpfgV80e09qREs60NQ"
    "xsUhY44yTBmLoNnVi6BdOWfNMGmMB1YeU67LI4BQf3qFwwcMDdhI9UcbAd+z8/xFNHzEJogvPv/vrY/+Szc17Hx2E6Tg7atvENSA"
    "KAQkXvXcs1s3/4x25fPPD6wIpBvvtKBmq59aCHO3PpjerYO9yWHLyNnSSALL5++9QrVi/i5EDnZ1Fxku/F1QpM48Bmkq10Iq1xpI"
    "5ZJETgBScGv81ckULDSv/b3KFiNEC5IahNDgBOUh3DajwGo3UWgn7D0O03sy0DwdPYoeKz64H8iVqLVjuNfIdan5wjJKiiRK01hG"
    "ksO1O7AVGNk34TVicc7J1zBqIwNzU1rTMZaRI87EFrBFrj9P4h6Xo6idJgdESz6S3Tm+1fBjJJJrEl4Mp8PNZmlYQ/c3iqgReeoH"
    "zkHaE6ec85mnY+TZAA0hgn7Kd8aViyznAaxE9AMpvTnRAP6frEVkbV18P+42BfQw1piWiDL+Zhxg9MyRWTmeTZB6K1IWMyKHNEHm"
    "qUAzl7F1YdjMkLRwGkTsYoasjRRkueYW0YPM9GShP7BOdlxCsl42SKyq9CrEIdMFa5HGO8T8AUJmZagAWo0T8hwxgiSEmiLHCUv4"
    "24kKuoJpnX+Ruvezu5uvoxR3blOCP4nKdpn9lD7OAeXARok4YtIz5ZwOLTH9Xuok5B1dkEHH4mU2fsA00NcrmTWCeSSixyyhjkqO"
    "bQeRa6J+DmbzmAfrYIm3HBYpMLaCZNyK7WOGYILtx9mVsUHuaK+0HixhHd2Yv4sMRAdlkEoVpszYdvLXLnVflxQsBxXHovXFZ5/v"
    "vHSdDGVor7BUJSp4aAlkaGUCOqBMBY+bpgI4daY1IGERpMpfDlZ6xDdOkXkF/sXWKX0iWJrilCrsPv4AfR2lP5K7KkQ8kKhstRtw"
    "nIKl8WqNN2sDzHBRjDEen+KofGbPetingvS3RNnGc5t71iNxKV6JrPCnLLc+C3Ox+IeQIMUzkhjo5eRel28+/+IQyqCdOHzsjO5V"
    "MYME5nVdKu873shYgQwgjlx3L9d01KAtevN4YQFrq3WjYU7XuplXBHJZN6JyjCjGDPHv68I73csRjoQDXfcrDY3W7WIcgVGKkHPq"
    "rPG7z6+2xy11hlQpzhk+RyefXolxMOYaqlq9+ILTeE7ubYBU4u7eh2j99dxL1tjDM0/ChyjrxxW+E5rPpbhKxaBJgdNmhMvosRop"
    "59pJnSDlTxQwXseQFtvkQUQ6pNR417D+DYv7GRni83NNBropXC2/eX/7o98PjNdxFf78QwIlpw1Cl1HENq6X6JfyoaqXGCpKid+T"
    "ZDKxOyj1NOrKWJt2oVOlxHD+6hN3wgqCsskyYhnp7APrGcofCbwI5fdQlGIMYzt5d5yonHkKy3nzQyajwB7zoVbUMZSFHxeE/dNp"
    "m2c7OxQE2xRbhrk+P8VsnxkoirMc25Mwef/Y5GP4XFfavKPSWuHRDLbGtuWaF9qjLZzUIEOdjhNd4y/u8rAyMLARllbU7UoGbCCG"
    "bcvDRiftGr9h56U7WxeuJmImYBtMT59WJ7NwttPIqSJHW89e4Ie4nI1EMhMQoVqsH1ksJI0TwuT552P5UMVLulyl5H/BlCb3rOiZ"
    "HhYWlihwUCAnsD6BF2LcBPpUjgpe5La6RppFa2lycqJWqNG/nbj0AdnFeNf7CgMxHwoaJpLuanpMe6FFGXsHhAnUJuaL+HoUhewT"
    "8EhH1ICAV9laVBvv9Ef4DJcYmtMJSlw2t0ZStrwBQxKkaK2Vze2UUtonPjFUx6IaCzWqqUtR20ht1MHFujXiqt3nMmBJuQZkJJJe"
    "JX+4TJA+18jArEtTF7ktNvxyUiOhrj3wzenpYWqtPugZpws0oI8Al2pS5Mh5ams2rg3u3Y7CU4Q76l7YypvDigf03iuq9s/dc+f/"
    "abBMh+cmt2edoRIPGfn8fSzHtPX8C1+99p5eC1wDZri1/ceLenUnLot0xrZHL2szvazL7bEWtotWUVjZM7FIE49WSMJ71psigr6W"
    "NbDUIjVxkZojFwlTKSW4JGh8bgu4VeSaxy5YYi5LXxga1yZE0qzbJ+j+A2PSoq9Fhsbor7bv8KDL7o+RoQUqEpYE6GBNYEQ6DEFw"
    "rxUQlMDOsr2iCaVTrqg3FAP4yElMbDjolM8M37Jiw+fFCRHtMA3TVlqeB22fjt7CcPzleeJOyUZGGSHO6H5Y0/dabS4xhqDsKogK"
    "snXbQXOPrzBbte1R5YWw1RINs1/VF3N4acB8V7Dsi0A229XcjjerZwYaqeTAach4Fsby6QyQN3gA9fiE0RTqndNlQKyOJ0j4ddaG"
    "v/zwypfo5uBagBgXz+IFGlCUzQsk1b9h7fqkQCPbMj0sXKVNIDUrTGQJYv6ZboVRGFZM6pVw+O8BCIdIG08UlruLhVrorbjdUj5F"
    "IfkHWABxi6Berm0+OL/gLAJ9Mn0MiVcudvGxmB630/R4MQxWu24Zi16XrKkjLjxAkYTwIrrWpj+OvIIRk3SNEin5KkklcJH+imtd"
    "V/mDRf/bSH3bZn+VkS3R7ydFUGEq/2xce3aqE0ZXYeq0EYICwrOCC+Tocyz2Ckg0M5OTfA/MqH7H/PQC1wt3RHZ5yYIfrdh6qIb0"
    "aLJCHIup9BCGcuBjmeYueh1oDxTiyVb+9G0CCEO0xwKYqhpikPZ81ePcl6DrFkNn1atR8tZoRPma38iFPfg3g0E19xsK7FgBwppV"
    "qZN4k9utmjZRGWxIQWhZOjMWOc9OqZCJIRS4kRWXfVM3qOmhfkqw4lhsMqli7s1AX+jQUh61UEfEnW+bW6ysviPN82MWkJXmWyPF"
    "u4ISIv/FMMow6j7tRU2g57QfmUfbu6lIZKYKwEYXTQ0NBveJNo+o2WSklxTQVO9Q+B2Fc1whb4NfqIeuS1Yqv+CedavRaCzPOKH+"
    "5vNbz16n5cOFk/7gbCewVFpSlJDeaiE2Q9Qs8thJBPXQPghyv2gcC+Doni4kZI4HEtbQ1ci3FbFpx1SorZMoKaZ6SO88U0zVCJQ6"
    "1ikgOeoaK8GOeLE9OOwB5ETFejugKCFYv/Vgp5ebNqqJ0Fl+h6rRfpg61NnpT8rkQyf950iezz8PjHb7jd9vv/IxMFoz8WxoWNNY"
    "+zVe4BHzxD2w7rHxePf46d3TgXtrHtUstQ/44ngqniGWQ6ywjyvsDwwPSOYZsD2E/dcLhJzFrQ+kNdXl0KQ1zK7HOVEJEiAftY1q"
    "UT/LfXEblvt2huEjJshtMWR7KKKmYQ7lR8rigCSCKccO8JKPJygpR1f9fQKp6ByTFC9ppnIyegTIkgim4vsxbErcL1oQYSWyETcd"
    "TDUilspHQ2J5GKmH3zHcd5fEPk6CQS8LieNo/VRfBgVdTVCHhjhiVPCVrwdf+bsJvuIxW1YRuYgRhTXqyeM41S3bIJgEBDsEy9XQ"
    "u5F/JVLDrjEJHrcJOkg3Dao6OG16aPHCIIjGMh2MsvHyTsR5RE9l/E04DqFv2y+89cXtj85ItsPy3LDkO0zN27x7/hoDQVoDa2mp"
    "VPy4qOJD/SGgO3ILh9qEanDcCUqpPajKGKIfSCtUT7nRibTBc5vp3L944DIvL4E5E5ImkRk94rU6QaiiRyLdACZkWAc73WW6jUWh"
    "DBYmKqSnujSCqZm5fhPxsmZh5fgEbkD3LBy4H0PxzTHI/f0LzkOn5ExNBlfxE7prTkYsrLml9RCDyywqtwNCFHA7zJU9kNAhf0So"
    "jlKLWivMMQbjxsaEWepL0y7NokjXlNoxpApSrHJKUEdy9oQlZBVY2wdUO4wwaTessluMyjxJxTWGTF5TkMkbG6JXqFF6NbKhrrmY"
    "M5xhIYCrXRhit0wuA9LaQ9umUgR0fbCYITsLTcMklkJnjRJ6DAdEWM7QpaR3ca8R3GxZsd4L3KyTpfh+L1Uafb7tRMnsD2c+dHzj"
    "Ivcsu0C6L391Iny478wLzdfhgS0g71SqNfUsQ2n2qER7gEkG/Bjm3w/RozG7QQmD3ES91BbVxml31Wkz6YcT62nFrocPBkffSZSq"
    "dBSeECt531A/HRbKirxBlLuAv8IGorLh5XBjQ13BlSJ/SR2k00qeYva++OzN7Ys/1ZUZzOWrE2gPnHgEc54D7cR4MR9uET/ZZ3s5"
    "b7YaDr2WCOwbbHmo7M7iYEhoFqJhfmv/dKfnzExP/4tt9UdaJIYltceEc7gdQiQTJiHkU4FgHNum3PeJl8Ks676lQXne7GQZmvvW"
    "gAXZnwUiYlSi9BL1w8cCQhhUHQJooS7zy1hfjnUVW0RJvnXCG6gPCueVHUMxvT4ofraO0MOaUlGXdQgd/MU2tYtUpxNLhV0ffmSS"
    "A+Mg5sochoVxh/RDZQzVHzxS8c7hAzVHOSRAuG5rEuruxbtgcjIAPaNDteStVD2EmyNKCGZXGry588bvCcb+hr69rWFLY9LIjLrL"
    "er1lsQ44Qi6m/GhQXe6i3ZJnr21WZP7iL5eKuemZ/ae33/ojyOiycExGFWZ9BaPUCsbo2fDzet0Ez56crCYqMifpR6LM8v/54Q9z"
    "+3LF3Ddy5ZyV+07uYG4DAzk15wGF+p07/3/uXc6/76J1RRc9EaTvl1QVB3bNjXEkTrFw3w1i+biqaz/EghJynpIcTqUkhyRy30AU"
    "+ScbosSEgn5XnxViY6c0bRQzUYWYsNMCyU/PSEagnJy6rsVArnjuKu4LxvpO2mWwtVrTrdTG0s4ia5AdSAYZW+Nl/BHw4mFitspO"
    "qhdmP9KtGnCLnc7QLLxdlFkXMLPYAS6rxxhsces9WZ4sf0yHudDmC59js87IPN96d7XSSd33GCNsgOwGAnbZVWI24e+7cVWSorXX"
    "stPhf4/pOw+zllFQRICBR9lrw+aQIyGWP4lGpSwnwda0x1VqMXQIFRPZVM8t4/6WohHWeTUttcjnv608pdniDWvqpiPFgG+89NW5"
    "13fefn9QaWZ0tKoDzoZNBNv57wFO5ZvZpZyRhQh8Hq7pLN2yEs0m+YrsrwPKTEujsQkrZohs0sKiB42KKGst7U3YrcXUXLiz9Zu3"
    "ts9do+hLLHPO03EiWHXDE8CPIx4iFXKnuNPNm5w8Lj1HWOCdrdwSwG/X2yQ7HT0OGUvpaI6PmkwkUMO8UhxABpKNPznpx2wfi3ln"
    "bJmLBHCRnC4cR5G97Mzk07+G87KE9d6ZBQLfNyLVGqWDEw2KUWsUWkuMKCyzxEWl1yms6YnBmpgnXk39rsA04GuhJe+rZ7yoISr2"
    "iVo0lnxpnFO+3j8QqBC4BsKSzzcKGMb6xZ1XrIVS3vhKoaQz/bjybrsQdLH9Va9tla0jvY4fhMAQivJ6q1KF6496bbSXFvXMGk6B"
    "aJZOV8QiOZFEbTtbgvXBUIwkxBsNiMUOdfNqqV62qkFnDYdXPFtudPNnufACmcstLDxjCThLZw6eCzB0MOhQcLw5VW6b7EE2mlFm"
    "4c6W2wrw7U4rc2YrtlGed4+bbxQ6sCAd23aW1ROiHG9+falYa9AdsPawIYuNvm02UMefl6CBJRH7Qm/xsBpj1uu1VXw4gcDi9EpP"
    "lL1ePrLTGCtDFJ1MAWu8conVcLm1OEZdPfRMy9rpTqipYaFhU6GQbZ4V2ApLsN6VKO/bhRX41hwSEl3tugMh0gRG8hDP7IpAejYR"
    "ts+GcoM2B6al6UUhD+UbzEGh+8X70NWUb79hi9Z1Ybs5Y97kDTePV6qR4YcWx4n0vt2AA64aydqEDXjWlIiSO2BeAaVbOZ1yWkNU"
    "1z35ilkqM6tdi+tCsVMzZznH3XyVcUgRbKW6hDY9+kC1qIY1JCpXURP6M9mtteV+1HPVDSlDq25lOeoxx9p64y1kPdRt821YzipO"
    "OOTA5VF1JQUJ1F/911ev5vTSkft23v1k6+brW3959u7mO6KOpANHSq0gVwXyHbWKT8hfAhAhHy1GwzZVck+pZyvq2TaXxkJdRK+Y"
    "NfFEPDIlxJPIfhx+t7QQPo0fx6LdnvVOP66nZeLaVVPcJfvIoWKNMDEo04mWsgH0qFuHYLJNH0cVqQT5zBh3mvyIaPz82d3zfyaZ"
    "UiyDES7BINp4X/wziFlX0qluiOswgFhgXxgaJPkuGsHxRYzkAOYWhZ6LgZUG01man1nY24B/BNGdh8sL9pCIm9hH2dA61CCIrCUg"
    "Sw17qIsbpwjrRhmpXpHuHJ+IFCBtJlXKMP0l0hUyvUK3dq7+ZevN63IP3RgYq8HB3yDzUtIpl5mTUvrbW1dvfXnhM5CFhUXSIXki"
    "Xj7OM0+K1yJm1Mi0wqcZbcuZHQclGRTyLE7cfCDDj88bA8UXsTEwYkWpFt1WxfdH2YOF7RaG8hwaOmBfXbgIs1OIepGS5KHjGqMG"
    "iQRkv8HpXtidvXhLYqnuwBrA3uHHgSieQ5k6xy+6KJSk8y/uvLm58/L7TBB1xpr5mrFEltZI2KNDKK7Zg9kSdLl8HKW+FsPTLlDR"
    "WyFqDyzT2lrMJco+Ir/5/B2Yb9x+RsjdZeAMd89fZQ1UKoyvxqG1wBsanEHDdXaHzH7yrfOkUWVn1b6Oy0HNjqx4KW19oZt8n/au"
    "RgENlxsbw7VXPa/qohZMoKlWfa4rHIXL7ergitDpGf7q5T/R2UPt9KtzL9HWhmFf06ZUHc7XpAFOSlhz9+94GoRiyIHkHQHrL1Ki"
    "GUbg/PNf/uTDrUsv40ol2YnyntwwsqYTMZnDw4/clURJ3zmphgjrz1KpwRiV5aPtefFxYQikttF2NVdzR6d7Nlg9gF4u6RCByKZQ"
    "nwyWQJ2Ef9QFhA4s07/qEq59mf4tWgIFRvVD3oMAm5raqKOmLM1Pq12fiW4Y65aMVcxwmSbNN8u33i/AahAyGllCRpL7/I/LHLvi"
    "/o2Y+8PZ9moym9Rp3ceDFxurcmytGnb6Lr2889IdCtv5kOz7t+DzoeNH4V8+gF+d20TyDDdolsKdZ97ZeuHPluy6ODkC4hi0JS8C"
    "lR/5gy30CCpA073XMSaHiOrPl5//DG10JLJYuznoqjOJtGn96MM6kRGC7THyxgem7TGwJOD0I0tZxsKw48FIRBmY6Pnl0FlfAhKB"
    "wLaiwHzHH2IOwPtyS3tHqWTcDuljO2/cjDWuMeFhSQSgLPBc3nJ+UJHfbIsFglW40z3dhRF13NqQ4L/VriEUbL65/dG7LISlVjRB"
    "T2J7b19nut3lVqsSrvGOzC+pnbaxAV1snxarOW0fhEWMd18C1GKJZbwjzsk4zuNoqdGZPwKS7wJsBsx3x/8WnFMlvEZmvwA9P/DN"
    "r53GsCohnZzBqtHxVbuf++tzL+b4oiwlzZ/EA+qHDKzgcZEagk4uAG3lKFB+oUgend+/4FiV0KvsZewevhIDbgAHMFLZjhJLGIrr"
    "oGONyVmAz+ii3diQF9jTcVpcH168/BAMnWNQUbMaD7IVZpOocg4T9Y8UokCEpR6RFHa8dk4RKT6J96c2yu6RMuAgj48FGusD5pv3"
    "PjANw0I4hYXYPWpyi68tmunGqLi/Se6g2a8I3WGFQB242yB9cb4c7OkViecgPITLiQDuNMWror80HQikIr213YYwM1k4mOxYXU+3"
    "kR3t3TTZHim8GpVJ/L5z/eZX77yV/F3QIBTwH/a9BtxHpXGNrIm75/9AiKWfDG6czXbbr76//dr5IV144Y/bz1Is61waAzBxbyyR"
    "6HasY8uF78EkCYOUcapTofPLGeKvEQYonTzOkeQvXL/mJMnL5X9vkLDMkrIDxLOA+TwP78W/35l5aHp6BPTpo3lyF1kU+dYgkAOr"
    "tRQGq/jN9O+U6ZNVPDk5ebRsNX0008AtWGM+4whkBc+bnlUs0Fh8aGrpG2YYFfSnbP31lds5Ep2BwNiiX8OxRHLqXJFc/QOcl9YS"
    "MBGWsIWZTz+IGDDIyXIX39t+5SOWS/mMUcr79+MmrD7bZLRE5+tSs7u1/fLHum9Tz9y1ZHOE6N4QwA+yiEUPZhfWdtyRCYWBkKil"
    "O3rntU9Az0zg9Oy/u/neF3feJ1uUgVWKtis0NV0mfRR0wI+hv1t/uczTIMBPn31fpu5RxDCH2evCg7xf3Wkly3KYmQm0oBZaNJbK"
    "Q7MTMhPtx0CTbegJDY3dJDSIru2BpekOeSgynzEtM9mDPjnEng5CazcCwm+h7HASZYe0K1Xpj/rZOomhcHiyy7AppiIvj59F6YcB"
    "dEtPumkCy5vrVKoEhrcaVjo6IWW3MWvlp9DiVoWNif/OnwJOuCBWLqw66yTXFE+xMu1gFSd1F/av1W3oV2aAl+InlnvtBL085ALV"
    "QnrpkArDjLcj+e6Q5I5MjjbY15/IvtuvR2QNSy7JMGqYldYe2N9PRLQcXc6vr1BNgxhGr97iIuTtjNjoqDSPiFHtqALKa+jIYgNY"
    "EKDmBbATvnr7d1u//BgWXFxyEHEvo8CVCF9EUEmbwPlWYiNGsLeGsqi4RpYLvIiytLy43Eb7B6Lx7YVZshDMRm9h67krOy+9LdV5"
    "zPRX9uqt964lm/7yg80vf/XB1nOvJZrf+uzdrU+vfnH7yvZ//SfiaFKjxx8Devu9wv5vPbjzEdYhTInjGe5UmFFT7aKGidBGQGMR"
    "/kxAZemWINWAlsfik+9otbk2XrzuqGiZUM/vgVYTMJBP90qwdUJX4U8m03eIYhNtwFWA48R1AdCmmlkAzxFru+BUFrvIcYgjfHnu"
    "WZFxjTYUDLehao947Rrisw1dTIpWU83CviYJ9grBjl68e+EWscBb0l2GL6DbcTNhpC4aYfQntv/z/Z0/vo4Gx8+fhX0R36vBUvq+"
    "PDQU9SWry7itRbdm2SO3g1lIbH62DW0I6LStt2G+NtleSZVWUD+CP5R2JUqTYA0AqQqKhT267HCHFrRiI0/35rGQDvJw0k633nvl"
    "qwvXlSUnHtmBr9PjAVu2jYxCC22Tc8QTbpXdQoUOGtEIC/1G1C2R7PY7piJoTDSvs0HKKqYel6OKH5RXxCNKG3RFMC+WGWLUGQyi"
    "fmmIammOpU0qcMbEizPz+HLJLR0keF849gjUDX8KVJYjWLLwreZ+mZycoFvkLxPaL7h++B3PoGXHG/CJXt51EMhPwfi5TIgpSMeH"
    "b+3T9F1YD9T3oow0IQLvi706Lwx9WGQdxU9LmG0dfHhBZcXMlg6Gko63SgdbPL4Wjw8GNKvCcIKSlydKjDFd8JHoLMZvwWckrRii"
    "pZqCZmcTI9eisobdNjmZnxWyiCA8ML/yChAYxEoRDXVK88CdzmSQEiLFoKYG/TNYkPCMYgZwrQLXqviYxgjgchUug/hxJt5jF38C"
    "oir8UuufGcTq7l64Y2FxbVijmrDTVzY2qhsb9TLPjxSWz8ZjfnwZw7r0KZh4fDk/a4P0VJIr+Z3SzHQ5ZNvUrNNSeO4oqqwUZ/tw"
    "aYTn6uzwh53VLMusCxKA303wOQQ6xUCGIqbTnY2xs08GjQaIIbMYTD8rg+nxxgwYd2Gr08VT2VL5zNbLV7965zJJ+rR4tG1h3mUX"
    "+9tv/hp9h4pTI24g+7YQ2AmB3P6MANkxJ08++/yZPo546IyI4q3Jw9N0zjBDhA75/T3rHQqotKY6UxbHSlqwb4auxJzjHwxVEsrY"
    "9Di2Ffl7Q2WU4anI9BvzCPhcf7eH9EqJfxITUIGXyojIPBVnQtNnmzLaQxtzExEJMCQkwDYBRoUCCTCSyFbtBRFOIZ4+s2cd2EeI"
    "MGyvI7rxzrUXz8QQTucsW+Ozxzt5dBYo6TSVIDgxg7IjMANHFCwfqnm5uubloubleCVkCB0KxQ1TFb0yInvaFWuMDDUT+tkf01rq"
    "xbVlM5xtIZUSW5B1p0LpXv9f2OVYvCx4bVgsEtTTYVlhQVzTw0bIzUta+w3hnopbiV1XMjTpUgzcK7F++SmO7IL9LxIUTKcx38OH"
    "UtZY+0gBaYjIbITCHQkUas7u/N95ejPLwyWcliNc26DwGktAwQ1kNNKEx6A0DyJGSCLGAu82od+JDypHmu9HHsXXBaeaKx2cSzPr"
    "uRSznsti1gcCpiHzQpm0nFXBMAWHjMksHIrT9GIh6KjvRbOjQI1X2TydYtmr0jwNxFk+JH16D06LYLA5ZzbBCeb6cMlekFJfBfkx"
    "lssjCaxawo7Qd61jXFZPVVdAESiIQLQjgE8xZpQHJLdDreQqyb0/o6r3seCenIbqKMZSScFArzpzQ4Pb0iL/aizyrxaWQ3+hD01g"
    "LOpD98Sqqnsfih0ZTl118Jv3o4MqnCDhgSGFx9DETaUoj2NjICp2WqLOsCokFhiwFVhTcywAFAcvT4YQLU8WCrTVwNOXvBav96Hj"
    "R1EtW6KnWbWu3etszMN0LPB8CMDqVQo+UoDVuHo4Cn4px4eoTg+GezerYHMwwNbFX+288cLOG7e3rl6haAE4W7+kcIhbVAEENPDb"
    "lCL46c5Hz2OeEAMmDsaJkljR17787acSyVlQ+a1f/H7rp1jIYvu9NwnZyqB+IrYnzssIqVQlzbcE0IXDCOzkdOS1gAh1y4ra6CEN"
    "akbiQ9ZRcuJbr58Zd4K+28ujgXABEzGyX0Ob5QzjS2S+C6eDIioIuHbchYE1R8s/bs+3aWMSNDaV4CDQysukWb8cpyphf/4sFe3n"
    "Zeovh8TcUpzzq3O/1UOprNFDyz4HTaSQsmbovOAxVDXUVq1lxJQ4zAIthHXTemvtZlrEWC68Ssgin5J54TnaoyLbGdkERnp+yDuY"
    "nClX5ALp06Unx9HMaEGEvAtdv+vmYGzNFMOUSMLmXmQkZlR156cXMP0GNb2mrv+tkvANrOfA0HmaU6FZzDiTm7mZ3sxj0pVmbLov"
    "79oEmUWS0XBnvmKOEgpvGSFG6N/5UIUupqefkVqSi8CqDsVRGq0ZG1lhs9p9Wq/hG3DIpj5bwhouyMlqbhdnFr81vVoNQ/vlJ6XL"
    "onD632+xfpZjrUjcYsciyYH/LQLoiHiFs/dWdDOg/b46FhqbHs6kvXlVs8dleHJX0tEBJEuvGka91fn92Mjq/AMLHFCBrdrKsxMD"
    "53bSqeecA0zVnDl0TJxWxJiL8j4nXYgcPlvGi9mFEO4Ou/AJk+zC0sREG5NBTFCOlGXWyEX3gwbmnqeT0f0xC4V3mjm/ORq2VUT+"
    "AyM///FussyPBQ2RZ25gSbkF6B+msyCyegYa49hZ5iOSzM1ZiOS5iyQAoEL8PF1JrtJYgXwW3C7j+KxaJars9YDS+gXGOonH68vc"
    "DaQVoAX9wE2+zlnTp0RCJaXnZOzwwBGBeoRvF2k+ZA4n9GU4of81wgm33/jcEg2Y4YOZnfISdZooUIALNe0mWFDitp1/l9j6h1rI"
    "4I0v//AnEhDfFrGDWZGFQmfGl7qhOyT+dNU4Lt6Qbq3UgigjgVKsvEf147peXrxy+KY2UQ1VMKODmdtohh2cAFCLUoWw8AEKaPML"
    "wDs4hpVUjMCpaCpGxpbHIQai/Ki1aoKtUwgM6BhkAUCfSjGHN3O2Q1DAF1m6ZQb1jwpoj+Hgvod+ou84c6dlzixBM1LQ22CbVjJ1"
    "fn7Qq7xqYGWXYfXaCOipx2gkazIh9LPMjbqVhMVB4pWdrLd5Ax7auvyKVqnqukJEIL1GAiEsSC7E9OqpdgnzTbFcU1CpIWjfTArj"
    "7uRyXod3dxPoYUFnXzeqNNCl9FQbLTDsJ4Qmn8K8RGxVL9zBSF7rKRT5qJv0QlFr6H8iPI2245XWC4VC2Efxnuw87QD2TT0I88LO"
    "lAvqOZGWRwUQPNv25oMFYRXCuycng4kSpcHjDzR0q0ZpblG3aCZ79+0DUdmb9/muKOOGIgOp5vAmh4fuZdUnCQZNmIBbc2VlEgwo"
    "ifpyGgOaRi8xcfnAXuffQ/UL1UblaKjNmxzLh+qZKMOcnYSA4QJTQQJJTcx8VMKlgONLL5oX879Qpg7lH0P0/nIaRSAqHYwEikAb"
    "fm8tncaZxfg6nGCq+qMW+ykD+kSgJg4qxBh0QCJ6TFZ5pSiyDIh6WArYMxYGb4AI9P/ae/MuR67rTvB/fQoUiuIBmIEobIlEIpVM"
    "UyVSK7V0yQtdzBYDQACISgABRgQykQQxh5JsHdqWR9OS2z6yNWOr3a2W3d1Wz3gZHUlufxdJRcl/+SvMvfct8d6LF4FAVsnHfwyT"
    "lQlEvH296+8G8OkMcoy9W95GfmHXIA1ecmjigS8FBQU56MG7786JWYI7/Tqu4akoFCiYE+19gR44v4Wzl2IXUc/XcZ1nS0WeAio+"
    "L/wvEHMJXu4sEi+WjsJNKv/dd4fzWsLeYLRAVHsKRUq62le42sO6jIHz677Ig0gPMwQD+7R/e+YRh/cEGuiReuUJ3M3+7eAJA+qj"
    "ZO+++yRjYwmjTIyrAdyFbAqZSMBIQWb47SSDV5MalQODFcAKfoy3j0f6mycw7PCIcUArceaMCPjTY/hXFKZEDX0cBbUVFUzFQ0Mw"
    "VvOLL87cBPjZxI0bM/w9aMIbipJMNg0zpnyH4ZcaJhpqqp2VPnOeMDQJCqnsPGERkMWETc4jMihYVS/USQ0Gv+VRyEkHzjCxFOAx"
    "pJ1c/LZXG2kTm8g4zTUaZDaDCfyFXY2BsjRt2DaCUwWX4GBOwxng79fDMdrRCIzNwchJ5oOx2JlvbM4fvBm/VLsYvDnetpz2bnAB"
    "H9o7ePa48b/97L3v/OyrP/np+9/86Xvf+ul7f3R5BI/1dO/yrx98+ytpGU/f/9pF/WJvEZY8dXj7wJlEmsoPVWA4GdkYCakWMCHm"
    "hAXoq72xQbloXX6HHm7bzu7B1Hj87x+/GX/p8uhd9ucFfF9FraGi4vutjYrGCi3BgHgP/n3t8SuN3/Ya71xCXx6/edO4fKmOhbjA"
    "918e1dyj+gsPXH/jj2pL2cbkYrsMBwmydbRREmTpBvhMYFwuxaRcJdh/rNqMui12kmps8dtaE32kmqCN/NbiO8J3Ryu8QEVr7t2r"
    "LQlc7Hoy9MaoKPX4Xyn0oui0dagsUaKzwSMcIQr5yd2LwoUP59jLEffXY6YUKUf6cQrlIucJz/AIHbHxd3VAbb+okpIHrWbg9TQk"
    "UxN+2F9U4Tt/Mw4iiq9wj4dvpU/wHBEf0I0Q31YHm5iKhC9+cO2jbEnYgfLRfXtzvhVvBUDkBz98v+pATYQN/fR//Ql9ZyUOqsza"
    "6xdIm/Oi0Ifrr1lOChYcRgM00mNehpAR+kYlEezQN6s751P2OikiMVXL6pCV40mJMQr5Vz0gKJJw7Mg0G2hEj2LPGSKw8FX+A8op"
    "+8HpwzTorh5kNNM5wppiWEpAKX6bgWY//QYiMH7wt9//4He+gfYMKDTXIGNZa2lUPvjJH/3zd7/O3KbF8KRr+RM+wu+gQp2tmJqP"
    "awqXAKwJ5jJKs4zXm3+eTnLd8ZkfD/+e8obXU4NqB5YOge8+Gm4G1WalWWl14f8q9zJi8i1YM0m0tgVWHAXRiEmOIPcJJLilPzBC"
    "vaoDi3Iu8IviJAqvkM3yolqjMW2IltXFq99kkLAt91gFciViYAtL5PWu262cuK1Kz21X+u5p5dTtVY7dzt1r4U8+Eyz9kQcTAaTE"
    "cqw+RRsH8ZiJJWlM2d78NzegLE5m2dE8qXSvO26vdDG9nOFKC7c1/NQ9pabjH9Z2oxplWImE/dcf1ROzZdiOet4S7PAl2OJL8ASW"
    "YNs+L/cniEv63FbdHJZximv7fEZn7+B0c6dNNGsVhdMIKKl/e/tBtOyALdFx26903H4F/1FDKyeVVtPt/7Y5DGnZ6gLGC/zf3DCg"
    "QKfRKTsIi06lBWu70T+soEvFkeZfaWnum31ua5W/Az/mxTMvihBKtw1XSruqxCb49JLg4z2foPYugIl8993PJbU68J/si8pojwMj"
    "PgEqFxCmz4P31z6JUgiVHwM1pBGliJQ9ovC+MlpD4iZh4s0vCCVxMg9DhGbCA+mlVrP5gL+tD4TXHVAGBAcB/E9VBcuqVI/mR9UP"
    "A1UDxNB8tyOjdzEisjJi96GZkuMHpnt+8ZthjSTivr0a7sUlYF+qR1jy8DbxY3IaekF+RWP3+lEtSI3ggzr0Nq6y55CMxkK+ntR0"
    "0c8RDOSnX/3NhkhI5VFXBLVbT1vH1gCOQkrsMRyLs9TeerS6cB9/egnMsOBAoovoXFh50yd/HCRILGGZaNSRiDAd6NkgnCd2A0or"
    "zOMu8mZBJEQWgZePUNWUnpTiyeCTy8cRejUB23OFKt8gkU+hrc1LyKa/UnA7dilL8aVNbTvVfIJwsQq+mYRGARp2Yeclw7OUrLYY"
    "UAWq1uoNPQ41lLQlceKJEpo+cZm3AHT1XuuCejvg444tQEP36IJ6x9QMuN7mJjzKXMM5wd/ykYKYwkaE/9GjE1QDQ2k2gvUVcJUD"
    "x3BEA98/hcWL9WNQhXRY67p7/f70OycRvtzpjLygsaCPLwlzGPjQVLhEYTIwrohgHJdMhDNP3Zy2yeBhLao7Yr2sBs3dYC5kKMpb"
    "FLatBi1YKukzZnG2GnR2KcMNPELCGNwLXhvaKHLMkC//DTOar2r11QeUBRuEjO81fiBAbiN7JXXJcq6E9QK0yT0mwBBkprVczFDQ"
    "MO4zqoZ8nPnWstqU/GY+HxGdlTy64SWaJWTzkL+FpWtVYzgh6SgMtIRkkZVJhXZMeis0axs9vUS7MwUUprDBGAsBhPOV7wtgWr1f"
    "Pkl39G6R0q+C9tWEHnIloB9XgzZ5q5F2CdZnHaVsqA9wAvRjE/B77E3krhpzF9oYuQF8CJTV71/TeeQsvM1ged6W51JyTvsCg+pI"
    "68Elwh2Lr8t6KchX5jwRyBAM2bNqmlS5ihdOlMC9UqNVJDsHftVTuXMxOqVWVJWhwLGzZC6agcVpTiOKnu2oKuvRPPUm8fkW4x5V"
    "WTiDwb3m7kxVABHa5KMkhO77KOj9ZOIvatUp3pExBhU+82E3T2IKLOQ78AFLgWNXKn/kbARzVDWc32vWt9n0S6p0eaFVF2eqQ3JA"
    "S8LCtZuNEnVngwctr3WZnJC+Mr9VYWxlc1+9x9uKS5ikxvPzl+dcCcL6kx5wKKQTaXw3YSGxKXH9gquoiI+ql0i4RFxNTIj3c6pC"
    "u87ak6Cm5SwTuQBVetIT6wbqCm9oYDHsAOzx2hfXTkuJ5EQgWXPfi2SCAMMhSVMlMli5hh3Crs5MlKXiMAqiHSEGMZzUeKwnVPSK"
    "gIZo9xEnPGqHg8S+F/mewyOo1PnU4HSFMnxGDBwsDOY2Qsxr1gIndFcRmdV8zJ9463mSUhw7EbaLFMyjJJp/2r/Fjws/8fhHb57A"
    "J1GZsNTOBNlC/ZcL5874ImH6B5zLTy7H/qY2gmHkDbxNwwPUB42W1vZlFavjXz5brWeb7Xx0heowJ0mNAkMzcIj38jmcHfciW/YE"
    "g25iGx3WxsfeJekqmEo1W+YrwFrfYIwStWX08NdXMMbZGs6Eqkdiqjcd9hEOIj4uEubDO7LVdNGCcUENDW/i6PLFF9/wjXaPqN1K"
    "EKhxOFrjkYxxL1/FJn0GkvlLIDWrkHCMBaM6BxeeTMrOi/zUBSg4r7ETBp1rudHNiy9W41l4g/ZCWX+0+NrZvo6KXjhcJehvbW59"
    "Wl14gXncs0cplQusWxmzSc+owHff5gHFuNBmzROEy9f95XpQCxxmvzGvbTeDwLkdhM504CmoBCO1xBLZLossK6Y5phXMaAJG089D"
    "7V5ecB7ogz/5LzkRI3g87WyIISFv/7owxv2PqWG4anKRg1IKVTN+01bp1zk1J0JcSFsMpqb/57/4GiT4+Q+hrr9NTTPQsFQLDViB"
    "CipI+/6P70Fj9RpkqSy8OO9MTlRPFuRLReWZXpMZrbJq86xZprrlG0s2XFHkE7K4kXlnfE14CSIBUAC2Gi0Gjn6h2T7CAYY2BpL4"
    "WoqzkthCoFvuBUL9xGiy9BSFl0Dp+XgKBLT7pS0I8nBw6l0AA3PUuhywTNn094REl/m+sXNyXt+iCQqdLcAEsuOQpUL7Co59nIlk"
    "9cF33iP/MrH2UvuK99lcM8URcegpWiSpWLpKqETmQL3Nr+gHT3/3+0+/9V29TIZP01HKEV2YK8e5A6dm+lCZgxhI4deBFMZNvFQI"
    "4Vsa8Ec4mmh8gW6NQH/A8bj2SRaj6jhN92T+HW66e7fL2qgutaA1/wIoM8axorgEbuPzh4jm5LF4h3BX0PXvcxwErgw/F1YRMD0r"
    "KM8BihHIUqAllaGLGP55PaVRJxmbGygPxYje7WCELnmiFJrb975ePRodVUlxZ8zT+9UjDJVGna8fVSvo+8pjk/3YhhbL59Vh1YeB"
    "tNuhqI0Tw+BmZ9qGejEwesYGZI9KWG9Ob2zoZcEChZ5xNBokIwdoGKTqWYjDdtPhUC7tZp5J2udf+djHPvfw05WPv/LFV4sB58i4"
    "nzEfERLUavQqebzYxB81XBeacIakKOlTJnshcQueOcG+4FDTGEjV0Sz3QmFvs8Hg0M73beiDEhNOi/gmTvofm7vzK9/84D9/5xd/"
    "95+s0d9Y8LjEfTuNA4dLHR6cj7RQcCga4ObLaUw4TDoyiFoSlbyNtk4ihyNLGs7XEVr7EpP/dmEw9o00dWWtJ7jZ30GPB2vsLhad"
    "Xq93Z7dz3Ej4IB9hJ8jOKoPPlJ02TJe5amIJu1RllzyJY36foYyK0aU60vH1HH01wAYgyMMBbwuyxiOUH1wPRmTdjVU34AzgA7KO"
    "4aS5qP78x78PVVYhDWvAHmBJOu8u3CS8evddOKiokLyFn4R0HmniPFEfv6nrxaG4pzPdE9KIQulIhJeUn+VzwOHxecOWXnb3xMzm"
    "nX1KndwJQkSUxcdQnreSUx0xG7QxrG71Sn8CN8KT9EpfnY/Fm00sgTVm5xPB4jKVK/szmGgc8gX7kz4ldvgi1felViTm+WrZB0jC"
    "QzeXF3yXjZiBXjVcSlN8HIcBPdd2A1wivLNs2TyErwwExjx4PuGjSfysyP9lqdplT+AGrReethr25sqBu9gZp6KcIoxdDa0ezo2L"
    "IaxbtKmrH9FfARJb/el736oe8ZeID/Sz977DojHrs1Ekn6IE6jL95/f+n19+9+som3YmyHeJuiof/A16bVaP6OlR9en7XxNhHPRZ"
    "LqptudGBsT7479/FLYCk/5e/X3UUVnTirpdJMIf5xYq0WmjBZUzxU8C0v//Kz3/0NYllz+Z/z061RtPMc3kZcn+Xh5OpfvYu0Rw1"
    "DzecQiRVGfNgD7CiL/gh2tPPvBjWOfxG9RrW+Vk/EXdCyLwntBaM81uw9CnOS/Xp7/7fH3yH/N+cSASlKbiCpsNKMMKHVP0X1kGS"
    "db9AiosGnQxSv4e+wOhk+Xv0+ZsCkeF76NOHwmtJkv3gl3+JPr+Ev/UfFPJM9Gixsl9eK8SFEBeYxrMQWbNVTZWrVcVOOSLdKo92"
    "drHUSRqBBKajKwyUVGwjSOUNAkjAaxH2osoN/GEwRAqCxZO2YYwqZaD5qSuKOP/gdnIfoUI1peKP3vrQW0DbLnngsCPydT9Kjmqi"
    "TRdvfeiFLYY0DWGzIFowXG2fwSn1H1Gsebj+f/7jf3hhu3SBLFl+aRHLzUz3Tk0+R5UpZn4t2PjjWguqIk3rDrNiSKYvYTqRLQlq"
    "ylPCmXxrIJq7JMRlLJqMPS7YM272hqrbpbv8Eup3YnglAnGQo6fCPFcwD092RGjDpL5NAdny2CJgiSJyzctnVQeEmIUazr2+ltOh"
    "p4V4XZZzgDWI7qSR6PfGsk5qkqQQRgFyadcAnPJLugIwZ/YGWPIbQHjAlmqLf/GwJjm+epaTuHeL0I/LAq+nKYHtGDAl6bnw5f/2"
    "9Gt/yPaVBFxhBKfGThTqT9IaxBWOuQnWm/El6TqT32yov/yG5/Z3ecwUFxhZjwJrkHFlcAnuW2p18BQK1F7W9xM6aW8rw0SG/wr4"
    "lgqUrgbKlnrrQ6Zv9P/+50//7C/QcvSv/4kAsHiYFIJe+GuSff1libAqv/fW/rvFHNRAAK/aBjdvWPPHdL680hz4jI595Q9oUqDW"
    "YJw6dkSayT/ZJrzcZNFG1RdkWIA5L6UVh/mQG3RI4nd0HoizdrtzJudAeA3X8S0FB4XPwMGLr0Rcw6jA571wi3jbM4ThULqyeFB9"
    "+q06WaOXK0JhM5Q9bWHA/NskUv/ykz+Vs8rEUYRw9+CFrUTJ+RA3k/7d7//8H79lTQ+9QmaJ9Y8NB37DUgJmTwRfd28d1SawLNXo"
    "EjzU3gvbyY6oAjVQSy6WE5AHKn6TWl66KNk1Mr7AZc+11gyJz7rrLfIMmGpzpcbGUn3sEb0eKvR61RgcgUHx0aWzRUMpGRzHI2sr"
    "8XXQ1DhdinKI1e8Jahivh+3cyB16GMOxWpJx4Bshx+R4wVq6THcOeodqej65g0LY9kEtrLtXwqZGgjbxVR3sUX8b0Nn5s4KFa8NM"
    "LIjtHAk4+10ravbHY2h2am99l2Yb91rOiac6KuxpbZKa9b34ot505RWiaWYN+YLUkC+QhnwOwlCRx8gIzQgME8FRaiK4H/KV9Rha"
    "kN6zVGAeOxGvAi2+FHtQyNdqSBOPPUKJE+EjzMOLKE2HtyHrqHRpAoykQSqc6oeJuanRkL699pGYbtZfbh203Rizi9E49GIarct0"
    "PjlQOGlaNDYkkGr+x46v6dmbFlW/4E8sWn5875MJ3lGr7rSK9P1Lpu9PGxECkYwiUsX9o1IQh24aoHmeJu7yVfhEPgdV7j2OfsD5"
    "FjRwpY2BOV7iBhwwwPg5k9YUmu0ud05yBI+PlnXNHs4z6H0cX2nYIMVaSybpicgVE81BST0Cbz4RriMgXl7q9JrNI3ryerBcJ+jZ"
    "+FKPP3nkQ3lI4pCbanBetSiSvv2Vp+//GG6F82qjMWg0qrD9gL0UBro+ot8xzIdEsxaRDqCKeIOSQ+WNef0sWxnjplmkPqzvCwHC"
    "8HjnMyi0yYXvs490mk0JJVvdCYuAxKweiof79ul/ZVfu7/Hy5g1IBQ1ITQmYfZ8iyEGLPV6QhwYL9ZyexLIfs5fPcYwveIV8wAay"
    "ftEfkW6IlgYxbGpv/AjPrdqxU21W6wPqL+uR0h0u9wHiuioGSInuhtPSbA6aTZoWRO1JTRyWqZlHbcZ1jWSjMDO0kxNDywmJ781S"
    "kSgQdRcTF2O6bz43qY3QLATFpKjQnDweo0JzkluJotLcy3diY0qok2CXJQvgUL1SgcXmGrJTYpMQisuNnnE9Ti5MRRIsYFEwMTT/"
    "bEhrwmuHnUDh3lBFo3VUBrhB6wP3qGd4Hs7o4m5x3m9mWtRUmEWn6mJI3wQmmITFhYOg8tM8S6ix4MVZqsL24Xe0ULzf+FuNpXvv"
    "67KrpP78NlLMqAr9g8q//OTHH/z376J9wY9+9LMv//BffvKPDBLPWRXAmiw3phSWYhNA+1eyyyg6vSASYlBtVPegAA0rw2BaFSLK"
    "jRG9ES0J3AhtNYXkkHeXGv2Vb9rU8N8DXiDtmEgjBiAN/YnIbUDQfpYEh4rU/KKqDkuVogQ+ff//tJYnCDdrDPqr4ViXEFSNoAlf"
    "CMi72s8YUjHCza+nEP3q4wdw9qJd94d7gkOsLT/SgrOzyXwclnQR1hL1WaK4do7UO1HY9yS7FJzjFsVcSGv8O3/CreseB06YNftD"
    "8ALlgByrZ9dYPyBJA0P+K1TIZ7zbcJ1kaZnxuXcxd2FPw4jBQQPUU3T7iEwBoedvoU3dzWNS20zPqy9sHz565PqkN8Vo99XLt5iR"
    "4lkITN72djB2w8kEiKIvhitnJr99gtTiOx63xQGGja5/Z6larl1argA616GP98bpuT4530aDkfLycer66pC7rCM8ZS9Tg+qPY0xx"
    "BXJeK4FeqlFzZDrfnk7nU3b7LwnsT0UFwGJoFlUn8ieDeSlrBB0kripNnxj1PUrjvf3oR9UCwn7uTzH2lqVKUzmj81ByjEkvIZy4"
    "K6R4sqnI7KVId/S6k7qRUyErhjTr23i90lwdleRf6lGkrKMJqzouCxcFuylgjpssiFzkLeNJGC0Gb9FHJLjeqKGM5Xa32tTfElYg"
    "gTvbWWlokijTCifqfOysJHX+SeBPIrTVcKaDsRNG44Fc+RdNWIuCnBnX4eoLBis02h3cuxcxq9lItZplh4J4SOsNno652pWfQPzM"
    "wAuEUeQaa7TmxxZPbho1PUS7CabGuPGjhx4C5nFDSIpzIZXbExii14X9vLq1gfd/yIxVVbaROQg02sLQHplioxa5rxHpfgIcd0EC"
    "xgSFaKCAZpRTpHDq9WfYs3fYrdwkBLF+E2ktSmC/bPvOLdu31O7NU6y+Go8qQMB/8P6PmeBVgKjtCe9o7gsmIU8HToUh+5yVdquh"
    "NLSJAD4e8N/uBkjpoF5gpQKLZGbBwJeUi81eJpjXmOmhisJHqwDdPS6Y6g34lYCUMGkoHo1mUO031W0X0rbT1yna343kFSR3Ych2"
    "ocd3YcJ2YWLbhYm2C0N1Fy6JfgvZRiygRZldb0VDnMubfnuEpwxk5idXNew39HpJvU6gNxH1Zi5aF8hNH54Lu0/OvHvncCFimJDz"
    "cYB/J+dAlC6R85KkDNCkQMkALWCGhshKVoCrHQsy5B7Zjbz44ojJMsMrYHrkSynd3M5q95qCarg5R7IDWBsgcqjAGUWgOGmmoZ/T"
    "EqBcR0plRKab+k5LAYQK/FYAZHUCLdcBY/7ii09SeoodIJ9cJuFvBP5NbTuchyN0Y4WKMdD8Dumh+aV5VSFZ8MTR1Q6wNSvTCMG2"
    "0CgegXlDhdOurjwKxJ5is9EfdPFiyxahw9Bt3bnF8ziefdq/jQnNCqeUYZJx8KwqvZfmOgROA7POvk1RjY6rN4VPDKoD6YwQOa02"
    "WdyxXXtz/vL4unbjqMsG3oVLZDVpfUGK7U3WpUIY2fI8Qe3GHc0DSPJbjvj0Bn+5KwOxGWox/hIWVMFR6QmvSLcVja4r1SOP80Sf"
    "2jz2FIDat/ErUS/LsJCMUFXLxHqWtV8iPq8oeeJNs7Z+PrD0UzxeinJOvVWhVi9OyCEjRQUWCyw/AucqmM8rulhEY/8HYQYEpEhJ"
    "z8k9So/UnsqBVhVPiEJFf2AKY1Zo8gXHAO6LFWwLHKSRm8C/1SgRskFda0SvshoiPJHlCH5pw8dcIkOiiPLjARWoAAlcm/CMHw8Q"
    "RI/2IUV4jJBym54TvGLqLt+I3OQj3WOgkWnHeUPyHmUbA95t6h/pW169Aa9u4VV9yxviTK5JKCyMvuExtHruJAooo7MZyKKdW/n5"
    "jR3uTcycXiOTa+Z9gLY8HvkUJoiYLox3mCH+V9/72Vf/GE1GDGh2VC9+gwQFP/jZe19WfTZ++rVvAsUkPAH+RofA/ybP+N4fkqEt"
    "ORdLcYTirFF1ThSD/iufxh09MZV2jodzGSFudf7gTbe2WiWbi3dXq5h+Jwv8uKi/8CBwVtf5Cd5Fhns1nmDCdK5nnIr2ErhlmSOH"
    "yvqbbP/cCbTLEmivpbuBGVi6iCsbnhO7n8GLnMGNJ/Ai3SlezqlgAB/gmiqUAyDqP7+1yFNzprvmIQgi4+YJX8O5kd8Zd38WYEvl"
    "PYBN5jqSYLn0I8rUeNLo16EnSqpbLRUrqnEDyaCrM0MYIYjC+oU7CUfrGA2mH2NFUAzcoDm6mtk5XjFReiPzCKlxTcQOQZw3LOsJ"
    "IYEoxkYF3m+LECpjHm2zuuhDNhnaj1edJwUpgAoI3vEpDTW62I3OWq01pVmzNVFa+Y4UUs690OKYO2LGGGiZATSeomNG3IzxOWJB"
    "wnLY7hSEYpvgMWDY4zckqgpiOhrgG3w0jOLh7Hmio45DnpEDa869kverIeqDV4zFWZ3P5NQ/IWjMKEe49cp8Lho6WIZJbSAaVUdf"
    "4MeXl9CpJynHLdcCKX5fnfv4rX5Wm9m8OmcZr84XX4SUGTJn5iKI9ueBLvOmHp4W2PfHtZsjW7EXLRltD105Pyy+XMr9UHdmWeeG"
    "ktUSqvl+rhh6vWZiq8gByhajVtETTg7OMRT7HPYklA9/b1XnixXjoln6g8MiAG8RosCewv7wL1zg792TRO+4Vs2K36u0tciZi87D"
    "UHXnQtqCOfk6wWhgV60gXNJnIbWoi9PcsjJFHF5QH3d/25rVCMqGqvkY/8LBgqkAogqokEuq9IPv/LUAKP5vyOGj25q1Rq22lPv9"
    "jKzt3/kxMzXOxTf3iTyESvMi0LB7mDUAr1e9AQ6572I7YHcN7o3efffexDGatJp7t7JFj2ZsnOXYaiHpxbWfXx0eVMXVUQoiirFX"
    "qhtoidLJdyktP1M2e6+S3AVDSgaMPPAxUTHcmobVP4pqqf1kCtz6+M03HyBgq8PBlfj7FDrkzTfhhsTfRxnJGpOnYYIBfD/iMoe6"
    "m8z8Jd2ZRKiZzdFUt+yawnTpazsmNjolZlZfuLrNiiEWQCG9ZgQ6Jw8jJVzHvbk7FqgkCCFM4MNzF84Ud1VH5UwNoa0vCMVLR4km"
    "EAlBijrRuYVCFcfe0pCPyVgpqvtBkpW/ZGKnLDOBLOYKKBUBPgElF6GjLPDnpCcXdo2BasxonscsBIvCx8y5ZlgI1pGbQQmhTcts"
    "hl+ZLFP7IRhJNQt/wBpXDnqFI9woLB9BtjI72zh58cU5D5icNrVkwUYoC9FljGp+Uf3lP/3j09//i6p8ikHkLqof/NnfffDHGGr6"
    "6f/xh09/7w95eAnelPO7NILBHCnmrRIXTY+uY4zxcq0HiFhcoSnVCzhv9fxciZHpgqKCLMh8PzfTSJNN84XFdAyeXIgjsRA9Quma"
    "nI8QpWsE65EDdY3PJxcTE6hrkgXqmjw7UNeYrz5PB97C+g3graPa6MUXR1DjBY8HfoRfyM/A8QQkV964aEFY7ilLOk9k8PrKTXwK"
    "D7Sql/G3IZGspGjvhanPTfGNqVK97LLB8CM+4+0cPNvE5Wn3rGHXpmIdf3gTD2gKv1itTZFXKpd6YA4Gk5YvzqZYXZxqXMFeJreb"
    "7mpTaVb6q011p54kf/WjTIgOctZXL5GpCtdzS7GfXqPYTzLWAcfTic4J6CMTUkDHG1oKNBlihASQHtATEaHoPXr1MwgsJAT6VTi4"
    "78UJr8gRmcU9YvNDH/tJmdi/Nql/EaBHRhXA5ScMy+LL/2AgaOSsURjs7yC0IgpVvs/ArX8BKb/8dS36CZ/vwWG9rF1fO3DdLx1E"
    "7J8OIhSBs3HjUmg2dunMbq51hD0lbENSIVw9IhbqCjihx6IE43RhpOAtSdNIYSzh0R7nhOh1UK25qvPTiOdiWgCgGdb+ToBqUjoL"
    "Ln/augBbFzG0OVplQTbubpCJuxuocXcFet9jSOhd02OMggtHLo+/K6Hr0OUM582A2WPHqjrNCJHoxpwWdKrCVQ3td5k8BJtAjreX"
    "9UHgThZwd9Mf91oc+MogsnDtKtze02/84Jdf/ccP3vuvFJARw+cIcL0Sbamxmm5mt1yNJ7/jaX9pGV0ajzuOrtIPjlL43EfwjIfO"
    "lBNZ3RObktd3h0iYwl+1PqhpATzr0jdlmR890RCw5nRblpt2Hs2Yzf2oE+KJILO50aqX+ClYqvIA8R3qWiMNDsPA59cBO4GM4WUh"
    "zOplPaXpBf5gTzlTrhnLAWfQEs4gKY/NYK2hDjFAvWaCotdfJ8k3cU1o3cCErEsGoEV6qtE5HVbobuS7C38RapzIBtiYjYu4gqgk"
    "TTgcqOa8f/7yRhBfK7htZ5lX98SrJ+dsnFcRNOTmXBl0dpdhemjZOceCxbgSMgWyH49Qkge9+qyNIXIW55998cVHivo1kSLAtcmd"
    "UU1e3bm2vID+wrRjr4HqWl0zwmrjriTC5MaZMl4OHjpT4uVeOX+CKtSlf4OIzOLD4JovY2hS6+IauuCu4EwohSKZe7uOZ+NSoihN"
    "d/c4QDGUl2pa76wJY4XYfeT1UrIlcAWYxn1QcEiGwIFZ1WChhgox08Phre74uqWwLCELSBTu88kPyzvkV1YIE07WpyTrUcjSxR46"
    "VBEnMfr1sxeLC7uYqJD2/kPFy1JifimnDZreo42qCgn9Qz3J13/x93CzfYNBklGh3CnewB0rq8NKYz4zFCo7rSckZXbWQsUhKQRD"
    "QIiy1w4deE7/c8ahQDYHw/p5tMT6PNwQSYVogr/SLX7t0rgyLX8tnI/Vhn8WMSbZyVSmC0J6J02bv6VAjf2NVRaYs0gKOpSKALkV"
    "IrAL/iaAY7fAynvK5AtMou7N/SiplnWK5mXlcBJWj3fVhbpCYutvZRisr+fZEOVyGk9/7/f/+dv/GWPiKEIXAQT45wpZ+HUFPhAZ"
    "CRV4XRM6/rm2wL78gw/+4f1soB6FE7kkJX4W6vdXONwjZiHHrrFDxn6jxEbODiZe9cRJT+u8X5NsvwotHixy55HmzPDV7/7sq/+J"
    "3FsLuqBpfhahLZztwsPraauEA90Q9+9sJNxGgSvbIk+oNtgw1oujJ5QtQsBUZKTRKZ+6irT41xseCRVD9CmSBr7qmIcGmwhyVRzL"
    "eUDiFWWT+NdbevXnMy8ycBWCc/3gfz39p+9UC6/ehRddaUapq1IbwDKTRvRUvI/+lLxTaH1symJw6wI3WA0YynHn0B82hLO8ISQG"
    "Af4Klpl9GYWB+IiAcPX6s/VLmdwq4brtCahcKIx+LCHWeUEysPLssFHbqDHkhEDVEKkbY+nQmFywwdrTAbXBDMW/6ihDLVvNi4Qh"
    "vyhsdzqeCIhv5MZZKptdA8rn5RgG/CXOMn6BaDtlboqi5qVIfatvW6KjVmWIH/V+MMTPixCZB0ZxvJIW/crFw9orWenRgLE+L7cu"
    "3nphCx92T9/7A4psp17NSJ8yaR5hLHACCAFm/qhqCYzCNl2eeoy4N6EeE2uWi9Km5woLefFooNrVXME7YrdRgcA/XqrSUrg8ry6u"
    "TFXCVVaVcLVHlQA8CBbUvEx7muoG9A0tuowu33ttGfbPtNr7VBwBm5VJHtTVNq7utTpkWo8pWqoAp5s4SulF/u76BfeYATs5vAmX"
    "ZcX/ldHqVizDt3SID4sGmrCsNgy5RyOsSSnNXxh6431lPoMa2Upoq7pkuJ83HB3jXnalC/HXs+z5dPbvNOuPaNYfwazfXBw61Tdy"
    "qpXT0RHiEBUsIduxCm2YEt0rOswMbffaPFnNOq4tx4ip/b5CAVNtKtXe0yK19xyHlF2VK9x9qwL3Nbt+e2Pqtzc22b2jCJ6gPZDm"
    "ztpvgrHGg/rp7/4XBuHED2KhXdzcTbt49Xy0i5tfoXbx6jDt4uYA7aKzkYrFyyztdpd9rWL1FGxtVpNTffpn/5eg9L6UxBdvwd38"
    "wXfe+8Xff6XywvZzfk2+qe84/BHHeOPkEYbrxXzP1GIWezdvkyZBTdZTTysvgWLJAt5ECNYKjJtAsXydnjI/Rn8Du2CMgYUjbVLn"
    "tXtRvYxLafWDH/3x0698+xd/9H24In75V3/7i7/7n4K6EYePsxZGOBhhR5EkMXUdOlfD0iGDxlhNyW088HUVmbb0ZjTdvrCL+QwE"
    "ULDz2zjQzsz1M/Peaw0MIdsraNVaZxg+t3K2QTLYsDVf7M6qF/+4qjOw7+OAFQjmpbezMW4L0tP6FNhAG+/nNQywc375T/8B+Vxp"
    "n5Pv/HatgiGK9gjVTr+uDZ5tjMqBvifVMt5EjKaXCT+H2oskLoYYNu92mpc3PJbTHPp1hLKnDSk0SZLynHjUTXqM/eLP/qaaORxs"
    "c6Y2G+j89WLhReiJAC2nRcVjofOZaLU56NDUuUqZhVfPp6vHU6DLLiE17lD8/3IvhR6Um46wEjaqR69ieHl287z6uK34Z70K9Ia4"
    "aekseJVEb0VeTxr8FbabRdhGnQjSKvwBE/V+iT8Hhm7KsS6rlZ9+7ZsV1AgDnR/WB/IN3WFX9ZRg3Ye1wuK1Hr4k0XKU11j2AueX"
    "dr5RqsEH8Ap+dcajJah+Y9lycyIRhqG7S12w3lmf32ulTjm3ZnCvXHfOL8Ap+c4acVAf0S+Bw3xv5iPfds9nAbaAmMUqmg4CS+Oo"
    "50KHJczZ9V6NdMb3Ulv9d9/lwbrqdRa5i0eTqW/lR+iDIyKuCZ+mFVCuh0VsWh4UsYmDlTlf4GOA/S7jt5ewoDg8xM1a+fL5NQ+X"
    "8/Y6SPJ9w/FteJ1vJFUs57PATpHmjMNv5iNf65F+EAj7y1/7+Q/fe/qj7/38H4FK/BpaUOGS/QEBZHP4XDjN/Y0PhzgCnv79/0tA"
    "rX+SLa16mTUNRyorCcl7V4eLYs98lz68Hk8Fir5yDYpXO5Hskf92YXQoKNdbreD0vW5gLAOM1mwNtgUPx5EHVAq5DeOHKi6A6lUD"
    "pbsbnz5GGwuI581GmelH6peHypdYBuQiq3/PACg0InM9Zi1lEFgwKFy4+KUpFsiPh1dY6TUjKdo9sA5IbuvX1UYNBSKgvlC/IBLz"
    "tbqRQVde2xgPPrH5/1fzr3Y17+RJJT5w9ysXSZ7YT/AOWvjn1yzy8sqPvCSMMNyFFyE9NMfroHq2txSktqCQs9+cwulacJCOmP86"
    "c2QiPKk9sRWrZH5jumHtHIQvKHNg+8r1waKJs8hRGubJGXuDQ/Baq00Ln0depEgjs2CS0OfHKKCqPoF/I/h3paIkLetarsfVNVpc"
    "ZFPwMI5YLgvjaJa61vOg91u2/zDLGTc0PiifUhzuYFz5RH309pPjWhWFB4gIA2sGqK8aW323dNnUzz6NU/eRB/EoClbJyx+qVD5C"
    "NEEl8ufnVfoYz3w/qVZGURjHYRRMg+XLAyySgVzREhAr6HKL8eWH08H9Zr952nzljMLNe0t/Dk9eazVbLXoSeUHsD+63eq2TFksz"
    "g+s0GkTToVdrHx874p/b7NbpPfMhtCXoswS0fGzv2+z9MIzG9hr6aoJGnEThcmpJ1+IFEeTf/ddOXuu/1pcPGu3B/f4r/ddOlUed"
    "wf1eu9frfYx3YATzMbh//GrvlY+1lUcNYHNYdaddp9XsOe1WE2rr1dU0CLOeTXR8zBKJGAxqEwT61OB+99VXTl57yBLyADXQ/vbD"
    "0y57iMZUWrsY9vr9Vz96fHJ8kj5RGtHuHDv9E/zf7Yo2hKsB2aFX2miSTsmaDv64XRphWBTXXlRj64M9aMsntETw4ciLxvanMMKt"
    "Tqvb6sF3tlpEMvqGyRCGRTxMB5fqYrMvG0Bf0xdt4w1fBZhgkjYbZ5U9grY8PH348GO4mhfrxB9raRq0UnBas0/5MtBbmb7A6u5P"
    "JhN4gBEuLOlm48gYn52LEUDRvQ4lkINpFIzP8BfUulgh1FZjFM7Xi2U8aPdwahbBksH4tSZRvQJXzmJV63Sbq43T7l3fON0efKwb"
    "JSDI0aDbN3Ofcb6h1Wxez86G3ugKBZTLsTbTCI4bGYM4gftg0G02K63OavOgBauowhLE3jJmrxvXKECDv0s41KJgNEi84XruRfg9"
    "PluFcYDn3wCOKQ+PhjNcBJN5eDNg0GFsVCqDAQvSC0m3SvvuH/s9b9w+6fDW4ZjzHIzp21ITJt4imN8OguUMWpDwBG4UbFn8uhYM"
    "pxwC/DyZ+5vBEvYTT3o1HG/TrrZg+FgvkfW0DQyukQXci8GyQW7B7dVGVDodyhkOKOpCAys78+CmXjZYcDFcIn509mQdJ8HktkF3"
    "LtTNH0+91aCXtrcDs3wmvEigcfiVL/7IGwfrmBJT44/5PGlTZJtVvsuwn3E4D8YVc78pM0BAcCuPwBNuZtCBBnwb+TB6N5G3Sns9"
    "YHtddzffWpYaPwV4H/Tm6bs6LRwu2MBWlthu1sLEy8zK4QXubfH93vDkZDzWS+cPlaJQzMAXmj5ZSpphMBW8e9eY0C6fvgYCFtDy"
    "VPLNvHhr7Vx60ivDJLuxBbpjFCS3A7cLb9F5ZUvnBBwPg9aDRkuuILYlcteBWMm0hPFXg+FP4oZmh9UZnDMN3rNmzskCTbiJt1pZ"
    "lu2A676frns8xMxh4q0ehrDzFwXNVrf3TVwZskPihhXcazYtCxnxthNcejhwUGPDbbb8BcvvxuvhVt3uaAWScyooMwmHgq0i4/w7"
    "o5zyoT+fB6s4iGlc2aLCdYTRCKUvGZZcoV/quRP7U32M+dnXbH7YNi9Eh5U5CrSz5kSZFKNyeSDj4LfENLb7ct5wfWiFHcOr/FFk"
    "x1nbPTYOtJxjM10qeB7iYsLi7QeZpdmPSQvE7iB/fI5olpdby9mpZXXhFwzkeIuQEG3qKK3MduaMNtqSHlF4JeIgbxrxzAOWSL2V"
    "eCUUApIfMMfpBjnOVmKfaUFhptuZX0wE2AZ1zbbpeLf2Xh84P3IlIp3SggHHQceTxjf2uf3MwNlpa9sbKRZcKXIf0BbTzha2rtKh"
    "KUNItbJ0lNi78L4hjhw4FukzdN52MvEmUE7R5BPe4OxVnC52+yVqH1H6S3UP8IhhO8CgZ6Yxu7Lyb9U0pavTUeaCs69sOOqWi+3d"
    "zyz1mIXVxEocbY0z0ToALG2yYPcUm59B+0FXoUDbpcgybfmJCVYXkqip4iIIytZyrfJTnBOVym5Isy43iZFTsGxFmTG+o7hI8Mig"
    "FcVXEH7PP4Xlhmvyoz/bz55B12JlRBRMgihOGiSM2spNxGIb88akxVaaZwfe0wZ9qhz3Ze+Unv1s5BdU7mqhDgwIHgguymQWLLeH"
    "0JQsf4VqEXeWcufm3F/2LS27v5+H0g7XcJ0Qr960tmowUIJKb/PGQcvnbqSGiKgPFr1bO2r3dibnfs2rX9BHZZaNvCRmW31B4w1y"
    "CIGXS2eK0YhnghxRx6P8IOwjS8xrEnvX1egh2QJ+ZttP3KEXZU68shtQIY57B4ydTlhCA2D+kkbCaIAeds6kuKyk8XMjbWULFtuC"
    "UbfeAFZ+lJW3So86DClVanmepKdau1+G69570Kk3n5tP7lqGUj3JWRSwbd7Zot+4mNgdeuO9bGMODSDyZypkV6NIMQ4WuUcSJcBY"
    "gfZGix7hsdHOu0Vlt10/rx1sp7H2Jhq1o+3kdRRD7hWaJME8q3RVZnoyhZagt1hX5surbQFhN/ZHYUR6gMEaRfs4AeyN/NpgkJOD"
    "DjWDGgDE2la9kmhNwGIkGlZJVHEny+3he+8MqOKGuCKaVC3tHbZhiHKPZ1GwvFKoboKFlZuJGAh+y/QVGVs3s1tOT0+LOSCz+Rm5"
    "od4EN15wjqirHrsMtTYwGpgKPz9ctlkoa6+rHHQaGiHGwMa/VWMpV06zXk9fNpjahUj4Cj9Z6CXri0zHD4rxOmp06vyL78WwCNaS"
    "xbw//EwohUbt/t0OoH0ECzvZcvYBtaCCh8HUP5CZkGPe49Q3H8qeXluTDsXsIUazuRrxKVakoT0r02vja9MT1Da/TPFTT6tyw6tt"
    "3jpQUkVrK1ulHlsiKZ3B2aT68QXpsIl5h5ciFwiWcDpUmvSTUh9qT9CyYFtSYiePAJ0xgsunDFuN54+NrSa+vmtnoiXB1xME3yEi"
    "PdY2OGeHB8sqOL/Fa+iarFMhqUp1UlSxlDw67qEmRKNDsgRSGwgkIafpqXINfrypTdgBRxm56B0n6sq9EzEh3s3WdGJlYSK4nu2J"
    "5HJhoRZtugp4N91atxRbNW4POqfIK/ioectgwa64MTJvhUdcBWZjhvW4FJGR73O3AwWnxRD182tX/u0k8hZ+XKFit80PK2FqlCg1"
    "Dbd77C/gIuGS7+ZOzB9QANo1mtYw8cZ+Y70q01RW1M0sVNbfr5hOlusvyaW06P1ysy0li1YED91nEU1DvWh/pDLNUkinye9QtDg+"
    "VO7faVtYG8uJy1TOpTUChwo4BfkBvPDo6vYMB6159k6DMJMHbeoZnEYUs2abEcW0cs5AU4egFVNBy9dSo8VuaFT1brPq1TutbhYH"
    "Ki3NG8IwrhP/jJraPIv49LJhyFXEMS0+J7UbzJCdXcFi5JqHkUPBEhvJw07tSSWJQBgY+FWO5SPyR1Ct7bsz1ZzLGDMDIIvWWwxA"
    "K48kW8d4dJD+QdcB8O6UFv3y9C6UVUC0ZZIvKebvfFs8uWzdVVzoNj+0kXNQbwNaKqoCp5TUVmV3qYJodF1w03PSv2mIPEVOV6g8"
    "jINRakLUtNwoJ/eMlQnpfs1jRmUqjESTd+eyVMtwe6hQO6Vl04usozI+rODF1iCln0FIozGbhsiGasPALNu9UmhKCi9ScQw9IZ/q"
    "UooBlXugtbZvW5vySyKCYY6zzSuyZ8BtgXGHcFQdy8Nwj0AWk+JSoFkxZQBEUiUz2GXT2VneWknLoaBFA2+S6Pv//qQ9Ou2OWt4O"
    "2YgVLLv07F+N0NCr4p7E6kEZr9BYiR/6CmXFUuukFbG5tVZ91znOPm670NUktCXfueE4tBOWNAOdlBKhy6UrLjO2faZh4qi7iZiX"
    "gm0sjBvPkX6+LJAmJWXNcgTHnafXKC3SOFSGbF2Nsn9A9l/mHT4yUbiyKq3P7s5eZrQnsi6CBCkacJEQnS8vc0jUPP08AsP9W58w"
    "1kq8OItMkzTrI0K8LcOjH24uxqlxMQB0N+5VNbMyRMPKyZizxkocx/d6ulUUTqrexXrEGYx5Ly0KhXuqzM4inhr7iRBw0ymST5kV"
    "WBQYpLLGs7ZzeVZgaVRZRnkJxhhp/Ttc/mUZKKVvTJyLFc7aimKHJBdu57gE18oVwwy1mnSJ0I3GMPK9qwH9buAD3qnhbd5tSK+n"
    "YSlbjUlEtEYqSurrTCtbbbxEMrRULerMVamkIxM/tPirbxXCUTXTw8tD6sKlTUvTonbPlbiqmhX93OnbtPXEeKiTyeTtiRcldxRQ"
    "MAFSFKgGBkyZgG9eHgfXZU1zdJmtGJ/K0BCrZ8W2lIzY2HLGceaS8uZztrfRsmp0d6uknm6VhPBuYnab8sUhk2s3XOgXiSZ4vRUC"
    "kbOM3B1MjVPrMlH4KvJlxzK22se51AVkaxAvYN3UpBeSx3fTtMoiSXN0FR+ymnSuWpQAezOfgaAGDqiV2TNPKaFyuESYm9KZrMp4"
    "no5lpsHjOeytMsfYaS9jfG+TBKVndad9gJyBH4usQePk0K7zfOO0oyVl4ZrSoCQHaaVnqXoXF3v+PSiGm0FibdVWsQNSzA4d0npq"
    "HBT+mk5AZfZEgrFh4RbBDkV7KaoMJZsN5mzN+O3Mijgrue67K9UEV1RQmQelBFOMsmJZUL1rsVDKpyPuPEF2qzLr/hMW6imt1u5p"
    "putoFp+qabWXyBFsD+XjqZ2NoZ/c+NAlViownaMaDm+lUcF9JI5K7RIX+6ybZ9JxkKXaIXyM3YoTe19amoeJibTeIzdt56mRWREu"
    "4t6k5RDLHoWEA3/aHPvMdorDw1hss4qVJrm0MmsAlLvNXJxKfcx+7M6XfZNIVLnPx0D2jVa3WXt96RJxoiXkMyHeooRqkmxV23lp"
    "RzP3VrE/EB8MaobyVZKUOTg+0KYNWpEEsKA5a7aArTv3Ral0BGTsSrkVlJ2MEvnQLEIbjV7aWHe5RukW+5xrgGU5J0yBryxwtIq3"
    "1oNfvibFPm8P0yt0lAaFq2356iIS3uKg54sh/NJkL1uV/nXF9bd3oATFvKMpe6spy0rKWkaa1LFOBPHS4sU2X6vXlpUGybbkSa7S"
    "ooqrRQE1KquouKHC9LcUpr+VtiRswLAUyO9YmkVYPIWYZuzP8+RfLAGcuHkeG/KkQVyX0hOi8p4Gi9nKt+Wz70b0qE/1a5Ng44+F"
    "ea7GjXbtPAU5Yu/11pHusBY+JRX1ySEOV3Wpl+o1s1ZM0PEKOSOkhz92o5ygRBEv80woX5baedOgquae9uoVVZ8PI4HSZBq5ijsb"
    "3/mG6DFXjcqzKr35bUrNCZLSem3lKtlnMl9MZ9T3Wi3nW5pblSJETGc6ZnWLdDKpmOH9dRAHkKDIOixr5C7KoNMj74yRidA316I4"
    "Z+9jfyVFhfadI82eFYEWWjCEU4u6O5LHF6m6j3upT1crNajH+N5dZIyd0/b1TbqHjpuGXQ/v7xyt6LDCEheRhc7/1zwO0p0eQ3k+"
    "jfh+6VOOTzfrOVkRPkT0ELuxEXP/1peTWDPtTM+EWJ2nEFazLcldDAaNG394FcBJPYqAVBt6USOZrRdDXXVG/7W83a8t/HHgVWqK"
    "lrHfRMf6LfPWfyfEuXebfbF5BctxPas8qOALOKRkIdKgttXpKYXkePkjx2KY0XW4IS6zKjbMbbmcAhUOJEK02qixC6qr2Ezi57SN"
    "q8if+FEMt+V4PfLHcPXSdFfYd2jxeOqkhlNMFxc7JJVzmITPSS9Uh+1DJ7PSs6J1t9VF5nfpexGtmXvBYhVGiYfaHmZ+4hhWvE4B"
    "D4SrkZXfWsQW/ScN1e7BS/cqiRfMsfRRHFeuu27H7VTerbz+yS9WPhPASop9+DZLklU8ePBASeqOwkXlpQe/BsPuRxUgRlZInfvx"
    "9tfi9QrbHVdqtZpYabPb1QzKolrr9YoHNGkNzk9cEIyCiIIFX/R1eB9GkBkG/h28aH3iEOmVkpGditF0WJtE0BKYnEpUmVaGkL2+"
    "fckZDH24On2HKYWdwQDXNlkeNBrJTYNxdo0NFAyj5c3P1Ke31qfv6E/jK//GzE/PjNzyoEGBCe1U9nzue3S7aYlVgbFeMjuJUPd4"
    "vwn/qU+5A4MlPVBWq5nHblZ6TDrMnMLUd7Yitfdmwag1t2Wi50X15WVU3tqz0ytKZamRnXnifoCNnnmVKh2z7+wVDudro41DugyX"
    "iEKjPUcSIvJio2HTyLslQk5/PFv7fIWZA4Dsrv5M0Ib6VHsJ7nQjO1z7gac/wtWfKrPtL2xTob425119R8cqz7mD45SdDITOtSWU"
    "JQcIpziBDSg0aW77OPIXiEOTrnvYMPPx4IRGne+RRsKIDkh+Jg3aBpp5W/0svXEHxgV8phrBDTJWcWea6ccgawwiu7JOgnlAZ5wr"
    "RBxbuo/x8a0Ue+xcYl4MXmbnMkPJrWE4uXMXjaaUNsO3pNFRFVR0m3JClQ1bvfJSBe1fFsNGa6srPvR0lKRrJLGX12WJ+6US93nl"
    "zVKpW01MPm8gVWohU0nfo2t/YACB7tkalCJQCJp2YecyUsq4/NlNYRBS4nFDK1gjsmaN461KwGT6cYzdQKVEAx23top+gkuvgQxg"
    "PkFTAhHZuZKBU0SKrFjlBnIEwajcP5Zn76jP2N2TeQL5di674aFXjKrY3kmFrxWyXm3vpG8VhRh2V2G+YFSzvpL5Uzp7ezfie+dG"
    "Ph5OW/ZnwJ5J6dHWlCMRk9pgTOrWLtpfwZ5FCrPJvrToi7n78E2b3thXVJun6RSk6fA03YI0XZ6mV5CmB2kED9LgGyfDkxDpDxQv"
    "gpQZAmlWIMqSRCLaBXqijttttvttv0OCQpEQtb320nAA2IutRibJZa0+lUwa5x+wCmHgEqQ1qNyyNCwZAsPnjRvDqcLi6CnpLU+Z"
    "n4qnYONjT4Pv0lTtomRtlm4aJgV1srcsJcaZKEjKX7O0mreWliy8EikKyqKXLN11UFQpe8tSIu9TkJS/RrMwWPNCvJO/7ldwJBen"
    "OqZUvT2pcO2vNrAVhdqTHfwFuxJSd8ql7rDUcBeWSk6X4epWaQvdeEVNuYVbuUxivJVJOMQPLosRG5FZUrNs0ZTwJCgR2+aCdFDB"
    "bz5GGeObl1td5Ju+bb+JwnI9AbdNk0ky79W3HfNtR33bNd921beZmrV6T823p8rbttmqttoqFExqbzskjRCEKnkqauxd64xoDEEp"
    "pEmJptXTslHWEtS17LYEfMqQat5meEiWwaSudYPFnDQ7lyTBTKfMBMFWtRUNDB6fE11SyR6J5WK8TF/g8Wa8ZI9EAjrUjBT8mUhC"
    "uJVaAnoiXsNRZuSnJ+I1HmDGe/ZIJKBjy0jBn0ES1VLdNGNnOKNqCuACGLPkz/1rIBtU5p6TLvSinpU/Gix43TEeK7yy8i7L15ov"
    "M0/5AyTN19E25X3xV62PJgQskohyTcMblRpNGWP1qWCL1WeSKVYfpiyx+pQxxBrRyzlf7RnyveoDhUN1kJXjkqrbikaFb+PbZeJt"
    "BtWXqmfcGiEGWncO3Jw9x+3BOd4pn4PR9wemP6BFKlmVn+uM8/KNa2++5rIrsyR+FpWvWjlnDugfTV/plkrBjb0cRpMcWjsTfchc"
    "H4EEeK16U//lPc0h9tAoU93Jz96vrOiufO+yYr3n1cdUtHfAXklPpOc1LHdpRuZEffbGpPLKA0dDlWWmU8ODMe1rTVGJe8bEKIr8"
    "MwpKe17jRJdO+ZNM3jTl84h7qHwOeUuVz5LeYYesOrzhyqfn4uADTjJ+YR6QA6/T8smVy/ZOmQ7dpxnR9PM6u0y5dkGTSLS9ZdzR"
    "oPpJ5LSqTvWRPw39yq9/svIbCJs6nPuVLwJtqLyAj58Nk7DyCLJVPvV57evDT32aPfpEEHnTYMkew/c31pWPh8ksGLECXveD6Das"
    "OvFtnPiLxjpwsBEwaVGAag1k6QbVT/nJRyMPTp7K6xQmqvrQg7WMmk7xPVzC3e5h+R/zn3i/sWaNYG/XARVDNL8jPyGoO9P3oxSH"
    "6VmVQAosIgdF3uBubY14hM8G9IxB6N+fdOCnxeHz7/tD+OkL3Hyufk4B8ycn8HMsAfPvT9qTtj/hSPn3fR++T1J0/Pt+F36aCir+"
    "/XEPfloMBv9+qw8/QwGAj+3o9iQA/v3eCfxMOPD9/ZMu/IxSwPs0sw50r2Dd3+91ej3qWniFsSG8Ttc74zIVaMloMvJPzjgbAu+P"
    "+80OagWB8Rncb7b73dHJmRD8QFea0Df/TPBFkKLTO/WwcGRCoLjTk5Nm70yKV6Ax/qRDRXAuZXDfa/XaTXwCXBk2oN1r986E1Asz"
    "+G2/fSaYtsH94Wlr1MI+AycEIzDqeP74TMh6oElj/5SaxBgl6O+43R+fnjHODCNmnLaG7TMpkRrcH00mHuXgrBuk8U+6pzhDSwra"
    "4LXgx+NfWaO68IMzjn4c7MlkAotEPsFVMvZ7fU880XoqlXgthgKtxXFodusOWcRW0JrAfMVjE6STCpwcUb/6I5xbZZkmjdUK5s/3"
    "YDpH/MmVf6vMKKUZT5QJwCcUg10ZZHzmrcc48M3j017vlD8LFnCWwUh6fa/Z5c/QlG5wv33c69C44CN/M8IdwRZddlNiVBxjT+Ij"
    "viWbw6bfaost2ew3veZYbslWq9VrjZQYFscwye10S7b67WbbE1sS3vU6HWVLtvz2Saelbsm21znutvmW9DuwpppiS466o8l4mG7J"
    "/sRr0oqiLdlv9ienE2VLyszKlpR9YVuy0x+OJ32+JdvDYb/Xl1uS5r/bcVp9DEnSddwWhQLh+/N4Mu6f9sT+lOXw/Ul5j3uQ99Rp"
    "d/uQl8V54Zv1ZDzuTEZys06OT/3mUNmsLAhJ99iBU8BptUR2uXMnw+Gk3RU715904b905/IQJqdOr4//83aLXTzpn7ROWmIXeyf9"
    "4cRLdzHlbfVOnBbkbx83RW6xp0fdIfRc7ul2e9zxfWVPU/5O12lDq9udvggrIzd478SHWZIbXDZdbHCz7Sx6jdzsrXHLa07UzX48"
    "6no0oXKzy+1fuNnTDS1XcP6Gbnbbraa2oWEdeidddUPLOZUbejLyjr1jfUPL8VM2dM/3T4Yn+oaWnUg39GlnlGblG7rf8yfeSFIb"
    "qO5qDWDM4zOuSRu48nNn4Hbkl+6g7XZjVT8+Wg+DUWPovxP4Uc1ttx1Ydh1YwYqm3EhzfAwD2RIhchRtup6sh8nczrFSFNeq6+lg"
    "1bRc2Ga9LksJR9GCsEXx42I8OGUfDQqD3m7mg1aff0YNFPdZF3IzIalmIizxuD3gLkBd87Rv9WWiDiRCaW6lbybq1PPO0b3ls7hG"
    "e8rvoRpj1Pj857+41VVEtALp3adffSPzDtYiy/ex17L5xhN69/QP/uMv/ujHmde0RCnBP//53z79y/+ZSUDrlRJA9qdf/UYmAS1e"
    "SvCbiHRjvsZ1TG9fxdWbeU1rur57aUtSzuAdXCLSC2SzmyWLuTMMx7fOfVruqqu7tJTA91mrWjNMz2TK8QlQQZBx+RTmaUyevwiR"
    "toameEtkDwJYv+OM4SaDLHZYjDeGRiRDvW017FRhSsN9m4r1LiZaLIMS8hZDA58OL4b6Lr6eujJ0j2LIyNAjA9gW5JqH1q1XPmy+"
    "CI2fH2Ix/JlANRVfUUY98lYDGkr14ZMQBps9VTxB45VmWYBfKy23Jc0X4RJAHksDp6M8GiIKd6/q9Jh/1c5imCrdjJQ+osallA2r"
    "qgRumza+qndbakSrYX8oWsx5sBpIJVyYUz+ZoubgdXCs7ZKAHWaEIwN3Kxs94zTfVS/tvzkypKq2wf+mCrezEnBJit9dWkUFryZH"
    "1cnTk52K+L03FBL39ON5LKF7jkXroSR0Iwlv/DFPbg+IpGOOqM/opLDYEPAcSqn2xnOdSCqQqrWIIsprgihwSjZxufAzSnuyy4ll"
    "vstgumNvOTWOFiAb5WuK2JQ69Cqxm+wgKyKf7utqOmylSxg1rnxaNbt2dq4azzjmm/7wceINyangsqRlPJkW2aziqcrHye3KP8eD"
    "/NJRHizXeAJfZg76rGf6wfsuu4EN11sVYMKs2IRqaaFFvupIY/ra8UuQNPDKNci82LhdlPCvVEcEWMTRFZx42qhgm8PLLd84lt0i"
    "WqIE46HP8vKee0N/fshpiNShflLB7bhabbWwffu9R3YuMALlcA+7GQAMK5oFlLcPZDMTdEvHDpmHCvzLXihG5RbGjBUXYR62KeCd"
    "5sxtgGqYWeeJBod3YkAXEfS0AX7DgHs1mwbgG3mBeUgerMDTDJQ1Bhozy2/1oXyTEjozEVuQLIxvbD7/Flh0SlwAxNeyYjc0Ntwr"
    "Wny/Ff5vlulJqQBWDM2yEgYMPaqoGTYaRzdgjbRoDCW2hupai/6p5HpZCtiLGaEVH2CWEA1FwRgUyPwu89SJmKeODtRf1qWQMqOr"
    "yYqg/lM4/o7hEsodirX0VGnqcNRVUnjT6dY8TuQb1WfXjItpszLBiUUj16y3nDTgJgSGowpZT3DEWMWvVIGs7NHJLxuNjnTHPXKk"
    "a6IjXeFdUnAF6aRvV/dvazIp6DH+Ip1cs9kdq86hsosV10SN3YfUJEo5FfeQhQo3bbyUyo6wwoL4T9LCU8lTccd6ECm9B7Hu69+3"
    "TmoGukBmZ+7lgz2+4MbSqLgrka0gE510du9oWY5vM7LKtpbtuUPaqt4ObCcAiWQ1qvXGen5p6QUk4bIIsZR4V/MC2NFs8QgZ6Wbr"
    "l4vdR0OmtBzKssZ1C6/q+orHn9QFWFi7YvbhOrbIFVjbC4pIjVupDTh2GU7UGxcWIY2QM4EqLWIOO0MrtltHpxSU4JOHRO3KesXa"
    "1vieEJF5bKchpNHGRYhx+WnU6uYI4CoHVy6ORCAEh8kyLos0pA3mTZCMZtvCyEV8T2kgHnQMscw8qJp+8fNXLpMjKCyXuH9sgJ22"
    "a10e+1mQbYVXB7ItViol4Yn9BmsTGciCOJ/l3Isl9qoQutfNVhTOfXesD9qAOBJ/fORm5C2KeXtBDtFXS4yEGh5Z9d394Wf9hAIL"
    "Z4lJ+Y6jDQs2uFo9sw8ergw5/3z0lDBaJ+XGjon93HAVJ1HJWF0ZxJX+Xqid3OBxdNykNJ5JImdNvHlDX9YQ+58PLdvfx3LnUkk2"
    "82Xe0Ip7tS2mAlo2XqiHAZBlEeEqEZGUOTWjDQZLcCABoeYtvJFttw27TUQR7GjMymfUuzitDqMumNyh8f6uPRkfQA4ZEbhKMw5K"
    "bc84bBRkzGb7bZMW6vsUI0NFjhttEKuHvhRFjWmpUu6eXcRrP+rrWXgJtQUIFKC0oTj6V87JM/SWSz86jPbXQqf2LXCx2YtDuJnd"
    "cYebe0+9tlkPKIrQNm/m7N3n/k0sf07gwD2LiWWG4U8kzD9/ZCHLDCiyPNwzimZlCzGjY3BmZFldMR2kLbLIS7zVyr1uIM5jhVVi"
    "R+fguBwdpFGcLkGC6FgdoqRhCJNTpiiRjXkM3oHVrZ/l+Blm3SmEitg6cgXwM5mdxuQ4Wx1F2zItOw3ghq1JHJ94Ft7Y8W9y0Xf6"
    "HH2HbyB2l/f2ou90mhauv6dy/c2dBYsm29Q9gDUWsJcuR4w5cGlhLqfTtywtY21xn7dnGbETrMY57qsj1tZGrNHmSIrKkLX9XNbE"
    "1sCi0k61PrnjyLuhIwO/wcBI1EnOTpBcyWh45agiSFglMKF6nqgYdCd65METW+TBVCeBpMz98cz3xs8ITGqqJioHUqcFEoasKGOl"
    "BFJuixDeff1mWM3c+ew5dYpV0i3bGawcEeg1iGrVo5FHIT80RFivjF4qX3wgwF9zBMZ2KYASLXyfYEGLXaCHZWhKODRiNbJegyFu"
    "hexBnYJhc9l+JUOaGHEWuc2OKpU8YOVlWP7JVI/SRA01iO6OLZaoQuMyJImINllmRR3S0pyZ42VX3KhVdkmlWeZZZVG+9uQOyNe8"
    "nmSYpTKbyluTYkpPcYagLJrbLkGs6lHnuKw4K01lJa5sGPVlOJjnE1TwLCVFomSuAr7iwb5zR8vE5kab5fGuS53hJjeeUuyGwUi5"
    "BbknXGAhQa8yoNdsLq6Dke6xO6obyIIioRUY/BlWKZXLTC4cIIjkl1yDC3c0MxF2M2vECl3NBHSTcD5+mcpw6HOFlZexomoIlOo4"
    "O717owXIMzMjNOqyUBDM5ijfVMh+HPLGVNx4uTX1vs93VkQ9/gomBQHhEfYya0/HkyXz0uC/WZMKTkfRyUDluXECFO21v81n/8Y2"
    "na6pH7fEesZDVm5AHpTDkBZaMT0ZZsiZ7TjIiqQxEqSmpsM5PxX84bPtdpvgWTMSi6l+dxYg9a4OMA/elx/WUcLA50VyjFmMEVQI"
    "Lsvfdiz9Ii+cgLqEnyXKA9aCsUnyhI43InBPkyf2puG2AF7ZVIRRnoWfeHtJJb7D99yLxwa6c57GQ98kYg5xixwe60+E02TZEVpD"
    "Wv712PP1MqINvVxkxfEFkrbD5e+we+qaXOYkXy4DN5xV5K2qkBKE+Ea08gRlc4k3xYCc19sMTE9MCBlqOvhqXvMs3Shc3cLIq2n5"
    "I4sBMWbApqipCbzEcmYmXAiiprVEHbwmg3E+U1pas1zJMohFoaQ1Y4NSG3KVf0onsqaMnPstqX3ICR6n8MenCuusm+v1SirmaBVp"
    "cyxVYsbWtlLanFt9Fn05k3IqaGzreexXWm47ljbbSl1qAExMuD1WAMrd9vEOyCFszXPdakjKaZfUcf5Wo7ifDvszU1Hq8EEFiJK4"
    "Irxe1M7QawRbzxf3JmGeJffOZTEK1TiCFTPGL189xSolVNLrlnR9XngmkpjNpUEz09ORGOncZSWhKa8aeVBR3LaNZCL2m4GMbLce"
    "KpTCahJo+DTybRcL7BwKZ5djWJXPxKIq41BT+jTGX7G6imEDWS/tVIvD42MpwrTjZ9TX3FE7w+xajGpZae47fhRaz116y05pVqFd"
    "hw6n1WhbdthS0CbvoKlRl6MugTqxgv4XnJM9u3tCZqlqYVQTHShPQ787s2JGYVe3h5DcmIdpnfJOmzM7tBThauVyFXYbLAaYlc0k"
    "sAHPcnC08KLdlpf3nRWhLSJxs7IQ5Bwq8MwOtcUovENEjox8KJWFcdkFhCcbAiJqDmy3Qmdl79Vueq/u3KtgObbuDZWqKBRY2vm/"
    "fSwk1EwxZg5Z5lcUcebQFXtFMWgOW7FXFJbm0AV7ha4GB27Dq7usy9FBttidA2jEMlO3V4hv2xejVWHUodGKzrzsBsbLxLYWIEO0"
    "LlCa29cC5CrWtdttKvIV8FBgkfLdZhebL5GZzP/VdyLeT3cywW/XLZK1yXzfpXLgfEGB+w5AS4nI9dk3DpRHUQxtKxTe6Qd3rtOb"
    "olvJqIJyHSV+xefpXR0prAbim7uESSoQBKUTGm1cg5mWJ2GUErF9xeio+0xErEXqp9qUH0Dbqg7LLKcLV2dFeDx3jj9ssY1IL19M"
    "SyxtgTcyXsXAAJIspwEFIsPH4qSjCo6EOAtfpX4LaF9anXdcE9nVp2vc3ThOtnuEA3vWM5VRIIWBl7ni6xxxBcu1BHrKvr7EWzcO"
    "w8Pp3vimsV7u6/Qhx33hKPcYkLgO6W05kAaaLQi3KVNN+g5Qtci4oZqPWFv11VQdYrAacly5oyVtTw/frbvA38XMSjYJSI1hDjAu"
    "T7FeGinkImEJJvNkr4i6XyieTgOYZu2QeSOYEYXqtKvYlO7c8SxY6rssI95W+jX3p+XsD7qHyczRIks6smEtlUOtp7mHQaGRqUEO"
    "Gkuiw0pg0ug803o3jwNmbwU3lGdKCklI1CyWGMkVxl4888UqoyhRlLCAIuEJrEwjl1zfcAVBfrS0MBsorUFE8nDpXWsWcEWypXQC"
    "m2L6ILsbLo0YJvi0QmRLjjtqxrCe24peE6mj2ogaRlCigDJSaK5ZT69mKl3erocLla9HdVGIOyp5Z4rbR2TL3k+C+6AU7nUQ2yh/"
    "qjq1kNtvDYvmhji0DSJcRGxb+dRugIgiXhZZngZ7v4dwChWSimOh6DLhDbW2/yvZwGakkdCWins9eyYbJFnKAerXswJ39GM+iLzI"
    "TGhMWgry/XO3+5Aljya5pkcyjbCVKj74lQxxeQCAQmOlHHnAwSJZK2+esSSCglVJgyr8oIsExm5eeuqVfpm0y6ndCSiH4jbNt7AV"
    "ul9OSz52l893nWTHiFcT7XcvYmnvQIvLbJl6Uv2i1Nr1j3mGXIaAFiWaaIuRUc43E3ekqbuJj9Hs5gDC3SCApDVw1+Zs1UVnK6zB"
    "TcKxd2snKvE9o5tML4pDtLH6YutauDI/vgvdL2wtVBOrvtWup19sbmWzPdUNDamN+2xnmKnU8lds2Em15Nlc7TGw8uMS5lWJyoZp"
    "1K4aU9pG7JYXbmhG9CwkzMHaOm6WsLrr0slY56X3AXam0rQxeKYB193kFIUWXYrNYrMfO6aB13CvDdewtM2VoT5/hlWJdSbTMuZR"
    "+WuU9hkraMCsAnSnmeGKW/DkaipEmkKmSU2osE48WhpjnXJM7dVsbIwNQDfbDTC0WFwdH8vnqHRLn6uP99p3UeK7M2XM0i8vY07k"
    "a8p7H21ntwZdzni1SUrntkkM0zvIHwUuzAj9ye+2p89KwAjwGoD0VIEhylFyIm8+mWYxuWNZhtuse0PGlvwgGyvRZ9WktW9V86vC"
    "YMKqXgSbWgBEfzQdOpLer7R6H3aUxW6H/rQ02M48TGaVmYioSudr0xTHkf+GCX5lUioNt9nyFzlALhNvlMTlxUeWQSy1YKiaSq4B"
    "oH1sogNtNxR0t7YuBslx2y/g7lhX7nY57RQLyjwddy6SYmpVmatM3pN379G9r4CD1G7Z7Hk3Qq7ZpN3aUwrR7frVnVtq5fb3WhIz"
    "v7aVl8wobGcZCIFcYCStXNyb6xgHgeFF0n6bYjeFI3pPnO5Nw1+vyF3OG9fznNQP0kFkcSFif5TePE3ZNnpRmXUO5Jyl9NHiQ4jF"
    "cXQ+g4swjM2thwnirW9zhoejs+cOUWY4OMB7PdPqjBAKU1bcxayEH9fQgzkPFMi9fjkvTNn6IikKQ5uvpw0SwgTlJLMf9jzDMHXv"
    "zLqJsvXPUDl7Ojq1SrWuIp92WrYmfEAuhNLHUBtN4tgzqnPWMthXDn3M09RbNCr+NYoGHDdRggQfJonMRW/IrAD/Ot0gJE1Wp7QQ"
    "Dg5yDiZBhIT1LJiPVQi5Jr11x36c3IVm67NBYAVU0nNM4RGUQ6nNUwOHEK6epTrEMjwEbQVbuC7gOrDI9XyLc8kvDY7eqBA/imbZ"
    "uhBGlXmQ3Zx9Q6tJqDFiePpWM+kszAzZq9m0ASFZmFkNyUIyWbMr7UIyMrObktHoTqxyQPu2pgwbx91sSwAH3sTbw+1JChXk+7XZ"
    "3tJ7vjtTPavbtrMaaqy4s2fxKi0m/fbyYNQA+ySWO6upgM22hDidUi7i6dbiGrsHm5HtHCwgQZhu9dBIya65t4r9gfiQlz91EO+X"
    "PxhNPwpIyouL1OMSS9dPTFalK2DpGFTRHt81uz22LOu6QrbiFoi8ten9YLhQ29nSdNLsE3w9WSQFXhUWkbzqWCEP8+vwqhKvF/D4"
    "1kCQ3Q8jauhudrQI3Ekw9+O7LQWlgEoy2xo+4ZnZKNPfLGDrM21MrYXGmi0PZ2B3/9HKjgZzz7J+ecFNoyEop7IyFIZ4LJNtvVBH"
    "mVbtWU5QD5t6KGPHaZSfLPJChNgmz7K79DFB1hKKdYyni6sovMFBshxvRtKVv2TDme8ppWeYzfHutmbhKKvZDHBvH1oHXOfWLMJs"
    "HC34LEpYk9JQC+YhDMKwdAiDfWa79uIJRukQ++twNQxSwUxqx5CBTWq5nUlUaU3s2mLiclOskR6zfaLCKy7WoMYW0NHCLF5gbUss"
    "CAX7TRpLmGfSnaIltOtqQ1V3NsWciWlllGTDXCj61rGRtBi5Pt90qzg8SgSlqtW403Bb5MJVuBiWzPxKK423O5su1feeHGfywOhR"
    "jCDdzFZLVD7GSfOkfmY3FPOv85m3Pee9Cc3uX+/TIPnXe9idO3NgPcbsHM6AQY6gjGY1j8mouDezMmYkmeAImDVebC04Q9l04+TQ"
    "KvIpLCzPW5azfGFp3Zscfg1fG0Y0Vk0F3BzePIV9mwQbf3xGUbZ166n7TQ9+Rieds1wORTm8cnzBpcfv9YwdiQK+pqWCQeDxuXPH"
    "c3FEEUQbQfgjcVd/LjZdXDulYPmlkeWyCP5Sq8XHy4WG+RWjiadN2URqfcMmd2vngn3yPC+Pg2uJcAlP8rDNyEsV36MYZSSSdLnY"
    "Ya/bNC+7s9VFnYJPZXLUigppxm7Afjkuqawt1s41DYf3IIEzwYqhQerBco+ifbj+nbR7xG82reJBhMUIxu1SxALFe9BQFRXb9P3K"
    "pw7D9oDaCOV5sExmjPquhWO4K/brDgmWu5RGgWljzbpZfrKrtJtS2vQR6oqdD7UThgqdhKEhFizG/Stpqddum0uxV1KSGQGp7iAu"
    "xs0dJ5X52Ou/ihCPdCQBZtaFtedU2NlXITD847LNz5YjW2rG82CFtu9WanHRi6ukDDtOCVWmtsMs1yiiQ5O9ZWEi6SNHAlSB/sIV"
    "MAjbXHY/k3Qfj3+8l8dvG8LZHqODqWy9I8oba8vhil2vNM2aKjAuZBtyrjqy+8hVwpoblbegArufN0JT7HEDnaaa1PXmiRlMRvM7"
    "oBaouzRrl2oBt6XLvb6lnZq3SxhbxnZzxV3BPFJC9n7QetBopSs6t4jijSiqGBdUwS6H/Ap27jJe+NsMgHTPwknmIp5qU/3MIaeY"
    "ITG0CiH696Kn20jNZXygnkoR1RWoJ6FYYJTCcQ4nzxIUOCxTgll5u28Toq2M/TMfvPGswsPPZrmP/edFWch9MSBMrnsI2AAfqZyM"
    "hegBS1OLlxmvkwPE41lZ+xKVfEtDzaUeEW2eyg2vKKFlGSQuwnItbRBV9NLLvGTMDat7ZrfeMeXSLHG0zYLC6TxUKU5uGY8if1zG"
    "TKnIvzoD8l809Pk6MNukYPM41rAW3W0Zq5TGge3WojJSSbyKzLZptXlto9l0a9i27I1x8JwOxnQsZtM8jUTWG4FSr+dbu6I3vTUN"
    "HuUEs3rTyPcz3bXUkY2sdDdLIb6wn4TDbeHt00wtn4to6fvRhiILyLw9jtxF0Rk3wE9v7+pZZefptYpaip7O7oeFjZgdFglUGVOd"
    "bmd3mLqgo02hI3nfFouza8TiVDwk9iNRme7NDEx6owqI2jYHkZwIeJubcgYq0WYy96bxnQ8BQ9WdW0EF+Mc7+Lpo+s6uVt5kmOvi"
    "6R5bnTu1zDmB7/KQO/K0DXqJbtQobxuZ41eTwk5sGGBTGnVdI7+LwlWqsiyLBUk+3vmG2aWrGpQDISDTDZdOSM+GsqTUVaiiEOlQ"
    "0V1iSZ+p/E2lpRVR+qTNCdvNC3KhCM2kn73GGBTTKYGKalOXWUd5qj4edmhrHOp35B0KKAIR3mh+CK69zEOy/V+pF6AaAipjKcZv"
    "4a7WqHbu0rDohk2RO532kXebuawP54MyfA8rGaPo/Qp4l4PjMHTSzmKTKuWMsniGZzHCEUWkUpPege7RooQIA5RhQXIDdo+V8vNM"
    "FfQkGJ7Aji8k0zyb6YJaVAJnm0XRqSZQjXsGPKRjOlHRIj98w4ZgrXIME5tZC1/b1GARaJyo2SGe7cV8V4XDshA6yk1uS74lDt/K"
    "maZJqEN5GE1m7HfL+b0vkIlyiuZfg9NQWCAoqv5uO2MurnpxWL2sy+urhX8yVe4uw8QvMq+TwGHRJvLjnJNLO5rsxtTmWoDC3HyM"
    "T5Gi2PWO0hxk4Fjg6tJRWnaIDa7IUtLolrc53kejctQPI8ityA3D5KRfED8RdrzdNFemir2Fn3MY8RQYY1kp1o8i5Vt8FazythQl"
    "mZQ31eU5FjnNmQVxYmdojUWECRW2uWdjm1t9awiMaKN7hhZelhqpm94lpWnllCUtoUPlLXtZoVUV8Jd2X02j6nX5s4NBqonaJJ1v"
    "dP1s4gGmX2imBR6KBm1oOg6ki5pqX4jtyp6H3Bk1TWduxVzTCJ5htI4OOm3YMbjHYlAXEvSVfsxpJ0gvkuPm9cxwIjmYdlTLfkZa"
    "Ky0mpbeOD6a3lFIOI4fK2V6KGmB3aH5dtuwZFnaHtpqwdq/KBk/TzPSaZ6VCP729DpLwuoS9jAj7rAaPbO6FdT8UAL9rA8BnbTzg"
    "cGk3M/j3REkmoQdr2ugrndSEYsVSEv1pCwXeOEZjnVTLR2Y8SlBN3bStX5KFnZh6DItjoBEOHXd1VzfsScNT2q1AznQUAhoIFY2M"
    "jWgKmJkEy4rb6tuDJcDLrRL2oZk7Wk4fI0/mep3OxlFOTNfcLMNccO+CLCZIQjZK7wGusgZ4QuZ2z8vHg9YcnlEgbx04Usx1XXFU"
    "x+M3LzEzmtOs4yj66GgyhVM63mp3bCW1BIr9+UQ1k7PFfhWFiCh9CjdhVRZAWpTJP2bShUsDPyNO/BX5GebpWPRYxofdUFaGacjC"
    "lvF60cRMdYTRyQ8Vj0U4ymDODGZj3nlpD8lRBnJPQF1kKQ6b3Vh+NJn8yDrYDSvvZzFKHvuJF8xjl7xIDXsJ9d0dHWcYEcCCQhsI"
    "rJn2z7GTl2Tc6OS+xOcrU5qpOtbnDYu1VOFVLws1mjhg9jOBTTxvw6tHVofZDeF9Cg3ytrAW/cRKXua0huXPeVlQLGmskeZxKEqI"
    "w3CQHQwuCRwaw2pcOMy4mXmVIEVGkwUFBB78BcLKj4LRAN6u516E3+OdO0PgFqsARi5GC4HL8lmhdfAFt0xy3HA19m4PjLXKsV/V"
    "AMFNESCY0w8CUpKxJly2a7LbzTSmcEZWymLAzr0hdN5GMGoxYjWfRRwUKJlb0OHdqRidpl3fKrFjT9jLcQSXyAKqSeDORf0ARZ03"
    "Bi+bKHNen1qNnVrtLrN2giIQWHdKarDcqVHbhxOy08IweWM4EHXqIptgvdpLfrxRY6SHGq8qzM0Wj7y5X3NPu3qOGC4Mnzj5/eRO"
    "O1Mfyw2bflmitY1eprl4hcQhq9tsaktx5zg+3vWB1ErCTKq220vT6eMYz4IFbEq9bIV4Y1bfWpnpW/YyEz6rEaodbWFue+VAqjaS"
    "u1XdPjWrJlK2UZoixXu6XhETfgJl8WVuDUfJTkJONIzXUaNV518EXVx31CujOGUKilaYjPdCS8RbOYDtGVz7phdOdiWfEJTftFIy"
    "m4wQiQe5g1T2nYejXCcJAo61ytL6/rF05FAiuLGzQSm2nSm2AjzcjGdl7gxpfvRG0LJ3crIri4vlKbF/8cBPlxW2f+d6q5V73SAo"
    "4gpXnzr0EL395qTSC9UGpsdNiUZK4sLMjwfO/jFKe9EIowAJWKDOKixstGQOFXaQb7LcguNVBOeVaNskvvFW5tStV2WmjlP/tFQF"
    "C1C/2yrwrxUPhMbyqFMvbFLuSOeFFCQKJYOCyNOz6KMiVzYWaTZaRa7MxQSN4lxAsJwBVZWccZK54V9D0TGnm/S4h41Q6Wc3r58U"
    "x1prMA9nrXdCiBqAtcFIj5YBgMcu9uyAPu/nb5DRUKJpidux0saIWmaH0ghb2BbULTzn1mSiZsr2tIrbQwihDkcKdSiSCa11DGdS"
    "l4jreAfeCxarMEqAgDYpld+qsfJXTrNez+5kOkGE/M0GyVm05rXgKiQaayoN0SKqNBIWU0UpIVia3dWgLDPUsPZ6MPQnDHTosF3C"
    "YroASw3zBflqFPZcBQF0ounQq7WPjx3xz2316zpMoHKMMtII+tbPxIuxbbY9kiKjc8/Y7mZPb/dOif2eP81tyzTHN0EymgHTFkGL"
    "nPTrDJErDyqPn/1OAZ1gbYA/tR0exEDALzxlttn5566qQlhLAVNplZaFA68bwlQeZYWLUlvdw7YMW/DWMzg9J3NFKmpXc2CH22yk"
    "3JkXYzLJlGXAd6XnaY6SQNnFhjwifWOr6jEy8RxAzx+fJ9Hav9yawgnBFa4if+JHqBUer0f+uLEIqZEV9h14xJQyc8rRR44gdBxG"
    "VTiWa92RJAvkp33sN/j9nj6gIsQXhbPLkhZuqys3Pt6M6vhI2ihXQVBIqTtWspdLNpXV4Oy7Jxza907ZXYwrl3WyhaIX9YJ2jCvS"
    "sZ9bOj+v3BEGPUSbsdP+sDpo+QSRzKw00O3F6WncSIIFXq2T9ZI5cqIYMq61nSfrxYpHhdl95AFJ7l/+0EceILkCf4fh+Bb+jIPr"
    "SjA+r+ISqr78kQfwHRPxtw9myWL+8of+P1nMBkE="
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
const MKROLES=[["recv","受付済にする"],["got","会場取得済にする"],["done","発表終了にする"],["drop","取り下げ（数に入れない）"],["direct","会場直（未受付にしない）"],["warn","注意（黄色のチップ）"],["op","オペが対応（発表者ツール・演台上げなど）"],["info","チップで表示するだけ"]];
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
