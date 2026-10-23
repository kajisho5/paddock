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
    "TuZ46IwyKgxn3SQcFfWN9quXQuFd5sSloUsJbT3uz43D83BEO5l0ZW6kh5F+aERk6awbWRVqIMPRJyLJVM+y+5bbpx4A45YstVoQ"
    "L05WKoQRFo1SoFmuAHGpdk+CHYnmK0B/+dK+9T10FIl0x+QVr7BZp6qYGsOy+rSDeGxQqD3DJqmOAwHdKvZ65pJfghuVPFWtwqeN"
    "8PuYuB2JA0sim9PrpVgcBYkyHvaKnvJnNRcKlvR0KDG4UDoWX0KvFesfCCmG8DAYk7hcDuESX1Viut3cjYc+Q2VFfI6+uubLIIvU"
    "U3YQupcrLCuDBIAQG4mRem+Khbo7oehOKKT3SPGYKqbHFFKfRGKOdvI6MQxC3TGcvUyMNlSDX159jLU8VH2M7T9YfXX0r5ApoOHr"
    "2UMIVPO9aisowcJZQTHRIwhVGmZC+f/F7qOGvEWvI4e3JZTWK6t/gamV1XtRXb3PkBEWn8+Nzqbg1riEHzduKcV6oVrkmx7uMu3R"
    "oVhCy16ntAlGwedHfFax64GT7rp3Y0djt7TxhMS23STbhRfLuJOWApP/xs3+gBs0FoZOtgXvd+zaHc8yh3UsSpw8ris8tuv2xPKg"
    "xw7dym2vfOyT3M6u0soR4oN6Beoq1YzMFT6Os51NJnG5F5/zHFX3HA0k4lGWZGp8Shhn8qKpYfy7i/2ks/YST5b4ozU2Sfc8Dcjv"
    "3CD5sb7WN5/d92O2MxZpSTZib+X328M1y02S7XsFHQ3jq0/k7hgqWO80GzuY4enb8X3bv29Tex/y4PkG28mDjc6rjfX2hqnsbWHf"
    "cdSbXPskkw10lDMyGV6rOBDZqOgtvqwqN3aeS7VIXcW6rOO5UgRceykVBJ89lx7fOkpXsL0mM621N2Qu2KRltpedVyrf8/WXMuP6"
    "2ovnMufzZ8/WZdbOeqf9QmZee77W2VC+5dY21l6+VI1tvHz24rlq79WLzjPdZ15H0K1ttOXwBRxlN9ZfvnzeVpU8f/HixVpH1rK+"
    "/uzZxsa6bPj5i04bsm6YSjvr7fbaOtSrdDE31jpQXENTR8hZeP5yY/3ZxjMNXB0hFVTXn7980X6lNUBNhFLUlZ7jdBdMTEVW4DjY"
    "HibuGW4qfPi+DVNeqGOc9qLdlge4Nr11JIyyIh5RZnr2aApFVTgLyroaxLOetONoi5bCIKv/d9ILyYl0HgCqhn63EdeDjMUrpDPT"
    "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"
    "7Sr4W7fdlMm75+u3rd+3Ha2Jl5leXlnl67s/Wq9vNy+tXa3/Zr94Lh8oby9qupGYe/Kb24+fvxT3Ja6kuE+z2113P+l9T9v9ywJx"
    "7wUstaLL3A0+edu8xRHoAXpYmvPuoXmLkMhyuPyD76lImrckQdyurrDb1RW8IpdjdLn8xNtP7WvefkPvt3E8td+wYC/e6OUXH6DD"
    "fYItvfoIKm8S8DXisBCOn8EbHn0DLz8+te8ebg15mL+6GnzzOjzrp6Xu4MMGlPvk/27wyZv/9tt//1t/9lv//s//tx9+687kP3CR"
    "m31483F1W214ID+A2epxAfe1k+2+BNXff/W9ruy87CWa7u1Sw9sF0QJv3j2pqi555Wu4te/TW1+9/VrDbrV+w0MUV08T9NE79BUD"
    "e5fQttNf7OyHaXafOS/A/Gtlyk8D9jxYn57ePkWUvP/iD95/+c/ef/nv3n/5k/df/Ont88t/cf/89fef//77z//4/Q8/f//F//3+"
    "y3/z/ot/dTv5xX9+/+Xv3274/I/+8os/+Ms//CfvP/+37z//g/df/Prt8/O/8/6LX3v/+a/+5Q//2Z//+P94//m//ssf/8elkJ/+"
    "L//Poq3ff/7/vv/8R++/+MdvHrAP+4FvXoR7438OyPjOd34OxrgHAj2q1kXzPPbWrfMewrvD6X+ovBfM8hXf0FeMWpcshv/9l796"
    "75Vfe3zQZ1zx5v3n//jWMU9P/5t/8Xu/sdin95//3r1jfvP95//+L/71H/70j/6ZJt8793fevNj8LrhFo7yYm68oyM9uLqdny3KX"
    "yq/ZkeCDpr+j/mV0PzThX/+Hn/79P37/+T+9139vyPMw/NVPfu0+PIsl/dOf/urf+/N/8uO/+smvv3lAlrF5tXP55aXnj07AT2+m"
    "ZiEOd1PzcfHZVx2C93vePTz5wh9+JlV+XjWDHj2Hy78b8+VfyPDjt2cWfF9UeFwHnL8aVvTiZ7w5GB/dTp98dN+Vf4vfXgzYz3ZF"
    "vLhbg6BYxu1rj/Puoy4Oirdt8expvPf3Z49aUCxvmu3DCt9rH6JYPrOe+10PwdfnYF59zfvzvDb8VVN3fz33MzEunpj6ncM+Jqp8"
    "cRp///4Ujz3yyb3v/udPuZtD7+60/ew7jx34dO4RGHz2/ef8JtmLHea2Tz6JD7W+ckPc1tE/LCs8RXi9HofsozxoWy8KXobjeVr/"
    "zQq/+9X47zZfH9zbe9tvHQl9UGqvd4/edOSr9defsYZ0g0Cfvlq8hX7GPQt0ujsMnkXiBqg+iEQTZHeBeOyxhWqe3nYvT4sGz6Zx"
    "X772cBiPPuflZPDKAgjTSxa3ffluufq40eGpp54H/tkj2D1K8V1Lv/9ymbj/5v2X//b9lz98/8U/+svfWhTK379P2T/+8x/9y7/4"
    "vd/Smbsquc3h+8Hfu0/v33mcxq9U7FLqB9T4VPQP33/5W7eiv/jj918uZuDL28FSxs+u8t8+GoO/+sl/edRhf/WT//rffvUfvf/h"
    "b3JTlZVN0HwL/BZ/C8JovrUU8vSrH/69pYS7jfmP9xJ++66CltL+95tG+vzvLCroKbjy8//0/vM/uZGC//of/vLHf3qr9/ZA//D9"
    "F0s5P37/xedL1YtO++mf/MmtGbcC/+mjCr2rLPzVsz4N6sPP6by/80oJ/s7NG/CwIm5m/zaUxtO7gj5sJ66eld8zeTWaxwj5+xal"
    "T59+8OAG9921r7q7uWVQvW2bLm4Ht/y23VdcQM1H3S8iKPSd79wXA7xTe0vZf09b6izXpne/SPyMS+5yaV4ufah4EazXFS+nP20+"
    "Lh5u/pzu4w/VPUwfvxT/ML8cu589t/zrymqoHgGDf0sj2uRv7U++//6LBRf89k1QvvhHj3Grzyb9d95//ht/9ZMf/8JL4Ov7L75Y"
    "SN7t2hd/9/GOZZxfh8Xe5PU2Nr97BxU3yfqzf/e7i4D8xf/5n3/6G//0Xu6PF/Bwl+ZFPBfb+Xf//Ef/6aW+Zczf//CL799T+/y1"
    "zXrz8d+g6Y9z6YZXnu3m1x7gVt+717jsWWfclhbuIZhPmvUpV+Pb4lvJU2LPMvzWLR3QU0q4ZeYVL1rkNQz6bH4KT/ygqb7hjr1V"
    "/2T7ny3+M8t6uHtiP+i2w804fc3WeVl2dwZ83cYFN90WPLfqtaKVy6+6VJ9WNp+iD25Loi/OvvvK0XD/+CXok+XzY+gViri15pff"
    "3NPFB83S/lsqpOXXT0djHCzo4VdefAtLg16M9zeWtIKHJ9f0V8JEPwj7Zw+fVre1pCG45ZnwvWppXnB/7ncPP7/Ur7bNT17I+jfv"
    "vMOuNy+t+AYVecUZFht/xzOvkMkHTHQPJLoZyKfFga9jk+DngpG7ZHyVVM332NdX4ZqfPcAB8u7hucjq/ha7xwKD+/2v4mNfUrnd"
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
