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
    "PwnmVxfJdM9+SN7rfbvy/sqymzJ69/x82fq97GiNnMRw0sLMX7/9yXq9vDy3drX+H/vFc/lAvhzUtBgxy3aJ6/Lj5y/ZfYkryu7T"
    "bHnr7ie972m7f5lF/72AuVZ0nrveZ2+rtxgCPUAPc3NmRP8WIZD5cv4H31ORVG8JHF+erjbL0xW8IuZrdH78ZLer9Wu7fUHvyziq"
    "9bc02Is3ev7FB+hwn2AzVR9B5cIB3zAcvve9n2c3PPoGXn6s1u8eloY8jB+vBv/lD4eSfjHX7X3YgHKf/N/3PnvzR7/5d77zx7/x"
    "7//kf//xd+6W/AdbZNEPbz5tl9WGB+IDmG0fF3BfO9nuS1Dt/Vc/aPLGSV6i6d7ONbydES3w5t2TqMqi15t85/Z9vtDq7TcattT6"
    "LQ/RtXiaoI/eoY8U7J1D60Z70bMfptl95rwA82+UaTwN2PNgfX55+xRR8v6rf/P+63/8/ut/9/7rP3j/1R8un1//s/vnr7//8l++"
    "//L33v/4y/df/d/vv/7X77/6F8vNr/7L+6//5fLCl7/7Z1/9mz/7nX/4/st/+/7Lf/P+q19fPr/86++/+rX3X/7qn/34H//JT//P"
    "91/+qz/76X+cC/nZ//r/zNL6/Zf/7/svf/L+q3/w5mHzYT/w/czypfG/AGR873u/AGPcA4EeResseR6ptRDvwb07nP6nynvBLB/5"
    "hj5Salk0K/73X//qnSq/9tjRZ1zx5v2X/2AhzFPv/9af/vbfnPXT+y9/+06Yv/X+y3//p//qd372u/9Yle7E/a03Lzq/8ZZolBd1"
    "85GA/GJxOT1rljtXfkOPeB8k/R31z6P7oQn/6j/87O/83vsv/9G9/ntDnofhz//g1+7DM2vSP/zZr/7tP/mHP/3zP/j1Nw/IPDav"
    "ErG/HHr+6AT8fFE1s+FwVzWfZl987BC8v/Pu4ckX/vBzTeXnVTPo0XM4/1ssX+7FGH789mwF3xcVHtcBx4/Dil78jIuD8dHt9Nkn"
    "9135S/z2rMB+vivixd3qedk8bt/ozrtPmtDL3tbZs6fxTu8vHqWgkC+S7cMpS699iEL+bPXc33rwvjkH/eIb3p/nteGPVd39eO5n"
    "wzh7stTvNuxjosoXp/EP7714pMhnd9r95c/ZxaF3d9p+8b1HAj7dewQGX/zwOb9J8qKH2d2TT+JDra/cEMs6+odlhacIr9fjkHyS"
    "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"
    "oWMH0Nt0MWDnNF+BVAzB0t3t9UhXbq8Gm86UGjd3hmqn7uMDJWMx+8sIfXc9BAg+SLSVPtu5JVdCA+V1iVatUr+0AhmhaYAeh28F"
    "suXeBLP7fFMIbuB7/QIAM1TYI8Tx/LUagKiAOnd1puSfN+i+Rot3SdiZZSgEmvf+FVP69QaXAaI2QkvI/LVsMvZt98Xgi6jHD24m"
    "C8Dr6Kjc0XmPe9G7jopppAC70bx1SZiL/B127878aq8kn105gnFe/yRfdHu9aSQ/EWS23LWplmS4kHv+dJ9SpHeTlVgIz2flbSSi"
    "Ja1rm74/xeJX7c72h3LSZLhtaSV/MEFh3Sd6PYENWCJs21Gks0fFriZcSFhy3cnoNCW79foNS6Rdz8iR5nqvj7F0KLij5di3r8Fo"
    "gQpLhDSGW67P2e1fpBbYInLsS1/WID0Iz2i5y/xA/v3oErIt6vCkT3hjX8oOkx9mh6kMqZGSM0Uaoulv0a4J+jq/NPj0Yu1+Dj5h"
    "T5D/ZgSFF2ors3zvlI4MxNcsELVI3YnjcNUKSCxRNF/Rfb2s+YVpJiONNuYgr/T2AqRrolhyW5IrMKGVPXOllenxJgAHOaPz85X4"
    "W1ny9SznZXS+NhKEy8dJppasuRRlNgeQKToCfm9LQQnQPODed4n0hlLp8pE2WTpUmOlFEyrvF7YOrRzH2KnymJ6hnCs85ZsCMRLg"
    "/fruUajkp4b7pwd4pcH0NfD6aGXASYAAOApXdxmiZzKZMj9WfpPZ74Zi+pUFI3f0CUTcM31Gyfk63RuSDrAzwNugjLU0yXz/CSSJ"
    "kby63hQtB3sygY4SOJixwpW9iz27VvkAutXcTf0J7u5V7cFc7KBy/XEaV85ppRxc9lY2c36zVqnpt9EuI+asR46e9KfpYCsv8iqz"
    "V1y1hdxKYcImmKWYqqkxNqHucSYAIEYf9uRVoOR2ich2iR/v0QpZiX4+MKlur1cXawal4UaD60xYrfwAKWMyMaKZLoNPV/7V2VEG"
    "6auBs1yGhtbYfO7Hv8yagLLm+3a92BkSP5qx2SwkO89nh7LcQO5WFsZ4KXZ9De3GfkpQLGeQr2bm10Gn1sa/TFzw0vw7VeuBmS1K"
    "Byv9EQRD/hqW5RAx7opJASdVpARzAAfXt0Zpx18yjpG/T/ywX6D1cSqii6N0QWQOyCP8foYoWqjh2lLJChREi66A8nB78JtvKS6o"
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
