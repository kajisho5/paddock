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
    "waZ/JNgWMP5i/I9x0AQ30t0b/cFiNjzeendPp3eXY5+0fZ57zfXd/X3fnZdkL+Wpt8+33t3Svn1ggVfo66Vod994um28fmfhqO6T"
    "WxTrzVK4/ebNn/3Lf/4n/+Tv/rc/+N0//vHvvLlJnrcv/qQXzP8NQfDupRtvfuUNQD0twR9k3inIllZ+9RYL9GgK/PCv/PAVMegb"
    "srjx/i89w4uF5k+JwB7fQ//i+fnRj24+uh/9yPzmYl069/D4Zu5XpvBtfp6ihl6yEVS3Nyrf1sOjRf7En3d2fbswUPLJdGehZ355"
    "+HnM9MLNr7hp+eEjP7275yZ6o92E6dNBtkXVfeeRK5a6Xz9YTIImT9qbY/sWbhA13iI4z28+HtyHTecPxmNy03WPW7u3LO7Jy4GS"
    "7O6LaD/E9929TM8zBn9YY7c6X3flpRDw5r/9l//r/Ze/97N/8Rt/8pP/9Obh8/txu+zFnkMevQnlImLKZcx35vxs4dOXL7fzPveA"
    "/Ntu/MIGtwdd0t057Ts3TitfyH6DAI9HDf/on972/j69lX3m7ncfeAX4MATksx/+lYUlf/jpfbdrWYc32Xh6OjUZLLClCZ61zy1Z"
    "x3e/W3zS37wiiX+5PrQLv99y2zzdvPHH3Tf8FOHeBI8q8NPvQjf33IKO/Oy2PbKM9fPyk6q54wT2MfXjzYZ4XOjho85+uPRv7yk7"
    "HxHTc2zgF9nrSfsgqz6ZHrxvT8JCm3s20x+0XVlVwfmzN7/ysy//1z/53X+2UOdlTn71ibRvk19EyE+fS5T3GNLP3rz/8d/92X/+"
    "vfdf/taf/OSP3n/562+AxwfAm5/95J/86U9+7/2P/96H2Xqcq6d5XwRV+UjnR077HyTx09UHCt/eqPLFLSXZM439G3H+UhqXr9HU"
    "Z28XPV8+6vnyWfvdm32s8o43uviuiJabZfuDsrq9n+gH3jd/9e7T++R5L5P3xet32N4M0Fu4vblIx7fmPVbu7VO/qP6clE9HC370"
    "o6ebY3C6JN3rR4tIMJ/el3Dr1Uuq56Vr5i3Md2H54MN51FcnPp6Bynfv+z4fCPokBZf+3Hr38F3zJX3ti0Q0u3uEy1OShJsqAj6B"
    "1rdI66fMtB9ca/6t3P1Eg976ydPpo3cP4cttwVsW4iJiHhNzvWnvktH/JLxxQ1D416czD9lD+Em0FL1JpnvyQ+re7ttV8FdvZymT"
    "d8/Pbye/bwdaEy+zvLyyy9elP1mvb4WX3q7W/32/eK4fKG/vaboZMbfDEuHtx89fivsWV1Lcl9mt1N1Pej/Rdv+yIKF7BUur6LJ2"
    "g8/etm9xBHqAHpbuLCjvLUIiy+XyD75nImnfkgRxe7rCbk9X8IpcrtHl8ZPdzrav7fYber/NI9t+S4O9eKOXX3yADvcFtlD1EVTe"
    "OOAbhsP3vvfz7IZH38DLj9n23cOtIw/Dx7vBmw/vJP1iaTv4cPzkvvi/H3z25o9/6+98509+89//6f/24+/cLfkPtshNP7z51L/t"
    "NjyQH8Cs/7iB+9rJdt+C6u+/+kFXdl72Ekv3dmnh7YJogTfvnkTVJnvla7j17/Mbrd5+o2O3Vr/lIeqrpwX66B36SMHeObTtjBc9"
    "+2GZ3VfOCzD/Rp3q04Q9T9bn6tuniJL3X/2b91//4/df/7v3X//h+6/+6Pb59T+7f/7G+y//5fsvf//9j798/9X//f7rf/3+q39x"
    "u/nVf37/9b+8Ffjy9/78q3/z57/7D99/+W/ff/lv3n/1G7fPL//6+69+/f2Xv/bnP/7Hf/rT/+P9l//qz3/6H5dKfva//D+LtH7/"
    "5f/7/sufvP/qH7x5wD6cBr4fWL91/heAjO997xdgjHsg0KNoXSTPI7VuxHvw7g6n/6H6XjDLR76hj5TaZtEz33n/9a/dqfLrjwN9"
    "xhVv3n/5D26EeRr93/qz3/mbi356/+Xv3Anzt95/+e//7F/97s9+7x/r8p24v/3mRed3wS0a5UXdfCQgv7i5nJ41y50rv6FHgg+S"
    "/o76l9n90IV/9R9+9nd+//2X/+je/r0jz9PwF3/46/fpWTTpH/3s1/72n/7Dn/7FH/7GmwdkmZtXedhf3nn+6AT8/KZqFsPhrmo+"
    "Lb742CF4L/Pu4ckX/vBzTeXnXTPo0XO4/LtZvvyLMfz47dkKvm8qPO4DDh+HFb34GW8Oxke302ef3A/l36K3FwX2810RL+7WICiW"
    "efvGcN590sVB8bYonj2Nd3p/8SgFrfIm2T6c2nvtQ7TKZ6vnXuoh+OYaPFff8P487w1/rOrub+d+NoyLJ0v9bsPeD8m1L07jH95H"
    "8UiRz+60+58/p24OvbvT9ovvPRLw6d4jMPjih8/pTbIXPcwpTz6JD62+ckPc9tE/bCs8RXi9nofskzxoWy8KXqbjeVn/91V+96vx"
    "32+/Obm317bfCAl9EGqvmDK8ychX+68/b0e1vxd52byFfk6ZHzztMz2zxA1QfWCJJsjuDPFIscXUVN92L6NFg2fVyJevPRz2o895"
    "uRm80gBz9JLEjS/fLU8fjzk8Uep54p89gt0jF9+l9Puvl4X7r99//W/ff/3j91/9/T//zUWg/J37kv39P/3JP/+z3/lNg7mLktsa"
    "vl/87fvy/u3HZfxKxC61fkCNT1X/+P3Xv3mr+qvff//1oga+vl0sdfz8Jv/tozL4iz/8L48y7C/+8L/+8a/9/fc//lvcVGVlEzTf"
    "Ab/D34Iwmu8slTz96sd/e6nhrmP+472G37qLoKW2//0mkb7864sIegqu/PI/vf/yD25GwX/9D3/+0z+6tXsb0N97/9VSz0/ff/Xl"
    "0vQi0372B39w68atwn/0KELvIgt/NdanSX34BcT766+E4G/fvAEPK+Km9u9T+Zi26cO8VdWz8Hs2XvnmMT7+fkDp86cfPOyD+9na"
    "1xrtlkD1lnGluF3c0tt2H7mA2k+6X0ZQ6Hvfu28GeKdbbjv/nrX0sDyb3v0y8XMeucuj6/LoQ8MLY71ueLn9efNp8XDz53Sffmju"
    "Yfr0pfqH68u1+8Vzz78prOLqETD4tyyiTf7W/OyH779acMFv3Rjlq7//GLf6rNJ/+/2Xf/Mv/vCnf+Ul8PX9V18tRt7t2Vd/47HE"
    "Ms+vw2Jv/Hqbm396BxU3zvqTf/dPFwb5s//zP//sb/6je70/XcDDnZsX9lx059/405/8p5f2ljl//+OvfnjP7POXduvNp/8dXX9c"
    "Sze88qw3vzGAW3vvXuOyZ5lx21q4h2A+SdanVI1vi+8kT3k9y/A7t2xATxnhlpVXvEiR1zDoi+EpPPGDpPqWO/bW/JPuf9b4z1bW"
    "w90T++r9Nnc31Me6zsuyuzPgmzrudn7hFjr92KvXgnbsP3apPu1sPkUf3LZEX5x9952j4f7x16DPls9PoVeHB2+9+ZU392zxQbP0"
    "/5YJafn109UYBwt6+NUX38LSoRfl/a0treDhyTX9UZjoB2b/4uHz6raXNAS3LBO+Vy3dC+7jfvfwi2v9uG9t8mKsf7vkHXa9eenF"
    "t0yRVzbDouPveOYVMvmAie6BRDcF+bQ58E1sEvxCMHLnjI+NquEe+/oqXPOLBzhA3j08V1ndX2L3WGFwL/8qPvYlk9v9lOaHPbWP"
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
