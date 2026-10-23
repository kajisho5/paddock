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
    "wq//6q9bM1Gm4X7rd9a23g2GW7BpvxPd2Xo3jPDX2vpg7e5d/DV89264uk6/1u+svtuUZXdX1/r4a3UwWH83xF9bna2+bGW4dadz"
    "p0PtrcWbaxutA/FlEZaAeNJoMrl1ciG3pjhFA2RPueXsMe/kJ+z3ME8HcfG4IHs0WfPx8zCJpUZ5EqctlSCN3r15/OLLx+YtEegt"
    "0hPLdnefP9/9KvxiOj2KewudQNeDPtL8vCUWtM/wWRKf21bgARpJk0nZQlVPi8RjrZ76G8g32qk4vfzSfElPLbQxtm9fOG9fsLco"
    "gLUTgwfoFLkEPfoPZgXe2Z+PHrzl6wHkmbMeMONHIZvmoCWuZnqttnfth2f9PGXv0vxoF8AL2kfJ2DNAG8WFeRzlgyjlzul5NCl3"
    "JkdmWFSwF3/Q3tmw4RlGJtJRbSbHwBtNNAyRxa8evH6MWhi5yZ8//kp//E77hamxQdPPBvolPr2JC+MRD3h4cGkGSnXRNiXql+YL"
    "QAVfZlhPl8j9hxE5/vb99yaQznj8RhuoqAl+OE1K04u2XtEdVCY2OX036RfJO0wFc99TVUiKgk6IiBN1mYlBrPdhkkXjEKvwfmbx"
    "KCn1vVFlS0u6b4NwobOMMllKQHhJgzq5YLKs2Lo17K6cTmK08nt8IS15UB8de5d28OKSRuOLyxli5JPTsM24C2QDwjU0ELq6tMcB"
    "P9JHAUZ4uSJHLkjp81pGNPBOTn0BrSnJNOBl/YKW5tI5XLqFGXpoyHl9iSaM9y9X9norBRwUaSpNk19JBpQ4VhzHtIYA1aEa8H4r"
    "eysInOXflTgju2Ff7JZU7RiWpafeDeIJtUjQniC/rh2gCEhPP0k83ygS4VONbagpFGnT0JZaUyTN8JEgE/LZfnApgRYLDl+6zD82"
    "3p3DtKlwNrtDD9r2tXNlaWQOhU3sq4xMVWJdhGOA9xZ01WLJpJM1zac0FUyPQJxsaga+uEiBl/S8fK17XSLtE7Misp/QK8N5fBkz"
    "lJz0PsHEZ5lUo9vhBJwk328fVF7bBTubsNXXNy+T62ap/BKpfDwmuLV0UmALfZWGbzEzS5Y5S+rTciYDX2qC1LpjUyWXzJKtDApl"
    "r/TSPUVvTVmGTHOXfJnxzqM3i5w5yhxjpXgrEjahy4IT5pcKyDNpBdBBUkaAU0f3bSW3qlp9lCjAgupSSISiH2PFna1EpW9UOESI"
    "Fhj2wfOWrAHEGKUNr9vtgP7X8pftO/zeeeej3j/ekL5j99t2JZRoIDEkWU5iNbP/+eJivpLR7mZLhcyoYyyqU5NKHCM29dNTuJE0"
    "ox78E3A5VTbGRdOLFca9q7MgFlEZ4CxmKtYL2dcoNKmr+haq2HA7F7IxSU/E5kNFUcRN35yrb4h4YJ8Q+UBfMKxKflxEOABHeGnx"
    "a1PDn08kQLjcjw/CTDdMLuz1yi/UKBStY8ehiZzGse+hozuCdYwZ2LUnj65/xs9+KZllukAyWGjplf7KWXqv7eusggY8cR2z51wY"
    "DVPhVCTykqAwF57o3qgiWu2ankPrqp/LqI+qeW4Bf0m0jdsHg0p4n5focutO5Qf7CYrM7VQTRyWSh/q7paSrPsgP4CKa30DiyqMe"
    "Aa5JibOJ0NCgTPdTkqr/bqkFrwciJWBgvkVLfMy/OAPgak4O0WRqMhqNf2ZEbgZBcGi6UCKAkJIHWsrM18hGhnI5KfT3qu+YppSh"
    "1Pd3og78F+j/YzLTWligY/QIjp1FdW8Udsp65mXYCSThcssU8VM3wDlgedPBe5aaTNSKbClhZqbxst54idq5mzZ/GLm4VC4VIVNc"
    "J0zNS7qMe6sK4ABW14c3cxUR+zCp0FlSg8AQN5LGR65l4htLj/udyrs56gDowA56W5keSLMDuI9qFmaJCqKLaDWKA8pMxxeoOBDk"
    "hIM0pD1Mzkqx5OYXFcqFCxThmBMdTnZly66BWZfLjVxVIoGIWIGI67DmlbQIVXKMKvhI7YUjPNrNFP40ZAR8+u6yRHeOtgCkQhzE"
    "fnoglToIBFVBePUuSARgAhy+OFPySZMDVUuk5DTzFQpSEd3rrGxUh9QPvQQqvPNvR9185Szs32/34C/+/wcrG0t9+CfoB9H9zV47"
    "gDIBVcME/i1l2zMXSOHofPfcE9AoAWaYLaUp4JmfVcyMc05zSgveb+EsRePkNrnwALlF1G4s+acQd/f/oe1Nmx7HsvPA7/4V3TmO"
    "jszA6wJI7GW1K7ADBLESJAgqFN0giJXYd7C6IrqqHBrJS3iXQu4Z93gZeZVkh+2xZiyP/ovSreWT/sIAfJd8s6o75HDEZEYyQQC8"
    "9+Lcc895nnPvPbgfLqdm1vBLy/f5/7sF282OYlGFh8URzFpyZ1H3K098Clrc1yPxesxR8IN7qrAfxJf5wr2Cx3oe9HHZhT4tLP17"
    "3/vufqEQ8+EjTry7usU5f+SMX3H46Yn6v3v4y+7bD+P5ubhL+fa7S9aiZWBcP+IfzbJ/4iNWcZ1ZxfUXsYpFdp88rc///l97Xp8/"
    "uPUyK/TuYaExT1rRlsvA5x4jSm35NJRfZ27Rx2+gz/v+4MftLS/9MUsx+6yZAcyyw/pZksurKmeNvt+/naGAn8/O6o3fz9J4Zd1f"
    "rSS+zx+5S78+dcVL/PD5zH1P0ruH7bisOl6SIX27/LkRRbaEuZZa2PHtt8t/9/N/+Lgk+y9s3Dx2pic9a+//f3dRveXg3effWif+"
    "6l2q0z1IcNe5p2jBvd+/bUCeoMezkZhVrF4eekHYT+PLbZo4XPIj1e++aBcdvzfhKVLw2duXw+/fLz4syrPwsCfnsTx9kT8udH+i"
    "oI8NWs3tWXj/MoC8tGj8Vyr6avKWvSOw2XfuZhezkLl7ix+eJtHfPY632Ry0cTB98twbcwu/O/uKorx30B2lNeV90vf+eW/iqyxO"
    "48cE4dFs589mO3/M47eElDJ/8Rb1ExVe5DTX/3L9SZsfXk48eS0EWpLRvJQSxcGSQGJ+hLb5a99YZ7xaLzPq33rKeahr4z0f6vJI"
    "i05/44mebnzZb/eyZiu655mcRffhjNvw8/GyDvpuQT4EcADgQVnszezpytfe8b6Y+C60p2GsjY/zqvcdK83SgfeD52nwp6+f/vLj"
    "wQxP75Jr73GFp656XNY3259XVqd86ulHsL2Eiu8P9cyyP4jqr0wfhaJ+aYX68I9+9MQVXkKK96f7EIzyP0QNngp++O4zVVhmvB+N"
    "4gf7eu/h+j7yHk8+NeZ5PdKPfuT43+inh4/e+X3vmcdMGq+e41mrXmbPv9Ws2SC9xPSe41rfjuN8uOXDq7Y+xHPW2Aejm96Nrlwv"
    "K68WW88X34cenPb17OX53qFvmuGvLK14HV151fLP3vwvb54Xr8yY8Wlu/RM3dx85yL2T75GixfS/6thZZz+Cjefx7dP6qvtLfJf5"
    "puf004tuL2Nl0ZunSYTYv7x5dw+Wps8vTP3OL757+sFsau73PxX8zfs/LBSW61kJv/e9V2p1P/NLsI8uzXnCDPdzS9Lil8VH5X2G"
    "5ZffXBZP++Yxov6Dxy9FEKRx7r/5ldfsemnd8o6gYm5Q8fQuhHup3/9Q9V9Nn5zh5/e9Zf7D+Gn+0Lrhp+1Ds8QRlux198nNB76Y"
    "Tc7chd92xdL4gKDQa8NGf2TYZjD+Qv6HyK/9RXT3Spv47dOpd/d8enc79knTZZlbT+/uL/xu3Th9uZ95+3zq3ZL37YMKvEJfL7e2"
    "94mnZeL1O7NGtZ8s61gXprD85s2f/st//sf/5O/+99//nT/68W+/WSzP25d40gvm/4YhePfSjDe//AZgnobgD1L37KdzLb+yrAZ6"
    "pAI//Es/fM2NFmSx6P5ffYYXs8yfMoE9voj+JfLzox8tMbof/cj45mCdG/fw+GruV1R46Z+ndUMv6QjK5ZXKy3h4ZORP+nlX17ez"
    "AsWfjHcVetaXh5+nTC/a/Eqb5h8+6tO7e3KiN+piTJ92ss2u7juPWjGX/frCTAnqLG6WwPay4CCs3dlwXt58/HAfJp0/kMd48XWP"
    "U7tLGvf4ZUtJeo9F1B9W+N2jTM89Bn8YY0uZr5vychPw5r//1//r/Ze/+7N/8et//JP/9Obh8/t+u/SFzyGP0YRiNjHF/Mx35Zwh"
    "34cvy46f+5L8ZTZ+VoPlQhu3d037zqJpxYvYFwjwuNfwD//pMvf36XLvs3a/+6ArwIdHQD774V+aVfKHn95nu+ZxuNjG8+O2ydqf"
    "YUvtP3ufJVvHd7+bf9ItUZHYu04PzazvS3Kbp5OLftxjw8/7FvxHF/jpd6ElPDejIy9dpkfmZ/28+KSs7ziBfcz9OGOip4EePPrs"
    "h6F7e8/Z+YiYnlcHfpG+7rQPtuqT8cH9difMsrmnM/1B0xZl6V8+e/PLP/vyf/vj3/lns3Re+uRXnkT7Nv5Fgvz0+Y7ivor0szfv"
    "f/x3f/Zffvf9l7/5xz/5w/df/tob4PEC8OZnP/knf/KT333/47/3obce++qp32dDVTzK+VHT/idF/HT0QcLLK1W+WHKSPcvYW4Tz"
    "F8q4eI2mPns7+/ni0c8Xz97vXu1jkXe80UZ3RzSfLJofFOXygqJlqcvHv3r36b3z3JfO++KVeXIXArosuHdm6/jWua+We/vULqq7"
    "xMXT5oIf/ejp5OCfr3H7+tJsEpynFyYsrXrJ9Tw3zVkW+s4q73/YkPqq6meg8t37vM8HgT5Zwbk9S+sevuu85K99sYhOe1/h8pQl"
    "YXFFwCfQellr/ZSa9kNozVvuu+9p0Bovftp/9O4heDktuPNAnE3MY2auN83dMnqfBIs2+Lk3Pe16SB+CT8L51sUy3bMfUvd63678"
    "v7LspozfPV9ftn4vO1pjNzXdrLSK13d/sl4vN8+tXa3/x37xXD5QLC9qWkjMsl0iWH78/CW/T3HF+X2YLXfd46T3PW33LzMSuhcw"
    "14rOY9f/7G39FkegB+hhbs6M5d8iJDIfzv/geyqS+i1JEMvVFbZcXcErcj5G58tPvF1rXvP2Bb0v/ag13/JgL9Ho+RcfoMN9gM1S"
    "fQSViwZ8gzh873s/jzc8xgZefqw17x6WhjxMH88G/+UPLyX9Yq7b/7AB5T74v+9/9uaPfvPvfOePf+Pf/8n//uPv3Jn8By6y+Ic3"
    "n3rLbMMD+QHMeo8TuK+DbPcpqO7+qx+0ReumL6vp3s41vJ0RLfDm3ZOpyuPXm3zn9n2+yOrtNxq21PqtCFFXPg3Qx+jQRw72rqFN"
    "q7/42Q/D7D5yXoD5N8q0njrsubM+P799WlHy/qt/8/7rf/z+63/3/us/eP/VHy6fX/+z++evv//yX77/8vfe//jL91/93++//tfv"
    "v/oXy8mv/sv7r//lcsOXv/tnX/2bP/udf/j+y3/7/st/8/6rX18+v/zr77/6tfdf/uqf/fgf/8lP/8/3X/6rP/vpf5wL+dn/+v/M"
    "1vr9l//v+y9/8v6rf/DmAfuwH/j+zvKl8b8AZHzve78AY9wXAj2a1tnyPEprEd6Dew84/U+V94JZPooNfeTU8nh2/O+//tW7VH7t"
    "8UGfccWb91/+g0UwT0//t/70t//m7J/ef/nbd8H8rfdf/vs//Ve/87Pf/ceafBfub7158fmtv6xGeXE3HxnIL5aQ07NnuWvlN/yI"
    "/8HS31H/3LsfmvCv/sPP/s7vvf/yH93rvzfkuRv+/A9+7d49syf9w5/96t/+k3/40z//g19/84DMffMqSfjLS88fg4CfL65mJg53"
    "V/Np/sXHAcH7Pe8enmLhDz+XKj/PmkGPkcP538J8+Rcy/PjtmQXfJxUe5wGnj5cVvcQZlwDjY9jps0/uu/KX9duzA/v5oYiXcKvv"
    "53O/feNx3n3SRn7+tsmfI413eX/xaAXFYrFsH1JGvI4hisUz67nf9eB/cwxeym9Ef57nhj92dffXcz8T4/yJqd857GOiypeg8Q/v"
    "T/Eokc/usvvLn3NLQO8etP3ie48CfDr3CAy++OFzfpP0xQ9z26eYxIdaX4Uhlnn0D9MKTyu8XvdD+knmN40b+i/d8Tys/8cKv8fV"
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
