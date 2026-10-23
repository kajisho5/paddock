#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
PADDOCK GATE  v1.3.0  —  SEVENTHWELL

学会の各会場の発表PC（オペレーターPC）用。自分の会場の演者フォルダをNASから読み、NASへの受信が完了したものを
この発表PC・バックアップPCなどのコピー先へコピーする。NASには一切書き込まない（読むだけ）。
一覧・会場ボード・PowerPoint解析・目印の表示は PADDOCK SCOUT をそのまま使う（sw_nas_watch を部品として読み込む）。
スライドショーをしているPCで使うので、通知も音も出さない。

起動:
  python sw_nas_operator.py
  python sw_nas_operator.py --port 8797
"""
import argparse
import base64
import hashlib
import ipaddress
import json
import os
import re
import secrets
import shutil
import socket
import subprocess
import sys
import threading
import time
import unicodedata
from urllib.parse import urlparse

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # 同梱Pythonでも隣の sw_nas_watch を読めるように
import sw_nas_watch as W  # noqa: E402

APP_NAME = "PADDOCK GATE"
VERSION = "1.7.2"
DEFAULT_PORT = 8797


def pick_data_dir():
    # exe をNAS上に置いて起動した場合は、NASに書かないようローカルのアプリ用フォルダへ保存する
    for d in W.data_dir_candidates("SW_NAS_OPERATOR_HOME", "sw_nas_operator_data", ".sw_nas_operator"):
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


def force_quiet(cfg):
    """発表PCではスライドショーをしているので、通知も音も出さない。Explorer で開く機能も使わない。"""
    cfg["notify"] = {k: False for k in W.NOTIFY_KINDS}
    cfg["ui"] = dict(cfg.get("ui") or {}, sound=False, sticky=False, os_open=False, click="app")
    return cfg


def watch_data_candidates(data_dir):
    """PADDOCK SCOUT（旧 SW NAS WATCH）の保存先（会場オペレーターモードの設定の引き継ぎ元）の候補。"""
    home = os.path.abspath(os.environ.get("SW_NAS_OPERATOR_HOME", "") or os.path.dirname(os.path.abspath(__file__)))
    cands = [os.path.join(home, "sw_nas_watch_data")]
    # ZIPを同じ場所に展開した場合：…\SW_NAS_WATCH\sw_nas_watch_data
    # Windowsの「すべて展開」で1段深くなった場合：…\SW_NAS_WATCH_v1.12.0_Windows\SW_NAS_WATCH\sw_nas_watch_data
    par = os.path.dirname(home)
    for base in (par, os.path.dirname(par)):
        if not base or W.is_remote_path(base):
            continue
        try:
            names = sorted(e.name for e in os.scandir(base)
                           if e.name.upper().startswith(("PADDOCK_SCOUT", "SW_NAS_WATCH")) and e.is_dir())
        except OSError:
            continue
        for n in names[:20]:
            cands.append(os.path.join(base, n, "sw_nas_watch_data"))
            cands.append(os.path.join(base, n, "PADDOCK_SCOUT", "sw_nas_watch_data"))
            cands.append(os.path.join(base, n, "SW_NAS_WATCH", "sw_nas_watch_data"))
    la = os.environ.get("LOCALAPPDATA", "")
    if la:
        cands.append(os.path.join(la, "SEVENTHWELL", "sw_nas_watch_data"))
    cands.append(os.path.join(os.path.expanduser("~"), ".sw_nas_watch"))
    me = os.path.normcase(os.path.abspath(data_dir))
    out, seen = [], set()
    for d in cands:
        k = os.path.normcase(os.path.abspath(d))
        if k != me and k not in seen:
            seen.add(k)
            out.append(d)
    return out


def import_from_watch(data_dir):
    """初回起動時：PADDOCK SCOUT で会場オペレーターモードを使っていたら、その設定と「コピー済み」の記録を引き継ぐ。
    （引き継ぎ元のファイルは読むだけで、変更しない）"""
    found = []
    for d in watch_data_candidates(data_dir):
        p = os.path.join(d, "config.json")
        try:
            with open(p, encoding="utf-8") as f:
                raw = json.load(f)
            mt = os.stat(p).st_mtime
        except (OSError, ValueError):
            continue
        op = raw.get("op") if isinstance(raw, dict) else None
        if not isinstance(op, dict) or not op.get("dests") or not raw.get("roots"):
            continue
        found.append((mt, d, raw, op))
    if found:
        _mt, d, raw, op = max(found, key=lambda x: x[0])     # 2つ以上見つかったら、最後に使ったもの
        n = 0
        try:
            for fn in os.listdir(d):
                if fn.startswith("copy_") and fn.endswith(".json"):
                    shutil.copy2(os.path.join(d, fn), os.path.join(data_dir, fn))
                    n += 1
        except OSError:
            pass
        raw["op"] = dict(op, enabled=True)
        return raw, d, n
    return None, None, 0


class OpManager(W.Manager):
    COPIER_CLASS = W.Copier      # 3つのアプリのうち、コピー（発表PCへの書き込み）をするのはこのアプリだけ

    def apply_config(self, new):
        super().apply_config(force_quiet(new))

    def watch_roots(self, cfg):
        # 会場の発表PC：自分の会場の監視フォルダだけを見る（ほかの監視フォルダまでNASに見に行かない）
        op = cfg.get("op") or {}
        roots = [r for r in cfg["roots"] if r["enabled"]]
        if op.get("enabled") and op.get("root"):
            return [r for r in roots if r["id"] == op["root"]]
        return roots

    def folder_payload(self, rid, group):
        out = super().folder_payload(rid, group)
        if out.get("op") and group:
            files = [it for it in out["items"] if not it["d"] and not it.get("mk")]
            top = pres_candidates(files)
            if len(top) > 1:
                nw = newest_of(out["path"], top)
                out["op"]["pres"] = {"n": len(top), "newest": nw["p"] if nw else ""}
        return out


def build_page():
    if not W.LEGACY_UI and W.UI_PACK:
        return W.ui_page()     # 新しい画面（React）：どのアプリかは画面の側で切り替える
    h = W.HTML

    def sub(old, new):
        nonlocal h
        if h.count(old) != 1:
            raise RuntimeError("画面の組み立てに失敗しました: %r" % old[:40])
        h = h.replace(old, new)
    sub("<title>PADDOCK SCOUT</title>", "<title>PADDOCK GATE</title>")
    sub('+"PADDOCK SCOUT";if(ret)return t;', '+"PADDOCK GATE";if(ret)return t;')
    sub("PADDOCK SCOUT<small>SEVENTHWELL · READ ONLY</small>", "PADDOCK GATE<small>SEVENTHWELL · 会場</small>")
    sub("PADDOCK SCOUT v__VERSION__ · © SEVENTHWELL",
        "PADDOCK GATE v%s（PADDOCK SCOUT v__VERSION__ ベース） · © SEVENTHWELL" % VERSION)
    sub("</style>\n</head>", OP_CSS + "\n</style>\n</head>")
    sub("</script>\n</body>", OP_JS + "\n</script>\n</body>")
    return h


# ---------------------------------------------------------------- メインPC⇄バックアップPCのファイル共有（確認・ワンボタン設定）
SHARE_DEFAULTS = {"share": "発表データ", "user": "share", "password": "share"}
SETUP_SUPPORTED = W.IS_WIN          # ワンボタン設定・接続情報の登録は Windows だけ
CRED_COMMENT = "SW NAS OPERATOR"    # このアプリが登録した接続情報（資格情報）の目印
_BAD_SHARE = re.compile(r'[\\/\[\]:|<>+=;,?*"\x00-\x1f]')
_BAD_USER = re.compile(r'[\\/\[\]:;|=,+*?<>@"\x00-\x1f]')
_HOST_RE = re.compile(r'^[^\\/:*?"<>|\s,;]{1,63}$')
_RESERVED_USERS = {"administrator", "guest", "defaultaccount", "wdagutilityaccount", "administrators", "users", "everyone"}
_AUTH_ERR = {5, 86, 1326, 1327, 1328, 1329, 1330, 1331, 1385, 1907, 1909, 2242}
_PATH_ERR = {51, 53, 64, 121, 1222, 1231, 1232}


def _nfc(s):
    return unicodedata.normalize("NFC", str(s))


def share_record_dir():
    base = os.environ.get("ProgramData") or r"C:\ProgramData"
    return os.path.join(base, "SEVENTHWELL", "PADDOCK_GATE")


def read_share_record():
    try:
        with open(os.path.join(share_record_dir(), "share_setup.json"), encoding="utf-8-sig") as f:
            d = json.load(f)
        return d if isinstance(d, dict) else None
    except (OSError, ValueError):
        return None


def computer_name():
    return os.environ.get("COMPUTERNAME") or socket.gethostname().split(".")[0]


def _is_ip(h):
    try:
        ipaddress.ip_address(h)
        return True
    except ValueError:
        return False


def local_ipv4s():
    ips = []
    try:
        for ai in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            if ai[4][0] not in ips:
                ips.append(ai[4][0])
    except OSError:
        pass
    try:   # 既定の経路のアドレス（パケットは送らない）
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            s.connect(("10.255.255.255", 1))
            ip = s.getsockname()[0]
            if ip in ips:
                ips.remove(ip)
            ips.insert(0, ip)
        finally:
            s.close()
    except OSError:
        pass
    return [ip for ip in ips if not ip.startswith(("127.", "169.254.", "0."))]


def _with_timeout(fn, timeout):
    box = {}

    def run():
        try:
            box["v"] = fn()
        except BaseException as e:   # noqa: BLE001 — 呼び出し元へそのまま渡す
            box["e"] = e
    th = threading.Thread(target=run, daemon=True)
    th.start()
    th.join(timeout)
    if th.is_alive():
        raise TimeoutError()
    if "e" in box:
        raise box["e"]
    return box.get("v")


def _resolve(host):
    if _is_ip(host):
        return [host]
    out = []
    for ai in socket.getaddrinfo(host, 445, socket.AF_INET, socket.SOCK_STREAM):
        if ai[4][0] not in out:
            out.append(ai[4][0])
    return out


_listdir = os.listdir


def _port_open(ip, port=445, timeout=2.5):
    try:
        socket.create_connection((ip, port), timeout).close()
        return True
    except OSError:
        return False


def _drive_unc(path):
    """ネットワークドライブ（Z: など）の接続先 \\\\PC名\\共有名 を返す（Windows）。"""
    if not W.IS_WIN or not re.match(r"^[A-Za-z]:", path or ""):
        return ""
    try:
        import ctypes
        buf = ctypes.create_unicode_buffer(1024)
        n = ctypes.c_ulong(1024)
        if ctypes.windll.mpr.WNetGetConnectionW(path[:2], buf, ctypes.byref(n)) == 0:
            return buf.value
    except Exception:
        pass
    return ""


def _unc_parts(path):
    m = re.match(r"^[\\/]{2}([^\\/]+)[\\/]+([^\\/]+)", path or "")
    if not m and W.IS_WIN and re.match(r"^[A-Za-z]:", path or "") and W.is_remote_path(path):
        m = re.match(r"^[\\/]{2}([^\\/]+)[\\/]+([^\\/]+)", _drive_unc(path))
    return (m.group(1), m.group(2)) if m else ("", "")


def _gb(n):
    return "%.0f GB" % (n / 1024 ** 3) if n >= 10 * 1024 ** 3 else "%.1f GB" % (n / 1024 ** 3)


def winerror_of(e_or_text):
    we = getattr(e_or_text, "winerror", None)
    if we is None and isinstance(e_or_text, str):
        m = re.search(r"WinError (\d+)", e_or_text)
        we = int(m.group(1)) if m else None
    return we


def classify_net_error(e, share="", stage="share"):
    """(メッセージ, 直し方, "cred"=アカウントの登録で直る見込み)"""
    we = getattr(e, "winerror", None)
    cred = "cred" if stage == "share" else ""
    if we == 1909:
        return ("相手のPCのアカウントがロックされています（パスワードを何度も間違えたため）",
                "10分ほど待ってから、正しいアカウントを下の欄で登録してください", cred)
    if we == 1793:
        return ("相手のPCの共有用アカウントの期限（30日）が切れています",
                "相手のPCで［このPCを設定する］をもう一度押してください（期限が延びます）", "")
    if we in (1907, 1330):
        return ("相手のPCで、このアカウントのパスワードの変更が必要になっています",
                "相手のPCで［このPCを設定する］をもう一度押してください", "")
    if we == 1385:
        return ("相手のPCが、このアカウントでのネットワークからのログオンを許可していません（相手のPCのセキュリティの方針）",
                "相手のPCの管理者に確認してください", "")
    if we in (5,) and stage == "write":
        return ("書き込みの権限がありません", "相手のPCで［このPCを設定する］をもう一度押してください（共有とフォルダの権限を付けます）", "")
    if we in _AUTH_ERR or (we is None and isinstance(e, PermissionError)):
        return ("ユーザー名・パスワードが違うか、権限がありません",
                "相手のPCで［このPCを設定する］をしたときのアカウント（既定は share / share）を、下の欄でこのPCに登録してください。"
                "登録しても同じときは、相手のPCで共有の権限を確認してください", cred)
    if we == 1219:
        return ("このPCは、別のユーザー名で相手のPCにつながっています",
                "下の欄でアカウントを登録してから、このPCを再起動してください（Windowsでは、同じPCへ別のユーザー名で同時につなげません）", cred)
    if we == 67:
        return ("共有フォルダ「%s」が相手のPCにありません（共有名が違うか、共有されていません）" % share,
                "相手のPCで［このPCを設定する］を押し、そこに出る「\\\\PC名\\共有名」をコピー先に指定してください", "")
    if we == 1272:
        return ("相手のPCが「パスワードなしの共有（ゲスト）」になっています。Windows 11（24H2以降）などはゲストでつなげません",
                "相手のPCで［このPCを設定する］（アカウントで共有）を押し、このPCでそのアカウントを登録してください", cred)
    if we in (1240, 1311, 1789):
        return ("相手のPCがこのPCからのログオンを受け付けません", "相手のPCで［このPCを設定する］を押し、このPCでそのアカウントを登録してください", cred)
    if we in _PATH_ERR:
        return ("相手のPCにつながりません", "相手のPCで［このPCを設定する］を押してください。電源・スリープ・LANケーブル・同じネットワークかも確認してください", "")
    if we == 112:
        return ("空き容量がありません", "", "")
    return (W._err(e), "", "")


# ---- 接続情報（資格情報）：このPCのユーザーの資格情報マネージャーに、目印つきで保存する
def _cred_api():
    import ctypes
    from ctypes import wintypes

    class FILETIME(ctypes.Structure):
        _fields_ = [("lo", ctypes.c_uint32), ("hi", ctypes.c_uint32)]

    class CREDENTIALW(ctypes.Structure):
        _fields_ = [("Flags", ctypes.c_uint32), ("Type", ctypes.c_uint32), ("TargetName", ctypes.c_wchar_p),
                    ("Comment", ctypes.c_wchar_p), ("LastWritten", FILETIME), ("CredentialBlobSize", ctypes.c_uint32),
                    ("CredentialBlob", ctypes.c_void_p), ("Persist", ctypes.c_uint32), ("AttributeCount", ctypes.c_uint32),
                    ("Attributes", ctypes.c_void_p), ("TargetAlias", ctypes.c_wchar_p), ("UserName", ctypes.c_wchar_p)]
    adv = ctypes.WinDLL("advapi32", use_last_error=True)
    adv.CredReadW.argtypes = [wintypes.LPCWSTR, ctypes.c_uint32, ctypes.c_uint32, ctypes.POINTER(ctypes.POINTER(CREDENTIALW))]
    adv.CredReadW.restype = wintypes.BOOL
    adv.CredWriteW.argtypes = [ctypes.POINTER(CREDENTIALW), ctypes.c_uint32]
    adv.CredWriteW.restype = wintypes.BOOL
    adv.CredDeleteW.argtypes = [wintypes.LPCWSTR, ctypes.c_uint32, ctypes.c_uint32]
    adv.CredDeleteW.restype = wintypes.BOOL
    adv.CredEnumerateW.argtypes = [wintypes.LPCWSTR, ctypes.c_uint32, ctypes.POINTER(ctypes.c_uint32),
                                   ctypes.POINTER(ctypes.POINTER(ctypes.POINTER(CREDENTIALW)))]
    adv.CredEnumerateW.restype = wintypes.BOOL
    adv.CredFree.argtypes = [ctypes.c_void_p]
    return ctypes, adv, CREDENTIALW


CRED_TYPE_DOMAIN_PASSWORD = 2       # cmdkey /add と同じ種類（Windowsのファイル共有が使う）
CRED_PERSIST_LOCAL_MACHINE = 2


def cred_read(target):
    """登録済みなら {"user":…, "comment":…}、なければ None"""
    if not W.IS_WIN:
        return None
    ctypes, adv, CREDENTIALW = _cred_api()
    p = ctypes.POINTER(CREDENTIALW)()
    if not adv.CredReadW(target, CRED_TYPE_DOMAIN_PASSWORD, 0, ctypes.byref(p)):
        return None
    try:
        return {"user": p.contents.UserName or "", "comment": p.contents.Comment or ""}
    finally:
        adv.CredFree(p)


def cred_write(target, user, password):
    ctypes, adv, CREDENTIALW = _cred_api()
    blob = password.encode("utf-16-le")
    buf = ctypes.create_string_buffer(blob, len(blob))
    c = CREDENTIALW()
    c.Type = CRED_TYPE_DOMAIN_PASSWORD
    c.TargetName = target
    c.Comment = CRED_COMMENT
    c.CredentialBlobSize = len(blob)
    c.CredentialBlob = ctypes.cast(buf, ctypes.c_void_p)
    c.Persist = CRED_PERSIST_LOCAL_MACHINE
    c.UserName = user
    if not adv.CredWriteW(ctypes.byref(c), 0):
        raise OSError(ctypes.get_last_error(), "接続情報を登録できませんでした")
    return True


def cred_list_ours():
    """このアプリが登録した接続情報の宛先（目印で探す。アプリのフォルダを消したあとでも見つかる）"""
    if not W.IS_WIN:
        return []
    ctypes, adv, CREDENTIALW = _cred_api()
    n = ctypes.c_uint32(0)
    arr = ctypes.POINTER(ctypes.POINTER(CREDENTIALW))()
    if not adv.CredEnumerateW(None, 0, ctypes.byref(n), ctypes.byref(arr)):
        return []
    out = []
    try:
        for i in range(n.value):
            c = arr[i].contents
            if c.Type == CRED_TYPE_DOMAIN_PASSWORD and (c.Comment or "") == CRED_COMMENT and c.TargetName:
                out.append(c.TargetName)
    finally:
        adv.CredFree(arr)
    return out


def cred_delete(target):
    ctypes, adv, _C = _cred_api()
    return bool(adv.CredDeleteW(target, CRED_TYPE_DOMAIN_PASSWORD, 0))


def run_elevated_ps(script, param_file, hs, hp):
    """管理者として PowerShell でスクリプトを実行し、終わるまで待つ（ユーザーアカウント制御の確認が出る。経過はそのウィンドウに出る）。
    戻り値: ("ok" | "canceled" | "error", 終了コード, メッセージ)"""
    import ctypes
    from ctypes import wintypes

    class SHELLEXECUTEINFOW(ctypes.Structure):
        _fields_ = [("cbSize", wintypes.DWORD), ("fMask", wintypes.ULONG), ("hwnd", wintypes.HWND),
                    ("lpVerb", wintypes.LPCWSTR), ("lpFile", wintypes.LPCWSTR), ("lpParameters", wintypes.LPCWSTR),
                    ("lpDirectory", wintypes.LPCWSTR), ("nShow", ctypes.c_int), ("hInstApp", wintypes.HINSTANCE),
                    ("lpIDList", ctypes.c_void_p), ("lpClass", wintypes.LPCWSTR), ("hkeyClass", wintypes.HKEY),
                    ("dwHotKey", wintypes.DWORD), ("hIconOrMonitor", wintypes.HANDLE), ("hProcess", wintypes.HANDLE)]
    shell32 = ctypes.WinDLL("shell32", use_last_error=True)
    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    user32 = ctypes.WinDLL("user32", use_last_error=True)
    shell32.ShellExecuteExW.argtypes = [ctypes.POINTER(SHELLEXECUTEINFOW)]
    shell32.ShellExecuteExW.restype = wintypes.BOOL
    user32.GetForegroundWindow.restype = wintypes.HWND
    k32.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
    k32.WaitForSingleObject.restype = wintypes.DWORD
    k32.GetExitCodeProcess.argtypes = [wintypes.HANDLE, ctypes.POINTER(wintypes.DWORD)]
    k32.GetExitCodeProcess.restype = wintypes.BOOL
    k32.CloseHandle.argtypes = [wintypes.HANDLE]
    ps = os.path.join(os.environ.get("SystemRoot") or r"C:\Windows", "System32", "WindowsPowerShell", "v1.0", "powershell.exe")
    sei = SHELLEXECUTEINFOW()
    sei.cbSize = ctypes.sizeof(SHELLEXECUTEINFOW)
    sei.fMask = 0x00000040 | 0x00000100            # SEE_MASK_NOCLOSEPROCESS | SEE_MASK_NOASYNC
    sei.hwnd = user32.GetForegroundWindow()        # 確認の画面を、いま操作している画面の手前に出す
    sei.lpVerb = "runas"
    sei.lpFile = ps
    sei.lpParameters = elevated_ps_args(script, param_file, hs, hp)
    sei.nShow = 1                                  # 経過が見えるように、ウィンドウを表示する
    if not shell32.ShellExecuteExW(ctypes.byref(sei)):
        err = ctypes.get_last_error()
        if err == 1223:                                 # ERROR_CANCELLED（確認で［いいえ］）
            return "canceled", None, ""
        return "error", None, "管理者として実行できませんでした（エラー %d）" % err
    if not sei.hProcess:
        return "error", None, "管理者として実行できませんでした"
    try:
        k32.WaitForSingleObject(sei.hProcess, 0xFFFFFFFF)   # 終わるまで待つ（経過はウィンドウに出ている）
        code = wintypes.DWORD(0)
        k32.GetExitCodeProcess(sei.hProcess, ctypes.byref(code))
        return "ok", code.value, ""
    finally:
        k32.CloseHandle(sei.hProcess)


def elevated_ps_args(script, param_file, hs, hp):
    """スクリプトとパラメータの SHA-256 を確かめてから実行する（管理者の確認のあとに書き換えられていたら中止＝終了コード 3）。
    パスは Base64 で渡す（引用符・日本語・空白を含んでもよい）。"""
    b64 = lambda s: base64.b64encode(s.encode("utf-8")).decode("ascii")   # noqa: E731
    cmd = ("$e=[Text.Encoding]::UTF8;$sp=$e.GetString([Convert]::FromBase64String('%s'));"
           "$pp=$e.GetString([Convert]::FromBase64String('%s'));"
           "$s=[IO.File]::ReadAllBytes($sp);$p=[IO.File]::ReadAllBytes($pp);$h=[Security.Cryptography.SHA256]::Create();"
           "if((([BitConverter]::ToString($h.ComputeHash($s))) -replace '-','') -ne '%s' -or "
           "(([BitConverter]::ToString($h.ComputeHash($p))) -replace '-','') -ne '%s'){Remove-Item -LiteralPath $pp -Force -ErrorAction SilentlyContinue;exit 3};"
           "$t=$e.GetString($s).TrimStart([char]0xFEFF);"
           "& ([ScriptBlock]::Create($t)) -ParamJson ($e.GetString($p)) -ParamFile $pp"
           % (b64(script), b64(param_file), hs.upper(), hp.upper()))
    return '-NoProfile -NonInteractive -ExecutionPolicy Bypass -Command "%s"' % cmd


ELEVATE = run_elevated_ps            # テストでは差し替える


class OpCopier(W.Copier):
    """コピー先に接続できないとき、ユーザー名・パスワードの誤りなら間をあけて試す
    （何度も失敗すると、相手のPCのアカウントがロックされるため）。"""
    AUTH_BACKOFF = (120, 300, 600)

    def __init__(self, mgr):
        super().__init__(mgr)
        self.auth_wait = {}

    def reset_backoff(self):
        self.auth_wait.clear()
        self.kick()

    def _dest_online(self, d):
        did = d["id"]
        w = self.auth_wait.get(did)
        if w and time.time() < w[0]:
            st = self.dest.setdefault(did, {"online": None, "error": ""})
            st["online"], st["error"] = False, w[2]
            return False
        if super()._dest_online(d):
            self.auth_wait.pop(did, None)
            return True
        err = (self.dest.get(did) or {}).get("error", "")
        if winerror_of(err) in _AUTH_ERR - {5}:
            n = (w[1] + 1) if w else 0
            delay = self.AUTH_BACKOFF[min(n, len(self.AUTH_BACKOFF) - 1)]
            self.auth_wait[did] = (time.time() + delay, n,
                                   err + "（アカウントがロックされないよう、%d分ごとに試します。［ネットワーク共有］で接続情報を登録するとすぐ試します）" % (delay // 60))
        return False


OpManager.COPIER_CLASS = OpCopier


def _shell_folders():
    """デスクトップ・ドキュメントなど（そのものは共有しない）。"""
    out = []
    up = os.environ.get("USERPROFILE", "")
    if up:
        out += [up, os.path.dirname(up)] + [os.path.join(up, n) for n in ("Desktop", "Documents", "Downloads", "Pictures", "Videos", "Music")]
    if W.IS_WIN:
        try:
            import ctypes
            for csidl in (0x10, 0x05, 0x27, 0x0D, 0x0E):   # デスクトップ・ドキュメント・ピクチャ・ミュージック・ビデオ（移動されていても）
                buf = ctypes.create_unicode_buffer(520)
                if ctypes.windll.shell32.SHGetFolderPathW(None, csidl, None, 0, buf) == 0 and buf.value:
                    out.append(buf.value)
        except Exception:
            pass
    return [p for p in out if p]


def _onedrive_roots():
    return [v for v in (os.environ.get(k, "") for k in ("OneDrive", "OneDriveConsumer", "OneDriveCommercial")) if v]


class NetTools:
    """コピー先への接続の確認と、メインPC⇄バックアップPCのファイル共有のワンボタン設定。
    ・確認：名前 → ポート445 → 共有フォルダ → 書き込み → 空き容量 の順に調べ、どこで止まったかと直し方を返す
    ・設定：利用者が画面で内容を確認して押したときだけ、管理者の確認（UAC）を経て PowerShell で行う。
      変更前の状態を記録し、［元に戻す］で戻せる（フォルダとデータは消さない）"""
    STALE_JOB = 20 * 60

    def __init__(self, mgr, data_dir):
        self.mgr = mgr
        self.data_dir = data_dir
        self.dir = os.path.join(data_dir, "share")
        self.creds_file = os.path.join(data_dir, "share_creds.json")
        self.links_file = os.path.join(data_dir, "share_links.json")
        self.lock = threading.Lock()
        self.check_lock = threading.Lock()
        self.job = None
        self._nas_cache = (0.0, set())

    # ---- NAS（監視フォルダ）のサーバー：接続情報を登録しない・書き込みの確認をしない
    def nas_hosts(self):
        t, v = self._nas_cache
        if time.time() - t < 60:
            return v
        hosts = set()
        for r in self.mgr.cfg["roots"]:
            h, _s = _unc_parts(r["path"])
            if h:
                hosts.add(h.lower())
                hosts.add(h.split(".")[0].lower())
        for h in list(hosts):
            if not _is_ip(h):
                try:
                    hosts.update(ip for ip in _with_timeout(lambda h=h: _resolve(h), 4))
                except Exception:
                    pass
        self._nas_cache = (time.time(), hosts)
        return hosts

    def is_nas_host(self, host, ips=()):
        nas = self.nas_hosts()
        h = (host or "").lower()
        return bool(h and (h in nas or h.split(".")[0] in nas or any(ip in nas for ip in ips)))

    # ---- 情報
    def _folder_ok(self, p):
        try:
            self.valid_folder(p)
            return True
        except ValueError:
            return False

    def defaults(self, rec):
        op = self.mgr.cfg["op"]
        folder = ""
        if rec and isinstance(rec.get("share"), dict):
            folder = rec["share"].get("path") or ""
        if not folder:
            venue = _nfc(op.get("venue") or "")
            for d in op["dests"]:
                p = d.get("path") or ""
                if d.get("enabled") and re.match(r"^[A-Za-z]:[\\/]", p) and not (W.IS_WIN and W.is_remote_path(p)):
                    p = p.replace("/", "\\").rstrip("\\")
                    base = p.rsplit("\\", 1)
                    if venue and len(base) == 2 and _nfc(base[1]) == venue and len(base[0]) > 2 and self._folder_ok(base[0]):
                        p = base[0]
                    if self._folder_ok(p):
                        folder = p
                        break
        if not folder:
            folder = "C:\\発表データ"
            if W.IS_WIN:
                try:
                    import ctypes
                    if ctypes.windll.kernel32.GetDriveTypeW("D:\\") == 3:
                        folder = "D:\\発表データ"
                except Exception:
                    pass
        me = computer_name().lower()
        peers = []
        for d in op["dests"]:
            h, _s = _unc_parts(d.get("path") or "")
            if d.get("enabled") and h and not self.is_nas_host(h) and h.lower() != me and h.lower() not in [x.lower() for x in peers]:
                peers.append(h)
        share = (rec or {}).get("share", {}).get("name") if isinstance((rec or {}).get("share"), dict) else ""
        user = (rec or {}).get("user", {}).get("name") if isinstance((rec or {}).get("user"), dict) else ""
        # コピー先がすべてほかのPC（タイトルPCなどで動かしている）なら、このPCは共有しないのが既定
        local = any(d.get("enabled") and d.get("path") and not _unc_parts(d["path"])[0] for d in op["dests"])
        share_this = bool(rec) or local or not peers
        return {"folder": folder, "share": share or SHARE_DEFAULTS["share"], "user": user or SHARE_DEFAULTS["user"],
                "password": SHARE_DEFAULTS["password"], "peers": ", ".join(peers), "nosleep": True, "wifi": False,
                "share_this": share_this, "restrict": False}

    def info(self):
        rec = read_share_record()
        comp = computer_name()
        d = {"supported": SETUP_SUPPORTED, "computer": comp, "ips": local_ipv4s(), "record": None,
             "job": self.job, "defaults": self.defaults(rec), "creds": self._creds_load(),
             "links": [os.path.splitext(os.path.basename(x["path"]))[0] for x in self._links_load()]}
        if rec:
            sh = rec.get("share") if isinstance(rec.get("share"), dict) else {}
            us = rec.get("user") if isinstance(rec.get("user"), dict) else {}
            d["record"] = {"share": sh.get("name") or "", "path": sh.get("path") or "",
                           "unc": ("\\\\%s\\%s" % (comp, sh["name"])) if sh.get("name") else "",
                           "user": us.get("name") or "", "updated": rec.get("updated") or "",
                           "firewall": bool(rec.get("firewall")), "power": bool(rec.get("power"))}
        return d

    # ---- 接続の確認
    def _probe_write(self, path):
        os.makedirs(W.long_path(path), exist_ok=True)
        fn = os.path.join(path, ".swnw_probe_%s.tmp" % secrets.token_hex(4))
        with open(W.long_path(fn), "wb") as f:
            f.write(b"SW NAS OPERATOR connection check")
        os.remove(W.long_path(fn))

    def check_unc(self, host, share, add, nas_ok=False):
        """\\\\host\\share まで（名前・ポート445・共有フォルダ）。つながったら True。"""
        try:
            ips = _with_timeout(lambda: _resolve(host), 8)
        except Exception:
            ips = []
        if not ips:
            add("name", False, "「%s」というPCが見つかりません" % host,
                "PC名が合っているか確認してください。見つからないときは、相手のPCのIPアドレスで指定します（例 \\\\192.168.0.21\\%s\\…。"
                "相手のPCのこの画面の上に出ています）。相手のPCで［このPCを設定する］をすると、名前でも見つかりやすくなります" % share)
            return False
        add("name", True, "IPアドレス %s" % host if _is_ip(host) else "%s → %s" % (host, ", ".join(ips[:4])))
        if not nas_ok and self.is_nas_host(host, ips):
            add("nas", None, "NAS（監視フォルダ）と同じサーバーです。このアプリはここへの接続情報の登録や書き込みの確認をしません",
                "コピー先には、通常はPC（この発表PC・バックアップPC）のフォルダを指定してください")
            return False
        okip = next((ip for ip in ips[:3] if _port_open(ip)), None)
        if not okip:
            add("port", False, "相手のPCのファイル共有（ポート445）につながりません",
                "相手のPCで［このPCを設定する］を押してください（ファイアウォール・Serverサービスを設定します）。"
                "相手のPCの電源・スリープ・LANケーブル（有線）、同じネットワークにつながっているかも確認してください")
            return False
        add("port", True, "ファイル共有（ポート445）に応答があります（%s）" % okip)
        root = "\\\\%s\\%s" % (host, share)
        try:
            _with_timeout(lambda: _listdir(root), 20)
        except TimeoutError:
            add("share", False, "共有フォルダ「%s」の応答がありません" % share, "しばらくしてから［もう一度確認］を押してください")
            return False
        except OSError as e:
            msg, hint, need = classify_net_error(e, share, "share")
            add("share", False, msg, hint, need, W._err(e))
            return False
        add("share", True, "共有フォルダ「%s」を開けました" % share)
        return True

    def check_dest(self, label, path):
        steps = []

        def add(k, ok, msg, hint="", need="", raw=""):
            steps.append({"k": k, "ok": ok, "msg": msg, "hint": hint, "need": need, "raw": raw})
        path = (path or "").strip()
        out = {"label": label, "path": path, "steps": steps, "host": "", "share": ""}
        if not path:
            add("path", False, "パスが入っていません")
            return out
        roots = [r["path"] for r in self.mgr.cfg["roots"]]
        if any(W.overlaps(path, r) for r in roots):
            add("path", False, "NAS（監視フォルダ）の中は指定できません")
            return out
        out["host"], out["share"] = _unc_parts(path)
        if out["host"] and not self.check_unc(out["host"], out["share"], add):
            return out
        try:
            _with_timeout(lambda: self._probe_write(path), 20)
        except TimeoutError:
            add("write", False, "書き込みの応答がありません", "しばらくしてから［もう一度確認］を押してください")
            return out
        except OSError as e:
            msg, hint, need = classify_net_error(e, out["share"], "write")
            if not out["host"]:
                hint, need = hint or "フォルダの場所・ドライブがあるか確認してください", ""
            add("write", False, "書き込めません: " + msg, hint, need, W._err(e))
            return out
        add("write", True, "書き込めます")
        try:
            free = shutil.disk_usage(path).free
            add("space", free >= 5 * 1024 ** 3, "空き %s" % _gb(free),
                "" if free >= 5 * 1024 ** 3 else "空き容量が少なくなっています。不要なファイルを消すか、別のドライブを指定してください")
        except OSError:
            pass
        return out

    def check(self, dests=None):
        if not self.check_lock.acquire(blocking=False):
            raise ValueError("確認中です。しばらくお待ちください")
        try:
            if dests is None:
                dests = [{"label": d["label"], "path": d["path"]} for d in self.mgr.cfg["op"]["dests"] if d["enabled"] and d["path"]]
            dests = [{"label": str(d.get("label") or "")[:30], "path": str(d.get("path") or "")[:1000]} for d in dests[:4]]
            res = [None] * len(dests)

            def one(i, d):
                try:
                    res[i] = self.check_dest(d["label"], d["path"])
                except Exception as e:
                    res[i] = {"label": d["label"], "path": d["path"], "steps": [{"k": "error", "ok": False, "msg": W._err(e)}]}
            ths = [threading.Thread(target=one, args=(i, d), daemon=True) for i, d in enumerate(dests)]
            for t in ths:
                t.start()
            end = time.time() + 70
            for t in ths:
                t.join(max(0.0, end - time.time()))
            for i, d in enumerate(dests):
                if res[i] is None:
                    res[i] = {"label": d["label"], "path": d["path"], "steps": [{"k": "timeout", "ok": False, "msg": "時間内に確認できませんでした"}]}
            return {"dests": res, "at": time.time()}
        finally:
            self.check_lock.release()

    def check_peer(self, host, share):
        steps = []

        def add(k, ok, msg, hint="", need="", raw=""):
            steps.append({"k": k, "ok": ok, "msg": msg, "hint": hint, "need": need, "raw": raw})
        return self.check_unc(host, share, add), steps

    # ---- 接続情報（資格情報）の登録
    def _creds_load(self):
        try:
            with open(self.creds_file, encoding="utf-8") as f:
                v = json.load(f).get("targets")
            return [t for t in v if isinstance(t, str)] if isinstance(v, list) else []
        except (OSError, ValueError, AttributeError):
            return []

    def _creds_save(self, targets):
        self.mgr.store.write_json(os.path.basename(self.creds_file), {"targets": targets})

    def add_cred(self, host, user, password):
        if not SETUP_SUPPORTED:
            raise ValueError("接続情報の登録は Windows だけで使えます")
        m = re.match(r"^[\\/]{2}([^\\/]+)", str(host or "").strip())
        host = m.group(1) if m else str(host or "").strip().strip("\\/")
        user = valid_user(user)
        password = valid_password(password)
        if not _HOST_RE.match(host):
            raise ValueError("相手のPCの名前（またはIPアドレス）が正しくありません")
        ips = []
        if not _is_ip(host):
            try:
                ips = [ip for ip in _with_timeout(lambda: _resolve(host), 6) if ip != host][:3]
            except Exception:
                ips = []
        if self.is_nas_host(host, ips):
            raise ValueError("「%s」はNAS（監視フォルダ）のサーバーです。NASへの接続に影響が出ないよう、ここでは登録しません" % host)
        uname = user if _is_ip(host) else "%s\\%s" % (host.split(".")[0].upper(), user)
        with self.lock:
            known = self._creds_load()
            done, errs, skipped = [], [], []
            for t in [host] + ips:
                try:
                    cur = cred_read(t)
                except Exception:
                    cur = {"comment": "?"}       # 確かめられないときは、上書きしない側に倒す
                if cur and cur.get("comment") != CRED_COMMENT and t not in known:
                    skipped.append(t)      # ほかで登録した接続情報は上書きしない（元に戻せないため）
                    continue
                try:
                    cred_write(t, uname, password)
                    ok = True
                except Exception:
                    ok = run_cmdkey(["/add:%s" % t, "/user:%s" % uname, "/pass:%s" % password]) == 0
                if ok:
                    done.append(t)
                    if t not in known:
                        known.append(t)
                else:
                    errs.append(t)
            self._creds_save(known)
        try:
            self.mgr.copier.reset_backoff()
        except Exception:
            pass
        return {"ok": bool(done) and not errs, "targets": done, "errors": errs, "skipped": skipped, "user": uname}

    def remove_creds(self):
        """このアプリが登録した接続情報だけを削除する（目印つき、またはこのアプリの記録にあるもの）。"""
        with self.lock:
            known = self._creds_load()
            targets = list(known)
            try:
                targets += [t for t in cred_list_ours() if t not in targets]
            except Exception:
                pass
            gone, deleted = [], []
            for t in targets:
                try:
                    cur = cred_read(t)
                except Exception:
                    cur = {"comment": ""}
                if cur is None:
                    gone.append(t)
                    continue
                if cur.get("comment") != CRED_COMMENT and t not in known:
                    continue
                try:
                    ok = cred_delete(t)
                except Exception:
                    ok = run_cmdkey(["/delete:%s" % t]) == 0
                if ok:
                    deleted.append(t)
            self._creds_save([t for t in known if t not in gone and t not in deleted])
        return deleted

    # ---- ワンボタン設定（管理者として実行）
    def valid_folder(self, p):
        p = str(p or "").strip().strip('"').replace("/", "\\")
        if not re.match(r"^[A-Za-z]:\\", p):
            raise ValueError("共有するフォルダは、このPCのドライブのフォルダを指定してください（例 D:\\発表データ）")
        p = p.rstrip("\\")
        if len(p) <= 2:
            raise ValueError("ドライブ全体（D:\\ など）は共有できません。フォルダを指定してください")
        if any(c in p[2:] for c in '<>:"|?*') or any(ord(c) < 32 for c in p):
            raise ValueError("フォルダ名に使えない文字があります")
        if W.IS_WIN:
            import ctypes
            if ctypes.windll.kernel32.GetDriveTypeW(p[:2] + "\\") != 3:
                raise ValueError("このPCの内蔵ドライブ（固定ドライブ）のフォルダを指定してください（USBメモリ・ネットワークドライブは不可）")
            for k in ("SystemRoot", "ProgramFiles", "ProgramFiles(x86)", "ProgramData"):
                v = os.environ.get(k)
                if v and W.overlaps(p, v):
                    raise ValueError("Windows・アプリのフォルダは共有できません")
        for sf in _shell_folders():
            if W.norm_key(p) == W.norm_key(sf):
                raise ValueError("デスクトップ・ドキュメント・ユーザーのフォルダそのものは共有できません。中に「発表データ」などのフォルダを作って指定してください")
        for od in _onedrive_roots():
            if W.is_under(p, od):
                raise ValueError("OneDrive の中は共有できません（コピーしたデータがインターネットへ同期されるため）")
        for r in self.mgr.cfg["roots"]:
            if W.overlaps(p, r["path"]):
                raise ValueError("NAS（監視フォルダ）は共有できません")
        if W.overlaps(p, self.data_dir):
            raise ValueError("このアプリの保存先は共有できません")
        return p

    def start(self, action, body):
        if not SETUP_SUPPORTED:
            raise ValueError("ワンボタン設定は Windows だけで使えます")
        params = {"job_id": secrets.token_hex(8), "action": action,
                  "current_user": os.environ.get("USERNAME", "")}
        peers, user, password, share = [], "", "", ""
        elevate = True
        if action == "setup":
            share = str(body.get("share") or "").strip()
            if not share or len(share) > 80 or _BAD_SHARE.search(share) or share.endswith("$"):
                raise ValueError("共有名が正しくありません（\\ / : * ? \" < > | などは使えません）")
            user = valid_user(body.get("user"))
            password = valid_password(body.get("password"))
            me = computer_name().lower()
            for h in re.split(r"[,\s、]+", str(body.get("peers") or "")):
                m = re.match(r"^[\\/]{2}([^\\/]+)", h.strip())    # \\BACKUP-PC\共有名 と入れられたときは PC名だけ使う
                h = m.group(1) if m else h.strip().strip("\\/")
                if not h:
                    continue
                if not _HOST_RE.match(h):
                    raise ValueError("相手のPCの名前（またはIPアドレス）が正しくありません: %s" % h)
                if self.is_nas_host(h):
                    raise ValueError("「%s」はNAS（監視フォルダ）のサーバーです。相手のPCには、メインPC・バックアップPCなどの名前を入れてください" % h)
                if h.lower() != me and h.lower() not in [x.lower() for x in peers]:
                    peers.append(h)
            peers = peers[:4]
            elevate = body.get("share_this", True) is not False
            if not elevate and not peers:
                raise ValueError("このPCを共有しないときは、開く相手のPC（メインPC・バックアップPCなど）を入れてください")
            peer_ips = []
            if elevate and body.get("restrict"):
                for h in peers:
                    try:
                        for ip in _with_timeout(lambda h=h: _resolve(h), 6):
                            if re.match(r"^\d{1,3}(\.\d{1,3}){3}$", ip) and ip not in peer_ips:
                                peer_ips.append(ip)
                    except Exception:
                        pass
                if not peer_ips:
                    raise ValueError("相手のPCのIPアドレスが分からないため、「相手のPCからだけ許可」にできません（相手のPCの電源・名前を確認するか、チェックを外してください）")
            if elevate:
                params.update(folder=self.valid_folder(body.get("folder")), share=share, user=user, password=password,
                              nosleep=bool(body.get("nosleep")), set_password=bool(body.get("set_password")), wifi=bool(body.get("wifi")),
                              peer_ips=peer_ips[:8])
        elif action == "undo":
            elevate = read_share_record() is not None
            if not elevate and not self._creds_load() and not self._links_load():
                raise ValueError("元に戻すものがありません")
        else:
            raise ValueError("unknown action")
        with self.lock:
            j = self.job
            if j and j["state"] == "running" and time.time() - j["started"] < self.STALE_JOB:
                raise ValueError("実行中です。管理者の確認の画面（タスクバーで点滅していることがあります）か、設定のウィンドウを確認してください")
            script = pf = hs = hp = None
            if elevate:
                os.makedirs(self.dir, exist_ok=True)
                script = os.path.join(self.dir, "sw_share_setup.ps1")
                sbytes = SHARE_PS.replace("\r\n", "\n").replace("\n", "\r\n").encode("utf-8-sig")
                with open(script, "wb") as f:
                    f.write(sbytes)
                pf = os.path.join(self.dir, "params-%s.json" % secrets.token_hex(6))
                pbytes = json.dumps(params, ensure_ascii=False).encode("utf-8")
                with open(pf, "wb") as f:
                    f.write(pbytes)
                hs, hp = hashlib.sha256(sbytes).hexdigest(), hashlib.sha256(pbytes).hexdigest()
            job = {"id": params["job_id"], "action": action, "elevate": elevate, "state": "running", "started": time.time(), "ok": None,
                   "steps": [], "msg": "管理者の確認（ユーザーアカウント制御）の画面で［はい］を押してください（出ないときはタスクバーを確認）"
                   if elevate else "実行しています…"}
            self.job = job
        threading.Thread(target=self._run_job, args=(job, script, pf, hs, hp, peers, user, password, share),
                         daemon=True, name="share-setup").start()
        return job

    def _run_elevated(self, job, script, pf, hs, hp):
        """管理者として設定・元に戻す。結果（dict）か、だめなら None（job に理由を入れる）。"""
        st, code, msg = ELEVATE(script, pf, hs, hp)
        if st == "canceled":
            job.update(state="canceled", ok=False, msg="管理者の確認で［いいえ］が選ばれたため、何も変更していません")
            return None
        if st != "ok":
            job.update(state="error", ok=False, msg=msg or "実行できませんでした")
            return None
        if code == 3:
            job.update(state="error", ok=False, msg="設定用のファイルが途中で書き換えられたため、何も変更せずに中止しました。もう一度押してください")
            return None
        res = None
        try:
            with open(os.path.join(share_record_dir(), "result.json"), encoding="utf-8-sig") as f:
                res = json.load(f)
        except (OSError, ValueError):
            pass
        if not isinstance(res, dict) or res.get("id") != job["id"]:
            job.update(state="error", ok=False, msg="結果を読み取れませんでした（途中で止まった可能性があります。もう一度お試しください）")
            return None
        return res

    def _run_job(self, job, script, pf, hs, hp, peers, user, password, share_name):
        try:
            if job["elevate"]:
                res = self._run_elevated(job, script, pf, hs, hp)
                if res is None:
                    return
            else:
                res = {"ok": True, "steps": []}
            steps = [s for s in (res.get("steps") or []) if isinstance(s, dict)]
            ok = bool(res.get("ok"))
            if job["action"] == "setup":
                if not ok:
                    if peers:
                        steps.append({"key": "cred", "label": "相手のPCの接続情報", "ok": None,
                                      "msg": "うまくいかなかった項目があるため、相手のPCの接続情報とショートカットは作っていません"})
                else:
                    for h in peers:
                        try:
                            r = self.add_cred(h, user, password)
                            msg2 = "「%s」へのアカウント「%s」を、このPCに登録しました" % ("・".join(r["targets"]), r["user"]) if r["targets"] else ""
                            if r["skipped"]:
                                msg2 += "（%s はほかで登録した接続情報があるため、変えていません）" % "・".join(r["skipped"])
                            if r["errors"]:
                                msg2 += "（%s は登録できませんでした）" % "・".join(r["errors"])
                            steps.append({"key": "cred", "label": "相手のPC（%s）の接続情報" % h, "ok": r["ok"] if r["targets"] else None, "msg": msg2.strip()})
                        except Exception as e:
                            steps.append({"key": "cred", "label": "相手のPC（%s）の接続情報" % h, "ok": False, "msg": W._err(e)})
                    for r in self.make_links(peers, share_name):
                        steps.append({"key": "link", "label": "デスクトップのショートカット", "ok": r["ok"] if r["ok"] else None,
                                      "msg": ("「%s」→ %s を作りました" % (r["name"], r["target"])) if r["ok"] else
                                      ("「%s」を作れませんでした: %s" % (r["name"], r.get("msg") or ""))})
                    for h in peers:
                        pok, pst = self.check_peer(h, share_name)
                        steps.append({"key": "peer", "label": "相手のPC（%s）" % h, "ok": True if pok else None,
                                      "msg": ("「\\\\%s\\%s」につながります" % (h, share_name)) if pok else
                                      ("「\\\\%s\\%s」にはまだつながりません（%s）。相手のPCでも［このPCを設定する］を押してください"
                                       % (h, share_name, (pst[-1]["msg"] if pst else "")))})
            elif ok:
                removed = self.remove_creds()
                if removed:
                    steps.append({"key": "cred", "label": "相手のPCの接続情報", "ok": True, "msg": "このPCに登録した接続情報を削除しました: " + "・".join(removed)})
                gone, kept = self.remove_links()
                if gone:
                    steps.append({"key": "link", "label": "デスクトップのショートカット", "ok": True, "msg": "作ったショートカットを削除しました: " + "・".join(gone)})
                if kept:
                    steps.append({"key": "link", "label": "デスクトップのショートカット", "ok": None, "msg": "削除しなかったもの（作ったものと違う・消せない）: " + "・".join(kept)})
            job.update(state="done", ok=ok, steps=steps, msg="")
        except Exception as e:
            job.update(state="error", ok=False, msg=W._err(e))
        finally:
            if pf:
                try:
                    os.remove(pf)
                except OSError:
                    pass
            self.mgr.log("SHARE %s: %s" % (job["action"], job["state"]))

    # ---- デスクトップのショートカット（このPCのユーザーのデスクトップに作る。目印つき）
    def _links_load(self):
        try:
            with open(self.links_file, encoding="utf-8") as f:
                v = json.load(f).get("links")
            return [x for x in v if isinstance(x, dict) and isinstance(x.get("path"), str)] if isinstance(v, list) else []
        except (OSError, ValueError, AttributeError):
            return []

    def _links_save(self, links):
        self.mgr.store.write_json(os.path.basename(self.links_file), {"links": links})

    def make_links(self, peers, share):
        items = []
        for h in peers:
            name = "%s の%s" % (h, share)
            name = re.sub(r'[\\/:*?"<>|]', "_", name)[:80]
            items.append({"name": name, "target": "\\\\%s\\%s" % (h, share)})
        if not items:
            return []
        try:
            out = LINK_RUNNER({"action": "create", "items": items})
        except Exception as e:
            return [{"name": it["name"], "target": it["target"], "ok": False, "msg": W._err(e)} for it in items]
        with self.lock:
            links = self._links_load()
            for r in out:
                if r.get("ok") and r.get("path") and r["path"] not in [x["path"] for x in links]:
                    links.append({"path": r["path"], "target": r.get("target", "")})
            self._links_save(links)
        return out

    def remove_links(self):
        with self.lock:
            links = self._links_load()
            if not links:
                return [], []
            try:
                out = LINK_RUNNER({"action": "delete", "items": [{"path": x["path"], "target": x.get("target", "")} for x in links]})
            except Exception as e:
                return [], ["%s（%s）" % (os.path.basename(x["path"]), W._err(e)) for x in links]
            gone = [r for r in out if r.get("ok")]
            done_paths = {r["path"] for r in gone}
            self._links_save([x for x in links if x["path"] not in done_paths and not any(r["path"] == x["path"] and r.get("missing") for r in out)])
            kept = [os.path.basename(r["path"]) for r in out if not r.get("ok") and not r.get("missing")]
            return [os.path.splitext(os.path.basename(r["path"]))[0] for r in gone], kept


# デスクトップのショートカットを作る・消す（ふつうのユーザーの権限で動かす PowerShell。Windows の WScript.Shell を使う）
LINK_PS = r"""
$ErrorActionPreference = 'Stop'
$e = [Text.Encoding]::UTF8
$req = $e.GetString([Convert]::FromBase64String($env:SWNAS_LINKREQ)) | ConvertFrom-Json
$mark = 'SW NAS OPERATOR'
$w = New-Object -ComObject WScript.Shell
$desk = [Environment]::GetFolderPath('Desktop')
$out = New-Object System.Collections.ArrayList
foreach ($it in @($req.items)) {
    if ($req.action -eq 'create') {
        $p = Join-Path $desk ([string]$it.name + '.lnk')
        $r = [ordered]@{ name = [string]$it.name; target = [string]$it.target; path = $p; ok = $false; msg = '' }
        try {
            if (Test-Path -LiteralPath $p) {
                if ([string]$w.CreateShortcut($p).Description -ne $mark) { $r.msg = '同じ名前のショートカットがすでにあります（そのままにしました）'; [void]$out.Add($r); continue }
            }
            $s = $w.CreateShortcut($p)
            $s.TargetPath = [string]$it.target
            $s.Description = $mark
            $s.Save()
            $r.ok = $true
        } catch { $r.msg = $_.Exception.Message }
        [void]$out.Add($r)
    } else {
        $p = [string]$it.path
        $r = [ordered]@{ path = $p; ok = $false; missing = $false; msg = '' }
        try {
            if (-not (Test-Path -LiteralPath $p)) { $r.missing = $true }
            elseif ([string]$w.CreateShortcut($p).Description -eq $mark) { Remove-Item -LiteralPath $p -Force; $r.ok = $true }
            else { $r.msg = '作ったものと違うため、そのままにしました' }
        } catch { $r.msg = $_.Exception.Message }
        [void]$out.Add($r)
    }
}
[Console]::OutputEncoding = $e
[Console]::Out.Write((ConvertTo-Json -InputObject $out.ToArray() -Compress -Depth 4))
"""


def run_link_ps(req):
    ps = os.path.join(os.environ.get("SystemRoot") or r"C:\Windows", "System32", "WindowsPowerShell", "v1.0", "powershell.exe")
    env = dict(os.environ, SWNAS_LINKREQ=base64.b64encode(json.dumps(req, ensure_ascii=False).encode("utf-8")).decode("ascii"))
    enc = base64.b64encode(LINK_PS.encode("utf-16-le")).decode("ascii")
    r = subprocess.run([ps, "-NoProfile", "-NonInteractive", "-ExecutionPolicy", "Bypass", "-EncodedCommand", enc],
                       capture_output=True, timeout=90, env=env, creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
    txt = r.stdout.decode("utf-8", "replace").lstrip("\ufeff").strip()
    data = json.loads(txt[txt.index("["):] if "[" in txt else "[]") if txt else []
    if isinstance(data, dict):
        data = [data]
    if r.returncode != 0 and not data:
        raise OSError(r.stderr.decode("utf-8", "replace")[-300:] or "ショートカットを作れませんでした")
    return [x for x in data if isinstance(x, dict)]


LINK_RUNNER = run_link_ps            # テストでは差し替える


def run_cmdkey(args):
    r = subprocess.run(["cmdkey"] + list(args), capture_output=True, timeout=20,
                       creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
    return r.returncode


def valid_user(u):
    u = str(u or "").strip()
    if not u or len(u) > 20 or _BAD_USER.search(u) or u.endswith(".") or u.lower() in _RESERVED_USERS:
        raise ValueError("共有用アカウントの名前が正しくありません（20文字まで。\\ / [ ] : ; | = , + * ? < > @ \" は使えません）")
    return u


def valid_password(p):
    p = str(p or "")
    if not p or len(p) > 127 or any(ord(c) < 32 for c in p):
        raise ValueError("パスワードを入れてください（空のパスワードでは、ほかのPCからつなげません）")
    return p


# ---------------------------------------------------------------- 演者のスライドを開く（このPCのコピーを開く。NASのファイルは開かない）
OPEN_DEFAULTS = {"enabled": True, "dest": "", "dbl": "file", "multi": "newest"}
PRES_EXT = (".pptx", ".ppsx", ".pptm", ".ppsm", ".ppt", ".pps", ".key", ".pdf")      # 発表ファイル（この順に優先）
SHOW_EXT = (".pptx", ".ppsx", ".pptm", ".ppsm", ".ppt", ".pps")                      # スライドショーで開けるもの
OPENABLE_STATES = ("ok", "edited")                                                     # コピー済み（コピー先で編集されたものも含む）


def _powerpoint_exe():
    if not W.IS_WIN:
        return ""
    try:
        import winreg
        for hive in (winreg.HKEY_CURRENT_USER, winreg.HKEY_LOCAL_MACHINE):
            try:
                with winreg.OpenKey(hive, r"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths\POWERPNT.EXE") as k:
                    v = winreg.QueryValue(k, None)
                    if v and os.path.isfile(v.strip('"')):
                        return v.strip('"')
            except OSError:
                continue
    except Exception:
        pass
    return ""


def open_native(path, how):
    """ファイル・フォルダを、このPCの既定のアプリで開く（how="show" は PowerPoint のスライドショー）。"""
    if W.IS_WIN:
        if how == "show":
            try:
                os.startfile(path, "show")       # PowerPoint の「スライド ショー」（右クリックメニューと同じ）
                return
            except OSError:
                exe = _powerpoint_exe()
                if not exe:
                    raise ValueError("PowerPoint が見つからないため、スライドショーで開けません（［開く］で開いてください）")
                subprocess.Popen([exe, "/S", path])
                return
        os.startfile(path)
    elif W.IS_MAC:
        subprocess.Popen(["open", path])
    else:
        subprocess.Popen(["xdg-open", path])


OPEN_FN = open_native               # テストでは差し替える


def pres_kind(p):
    e = os.path.splitext(p)[1].lower()
    return 0 if e in SHOW_EXT else 1 if e == ".key" else 2 if e == ".pdf" else None


def pres_candidates(files):
    """開く候補の発表ファイル：PowerPoint があれば PowerPoint（.pptx/.ppt…）だけ、なければ Keynote、なければ PDF"""
    pres = [it for it in files if pres_kind(it["p"]) is not None]
    if not pres:
        return []
    best = min(pres_kind(it["p"]) for it in pres)
    return [it for it in pres if pres_kind(it["p"]) == best]


def arrival_time(path, fallback=0):
    """NASにファイルが入った時刻の目安：作成日時（コピーされた時刻）と更新日時の新しいほう。属性を見るだけ"""
    try:
        st = os.stat(W.long_path(path))
    except OSError:
        return fallback
    born = getattr(st, "st_birthtime", None)
    if born is None and W.IS_WIN:
        born = st.st_ctime
    return max(born or 0, st.st_mtime)


def newest_of(base, items):
    """いちばん後から入ったもの。差が2秒未満で決められないときは None（フォルダを開く）"""
    if len(items) < 2:
        return items[0] if items else None
    ts = sorted(((arrival_time(os.path.join(base, *it["p"].split("/")), it.get("m", 0)), it) for it in items),
                key=lambda x: x[0], reverse=True)
    if ts[0][0] - ts[1][0] < 2:
        return None
    return ts[0][1]


class Opener:
    """演者のスライド・フォルダを、このPCのコピー先（コピー済みのもの）から開く。
    NAS上のファイルは開かない（会場側・受付の差し替えに影響を出さないため。PowerPointの鍵ファイルもNASに作らない）。"""
    LABELS = {"todo": "コピー待ち", "copying": "コピー中", "wait": "NASへの受信が終わるのを待っています", "srcbusy": "NAS側で使用中",
              "busy": "差し替え待ち", "off": "コピー先に接続できません", "err": "コピーできませんでした"}

    def __init__(self, mgr, data_dir):
        self.mgr = mgr
        self.name = "open_settings.json"
        d = mgr.store.read_json(self.name, None)
        self.settings = self._valid(d if isinstance(d, dict) else {})

    def _valid(self, d):
        out = dict(OPEN_DEFAULTS)
        out["enabled"] = bool(d.get("enabled", OPEN_DEFAULTS["enabled"]))
        dest = str(d.get("dest") or "")
        out["dest"] = dest if re.fullmatch(r"d[0-9a-f]{8}", dest) else ""
        out["dbl"] = d.get("dbl") if d.get("dbl") in ("file", "show", "folder") else OPEN_DEFAULTS["dbl"]
        out["multi"] = d.get("multi") if d.get("multi") in ("newest", "folder") else OPEN_DEFAULTS["multi"]
        return out

    def dest(self):
        op = self.mgr.cfg["op"]
        ds = [d for d in op["dests"] if d.get("enabled") and d.get("path")]
        for d in ds:
            if d["id"] == self.settings["dest"]:
                return d
        for d in ds:   # 自動：このPCのフォルダ（ネットワーク上でないもの）
            if not _unc_parts(d["path"])[0] and not (W.IS_WIN and W.is_remote_path(d["path"])):
                return d
        return ds[0] if ds else None

    def get(self):
        d = self.dest()
        return {"settings": self.settings, "dest": {"id": d["id"], "label": d["label"]} if d else None}

    def set(self, body):
        self.settings = self._valid(body if isinstance(body, dict) else {})
        self.mgr.store.write_json(self.name, self.settings)
        return self.get()

    def _state(self, it, did):
        return ((it.get("cp") or {}).get(did) or [None])[0]

    def open(self, root, group, rel, how):
        if not self.settings["enabled"]:
            raise ValueError("［設定］→「演者のスライドを開く」がオフになっています")
        if how not in ("folder", "file", "show"):
            raise ValueError("開き方が正しくありません")
        op = self.mgr.cfg["op"]
        if not op["enabled"] or op["root"] != root:
            raise ValueError("このPCの会場とコピー先が設定されていません")
        d = self.dest()
        if not d:
            raise ValueError("コピー先がありません（［設定］→「このPCの会場とコピー先」）")
        prefix = (op["venue"] + "/") if op["venue"] else ""
        group = str(group or "")
        if not group or (prefix and not group.startswith(prefix)):
            raise ValueError("この会場の演者フォルダではありません")
        sub = W.op_sub(op, group)
        base = os.path.join(d["path"], *sub.split("/"))
        fp = self.mgr.folder_payload(root, group)
        files = [it for it in fp["items"] if not it.get("d") and not it.get("mk")]
        msg = ""
        target = None
        if rel:
            target = next((it for it in files if it["p"] == rel), None)
            if not target:
                raise ValueError("ファイルが見つかりません（NAS側で名前が変わった・消えた可能性）")
        elif how != "folder":
            top = pres_candidates(files)
            if len(top) == 1:
                target = top[0]
            elif top:
                nw = newest_of(fp["path"], top) if self.settings["multi"] == "newest" else None
                if nw:
                    target = nw
                    msg = "発表ファイルが%d個あるため、後から入った「%s」を開きました" % (len(top), nw["p"].split("/")[-1])
                else:
                    msg = "発表ファイルが%d個あるため、フォルダを開きました（フォルダ画面の［開く］から選べます）" % len(top)
            else:
                msg = "発表ファイル（PowerPoint・PDFなど）がないため、フォルダを開きました"
        if target is None:
            if not os.path.isdir(W.long_path(base)):
                raise ValueError("「%s」にはまだこの演者のフォルダがありません（コピーが終わってから開いてください）" % d["label"])
            OPEN_FN(base, "folder")
            return {"ok": True, "what": "folder", "path": base, "dest": d["label"], "msg": msg}
        st = self._state(target, d["id"])
        name = target["p"].split("/")[-1]
        if st not in OPENABLE_STATES:
            raise ValueError("「%s」は「%s」へまだコピーが終わっていません（%s）。終わってから開いてください"
                             % (name, d["label"], self.LABELS.get(st, "コピー待ち")))
        path = os.path.join(base, *target["p"].split("/"))
        if not os.path.isfile(W.long_path(path)):
            raise ValueError("「%s」の中に「%s」が見つかりません" % (d["label"], name))
        show = how == "show" and os.path.splitext(name)[1].lower() in SHOW_EXT
        OPEN_FN(path, "show" if show else "file")
        return {"ok": True, "what": "show" if show else "file", "path": path, "dest": d["label"], "name": name, "msg": msg}


class OpHandler(W.Handler):
    server_version = "SWNasOperator/" + VERSION

    def send_page(self):
        body = self.server.page.replace("__TOKEN__", self.server.token).replace("__VERSION__", W.VERSION).replace(
            "__APPKIND__", "operator").encode("utf-8")
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

    def do_GET(self):
        if not self.host_ok():
            return self.deny(403, "host not allowed")
        u = urlparse(self.path)
        if u.path in ("/", "/index.html"):
            return self.send_page()
        if u.path == "/api/ping":
            return self.send_json({"app": APP_NAME, "version": VERSION})
        if u.path == "/api/op/open/settings":
            if not self.is_local():
                return self.deny(403, "この操作はアプリを動かしているPCからのみ可能です")
            return self.send_json(self.server.opener.get())
        if u.path.startswith("/api/op/net"):
            if not self.is_local():
                return self.deny(403, "この操作はアプリを動かしているPCからのみ可能です")
            if u.path == "/api/op/net":
                return self.send_json(self.server.net.info())
            if u.path == "/api/op/net/job":
                return self.send_json({"job": self.server.net.job})
            return self.deny(404, "not found")
        return super().do_GET()

    def do_POST(self):
        u = urlparse(self.path)
        if not u.path.startswith("/api/op/"):
            return super().do_POST()
        if not self.is_local() or (self.headers.get("Host") or "").lower() not in self.server.allowed_hosts:
            return self.deny(403, "この操作はアプリを動かしているPCからのみ可能です")
        if self.headers.get("X-SW-Token") != self.server.token:
            return self.deny(403, "token")
        try:
            n = int(self.headers.get("Content-Length") or 0)
            if n > 100_000:
                return self.deny(413, "too large")
            body = json.loads(self.rfile.read(n).decode("utf-8") or "{}") if n else {}
            if not isinstance(body, dict):
                raise ValueError("bad json")
        except (ValueError, UnicodeDecodeError):
            return self.deny(400, "bad json")
        net = self.server.net
        try:
            if u.path == "/api/op/open":
                return self.send_json(self.server.opener.open(str(body.get("root") or ""), str(body.get("group") or ""),
                                                              str(body.get("rel") or ""), str(body.get("how") or "")))
            if u.path == "/api/op/open/settings":
                return self.send_json(self.server.opener.set(body))
            if u.path == "/api/op/net/check":
                d = body.get("dests")
                return self.send_json(net.check(d if isinstance(d, list) else None))
            if u.path == "/api/op/net/cred":
                return self.send_json(net.add_cred(body.get("host"), body.get("user"), body.get("password")))
            if u.path == "/api/op/net/setup":
                return self.send_json({"job": net.start("setup", body)})
            if u.path == "/api/op/net/undo":
                return self.send_json({"job": net.start("undo", body)})
            return self.deny(404, "not found")
        except (ValueError, KeyError) as e:
            return self.deny(400, str(e).strip("'\""))
        except Exception as e:
            return self.deny(500, "%s: %s" % (type(e).__name__, e))


def main():
    for _s in (sys.stdout, sys.stderr):
        try:
            _s.reconfigure(errors="replace")
        except Exception:
            pass
    ap = argparse.ArgumentParser(description="%s — 学会の会場の発表PC用：自分の会場の演者フォルダをコピーする" % APP_NAME)
    ap.add_argument("--port", type=int, default=DEFAULT_PORT)
    ap.add_argument("--no-browser", action="store_true", help="画面を自動で開かない")
    ap.add_argument("--browser", choices=["app", "default"], default="app")
    ap.add_argument("--data-dir", default="", help="設定・コピーの記録の保存先（既定: このファイルの横）")
    ap.add_argument("--legacy-ui", action="store_true", help="旧画面（v1.13 まで）で表示する")
    a = ap.parse_args()
    W.use_legacy(a.legacy_ui)
    W.disable_quick_edit()

    data_dir = a.data_dir or pick_data_dir()
    os.makedirs(data_dir, exist_ok=True)
    moved = None if a.data_dir else W.carry_over_renamed(data_dir, "SW_NAS_OPERATOR_HOME", "sw_nas_operator_data", "SW_NAS_OPERATOR")
    if moved:
        print("前の名前（SW NAS OPERATOR）のフォルダから設定を引き継ぎました: %s" % moved)
    store = W.LocalStore(data_dir)
    raw = store.read_json("config.json", None)
    imported = None
    if raw is None:
        raw, src, n = import_from_watch(data_dir)
        if raw is not None:
            imported = "PADDOCK SCOUT の会場オペレーターモードの設定を引き継ぎました（%s、コピーの記録 %d件）" % (src, n)
    cfg, cfg_msg = W.startup_config(store, data_dir, raw)
    if cfg_msg:
        print(cfg_msg)
    force_quiet(cfg)
    try:
        cfg = W.validate_cfg(cfg, data_dir)
    except ValueError as e:
        raise SystemExit(str(e))

    url = "http://127.0.0.1:%d/" % a.port
    if not W.claim_port("127.0.0.1", a.port, url, APP_NAME, None if a.no_browser else (lambda: W.open_ui(url, data_dir, a.browser))):
        return
    store.roots = [r["path"] for r in cfg["roots"]]
    store.write_json("config.json", cfg)      # 2つ目の起動（すでに起動中）では設定ファイルに触れない

    mgr = OpManager(store, cfg)
    srv = W.Server(("127.0.0.1", a.port), OpHandler)
    srv.mgr = mgr
    srv.token = secrets.token_urlsafe(24)
    srv.lan = False
    srv.stopping = False
    srv.appkind = "operator"
    srv.allowed_hosts = {"127.0.0.1:%d" % a.port, "localhost:%d" % a.port, "[::1]:%d" % a.port}
    srv.page = build_page()
    srv.net = NetTools(mgr, data_dir)
    srv.opener = Opener(mgr, data_dir)
    mgr.start()
    W.start_autoquit(srv, enabled=False)

    op = cfg["op"]
    print("=" * 64)
    print(" %s v%s   (会場の発表PC用：NASは読むだけ・コピー先へコピーします)" % (APP_NAME, VERSION))
    print(" 画面: %s" % url)
    print(" 保存先: %s" % data_dir)
    if imported:
        print(" " + imported)
    for r in cfg["roots"]:
        print(" 監視: [%s] %s  (階層%d)" % (r["label"] or W.default_label(r["path"]), r["path"], r["depth"]))
    if op.get("enabled"):
        print(" 会場: %s" % (op.get("venue") or "（監視フォルダ全体）"))
        for d in op["dests"]:
            if d["enabled"]:
                print(" コピー先: [%s] %s" % (d["label"], d["path"]))
    else:
        print(" まだ設定されていません → 画面の［設定］で、学会名フォルダ・自分の会場・コピー先を設定してください")
    print(" 通知・音は出しません（スライドショーの邪魔をしないため）")
    rec = read_share_record()
    if rec and isinstance(rec.get("share"), dict):
        print(" ※ このPCには共有の設定が残っています（\\\\%s\\%s）。イベントが終わったら、画面の［ネットワーク共有］→［元に戻す］"
              % (computer_name(), rec["share"].get("name") or ""))
    print(" " + ("画面の［終了］（電源のボタン）で止まります。ウィンドウを閉じても、コピーは裏で続けます（もう一度起動すると画面が開きます）" if W.AUTOQUIT else "このウィンドウを閉じると止まります（Ctrl+C で終了）"))
    print("=" * 64, flush=True)
    if not a.no_browser:
        threading.Timer(0.6, W.open_ui, args=(url, data_dir, a.browser)).start()
    try:
        srv.serve_forever(poll_interval=0.5)
    except KeyboardInterrupt:
        print("\n終了します…")
    finally:
        srv.stopping = True
        mgr.stop()
        srv.server_close()


# ---------------------------------------------------------------- 共有のワンボタン設定（管理者として実行する PowerShell）
SHARE_PS = r'''param([string]$ParamJson, [string]$ParamFile)
# SW NAS OPERATOR : メインPC⇄バックアップPCのファイル共有をまとめて設定する／元に戻す
# ・利用者が画面で内容を確認して押したときだけ、管理者の確認（UAC）を経て実行される（このウィンドウに経過を表示）
# ・変更する前の状態を、変更するたびに記録し、［元に戻す］で戻す。フォルダとデータは消さない
# ・ネットワークの種類（パブリック／プライベート）は変えない。ファイアウォールは「有線・同じネットワーク内から」だけ許可
# ・Windows PowerShell 5.1 で動くこと（PowerShell 7 専用の書き方を使わない）
$global:ErrorActionPreference = 'Stop'     # モジュールのコマンド（New-SmbShare など）にも効かせる
$ErrorActionPreference = 'Stop'
$script:FwGroup = 'SW NAS OPERATOR'
$script:AcctDesc = 'SW NAS OPERATOR file sharing'
$script:ShareDesc = 'SW NAS OPERATOR'
$script:Steps = New-Object System.Collections.ArrayList
$script:Rec = $null
$script:RecDir = Join-Path $env:ProgramData 'SEVENTHWELL\SW_NAS_OPERATOR'
$script:RecPath = Join-Path $script:RecDir 'share_setup.json'
$script:ResPath = Join-Path $script:RecDir 'result.json'
$script:Services = @('LanmanServer', 'LanmanWorkstation', 'FDResPub', 'fdPHost')

function Add-Step([string]$Key, [string]$Label, $Ok, [string]$Msg) {
    [void]$script:Steps.Add([ordered]@{ key = $Key; label = $Label; ok = $Ok; msg = $Msg })
    $mark = '・'
    if ($Ok -eq $true) { $mark = 'OK' } elseif ($Ok -eq $false) { $mark = 'NG' }
    try { Write-Host ('  [{0}] {1}: {2}' -f $mark, $Label, $Msg) } catch { $null = $_ }
}

function ConvertTo-Hash($Obj) {
    $h = @{}
    if ($null -ne $Obj) {
        if ($Obj -is [System.Collections.IDictionary]) {
            foreach ($k in $Obj.Keys) { $h[$k] = $Obj[$k] }
        } else {
            foreach ($p in $Obj.PSObject.Properties) { $h[$p.Name] = $p.Value }
        }
    }
    return $h
}

function Get-List($Value) {
    $out = New-Object System.Collections.ArrayList
    if ($null -ne $Value) { foreach ($v in @($Value)) { if ($null -ne $v) { [void]$out.Add($v) } } }
    return , $out
}

function Read-JsonFile([string]$Path) {
    if (-not $Path -or -not (Test-Path -LiteralPath $Path)) { return $null }
    $t = [IO.File]::ReadAllText($Path, [Text.Encoding]::UTF8)
    if (-not $t.Trim()) { return $null }
    return ($t | ConvertFrom-Json)
}

function Write-JsonFile([string]$Path, $Obj) {
    $dir = Split-Path -Parent $Path
    if ($dir -and -not (Test-Path -LiteralPath $dir)) { [void][IO.Directory]::CreateDirectory($dir) }
    $json = ConvertTo-Json -InputObject $Obj -Depth 8
    $tmp = $Path + '.tmp'
    [IO.File]::WriteAllText($tmp, $json, (New-Object System.Text.UTF8Encoding($false)))
    Move-Item -LiteralPath $tmp -Destination $Path -Force
}

function Save-Record {
    # 変更するたびに記録する（途中で止まっても［元に戻す］で戻せるように）
    $script:Rec.updated = (Get-Date).ToString('s')
    $script:Rec.computer = [string]$env:COMPUTERNAME
    Write-JsonFile $script:RecPath $script:Rec
    Set-FileOwnerAdmins $script:RecPath
}

function Get-NormPath([string]$Path) {
    return ([IO.Path]::GetFullPath($Path)).TrimEnd('\').ToLowerInvariant()
}

function Test-SamePath([string]$A, [string]$B) {
    if (-not $A -or -not $B) { return $false }
    return ((Get-NormPath $A) -eq (Get-NormPath $B))
}

function Test-Under([string]$Child, [string]$Parent) {
    if (-not $Child -or -not $Parent) { return $false }
    $c = Get-NormPath $Child
    $p = Get-NormPath $Parent
    return ($c -eq $p -or $c.StartsWith($p + '\'))
}

function Get-DriveKind([string]$Path) {
    $drv = New-Object System.IO.DriveInfo($Path.Substring(0, 1))
    return [string]$drv.DriveType
}

function Test-Folder([string]$Path) {
    return (Test-Path -LiteralPath $Path -PathType Container)
}

function Initialize-Folder([string]$Path) {
    # 作ったら $true（すでにあれば $false）
    if (Test-Folder $Path) { return $false }
    [void][IO.Directory]::CreateDirectory($Path)
    return $true
}

function Invoke-Icacls([string[]]$IcaclsArgs) {
    & icacls.exe @IcaclsArgs | Out-Null
    return $LASTEXITCODE
}

function Protect-RecordDir {
    # 記録の置き場所（ProgramData\SEVENTHWELL と その中）：持ち主は管理者、管理者とSYSTEMだけが書ける（ふつうのユーザーは読むだけ）
    # 権限は丸ごと置き換える（前からある別の許可は残さない）
    $sddl = 'O:BAG:SYD:PAI(A;OICI;FA;;;SY)(A;OICI;FA;;;BA)(A;OICI;0x1200a9;;;BU)'
    foreach ($d in @((Split-Path -Parent $script:RecDir), $script:RecDir)) {
        [void][IO.Directory]::CreateDirectory($d)
        $sec = New-Object System.Security.AccessControl.DirectorySecurity
        $sec.SetSecurityDescriptorSddlForm($sddl)
        [IO.Directory]::SetAccessControl($d, $sec)
    }
    foreach ($f in @(Get-ChildItem -LiteralPath $script:RecDir -Force -ErrorAction SilentlyContinue)) {
        $null = Invoke-Icacls @($f.FullName, '/reset', '/C', '/Q')   # 中のファイルの権限も上に合わせる（持ち主は変えない）
    }
}

function Test-TrustedFile([string]$Path) {
    # 記録の持ち主が管理者（またはSYSTEM）か。ふつうのユーザーが置いた記録は信用しない
    try {
        $o = (Get-Acl -LiteralPath $Path).GetOwner([System.Security.Principal.SecurityIdentifier]).Value
        return ($o -eq 'S-1-5-32-544' -or $o -eq 'S-1-5-18')
    } catch { return $false }
}

function Set-FileOwnerAdmins([string]$Path) {
    $null = Invoke-Icacls @($Path, '/setowner', '*S-1-5-32-544', '/C', '/Q')
}

function Test-ExplicitAce([string]$Folder, [string]$Sid) {
    try {
        foreach ($a in @((Get-Acl -LiteralPath $Folder).Access)) {
            if (-not $a.IsInherited) {
                try { if ($a.IdentityReference.Translate([System.Security.Principal.SecurityIdentifier]).Value -eq $Sid) { return $true } } catch { $null = $_ }
            }
        }
    } catch { $null = $_ }
    return $false
}

function Get-FolderAccessSddl([string]$Folder) {
    return (Get-Acl -LiteralPath $Folder).GetSecurityDescriptorSddlForm('Access')
}

function Restore-FolderAccess([string]$Folder, [string]$Sddl) {
    $acl = Get-Acl -LiteralPath $Folder
    $acl.SetSecurityDescriptorSddlForm($Sddl, 'Access')
    Set-Acl -LiteralPath $Folder -AclObject $acl -ErrorAction Stop
}

function Get-ActiveProfileNames {
    # いまつながっているネットワークの種類（ファイアウォールのプロファイル名）
    $names = @()
    try {
        foreach ($cp in @(Get-NetConnectionProfile -ErrorAction Stop)) {
            $c = [string]$cp.NetworkCategory
            if ($c -eq 'DomainAuthenticated') { $c = 'Domain' }
            if ($names -notcontains $c) { $names += $c }
        }
    } catch { $null = $_ }
    return , $names
}

function Get-ActiveScheme {
    $o = (& powercfg.exe /getactivescheme) -join ' '
    $m = [regex]::Match($o, '[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}')
    if (-not $m.Success) { return $null }
    return $m.Value
}

function Get-PowerAc([string]$Scheme, [string]$Setting) {
    # 数値の設定は「最小・最大・増分・AC・DC」の順に 0x… が並ぶ（表示言語に関係なく）
    $o = (& powercfg.exe /q $Scheme SUB_SLEEP $Setting) -join "`n"
    if ($LASTEXITCODE -ne 0) { return $null }
    $m = [regex]::Matches($o, '0x([0-9a-fA-F]{8})')
    if ($m.Count -lt 4) { return $null }
    return [Convert]::ToInt64($m[3].Groups[1].Value, 16)
}

function Set-PowerAc([string]$Scheme, [string]$Setting, [long]$Seconds) {
    & powercfg.exe /setacvalueindex $Scheme SUB_SLEEP $Setting $Seconds | Out-Null
    if ($LASTEXITCODE -ne 0) { throw ('powercfg {0}' -f $LASTEXITCODE) }
    if ($Scheme -eq (Get-ActiveScheme)) {
        & powercfg.exe /setactive $Scheme | Out-Null
        if ($LASTEXITCODE -ne 0) { throw ('powercfg {0}' -f $LASTEXITCODE) }
    }
}

function Get-AutoLogonUser {
    try {
        $v = Get-ItemProperty -Path 'HKLM:\SOFTWARE\Microsoft\Windows NT\CurrentVersion\Winlogon' -Name 'DefaultUserName' -ErrorAction Stop
        return [string]$v.DefaultUserName
    } catch { return '' }
}

function Test-LocalAdmin([string]$Name) {
    # 確かめられないときは「管理者」とみなす（既存のアカウントを使わない側に倒す）
    try {
        $g = Get-CimInstance -ClassName Win32_Group -Filter "LocalAccount=True AND SID='S-1-5-32-544'" -ErrorAction Stop
        $m = @(Get-CimAssociatedInstance -InputObject $g -ResultClassName Win32_UserAccount -ErrorAction Stop | Where-Object { $_.LocalAccount -and [string]$_.Name -eq $Name })
        return ($m.Count -gt 0)
    } catch { return $true }
}

function Get-StartType([string]$Mode) {
    switch ($Mode) { 'Auto' { return 'Automatic' } 'Manual' { return 'Manual' } 'Disabled' { return 'Disabled' } }
    return $null
}

function Get-AdminsName {
    $sid = New-Object System.Security.Principal.SecurityIdentifier('S-1-5-32-544')
    return $sid.Translate([System.Security.Principal.NTAccount]).Value
}

function Get-OpenFileCount([string]$Folder) {
    $n = 0
    foreach ($f in @(Get-SmbOpenFile -ErrorAction SilentlyContinue)) {
        if (Test-Under ([string]$f.Path) $Folder) { $n++ }
    }
    return $n
}

function Wait-Close {
    try { Write-Host ''; Write-Host '終わりました。このウィンドウは数秒で閉じます。'; Start-Sleep -Seconds 4 } catch { $null = $_ }
}

# ------------------------------------------------------------------ 設定
function Invoke-Setup($P) {
    $Rec = $script:Rec
    $uname = [string]$P.user
    $sname = [string]$P.share
    $folder = [string]$P.folder
    $acct = '{0}\{1}' -f $env:COMPUTERNAME, $uname

    # ---- 先に確かめる（ここで止まるときは何も変更しない）
    $pre = @()
    if ($folder -notmatch '^[A-Za-z]:\\.+') { $pre += '共有するフォルダは、このPCのドライブのフォルダを指定してください（例 D:\発表データ）' }
    else {
        try {
            if ((Get-DriveKind $folder) -ne 'Fixed') { $pre += 'このPCの内蔵ドライブ（固定ドライブ）のフォルダを指定してください' }
        } catch { $pre += ('ドライブを確認できません: ' + $_.Exception.Message) }
        foreach ($sys in @($env:SystemRoot, $env:ProgramFiles, ${env:ProgramFiles(x86)}, $env:ProgramData)) {
            if ($sys -and ((Test-Under $folder $sys) -or (Test-Under $sys $folder))) { $pre += 'Windows・アプリのフォルダは共有できません'; break }
        }
        if ($env:SystemDrive -and (Test-SamePath $folder ($env:SystemDrive + '\Users'))) { $pre += 'ユーザーのフォルダそのものは共有できません' }
    }
    if ($Rec.user) {
        $ru = ConvertTo-Hash $Rec.user
        if ($ru.name -and $ru.name -ne $uname) { $pre += ('前回はアカウント「{0}」で設定しています。名前を変えるときは、先に［元に戻す］をしてください' -f $ru.name) }
    }
    if ($Rec.share) {
        $rs = ConvertTo-Hash $Rec.share
        if (($rs.name -and $rs.name -ne $sname) -or ($rs.path -and -not (Test-SamePath $rs.path $folder))) {
            $pre += ('前回は「{0}」（{1}）を共有しています。変えるときは、先に［元に戻す］をしてください' -f $rs.name, $rs.path)
        }
    }
    try {
        $ex = Get-SmbShare -Name $sname -ErrorAction SilentlyContinue
        if ($ex -and -not (Test-SamePath ([string]$ex.Path) $folder)) { $pre += ('共有名「{0}」は別のフォルダ（{1}）で使われています。別の共有名にしてください' -f $sname, $ex.Path) }
    } catch { $pre += ('共有の一覧を読めません: ' + $_.Exception.Message) }
    $u0 = Get-LocalUser -Name $uname -ErrorAction SilentlyContinue
    $ours = $false
    if ($u0) {
        $ours = ([string]$u0.Description -eq $script:AcctDesc)
        if (-not $ours) {
            $who = @([string]$P.current_user, [string]$env:USERNAME, (Get-AutoLogonUser)) | Where-Object { $_ }
            if ($who -contains $uname) { $pre += ('アカウント「{0}」はこのPCにログインしているアカウントです。共有用には別の名前にしてください' -f $uname) }
            elseif (Test-LocalAdmin $uname) { $pre += ('アカウント「{0}」は管理者のアカウントです。共有用には別の名前にしてください' -f $uname) }
        }
    }
    if ($pre.Count) {
        foreach ($m in $pre) { Add-Step 'pre' '確認' $false $m }
        return $false
    }

    $allOk = $true

    # ---- 1. Windowsファイアウォール（このアプリ用の規則。有線（またはWi-Fiも）・同じネットワーク内からだけ）
    try {
        $ifType = 'Wired'
        if ($P.wifi) { $ifType = 'Any' }
        $remote = @(@($P.peer_ips) | Where-Object { [string]$_ -match '^\d{1,3}(\.\d{1,3}){3}$' } | ForEach-Object { [string]$_ })
        $from = '相手のPC（' + ($remote -join '・') + '）からだけ'
        if (-not $remote.Count) { $remote = @('LocalSubnet'); $from = '同じネットワーク内のPCからだけ' }
        $Rec.firewall = $true
        Save-Record
        Get-NetFirewallRule -Group $script:FwGroup -ErrorAction SilentlyContinue | Remove-NetFirewallRule -ErrorAction Stop
        $rules = @(
            @('SWNAS-SMB-TCP-445', 'ファイル共有 (SMB TCP 445)', 'TCP', '445'),
            @('SWNAS-NB-TCP-139', 'ファイル共有 (NetBIOS TCP 139)', 'TCP', '139'),
            @('SWNAS-NB-UDP-137', 'PC名の検索 (NetBIOS UDP 137)', 'UDP', '137'),
            @('SWNAS-NB-UDP-138', 'PC名の検索 (NetBIOS UDP 138)', 'UDP', '138'),
            @('SWNAS-LLMNR-UDP-5355', 'PC名の検索 (LLMNR UDP 5355)', 'UDP', '5355')
        )
        foreach ($r in $rules) {
            New-NetFirewallRule -Name $r[0] -DisplayName ('SW NAS OPERATOR - ' + $r[1]) -Group $script:FwGroup -Direction Inbound -Action Allow -Profile Any -InterfaceType $ifType -RemoteAddress $remote -Protocol $r[2] -LocalPort $r[3] -ErrorAction Stop | Out-Null
        }
        New-NetFirewallRule -Name 'SWNAS-ICMPv4-Echo' -DisplayName 'SW NAS OPERATOR - 応答確認 (ping)' -Group $script:FwGroup -Direction Inbound -Action Allow -Profile Any -InterfaceType $ifType -RemoteAddress $remote -Protocol ICMPv4 -IcmpType 8 -ErrorAction Stop | Out-Null
        $n = @(Get-NetFirewallRule -Group $script:FwGroup -ErrorAction SilentlyContinue).Count
        if ($n -ne 6) { throw ('規則を確認できませんでした（{0}/6）' -f $n) }
        $where = '有線LAN'
        if ($P.wifi) { $where = '有線LAN・Wi-Fi' }
        Add-Step 'firewall' 'Windowsファイアウォール' $true ('{0}、ファイル共有・PC名の検索・pingを許可（{1}）' -f $from, $where)
    } catch { Add-Step 'firewall' 'Windowsファイアウォール' $false ('設定できませんでした: ' + $_.Exception.Message); $allOk = $false }
    try {
        $blocked = @()
        $active = Get-ActiveProfileNames
        foreach ($fp in @(Get-NetFirewallProfile -PolicyStore ActiveStore -ErrorAction Stop)) {
            if ($active.Count -and $active -notcontains [string]$fp.Name) { continue }   # いまつながっているネットワークの種類だけ見る
            if ([string]$fp.Enabled -eq 'False') { continue }
            if ([string]$fp.AllowLocalFirewallRules -eq 'False' -or [string]$fp.AllowInboundRules -eq 'False') { $blocked += [string]$fp.Name }
        }
        if ($blocked.Count) {
            Add-Step 'firewall_gpo' 'ファイアウォールの方針' $false ('このPCの方針（グループポリシーなど）で、追加した規則が使われない設定になっています: ' + ($blocked -join '・') + '。PCの管理者に確認してください')
            $allOk = $false
        }
    } catch { $null = $_ }
    try {
        $fp3 = @(Get-CimInstance -Namespace 'root/SecurityCenter2' -ClassName 'FirewallProduct' -ErrorAction Stop | Where-Object { [string]$_.displayName -notmatch 'Windows' })
        if ($fp3.Count) {
            Add-Step 'firewall3' '他社のセキュリティソフト' $null ('「{0}」が入っています。そちらのファイアウォールでも、ファイル共有の許可が必要な場合があります' -f (($fp3 | ForEach-Object { [string]$_.displayName }) -join '」「'))
        }
    } catch { $null = $_ }

    # ---- 2. サービス（止めることはしない。自動起動にして、止まっていれば起動）
    $known = Get-List $Rec.services
    $bad = @()
    $labels = @{ LanmanServer = 'ファイル共有（Server）'; LanmanWorkstation = 'ほかのPCへの接続（Workstation）'; FDResPub = 'ネットワークにこのPCを表示（FDResPub）'; fdPHost = 'ネットワークのPCを探す（fdPHost）' }
    foreach ($name in $script:Services) {
        $must = ($name -eq 'LanmanServer' -or $name -eq 'LanmanWorkstation')
        try {
            $w = Get-CimInstance -ClassName Win32_Service -Filter ("Name='{0}'" -f $name) -ErrorAction Stop
            if (-not $w) { throw 'サービスが見つかりません' }
            $mode = [string]$w.StartMode
            if ($mode -ne 'Auto') {
                $hit = @($known | Where-Object { $_.name -eq $name })
                if (-not $hit.Count) { [void]$known.Add([ordered]@{ name = $name; start = $mode }); $Rec.services = $known.ToArray(); Save-Record }
                Set-Service -Name $name -StartupType Automatic -ErrorAction Stop
            }
            if ([string]$w.State -ne 'Running') { Start-Service -Name $name -ErrorAction Stop }
        } catch { if ($must) { $bad += ('{0}: {1}' -f $labels[$name], $_.Exception.Message) } }
    }
    $Rec.services = $known.ToArray()
    if ($bad.Count) { Add-Step 'services' 'ファイル共有のサービス' $false ($bad -join ' / '); $allOk = $false }
    else { Add-Step 'services' 'ファイル共有のサービス' $true '自動で起動するように設定（Server・Workstation など）' }

    # ---- 3. SMB2/3（SMB1 は使わない）
    try {
        $c = Get-SmbServerConfiguration -ErrorAction Stop
        if (-not $c.EnableSMB2Protocol) {
            if ($null -eq $Rec.smb2_prev) { $Rec.smb2_prev = $false; Save-Record }
            Set-SmbServerConfiguration -EnableSMB2Protocol $true -Force -ErrorAction Stop
            Add-Step 'smb' 'SMB' $true 'SMB2/3 を有効にしました'
        }
    } catch { Add-Step 'smb' 'SMB' $false ('確認できませんでした: ' + $_.Exception.Message) }

    # ---- 4. 共有用アカウント（普通のアカウント。管理者にはしない）
    $userOk = $false
    $ur = @{ name = $uname; sid = ''; created = $false; enabled_prev = $null; group_added = $false }
    if ($Rec.user) { $ur = ConvertTo-Hash $Rec.user }
    $expires = (Get-Date).AddDays(30)    # ［元に戻す］を忘れても、30日で使えなくなる（設定し直すと延びる）
    try {
        $sec = ConvertTo-SecureString ([string]$P.password) -AsPlainText -Force
        $u = Get-LocalUser -Name $uname -ErrorAction SilentlyContinue
        if (-not $u) {
            $ur.created = $true
            $Rec.user = $ur
            Save-Record
            New-LocalUser -Name $uname -Password $sec -PasswordNeverExpires -UserMayNotChangePassword -AccountExpires $expires -Description $script:AcctDesc -ErrorAction Stop | Out-Null
            $msg = ('アカウント「{0}」を作りました（管理者ではない普通のアカウント。{1}まで使えます）' -f $uname, $expires.ToString('M月d日'))
        } else {
            if ($ours) {
                Set-LocalUser -Name $uname -Password $sec -PasswordNeverExpires $true -AccountExpires $expires -ErrorAction Stop
                $msg = ('アカウント「{0}」のパスワードを設定しました（{1}まで使えます）' -f $uname, $expires.ToString('M月d日'))
            } elseif ($P.set_password) {
                Set-LocalUser -Name $uname -Password $sec -ErrorAction Stop
                $msg = ('アカウント「{0}」のパスワードを変えました' -f $uname)
            } else {
                $msg = ('アカウント「{0}」はすでにあるので、そのまま使います（パスワードは変えていません。両方のPCで同じパスワードにしてください）' -f $uname)
            }
            if (-not $u.Enabled) {
                if ($null -eq $ur.enabled_prev) { $ur.enabled_prev = $false; $Rec.user = $ur; Save-Record }
                Enable-LocalUser -Name $uname -ErrorAction Stop
            }
        }
        $u = Get-LocalUser -Name $uname -ErrorAction Stop
        $ur.sid = [string]$u.SID.Value
        $Rec.user = $ur
        Save-Record
        try {
            Add-LocalGroupMember -SID 'S-1-5-32-545' -Member $uname -ErrorAction Stop
            if (-not $ur.created) { $ur.group_added = $true; $Rec.user = $ur; Save-Record }
        } catch {
            if ([string]$_.FullyQualifiedErrorId -notlike '*MemberExists*') { throw }
        }
        $userOk = $true
        Add-Step 'user' '共有用アカウント' $true $msg
    } catch {
        Add-Step 'user' '共有用アカウント' $false ('作れませんでした: ' + $_.Exception.Message + '（パスワードがこのPCの規則に合わない場合は、長く・複雑にしてください）')
        $allOk = $false
    }

    # ---- 5. フォルダ・権限・共有
    if ($userOk) {
        try {
            $fr = @{ path = $folder; created = $false }
            if ($Rec.folder) { $fr = ConvertTo-Hash $Rec.folder }
            if ((Initialize-Folder $folder) -and -not $Rec.folder) { $fr.created = $true }
            $Rec.folder = $fr
            Save-Record
            $sid = [string]$ur.sid
            if (-not $Rec.acl) {
                $acl = [ordered]@{ path = $folder; sid = $sid; orig = $null }
                if (Test-ExplicitAce $folder $sid) { $acl.orig = Get-FolderAccessSddl $folder }   # 前から権限があれば、元の権限を丸ごと覚えておく
                $Rec.acl = $acl
                Save-Record
            }
            $rc = Invoke-Icacls @($folder, '/grant', ('*{0}:(OI)(CI)M' -f $sid))
            if ($rc -ne 0) { throw ('フォルダの権限を設定できませんでした（icacls {0}）' -f $rc) }

            $sr = @{ name = $sname; path = $folder; created = $false; granted = $null }
            if ($Rec.share) { $sr = ConvertTo-Hash $Rec.share }
            $sh = Get-SmbShare -Name $sname -ErrorAction SilentlyContinue
            if ($sh) {
                $acc = @(Get-SmbShareAccess -Name $sname -ErrorAction Stop | Where-Object { [string]$_.AccountName -eq $acct -and [string]$_.AccessControlType -eq 'Allow' -and [string]$_.AccessRight -eq 'Full' })
                if (-not $acc.Count) {
                    if (-not $sr.created) { $sr.granted = $acct; $Rec.share = $sr; Save-Record }
                    Grant-SmbShareAccess -Name $sname -AccountName $acct -AccessRight Full -Force -ErrorAction Stop | Out-Null
                }
                $smsg = ('「\\{0}\{1}」（{2}）はすでに共有されています。アカウント「{3}」が読み書きできます' -f $env:COMPUTERNAME, $sname, $folder, $uname)
            } else {
                $sr.created = $true
                $Rec.share = $sr
                Save-Record
                New-SmbShare -Name $sname -Path $folder -FullAccess @($acct, (Get-AdminsName)) -CachingMode None -Description $script:ShareDesc -ErrorAction Stop | Out-Null
                $smsg = ('「{0}」を「\\{1}\{2}」として共有しました（アカウント「{3}」が読み書きできます）' -f $folder, $env:COMPUTERNAME, $sname, $uname)
            }
            $Rec.share = $sr
            Save-Record
            $chk = Get-SmbShare -Name $sname -ErrorAction Stop
            if (-not (Test-SamePath ([string]$chk.Path) $folder)) { throw '共有を確認できませんでした' }
            $acc = @(Get-SmbShareAccess -Name $sname -ErrorAction Stop | Where-Object { [string]$_.AccountName -eq $acct -and [string]$_.AccessControlType -eq 'Allow' })
            if (-not $acc.Count) { throw '共有の権限を確認できませんでした' }
            Add-Step 'share' 'フォルダの共有' $true $smsg
        } catch { Add-Step 'share' 'フォルダの共有' $false ('共有できませんでした: ' + $_.Exception.Message); $allOk = $false }
    } else {
        Add-Step 'share' 'フォルダの共有' $false 'アカウントを作れなかったため、共有していません'
    }

    # ---- 6. スリープしない（電源接続時。いまの電源プランに対して。プランごとに元の値を覚える）
    if ($P.nosleep) {
        try {
            $scheme = Get-ActiveScheme
            if (-not $scheme) { throw '今の電源プランを読み取れませんでした（変更していません）' }
            $plist = Get-List $Rec.power
            $hit = @($plist | Where-Object { [string]$_.scheme -eq $scheme })
            if (-not $hit.Count) {
                $st = Get-PowerAc $scheme 'STANDBYIDLE'
                $hb = Get-PowerAc $scheme 'HIBERNATEIDLE'
                if ($null -eq $st) { throw '今の設定を読み取れませんでした（変更していません）' }
                [void]$plist.Add([ordered]@{ scheme = $scheme; standby_ac = $st; hibernate_ac = $hb })
                $Rec.power = $plist.ToArray()
                Save-Record
                $hb0 = $hb
            } else { $hb0 = $hit[0].hibernate_ac }
            Set-PowerAc $scheme 'STANDBYIDLE' 0
            if ($null -ne $hb0) { Set-PowerAc $scheme 'HIBERNATEIDLE' 0 }
            Add-Step 'power' 'スリープ' $true '電源につないでいる間はスリープ・休止状態にしない（いまの電源プラン）'
        } catch { Add-Step 'power' 'スリープ' $false ('設定できませんでした: ' + $_.Exception.Message) }
    }
    return $allOk
}

# ------------------------------------------------------------------ 元に戻す
function Test-ProtectedAccount([string]$Name, $P) {
    # ログイン中・自動ログオン・管理者のアカウントは、無効にしたりグループから外したりしない
    $who = @([string]$P.current_user, [string]$env:USERNAME, (Get-AutoLogonUser)) | Where-Object { $_ }
    if ($who -contains $Name) { return $true }
    return (Test-LocalAdmin $Name)
}

function Invoke-Undo($P) {
    $Rec = $script:Rec
    if (-not $Rec) {
        Add-Step 'undo' '元に戻す' $false '設定の記録がありません（このPCで［このPCを設定する］をしていないか、すでに元に戻しています）'
        return $false
    }
    if ([int]$Rec.version -ne 2) {
        Add-Step 'undo' '元に戻す' $false '設定の記録の形式が違うため、元に戻せません（何も変更していません）'
        return $false
    }
    $ok = $true
    $base = ''
    if ($Rec.share) { $base = [string](ConvertTo-Hash $Rec.share).path }
    if (-not $base -and $Rec.folder) { $base = [string](ConvertTo-Hash $Rec.folder).path }
    if ($Rec.share -and $base) {
        $n = Get-OpenFileCount $base
        if ($n -gt 0) {
            Add-Step 'open' '開いているファイル' $false ('ほかのPCが共有のファイルを開いています（{0}件）。閉じてから、もう一度［元に戻す］を押してください（何も変更していません）' -f $n)
            return $false
        }
    }
    if ($Rec.share) {
        try {
            $s = ConvertTo-Hash $Rec.share
            $w = Get-CimInstance -ClassName Win32_Service -Filter "Name='LanmanServer'" -ErrorAction Stop
            if ($w -and [string]$w.State -ne 'Running') { Start-Service -Name 'LanmanServer' -ErrorAction Stop }   # 止まっていると共有の一覧が読めず、やめられないため
            $cur = Get-SmbShare -Name $s.name -ErrorAction SilentlyContinue
            if ($cur -and -not (Test-SamePath ([string]$cur.Path) ([string]$s.path))) {
                Add-Step 'share' 'フォルダの共有' $null ('「{0}」は別のフォルダの共有になっているので、そのままにしました' -f $s.name)
            } elseif ($s.created) {
                if ($cur -and [string]$cur.Description -ne $script:ShareDesc) {
                    Add-Step 'share' 'フォルダの共有' $null ('「{0}」は作った共有と違うため、そのままにしました' -f $s.name)
                } else {
                    if ($cur) { Remove-SmbShare -Name $s.name -Force -ErrorAction Stop }
                    if (Get-SmbShare -Name $s.name -ErrorAction SilentlyContinue) { throw '共有をやめられませんでした' }
                    Add-Step 'share' 'フォルダの共有' $true ('「{0}」の共有をやめました（フォルダとデータはそのまま）' -f $s.name)
                }
            } elseif ($s.granted) {
                if ($cur) { Revoke-SmbShareAccess -Name $s.name -AccountName $s.granted -Force -ErrorAction Stop | Out-Null }
                Add-Step 'share' 'フォルダの共有' $true ('「{0}」に付けた権限を外しました' -f $s.name)
            }
        } catch { Add-Step 'share' 'フォルダの共有' $false $_.Exception.Message; $ok = $false }
    }
    if ($Rec.acl) {
        try {
            $a = ConvertTo-Hash $Rec.acl
            if ($a.sid -and $a.path -and (Test-SamePath ([string]$a.path) $base) -and (Test-Folder ([string]$a.path))) {
                if ($a.orig) {
                    Restore-FolderAccess ([string]$a.path) ([string]$a.orig)
                    Add-Step 'acl' 'フォルダの権限' $true 'フォルダの権限を元に戻しました'
                } else {
                    $rc = Invoke-Icacls @([string]$a.path, '/remove:g', ('*' + [string]$a.sid))
                    if ($rc -ne 0) { throw ('icacls {0}' -f $rc) }
                    Add-Step 'acl' 'フォルダの権限' $true '付けた権限を外しました'
                }
            }
        } catch { Add-Step 'acl' 'フォルダの権限' $false $_.Exception.Message; $ok = $false }
    }
    if ($Rec.user) {
        try {
            $u = ConvertTo-Hash $Rec.user
            $cur = Get-LocalUser -Name $u.name -ErrorAction SilentlyContinue
            if ($u.created) {
                if ($cur -and [string]$cur.Description -eq $script:AcctDesc -and (-not $u.sid -or [string]$cur.SID.Value -eq [string]$u.sid)) {
                    Remove-LocalUser -Name $u.name -ErrorAction Stop
                    Add-Step 'user' '共有用アカウント' $true ('アカウント「{0}」を削除しました' -f $u.name)
                } elseif ($cur) {
                    Add-Step 'user' '共有用アカウント' $null ('アカウント「{0}」は作ったものと違うため、残しました' -f $u.name)
                }
            } elseif ($cur -and ($u.group_added -or $u.enabled_prev -eq $false)) {
                if (Test-ProtectedAccount ([string]$u.name) $P) {
                    Add-Step 'user' '共有用アカウント' $null ('アカウント「{0}」はログイン・管理者に使われているため、そのままにしました' -f $u.name)
                } else {
                    if ($u.group_added) { try { Remove-LocalGroupMember -SID 'S-1-5-32-545' -Member $u.name -ErrorAction Stop } catch { $null = $_ } }
                    if ($u.enabled_prev -eq $false) { Disable-LocalUser -Name $u.name -ErrorAction Stop }
                    Add-Step 'user' '共有用アカウント' $true ('アカウント「{0}」は元からあったので残しました（無効・グループを元に戻しました）' -f $u.name)
                }
            } elseif ($cur) {
                Add-Step 'user' '共有用アカウント' $true ('アカウント「{0}」は元からあったので残しました' -f $u.name)
            }
        } catch { Add-Step 'user' '共有用アカウント' $false $_.Exception.Message; $ok = $false }
    }
    if ($Rec.firewall) {
        try {
            Get-NetFirewallRule -Group $script:FwGroup -ErrorAction SilentlyContinue | Remove-NetFirewallRule -ErrorAction Stop
            if (@(Get-NetFirewallRule -Group $script:FwGroup -ErrorAction SilentlyContinue).Count) { throw '規則を削除できませんでした' }
            Add-Step 'firewall' 'Windowsファイアウォール' $true '追加した規則を削除しました'
        } catch { Add-Step 'firewall' 'Windowsファイアウォール' $false $_.Exception.Message; $ok = $false }
    }
    $svc = Get-List $Rec.services
    if ($svc.Count) {
        $bad = @()
        $done = 0
        foreach ($s in $svc) {
            $name = [string]$s.name
            $st = Get-StartType ([string]$s.start)
            if (-not ($script:Services -contains $name) -or -not $st) { continue }
            if ($name -eq 'LanmanWorkstation' -and $st -eq 'Disabled') { continue }   # NASにつなぐのに使うので、無効には戻さない
            try { Set-Service -Name $name -StartupType $st -ErrorAction Stop; $done++ } catch { $bad += ('{0}: {1}' -f $name, $_.Exception.Message) }
        }
        if ($bad.Count) { Add-Step 'services' 'サービス' $false ($bad -join ' / '); $ok = $false }
        elseif ($done) { Add-Step 'services' 'サービス' $true '起動の設定を元に戻しました（いま動いているサービスは止めません。次の再起動から元どおり）' }
    }
    if ($Rec.smb2_prev -eq $false) {
        try { Set-SmbServerConfiguration -EnableSMB2Protocol $false -Force -ErrorAction Stop; Add-Step 'smb' 'SMB' $true 'SMB2/3 の設定を元に戻しました' }
        catch { Add-Step 'smb' 'SMB' $false $_.Exception.Message; $ok = $false }
    }
    $plist = Get-List $Rec.power
    if ($plist.Count) {
        try {
            foreach ($pw in $plist) {
                $sc = [string]$pw.scheme
                if ($sc -notmatch '^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$') { continue }
                if ($null -ne $pw.standby_ac) { Set-PowerAc $sc 'STANDBYIDLE' ([long]$pw.standby_ac) }
                if ($null -ne $pw.hibernate_ac) { Set-PowerAc $sc 'HIBERNATEIDLE' ([long]$pw.hibernate_ac) }
            }
            Add-Step 'power' 'スリープ' $true 'スリープの設定を元に戻しました'
        } catch { Add-Step 'power' 'スリープ' $false $_.Exception.Message; $ok = $false }
    }
    if ($Rec.folder) {
        $f = ConvertTo-Hash $Rec.folder
        Add-Step 'folder' 'フォルダ' $null ('フォルダとデータは消していません: {0}' -f $f.path)
    }
    return $ok
}

# ------------------------------------------------------------------ 本体
function Invoke-Main([string]$Json, [string]$File) {
    if ($File) { try { Remove-Item -LiteralPath $File -Force -ErrorAction SilentlyContinue } catch { $null = $_ } }   # パスワードを含むので、すぐ消す
    $P = $Json | ConvertFrom-Json
    $result = [ordered]@{ id = [string]$P.job_id; action = [string]$P.action; ok = $false; steps = @(); finished = $null; computer = [string]$env:COMPUTERNAME }
    try { Write-Host 'SW NAS OPERATOR : ファイル共有の設定' ; Write-Host '' } catch { $null = $_ }
    $mtx = $null
    try {
        try { $mtx = New-Object System.Threading.Mutex($false, 'Global\SEVENTHWELL_SWNASOPERATOR_ShareSetup') } catch { $mtx = $null }
        $got = $true
        if ($mtx) { try { $got = $mtx.WaitOne(0) } catch [System.Threading.AbandonedMutexException] { $got = $true } }
        if (-not $got) { $mtx.Dispose(); $mtx = $null; throw '別の設定（または元に戻す）がまだ実行中です。そのウィンドウが閉じてから、もう一度押してください（何も変更していません）' }
        Protect-RecordDir
        if (Test-Path -LiteralPath $script:RecPath) {
            if (Test-TrustedFile $script:RecPath) {
                $raw = Read-JsonFile $script:RecPath
                if ($raw) { $script:Rec = ConvertTo-Hash $raw }
            } else {
                $stamp = (Get-Date).ToString('yyyyMMdd-HHmmss')
                Move-Item -LiteralPath $script:RecPath -Destination ($script:RecPath -replace '\.json$', ('.untrusted-' + $stamp + '.json')) -Force
                Add-Step 'record' '設定の記録' $null '管理者以外が置いた記録があったため、使わずに別の名前にしました'
            }
        }
        if ($P.action -eq 'setup') {
            if ($script:Rec -and [int]$script:Rec.version -ne 2) { throw '設定の記録の形式が違います（何も変更していません）' }
            if (-not $script:Rec) { $script:Rec = @{ version = 2; created = (Get-Date).ToString('s') } }
            $result.ok = Invoke-Setup $P
        } elseif ($P.action -eq 'undo') {
            $result.ok = Invoke-Undo $P
            if ($script:Rec -and $result.ok) {
                $stamp = (Get-Date).ToString('yyyyMMdd-HHmmss')
                Move-Item -LiteralPath $script:RecPath -Destination ($script:RecPath -replace '\.json$', ('.undone-' + $stamp + '.json')) -Force
            }
        } else {
            throw ('unknown action: ' + $P.action)
        }
    } catch {
        Add-Step 'error' 'エラー' $false $_.Exception.Message
        $result.ok = $false
    } finally {
        if ($mtx) { try { $mtx.ReleaseMutex() } catch { $null = $_ }; $mtx.Dispose() }
    }
    $result.steps = $script:Steps.ToArray()
    $result.finished = (Get-Date).ToString('s')
    try { Write-JsonFile $script:ResPath $result } catch { $null = $_ }
    Wait-Close
}

if ($ParamJson) { Invoke-Main $ParamJson $ParamFile }
'''

# ---------------------------------------------------------------- UI（PADDOCK SCOUT の画面に足す部分）
OP_CSS = r'''
/* ===== PADDOCK GATE ===== */
.opsetup{border:1px solid rgba(139,92,246,.45);background:rgba(139,92,246,.08);border-radius:12px;padding:12px 14px;margin:0 0 14px;font-size:13px;line-height:1.7}
.opsetup b{color:var(--foreground)}
.opsetup ol{margin:4px 0 0;padding-left:20px}
.opsetup .alt{margin-top:8px;padding-top:8px;border-top:1px dashed rgba(139,92,246,.35)}
/* ネットワーク共有（メインPC⇄バックアップPC） */
#netov{position:fixed;inset:0;background:rgba(0,0,0,.65);backdrop-filter:blur(2px);display:none;align-items:flex-start;justify-content:center;z-index:55;overflow:auto;padding:48px 16px}
#netov.open{display:flex}
.netdlg{width:min(940px,100%)}
.nsme{display:grid;gap:6px;margin-top:16px;padding:12px 14px;border:1px solid var(--border);border-radius:10px;background:var(--card);font-size:13.5px}
.nsme .k{display:inline-block;min-width:104px;color:var(--muted-fg)}
.nsd{border:1px solid var(--border);border-radius:10px;padding:10px 12px;margin:0 0 10px}
.nsd.bad{border-color:rgba(248,113,113,.45)}
.nsdh{display:flex;gap:10px;align-items:center;margin-bottom:6px;font-size:13.5px;flex-wrap:wrap}
.nsdh .mono{color:var(--muted-fg);font-size:12.5px;word-break:break-all;flex:1;min-width:0}
.nsdh .tag{font-size:11.5px;font-weight:600;padding:1px 8px;border-radius:6px;border:1px solid var(--border)}
.nsd.good .tag{color:var(--emerald);border-color:rgba(52,211,153,.4)}
.nsd.bad .tag{color:var(--red);border-color:rgba(248,113,113,.45)}
.nst{display:flex;gap:8px;font-size:13px;line-height:1.6;padding:2px 0}
.nst .ni{flex:none}.nst .ni svg{width:15px;height:15px;margin-top:3px}
.nst.ok .ni{color:var(--emerald)}.nst.ng .ni{color:var(--red)}.nst.na .ni{color:var(--dim)}
.nst .nh{color:var(--amber);font-size:12.5px}
.nst .nr{color:var(--dim);font-size:11.5px;word-break:break-all}
.nscred{display:flex;gap:8px;align-items:center;flex-wrap:wrap;margin-top:8px;padding-top:8px;border-top:1px dashed var(--border);font-size:13px}
.nscred input{width:150px}
.nsrow{display:flex;gap:8px;align-items:center;flex-wrap:wrap;min-width:0}
.nsrow input[type=text]{flex:1;min-width:120px}
.nschg{margin-top:14px;border:1px solid var(--border);border-radius:10px;padding:10px 14px;font-size:13px;background:var(--card)}
.nschg summary{cursor:pointer;font-weight:600}
.nschg ul{margin:8px 0 0;padding-left:20px;line-height:1.75;color:var(--muted-fg)}
.nschg b{color:var(--foreground)}
.nsagree{margin-top:12px;font-size:13.5px}
.nsbtns{display:flex;gap:10px;align-items:center;margin-top:12px;flex-wrap:wrap}
.nsjob{margin-top:14px;border-top:1px solid var(--border);padding-top:12px}
.netdlg h3 button.sm{height:26px;padding:0 10px;font-size:12px;margin-left:8px;vertical-align:middle}
.netdlg .dim{color:var(--dim)}
table.files button.oo{height:24px;padding:0 8px;font-size:12px}
#nsForm .no{display:none}#nsForm.noshare .so{display:none}#nsForm.noshare span.no{display:inline}
#nsForm.noshare ul.no{display:block}
#bNet.has{position:relative}
#bNet.has::after{content:"";position:absolute;top:5px;right:5px;width:7px;height:7px;border-radius:50%;background:var(--amber)}
'''

OP_JS = r'''
/* ===================== PADDOCK GATE（会場の発表PC）===================== */
/* 通知・音・自動表示・テスト通知は使わない（スライドショーの邪魔をしないため） */
FOLLOW=false;
(()=>{const s=$("#swFollow");if(s)s.closest("label").style.display="none";const t=$("#bTest");if(t)t.style.display="none"})();
const opReady=()=>!!(S&&S.op&&S.op.enabled);
renderBanner=function(){const b=$("#banner");let h="",cls="";
  if(!S.roots.length||!opReady())h=`このPCで見る会場と、データのコピー先がまだ設定されていません。<button class="pri" onclick="openCfg()">設定を開く</button> <button class="ghost" onclick="netOpen()">ネットワーク共有</button>`;
  const off=S.roots.filter(r=>r.enabled&&r.online===false);
  const offd=opDests().filter(d=>d.online===false);
  if(offd.length){h=offd.map(d=>`コピー先「${esc(d.label)}」に接続できません（つながったら自動でコピーします）`).join("　")+` <button class="pri" onclick="netOpen()">原因を調べる</button>`+(h?"<br>"+h:"");cls="warn"}
  if(off.length){h=off.map(r=>`${esc(nfc(r.label))}: ${esc(r.error)}`).join("　")+(h?"<br>"+h:"");cls="bad"}
  b.innerHTML=h?(cls?IC.alert:IC.info)+`<span style="flex:1">${h}</span>`:"";b.className=cls;b.style.display=h?"flex":"none"};
/* はじめて起動したとき（まだ設定していないとき）は、設定を開く */
let OPSETUP_SHOWN=false;
const _opRA=renderAll;renderAll=function(){_opRA();
  if(!OPSETUP_SHOWN&&S&&S.local&&!opReady()&&!$("#modal").classList.contains("open")){OPSETUP_SHOWN=true;openCfg()}};
const _opRC=renderCfg;renderCfg=function(){_opRC();
  const dlg=$("#modal .dlg");if(!dlg||opReady())return;
  const d=document.createElement("div");d.className="opsetup";
  d.innerHTML=`<b>はじめに設定してください</b><ol><li>「監視フォルダ」に、NASの学会名フォルダを追加（［参照…］→［追加］）</li><li>「このPCの会場とコピー先」で、自分の会場を選ぶ</li><li>コピー先（この発表PCのフォルダ、バックアップPCの共有フォルダ）を入れて［保存］</li></ol>
    <div class="alt">このPCが<b>バックアップPC（コピーされる側）</b>なら、ここの設定は不要です。<button class="ghost" onclick="closeCfg();netOpen()">ネットワーク共有</button> で［このPCを設定する］だけ押してください。</div>`;
  const h=dlg.querySelector("h3");if(h)dlg.insertBefore(d,h)};
/* 設定画面のコピー先の下に「接続を確認・共有を設定」 */
const _opRC2=renderCfg;renderCfg=function(){_opRC2();
  const dl=$("#dlist");if(!dl||$("#bNetCfg"))return;
  const p=document.createElement("p");p.className="hint";
  p.innerHTML=`<button class="ghost" id="bNetCfg">${IC.hd}接続を確認・共有を設定…</button>　バックアップPCにつながらないときは、ここからファイル共有をまとめて設定できます（保存してから確認してください）`;
  dl.parentNode.insertBefore(p,dl.nextSibling);$("#bNetCfg").onclick=()=>netOpen()};

/* ===================== メインPC⇄バックアップPCのネットワーク共有（接続の確認・ワンボタン設定）===================== */
const NET={info:null,chk:null,busy:false,form:null,job:null,timer:0,undoArm:0,cred:{}};
(()=>{const b=document.createElement("button");b.id="bNet";b.className="ghost";b.innerHTML=IC.hd+"ネットワーク共有";
  b.title="コピー先（バックアップPCなど）への接続を確認し、ファイル共有をまとめて設定します";b.onclick=()=>netOpen();
  const c=$("#bCfg");if(c)c.parentNode.insertBefore(b,c)})();
function netOpen(){let ov=$("#netov");
  if(!ov){ov=document.createElement("div");ov.id="netov";ov.addEventListener("mousedown",e=>{if(e.target===ov)netClose()});document.body.appendChild(ov)}
  ov.classList.add("open");NET.form=null;NET.chk=null;netRender();
  netLoad().then(()=>netCheck())}
function netClose(){const ov=$("#netov");if(ov)ov.classList.remove("open")}
document.addEventListener("keydown",e=>{const ov=$("#netov");if(e.key==="Escape"&&ov&&ov.classList.contains("open")){e.stopImmediatePropagation();e.preventDefault();netClose()}},true);
function netBadge(){const b=$("#bNet");if(!b||!NET.info)return;const I=NET.info,R=I.record,has=!!(R||(I.creds||[]).length||(I.links||[]).length);b.classList.toggle("has",has);
  b.title=has?`このPCには共有の設定（${R&&R.unc?R.unc+"・":""}接続情報・ショートカット）が残っています。イベントが終わったら、ここから［元に戻す］を押してください`:"コピー先（バックアップPCなど）への接続を確認し、ファイル共有をまとめて設定します"}
setTimeout(()=>{if(!NET.info)api("/api/op/net").then(j=>{if(!NET.info){NET.info=j;netBadge()}}).catch(()=>{})},4000);
async function netLoad(){try{NET.info=await api("/api/op/net");netBadge();if(NET.info.job&&!NET.job)NET.job=NET.info.job;if(NET.job&&NET.job.state==="running")netPoll()}
  catch(e){NET.info={error:e.message}}netRender()}
async function netCheck(){if(NET.busy)return;NET.busy=true;netRender();
  try{NET.chk=await api("/api/op/net/check",{})}catch(e){NET.chk={error:e.message}}NET.busy=false;netRender()}
function netKeep(){const g=id=>{const e=$("#"+id);return e?(e.type==="checkbox"?e.checked:e.value):undefined};
  if($("#nsFolder")&&$("#nsFolder").dataset.ready==="1")NET.form={folder:g("nsFolder"),share:g("nsShare"),user:g("nsUser"),password:g("nsPass"),peers:g("nsPeers"),nosleep:g("nsSleep"),set_password:g("nsSetPw"),wifi:g("nsWifi"),restrict:g("nsRestrict"),agree:g("nsAgree"),
    share_this:(($("input[name=nsMode]:checked")||{}).value!=="0")};
  document.querySelectorAll("#netov [data-credhost]").forEach(e=>{NET.cred[e.dataset.credhost]={user:e.querySelector(".cu").value,password:e.querySelector(".cp2").value}})}
function netStep(s){const k=s.ok===true?"ok":s.ok===false?"ng":"na";
  return `<div class="nst ${k}"><span class="ni">${k==="ok"?IC.chk:k==="ng"?IC.x:IC.info}</span><div><div>${s.label?`<b>${esc(s.label)}</b>　`:""}${esc(s.msg||"")}</div>${s.hint?`<div class="nh">→ ${esc(s.hint)}</div>`:""}${s.raw&&s.raw!==s.msg?`<div class="nr mono">${esc(s.raw)}</div>`:""}</div></div>`}
function netRender(){const ov=$("#netov");if(!ov||!ov.classList.contains("open"))return;netKeep();
  const I=NET.info||{},D=I.defaults||{},F=NET.form||Object.assign({agree:false},D),R=I.record,job=NET.job,running=!!(job&&job.state==="running");
  const hasUndo=!!(R||(I.creds||[]).length||(I.links||[]).length);
  let h=`<div class="dlg netdlg"><div style="display:flex;gap:12px;align-items:flex-start"><div style="flex:1"><h2>ネットワーク共有（メインPC・バックアップPC・タイトルPC など）</h2>
    <p class="desc">コピー先（バックアップPCなど）につながるかを調べます。つながらないときは、ファイル共有に必要な設定をまとめて行えます。</p></div><button class="ghost" id="nsClose">${IC.x}閉じる</button></div>`;
  if(I.error)h+=`<p class="err">${esc(I.error)}</p>`;
  const ip0=(I.ips||[])[0];
  h+=`<div class="nsme"><div><span class="k">このPCの名前</span><b class="mono">${esc(I.computer||"…")}</b></div>
    <div><span class="k">IPアドレス</span><span class="mono">${esc((I.ips||[]).join("　")||"—")}</span></div>
    ${R&&R.unc?`<div><span class="k">このPCの共有</span><b class="mono">${esc(R.unc)}</b>（${esc(R.path)}）<br><span class="k"></span><span class="dim">ほかのPCのコピー先にはこのパス（の中のフォルダ）を指定します${ip0?`。名前で見つからないときは <span class="mono">\\\\${esc(ip0)}\\${esc(R.share)}</span>`:""}</span></div>`
      :`<div><span class="k">このPCの共有</span><span class="dim">まだ設定していません</span></div>`}</div>`;
  h+=`<h3>① コピー先への接続<button class="ghost sm" id="nsRe" ${NET.busy?"disabled":""}>${NET.busy?"確認中…":"もう一度確認"}</button></h3>`;
  const C=NET.chk;
  if(!C)h+=`<p class="hint">${NET.busy?"確認しています…（つながらない場合は1分ほどかかることがあります）":"—"}</p>`;
  else if(C.error)h+=`<p class="err">${esc(C.error)}</p>`;
  else if(!C.dests.length)h+=`<p class="hint" style="margin-top:0">コピー先がまだ設定されていません（［設定］→「このPCの会場とコピー先」）。<br>このPCが<b>バックアップPC（コピーされる側）</b>なら、下の ② で［このPCを設定する］を押すだけでOKです。</p>`;
  else for(const d of C.dests){const bad=d.steps.find(s=>s.ok===false);const need=bad&&bad.need==="cred"&&d.host;const skip=!bad&&d.steps.some(s=>s.k==="nas");
    h+=`<div class="nsd ${bad?"bad":skip?"":"good"}"><div class="nsdh"><b>${esc(d.label)}</b><span class="mono">${esc(d.path)}</span><span class="tag">${bad?"つながりません":skip?"確認しません":"OK"}</span></div>${d.steps.map(netStep).join("")}`;
    if(need){const c=NET.cred[d.host]||{user:D.user||"share",password:D.password||"share"};
      h+=`<div class="nscred" data-credhost="${esc(d.host)}"><span>「${esc(d.host)}」のアカウント</span><input type="text" class="cu" value="${esc(c.user)}" placeholder="ユーザー名" spellcheck="false"><input type="text" class="cp2" value="${esc(c.password)}" placeholder="パスワード" spellcheck="false"><button class="pri" data-cred="${esc(d.host)}" ${I.supported?"":"disabled"}>このPCに登録して確認</button></div>`}
    h+=`</div>`}
  const shareOn=F.share_this!==false;
  h+=`<h3>② ファイル共有の設定（ワンボタン）</h3>`;
  if(!I.supported)h+=`<p class="err" style="margin-top:0">この機能は Windows だけで使えます。</p>`;
  h+=`<div id="nsForm" class="${shareOn?"":"noshare"}">
   <div class="checks" style="flex-direction:column;gap:8px;margin:0 0 4px">
    <label><input type="radio" name="nsMode" value="1" ${shareOn?"checked":""}><span><b>このPCのフォルダを共有する</b>（メインPC・バックアップPCなど、コピーされるPC。それぞれで1回）</span></label>
    <label><input type="radio" name="nsMode" value="0" ${shareOn?"":"checked"}><span><b>このPCは共有しない</b>（タイトルPCなど、ほかのPCを開くだけ。管理者の確認は出ません）</span></label>
   </div>
   <div class="grid2" style="margin-top:12px">
    <span class="so">共有するフォルダ</span><span class="nsrow so"><input type="text" id="nsFolder" class="mono" value="${esc(F.folder||"")}" data-ready="${I.defaults?1:0}" spellcheck="false"><button class="ghost" id="nsPick">参照…</button></span>
    <span><span class="so">共有名</span><span class="no">相手の共有名</span></span><span class="nsrow"><input type="text" id="nsShare" value="${esc(F.share||"")}" style="max-width:220px" spellcheck="false"><span class="dim so">→ ほかのPCからは <b class="mono" id="nsUnc"></b>（共有名はどのPCでも同じにします）</span></span>
    <span>共有用アカウント</span><span class="nsrow"><input type="text" id="nsUser" value="${esc(F.user||"")}" style="max-width:150px" spellcheck="false"><span>パスワード</span><input type="text" id="nsPass" value="${esc(F.password||"")}" style="max-width:150px" spellcheck="false"><span class="dim">どのPCでも同じにする</span></span>
    <span>開く相手のPC</span><span class="nsrow"><input type="text" id="nsPeers" class="mono" value="${esc(F.peers||"")}" placeholder="例: MAIN-PC, BACKUP-PC（名前かIPアドレス。複数はカンマ区切り）" spellcheck="false"></span>
    <span></span><span class="hint" style="margin:0">入れたPCの接続情報をこのPCに登録し、<b>デスクトップにショートカット</b>「（PC名） の${esc(F.share||"共有名")}」を作ります。コピーしているPCが落ちたときなどに、手で開いてコピーできます。<span class="so">空欄でも共有の設定はできます。</span></span>
   </div>
   <div class="checks so" style="flex-direction:column;gap:8px;margin-top:12px">
    <label><input type="checkbox" id="nsSleep" ${F.nosleep!==false?"checked":""}>電源につないでいる間は、このPCをスリープさせない（スリープ中は相手のPCから使えないため）</label>
    <label><input type="checkbox" id="nsSetPw" ${F.set_password?"checked":""}>同じ名前のアカウントがすでにあるときは、パスワードを上の内容に変える（管理者・ログイン中のアカウントは使えません）</label>
    <label><input type="checkbox" id="nsRestrict" ${F.restrict?"checked":""}>このPCに入れるのを、上の「開く相手のPC」からだけに限る（IPアドレスが変わるとつながらなくなります。タイトルPCなど、このPCを開くPCも全部入れてください）</label>
    <label><input type="checkbox" id="nsWifi" ${F.wifi?"checked":""}>Wi-Fi でも共有する（おすすめしません。ふつうは有線LANだけ。会場のWi-Fiにつないでいる人からも見えてしまうため）</label>
   </div>
   <p class="hint so" style="margin:8px 0 0">パスワードの既定（share）は、閉じた現場LAN向けです。ほかの人もつなぐネットワークでは、すべてのPCで別のパスワードにしてください。</p>
   <details class="nschg" open><summary>このPCで変更する内容</summary><ul class="so">
    <li>Windowsファイアウォールに、<b>有線LANの、同じネットワーク内のPCからだけ</b>（「相手のPCからだけ」にチェックしたときは、そのPCからだけ）、ファイル共有（SMB）・PC名の検索・ping を許可する規則を追加する（グループ名「SW NAS OPERATOR」。ネットワークの種類「パブリック／プライベート」は変えません）</li>
    <li>ファイル共有のサービス（Server・Workstation など）を自動で起動するようにする</li>
    <li>共有用アカウントを作る（管理者ではない普通のアカウント。30日で使えなくなります（もう一度押すと延びる）。すでにあればそのまま使う。ログイン画面にも表示されます）</li>
    <li>上のフォルダを作って共有し、そのアカウントに読み書き（変更）の権限を付ける</li>
    <li>スリープさせない（チェックしたとき。電源接続時だけ）</li>
    <li>開く相手のPCの接続情報を、このPCのWindowsの資格情報に登録し、デスクトップにショートカットを作る（上の設定がすべてうまくいったとき。NASのサーバーには登録しません）</li>
   </ul><ul class="no">
    <li>開く相手のPCの接続情報を、このPCのWindowsの資格情報に登録する（NASのサーバーには登録しません）</li>
    <li>デスクトップに、相手のPCの共有フォルダへのショートカットを作る</li>
    <li>このPCの共有・ファイアウォール・アカウントなどは変えません</li>
   </ul><p class="hint" style="margin:6px 0 0">［元に戻す］で戻せます（作ったショートカット・登録した接続情報も消します。フォルダとデータは消しません。レンタルPCは返す前に押してください）。<span class="so">変更前の状態は変更のたびに記録します。SMB1・パスワードなしの共有（ゲスト）は使いません。経過は、管理者の確認のあとに開くウィンドウにも表示されます。</span></p></details>
   <label class="lbl nsagree"><input type="checkbox" id="nsAgree" ${F.agree?"checked":""}>上の内容で、このPCの設定を変更する</label>
   <div class="nsbtns"><button class="pri" id="nsRun"></button>
   ${hasUndo?`<button class="ghost danger" id="nsUndo">${running&&job.action==="undo"?"元に戻しています…":NET.undoArm>Date.now()?"もう一度押すと元に戻します":"元に戻す"}</button>`:""}
   ${R&&R.updated?`<span class="dim">前回の設定: ${esc(String(R.updated).replace("T"," "))}</span>`:""}</div></div>`;
  if(job){const fin=job.state==="done";
    h+=`<div class="nsjob">${job.msg?`<p class="${job.state==="error"||job.state==="canceled"?"err":"hint"}" style="margin-top:0">${esc(job.msg)}</p>`:""}${(job.steps||[]).map(netStep).join("")}
      ${fin?`<p class="hint">${job.ok?"✓ 終わりました。":"一部うまくいきませんでした（✕の項目を確認してください）。"}${job.action==="setup"&&job.elevate?"ほかのPCでも同じように押してから、① の［もう一度確認］でつながるか確かめてください。":""}</p>`:""}</div>`}
  h+=`</div>`;
  ov.innerHTML=h;
  const unc=()=>{const e=$("#nsUnc");if(e)e.textContent="\\\\"+(I.computer||"このPC")+"\\"+($("#nsShare").value.trim()||"共有名")};unc();
  const runBtn=$("#nsRun"),agr=$("#nsAgree"),form=$("#nsForm");
  const mode=()=>{const on=($("input[name=nsMode]:checked")||{}).value!=="0";form.classList.toggle("noshare",!on);
    runBtn.textContent=running&&job.action==="setup"?"実行中…":on?"このPCを設定する（管理者の確認が出ます）":"接続情報とショートカットを作る"};mode();
  const upd=()=>{runBtn.disabled=!I.supported||running||!agr.checked;const u=$("#nsUndo");if(u)u.disabled=!I.supported||running};upd();
  ov.querySelectorAll("input[name=nsMode]").forEach(r=>r.onchange=mode);
  agr.onchange=upd;$("#nsShare").oninput=unc;
  $("#nsClose").onclick=netClose;$("#nsRe").onclick=netCheck;
  $("#nsPick").onclick=async()=>{try{const j=await api("/api/pick",{dest:true});if(j.path)$("#nsFolder").value=j.path}catch(e){toast(e.message,5000)}};
  ov.querySelectorAll("[data-cred]").forEach(b=>b.onclick=async()=>{const box=b.closest("[data-credhost]");b.disabled=true;
    try{const j=await api("/api/op/net/cred",{host:b.dataset.cred,user:box.querySelector(".cu").value,password:box.querySelector(".cp2").value});
      toast((j.targets.length?"接続情報を登録しました: "+j.targets.join("・"):"")+(j.errors.length?"　登録できませんでした: "+j.errors.join("・"):"")+(j.skipped&&j.skipped.length?"　"+j.skipped.join("・")+" はほかで登録した接続情報があるため変えていません（Windowsの資格情報マネージャーで確認してください）":""),9000)}
    catch(e){toast(e.message,6000)}NET.busy=false;netCheck()});
  runBtn.onclick=async()=>{netKeep();const f=NET.form;
    try{const j=await api("/api/op/net/setup",{share_this:f.share_this,folder:f.folder,share:f.share,user:f.user,password:f.password,peers:f.peers,
        nosleep:f.nosleep,set_password:f.set_password,wifi:f.wifi,restrict:f.restrict});
      NET.job=j.job;agr.checked=false;netRender();netPoll()}catch(e){toast(e.message,7000)}};
  const ub=$("#nsUndo");if(ub)ub.onclick=async()=>{if(NET.undoArm<Date.now()){NET.undoArm=Date.now()+5000;netRender();setTimeout(netRender,5100);return}
    NET.undoArm=0;try{const j=await api("/api/op/net/undo",{});NET.job=j.job;netRender();netPoll()}catch(e){toast(e.message,7000)}};
}
function netPoll(){clearTimeout(NET.timer);NET.timer=setTimeout(async()=>{
  try{const j=await api("/api/op/net/job");NET.job=j.job}catch(e){}
  if(NET.job&&NET.job.state==="running"){netRender();netPoll();return}
  await netLoad();if(NET.job&&NET.job.state==="done")setTimeout(netCheck,800)},1000)}
/* ===================== 演者のスライドを開く（このPCのコピーから。NASのファイルは開かない）===================== */
const OPEN={settings:{enabled:true,dest:"",dbl:"file",multi:"newest"},dest:null};
function openLoad(){return api("/api/op/open/settings").then(j=>{OPEN.settings=j.settings;OPEN.dest=j.dest}).catch(()=>{})}
openLoad();
async function opOpen(root,group,rel,how){
  if(!S||!S.local){toast("開くのは、このアプリを動かしているPCでのみできます",4000);return}
  try{const j=await api("/api/op/open",{root,group,rel:rel||"",how});
    toast((j.what==="folder"?"フォルダを開いています（"+j.dest+"）":j.what==="show"?"スライドショーで開いています: "+j.name+"（"+j.dest+"）":"開いています: "+j.name+"（"+j.dest+"）")+(j.msg?"\n"+j.msg:""),j.msg?7000:3000)}
  catch(e){toast(e.message,8000)}}
/* 演者をダブルクリック → 設定に合わせて、発表ファイル（またはフォルダ）をこのPCのコピーから開く */
openFolderOS=function(root,group){
  if(!OPEN.settings.enabled){toast("ダブルクリックで開くには、［設定］→「演者のスライドを開く」をオンにしてください",7000);return}
  opOpen(root,group,"",OPEN.settings.dbl==="folder"?"folder":OPEN.settings.dbl)};
/* 設定画面に「演者のスライドを開く」 */
const _opRC3=renderCfg;renderCfg=function(){_opRC3();
  if($("#opOpenSet"))return;const dlg=$("#modal .dlg");if(!dlg)return;
  const h3=[...dlg.querySelectorAll("h3")].find(x=>x.textContent.trim()==="検出");if(!h3)return;
  const st=OPEN.settings,ds=((CFG&&CFG.op&&CFG.op.dests)||[]).filter(d=>d.id&&String(d.path||"").trim());
  const d=document.createElement("div");d.id="opOpenSet";
  d.innerHTML=`<h3>演者のスライドを開く</h3>
   <p style="margin:0"><label class="lbl"><input type="checkbox" id="ooOn" ${st.enabled?"checked":""}>演者をダブルクリック・フォルダ画面の［開く］で、発表ファイルを開けるようにする</label></p>
   <div class="grid2" style="margin-top:10px">
    <span>開くコピー</span><span><select id="ooDest"><option value="">自動（このPCのフォルダのコピー先）</option>${ds.map(x=>`<option value="${esc(x.id)}" ${x.id===st.dest?"selected":""}>${esc(x.label)}（${esc(x.path)}）</option>`).join("")}</select></span>
    <span>ダブルクリックしたとき</span><span class="checks" style="flex-direction:column;gap:6px;align-items:flex-start">
     <label><input type="radio" name="ooDbl" value="file" ${st.dbl==="file"?"checked":""}>発表ファイルを開く（PowerPoint など）</label>
     <label><input type="radio" name="ooDbl" value="show" ${st.dbl==="show"?"checked":""}>発表ファイルをスライドショーで開く（PowerPoint のとき）</label>
     <label><input type="radio" name="ooDbl" value="folder" ${st.dbl==="folder"?"checked":""}>演者フォルダを開く（Explorer）</label></span>
    <span>発表ファイルが2つ以上あるとき</span><span class="checks" style="flex-direction:column;gap:6px;align-items:flex-start">
     <label><input type="radio" name="ooMulti" value="newest" ${st.multi!=="folder"?"checked":""}>後から入ったほうを開く（差し替え版が後から届いたとき用。どちらか決められないときはフォルダ）</label>
     <label><input type="radio" name="ooMulti" value="folder" ${st.multi==="folder"?"checked":""}>フォルダを開く（どれを使うか目で選ぶ）</label></span>
   </div>
   <p class="hint">開くのは、<b>このPCのコピー先にコピーが終わったファイル</b>です。NAS上のファイルは開きません（会場側の作業や、受付での差し替えに影響を出さないため）。コピー中・コピー待ちのときは開かずに知らせます。<br>コピー先を追加・変更したときは、［保存］してからもう一度開くと「開くコピー」に出ます。</p>`;
  dlg.insertBefore(d,h3)};
const _opSC=saveCfg;saveCfg=async function(){
  if($("#ooOn")){try{const j=await api("/api/op/open/settings",{enabled:$("#ooOn").checked,dest:$("#ooDest").value,
      dbl:(document.querySelector("input[name=ooDbl]:checked")||{}).value||"file",
      multi:(document.querySelector("input[name=ooMulti]:checked")||{}).value||"newest"});OPEN.settings=j.settings;OPEN.dest=j.dest}
    catch(e){const c=$("#cerr");if(c)c.textContent=e.message;else toast(e.message,5000);return}}
  const r=await _opSC();openLoad().then(()=>{if(F)renderFolder()});return r};
/* フォルダ画面：［このPCのコピーを開く］と、ファイルごとの［開く］［スライドショー］ */
const _opRF=renderFolder;renderFolder=function(){_opRF();
  const fe=foldEl();if(!fe||!F||!F.group||!OPEN.settings.enabled||!F.op)return;
  const dest=OPEN.dest,did=dest&&dest.id;if(!did)return;
  const acts=fe.querySelector(".fh .acts");
  if(acts&&!acts.querySelector("[data-oo]")){const b=document.createElement("button");b.dataset.oo="folder";b.className="pri";
    b.innerHTML=IC.folder+"フォルダを開く（"+esc(dest.label)+"）";b.title="この演者のフォルダを、このPCのコピー（"+dest.label+"）から Explorer で開きます";
    b.onclick=()=>opOpen(F.root,F.group,"","folder");acts.insertBefore(b,acts.firstChild)}
  const tb=fe.querySelector("table.files");if(!tb||tb.dataset.oo)return;tb.dataset.oo="1";
  const hr=tb.querySelector("thead tr");if(hr){const th=document.createElement("th");th.textContent="開く（"+dest.label+"）";hr.appendChild(th)}
  const rows=F.items.map(i=>Object.assign({k:sortKey(i.p,i.d)},i)).sort((a,b)=>cmpKeys(a.k,b.k));
  const trs=[...tb.querySelectorAll("tbody tr")];if(trs.length!==rows.length)return;
  rows.forEach((it,ix)=>{const td=document.createElement("td");td.style.whiteSpace="nowrap";
    if(!it.d&&!it.mk){const st=it.cp&&it.cp[did]?it.cp[did][0]:"";const ok=st==="ok"||st==="edited";
      const ext=(it.p.match(/\.[^.\/]+$/)||[""])[0].toLowerCase();const show=[".pptx",".ppsx",".pptm",".ppsm",".ppt",".pps"].includes(ext);
      const why=ok?"":"（"+((CPL[st]||["コピー待ち"])[0])+"。コピーが終わると開けます）";
      td.innerHTML=`<button class="ghost oo" data-oo="file" ${ok?"":"disabled"} title="このPCのコピーを開く${esc(why)}">開く</button>${show?` <button class="ghost oo" data-oo="show" ${ok?"":"disabled"} title="スライドショーで開く${esc(why)}">スライドショー</button>`:""}`;
      td.querySelectorAll("button").forEach(b=>b.onclick=e=>{e.stopPropagation();opOpen(F.root,F.group,it.p,b.dataset.oo)});
      const pr=F.op.pres;if(pr&&pr.newest===it.p){const nm=trs[ix].querySelector("td.nm");if(nm)nm.insertAdjacentHTML("beforeend",` <span class="tag t-info" title="発表ファイルが${pr.n}個あります。これがいちばん後からNASに入ったものです${OPEN.settings.multi!=="folder"?"（ダブルクリックで開くのはこれ）":""}">後から入った</span>`)}}
    trs[ix].appendChild(td)})};
'''

if __name__ == "__main__":
    main()
