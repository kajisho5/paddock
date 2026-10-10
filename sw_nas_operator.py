#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
SW NAS OPERATOR  v1.0.0  —  SEVENTHWELL

学会の各会場の発表PC（オペレーターPC）用。自分の会場の演者フォルダをNASから読み、NASへの受信が完了したものを
この発表PC・バックアップPCなどのコピー先へコピーする。NASには一切書き込まない（読むだけ）。
一覧・会場ボード・PowerPoint解析・目印の表示は SW NAS WATCH をそのまま使う（sw_nas_watch を部品として読み込む）。
スライドショーをしているPCで使うので、通知も音も出さない。

起動:
  python sw_nas_operator.py
  python sw_nas_operator.py --port 8797
"""
import argparse
import json
import os
import secrets
import shutil
import sys
import threading
from urllib.parse import urlparse
from urllib.request import urlopen

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # 同梱Pythonでも隣の sw_nas_watch を読めるように
import sw_nas_watch as W  # noqa: E402

APP_NAME = "SW NAS OPERATOR"
VERSION = "1.0.0"
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
    """SW NAS WATCH の保存先（会場オペレーターモードの設定の引き継ぎ元）の候補。"""
    home = os.path.abspath(os.environ.get("SW_NAS_OPERATOR_HOME", "") or os.path.dirname(os.path.abspath(__file__)))
    cands = [os.path.join(home, "sw_nas_watch_data")]
    # ZIPを同じ場所に展開した場合：…\SW_NAS_WATCH\sw_nas_watch_data
    # Windowsの「すべて展開」で1段深くなった場合：…\SW_NAS_WATCH_v1.12.0_Windows\SW_NAS_WATCH\sw_nas_watch_data
    par = os.path.dirname(home)
    for base in (par, os.path.dirname(par)):
        if not base or W.is_remote_path(base):
            continue
        try:
            names = sorted(e.name for e in os.scandir(base) if e.name.upper().startswith("SW_NAS_WATCH") and e.is_dir())
        except OSError:
            continue
        for n in names[:20]:
            cands.append(os.path.join(base, n, "sw_nas_watch_data"))
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
    """初回起動時：SW NAS WATCH で会場オペレーターモードを使っていたら、その設定と「コピー済み」の記録を引き継ぐ。
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


def build_page():
    h = W.HTML

    def sub(old, new):
        nonlocal h
        if h.count(old) != 1:
            raise RuntimeError("画面の組み立てに失敗しました: %r" % old[:40])
        h = h.replace(old, new)
    sub("<title>SW NAS WATCH</title>", "<title>SW NAS OPERATOR</title>")
    sub('+"SW NAS WATCH";if(ret)return t;', '+"SW NAS OPERATOR";if(ret)return t;')
    sub("SW NAS WATCH<small>SEVENTHWELL · READ ONLY</small>", "SW NAS OPERATOR<small>SEVENTHWELL · 会場</small>")
    sub("SW NAS WATCH v__VERSION__ · © SEVENTHWELL",
        "SW NAS OPERATOR v%s（SW NAS WATCH v__VERSION__ ベース） · © SEVENTHWELL" % VERSION)
    sub("</style>\n</head>", OP_CSS + "\n</style>\n</head>")
    sub("</script>\n</body>", OP_JS + "\n</script>\n</body>")
    return h


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
        return super().do_GET()


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
    a = ap.parse_args()
    W.disable_quick_edit()

    data_dir = a.data_dir or pick_data_dir()
    os.makedirs(data_dir, exist_ok=True)
    store = W.LocalStore(data_dir)
    raw = store.read_json("config.json", None)
    imported = None
    if raw is None:
        raw, src, n = import_from_watch(data_dir)
        if raw is not None:
            imported = "SW NAS WATCH の会場オペレーターモードの設定を引き継ぎました（%s、コピーの記録 %d件）" % (src, n)
    cfg, cfg_msg = W.startup_config(store, data_dir, raw)
    if cfg_msg:
        print(cfg_msg)
    force_quiet(cfg)
    try:
        cfg = W.validate_cfg(cfg, data_dir)
    except ValueError as e:
        raise SystemExit(str(e))

    url = "http://127.0.0.1:%d/" % a.port
    if not W.port_free("127.0.0.1", a.port):
        try:
            with urlopen(url + "api/ping", timeout=2) as r:
                if json.loads(r.read().decode("utf-8")).get("app") == APP_NAME:
                    print("%s はすでに起動しています。画面を開きます: %s" % (APP_NAME, url))
                    if not a.no_browser:
                        W.open_ui(url, data_dir, a.browser)
                    return
        except Exception:
            pass
        raise SystemExit("ポート %d が使用中です。--port で別の番号を指定してください" % a.port)
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
    mgr.start()

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
    print(" このウィンドウを閉じるとコピーが止まります（Ctrl+C で終了）")
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


# ---------------------------------------------------------------- UI（SW NAS WATCH の画面に足す部分）
OP_CSS = r'''
/* ===== SW NAS OPERATOR ===== */
.opsetup{border:1px solid rgba(139,92,246,.45);background:rgba(139,92,246,.08);border-radius:12px;padding:12px 14px;margin:0 0 14px;font-size:13px;line-height:1.7}
.opsetup b{color:var(--foreground)}
.opsetup ol{margin:4px 0 0;padding-left:20px}
'''

OP_JS = r'''
/* ===================== SW NAS OPERATOR（会場の発表PC）===================== */
/* 通知・音・自動表示・テスト通知は使わない（スライドショーの邪魔をしないため） */
FOLLOW=false;
(()=>{const s=$("#swFollow");if(s)s.closest("label").style.display="none";const t=$("#bTest");if(t)t.style.display="none"})();
const opReady=()=>!!(S&&S.op&&S.op.enabled);
renderBanner=function(){const b=$("#banner");let h="",cls="";
  if(!S.roots.length||!opReady())h=`このPCで見る会場と、データのコピー先がまだ設定されていません。<button class="pri" onclick="openCfg()">設定を開く</button>`;
  const off=S.roots.filter(r=>r.enabled&&r.online===false);
  const offd=opDests().filter(d=>d.online===false);
  if(offd.length){h=offd.map(d=>`⚠ コピー先「${esc(d.label)}」に接続できません（つながったら自動でコピーします）`).join("　")+(h?"<br>"+h:"");cls="warn"}
  if(off.length){h=off.map(r=>`⚠ ${esc(nfc(r.label))}: ${esc(r.error)}`).join("　")+(h?"<br>"+h:"");cls="bad"}
  b.innerHTML=h?(cls?IC.alert:IC.info)+`<span style="flex:1">${h}</span>`:"";b.className=cls;b.style.display=h?"flex":"none"};
/* はじめて起動したとき（まだ設定していないとき）は、設定を開く */
let OPSETUP_SHOWN=false;
const _opRA=renderAll;renderAll=function(){_opRA();
  if(!OPSETUP_SHOWN&&S&&S.local&&!opReady()&&!$("#modal").classList.contains("open")){OPSETUP_SHOWN=true;openCfg()}};
const _opRC=renderCfg;renderCfg=function(){_opRC();
  const dlg=$("#modal .dlg");if(!dlg||opReady())return;
  const d=document.createElement("div");d.className="opsetup";
  d.innerHTML=`<b>はじめに設定してください</b><ol><li>「監視フォルダ」に、NASの学会名フォルダを追加（［参照…］→［追加］）</li><li>「このPCの会場とコピー先」で、自分の会場を選ぶ</li><li>コピー先（この発表PCのフォルダ、バックアップPCの共有フォルダ）を入れて［保存］</li></ol>`;
  const h=dlg.querySelector("h3");if(h)dlg.insertBefore(d,h)};
'''

if __name__ == "__main__":
    main()
