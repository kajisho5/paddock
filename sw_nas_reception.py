#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
SW NAS RECEPTION  v1.2.1  —  SEVENTHWELL

学会の受付PC用。演者のデータ（USB・ドラッグ＆ドロップ）を受け取り、NAS上の演者フォルダへ入れる。
監視・解析・一覧・会場ボードは SW NAS WATCH をそのまま使う（sw_nas_watch を部品として読み込む）。
SW NAS WATCH 本体には書き込みの処理は一切ない。NASへ書くのはこのアプリだけ。

受付の流れ
  1. 演者を選ぶ → ファイル・フォルダをドロップ／USBから取り込む
  2. いったんこの受付PCのトレイに受け取る（内容のハッシュを記録し、PowerPointを先に解析して注意点を出す）
  3. 「受付する」→ NASの演者フォルダへ書き込む

NASへの書き込みのルール
  ・書くのは「監視フォルダの中の演者フォルダ」の中だけ。演者フォルダを作るのはセッションフォルダの中だけ。
  ・NAS上のファイルを消すことはない（失敗したときに自分の一時ファイルを片付けるだけ）。
  ・一時ファイル（隠しファイル .swnr_～.part）に書き、読み直して内容（SHA-256）を照合してから、一瞬で置き換える。
  ・同じ名前のファイルが会場PCで開かれている（~$ の鍵ファイルがある／置き換えできない）ときは上書きしない。
  ・同じ内容のファイルがすでにあれば書き込まない。
  ・上書きする前の版は、この受付PCに保存してから置き換える（保存できなければ置き換えない）。
  ・受け取ったデータは、この受付PCにも残す（予備）。

起動:
  python sw_nas_reception.py
  python sw_nas_reception.py --root "\\192.168.0.10\share\学会名" --depth 3 --port 8795
"""
import argparse
import hashlib
import re
import json
import os
import secrets
import shutil
import socket
import string
import subprocess
import sys
import threading
import time
import unicodedata
from urllib.parse import parse_qs, urlparse

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # 同梱Pythonでも隣の sw_nas_watch を読めるように
import sw_nas_watch as W  # noqa: E402

APP_NAME = "SW NAS RECEPTION"
VERSION = "1.3.1"
DEFAULT_PORT = 8795
RX_TMP = ".swnr_"                      # NASへ書く途中の一時ファイル（SW NAS WATCH は常に無視する）
CHUNK = 1 << 20
JUNK = W.compile_ignore(W.DEFAULT_IGNORE)
BAD_CHARS = set('<>:"/\\|?*')
RESERVED = {"CON", "PRN", "AUX", "NUL"} | {"COM%d" % i for i in range(1, 10)} | {"LPT%d" % i for i in range(1, 10)}
PRES_EXTS = set(W.PPT_CAT_EXTS) | {"key", "pdf"}
DEFAULT_RX = {"verify": True, "keep_local": True, "pc_name": "", "flag_dir": "", "auto_recv": True}
MAX_FILES = 20000


# ---------------------------------------------------------------- helpers
def nfc(s):
    return unicodedata.normalize("NFC", str(s))


def safe_part(n):
    """Windows/NASで問題なく使えるフォルダ名・ファイル名か。"""
    if not n or n in (".", "..") or len(n) > 200 or n.endswith((" ", ".")):
        return False
    if any(c in BAD_CHARS or ord(c) < 32 for c in n):
        return False
    return n.split(".")[0].strip().upper() not in RESERVED


def clean_rel(rel):
    parts = [nfc(p) for p in str(rel).replace("\\", "/").split("/") if p != ""]
    if not parts or len(parts) > 16 or not all(safe_part(p) for p in parts):
        raise ValueError("使えない名前が含まれています: %s" % rel)
    return "/".join(parts)


def is_junk(rel):
    for p in rel.split("/"):
        if p.startswith(RX_TMP) or (JUNK is not None and JUNK.match(p.lower())):
            return True
    return False


def free_bytes(p):
    try:
        return shutil.disk_usage(p).free
    except OSError:
        return None


def sha256_of(path, opener=None):
    h = hashlib.sha256()
    n = 0
    with (opener or (lambda x: open(x, "rb")))(path) as f:
        while True:
            b = f.read(CHUNK)
            if not b:
                break
            h.update(b)
            n += len(b)
    return h.hexdigest(), n


def fmt_size(n):
    for u in ("B", "KB", "MB", "GB"):
        if n < 1024 or u == "GB":
            return ("%d %s" % (n, u)) if u == "B" else ("%.1f %s" % (n, u))
        n /= 1024.0


def is_busy_error(e):
    return getattr(e, "winerror", None) in (5, 32, 33) or isinstance(e, PermissionError)


def pick_data_dir():
    # exe をNAS上に置いて起動した場合は、NASに書かないようローカルのアプリ用フォルダへ保存する
    for d in W.data_dir_candidates("SW_NAS_RECEPTION_HOME", "sw_nas_reception_data", ".sw_nas_reception"):
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


# ---------------------------------------------------------------- tray（この受付PCでの一時受け取り）
class Tray:
    def __init__(self, base_dir, rid, group):
        self.rid, self.group = rid, group
        self.key = rid + "|" + group
        self.dir = os.path.join(base_dir, hashlib.sha1(self.key.encode("utf-8")).hexdigest()[:16])
        self.files = {}      # rel -> {"size", "sha", "src", "t"}
        self.ana = {}        # rel -> {"ver", "res"}
        self.ver = 0
        self.lock = threading.RLock()

    def path_of(self, rel):
        return W.long_path(os.path.join(self.dir, "files", *rel.split("/")))

    def find_ci(self, rel):
        """大文字小文字だけが違う同じ名前（Windowsでは同じファイルになる）がトレイにあれば、その名前を返す。"""
        cf = rel.casefold()
        return next((k for k in self.files if k != rel and k.casefold() == cf), None)

    def save(self):
        os.makedirs(self.dir, exist_ok=True)
        tmp = os.path.join(self.dir, "meta.json.tmp")
        with open(tmp, "wb") as f:
            f.write(W.json_bytes({"rid": self.rid, "group": self.group, "files": self.files}))
        os.replace(tmp, os.path.join(self.dir, "meta.json"))

    @classmethod
    def load(cls, base_dir, d):
        try:
            with open(os.path.join(base_dir, d, "meta.json"), encoding="utf-8") as f:
                m = json.load(f)
            t = cls(base_dir, str(m["rid"]), str(m["group"]))
            for rel, info in (m.get("files") or {}).items():
                if os.path.isfile(t.path_of(rel)):
                    t.files[rel] = info
            return t
        except (OSError, ValueError, KeyError, TypeError):
            return None


# ---------------------------------------------------------------- 受付の本体
class Rx:
    def __init__(self, mgr, data_dir, extra_drives=None):
        self.M = mgr
        self.data = data_dir
        self.stage = os.path.join(data_dir, "staging")
        self.recv_dir = os.path.join(data_dir, "received")
        self.bak_dir = os.path.join(data_dir, "backup")
        for d in (self.stage, self.recv_dir, self.bak_dir):
            os.makedirs(d, exist_ok=True)
        self.log_path = os.path.join(data_dir, "receipts.jsonl")
        self.set_path = os.path.join(data_dir, "rx.json")
        self.settings = dict(DEFAULT_RX)
        try:
            with open(self.set_path, encoding="utf-8") as f:
                raw = json.load(f)
            self.settings.update({k: raw[k] for k in DEFAULT_RX if k in raw})
        except (OSError, ValueError):
            pass
        if not self.settings.get("pc_name"):
            self.settings["pc_name"] = socket.gethostname()[:40]
        self.extra = [os.path.abspath(p) for p in (extra_drives or [])]
        self.trays = {}
        self.jobs = {}
        self.lock = threading.Lock()
        self.wlock = threading.Lock()      # NASへの書き込みは1件ずつ
        for d in sorted(os.listdir(self.stage)):
            t = Tray.load(self.stage, d)
            if t and t.files:
                self.trays[t.key] = t

    # ---- settings
    def save_settings(self, body):
        s = dict(self.settings)
        if "verify" in body:
            s["verify"] = bool(body["verify"])
        if "keep_local" in body:
            s["keep_local"] = bool(body["keep_local"])
        if "pc_name" in body:
            s["pc_name"] = str(body["pc_name"]).strip()[:40] or socket.gethostname()[:40]
        if "auto_recv" in body:
            s["auto_recv"] = bool(body["auto_recv"])
        if "flag_dir" in body:
            fd = str(body["flag_dir"] or "").strip().strip('"')
            if fd and fd != self.settings.get("flag_dir") and not os.path.isdir(W.long_path(fd)):
                raise ValueError("目印画像のフォルダが見つかりません: %s" % fd)
            s["flag_dir"] = fd
        self.settings = s
        tmp = self.set_path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(s, f, ensure_ascii=False)
        os.replace(tmp, self.set_path)
        return s

    # ---- NAS側の確認
    def presenter(self, rid, group, check=False):
        """演者フォルダの場所。check=True（NASへ書き込む前）は、NAS上に今あることを必ず確かめる
        （一覧が少し古いと、名前を変えた・消したフォルダを作り直してしまうため）。"""
        w = self.M.watchers.get(rid)
        if not w:
            raise KeyError("監視フォルダが見つかりません（設定を確認してください）")
        segs = group.split("/") if group else []
        # Windowsでは末尾の「.」「空白」が無視される（「...」が親フォルダを指してしまう等）ので、そういう名前は受け付けない
        if len(segs) != w.depth or any(x in ("", ".", "..") or x.strip(" .") == "" or x.endswith((" ", "."))
                                       or any(c in x for c in "\\/:") or any(ord(c) < 32 for c in x) for x in segs):
            raise ValueError("演者フォルダを選んでください")
        path = os.path.join(w.path, *segs)
        with w.lock:
            known = w.current.get(group) == W.DIR
        if (check or not known) and not os.path.isdir(W.long_path(path)):
            raise KeyError("演者フォルダがNAS上に見つかりません（削除・名前変更された可能性）")
        return w, path

    def nas_roots(self):
        return [r["path"] for r in self.M.cfg["roots"]]

    def tray(self, rid, group, create=False):
        key = rid + "|" + group
        with self.lock:
            t = self.trays.get(key)
            if t is None and create:
                t = self.trays[key] = Tray(self.stage, rid, group)
            return t

    def job_of(self, key):
        with self.lock:
            return self.jobs.get(key)

    def _busy(self, key):
        j = self.job_of(key)
        return bool(j and j["state"] == "run")

    def _drop_ci(self, t, rel):
        """大文字小文字だけが違う古い項目をトレイから外す（Windowsでは同じファイルなので、新しい方だけを残す）。"""
        old = t.find_ci(rel)
        if not old:
            return
        try:
            op, np_ = t.path_of(old), t.path_of(rel)
            if os.path.exists(op) and not (os.path.exists(np_) and os.path.samefile(op, np_)):
                os.remove(op)
        except OSError:
            pass
        t.files.pop(old, None)

    # ---- トレイへ受け取る（ブラウザから）
    def upload(self, rid, group, rel, length, rfile):
        def drain():
            left = length
            while left > 0:
                b = rfile.read(min(CHUNK, left))
                if not b:
                    break
                left -= len(b)
        try:
            self.presenter(rid, group)
            rel = clean_rel(rel)
        except (KeyError, ValueError):
            drain()
            raise
        if is_junk(rel):
            drain()
            return {"ok": True, "skipped": rel}
        t = self.tray(rid, group, True)
        if self._busy(t.key):
            drain()
            raise ValueError("NASへの書き込み・取り込みの途中です。終わってから追加してください")
        fr = free_bytes(self.stage)
        if fr is not None and fr < length + 300 * 1024 * 1024:
            drain()
            raise ValueError("この受付PCの空き容量が足りません（%s 必要）" % fmt_size(length))
        dst = t.path_of(rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        tmp = dst + ".part~"
        h = hashlib.sha256()
        n = 0
        try:
            with open(tmp, "wb") as f:
                left = length
                while left > 0:
                    b = rfile.read(min(CHUNK, left))
                    if not b:
                        break
                    f.write(b)
                    h.update(b)
                    n += len(b)
                    left -= len(b)
            if n != length:
                raise ValueError("受け取りが途中で切れました（%s / %s）" % (fmt_size(n), fmt_size(length)))
            os.replace(tmp, dst)
        finally:
            if os.path.exists(tmp):
                try:
                    os.remove(tmp)
                except OSError:
                    pass
        with t.lock:
            self._drop_ci(t, rel)
            t.files[rel] = {"size": n, "sha": h.hexdigest(), "src": "ドロップ", "t": time.time()}
            t.ver += 1
            t.save()
        return {"ok": True, "rel": rel, "size": n}

    # ---- トレイへ受け取る（USB・ドライブから）
    def start_import(self, rid, group, paths):
        self.presenter(rid, group)
        t = self.tray(rid, group, True)
        if self._busy(t.key):
            raise ValueError("NASへの書き込み・取り込みの途中です")
        items = []

        def is_link(x):     # シンボリックリンク・ジャンクションはたどらない（NASやこのアプリの保存先を指していることがある）
            try:
                return os.path.islink(x) or (hasattr(os.path, "isjunction") and os.path.isjunction(x))
            except OSError:
                return True
        roots = self.nas_roots()
        for p in paths or []:
            p = os.path.abspath(str(p))
            if not os.path.exists(p):
                raise ValueError("見つかりません: %s" % p)
            for nr in roots:
                if W.overlaps(p, nr):
                    raise ValueError("NASの監視フォルダの中からは取り込めません: %s" % p)
            if W.is_under(p, self.data) or W.is_under(self.data, p):
                raise ValueError("このアプリの保存先（またはそれを含むフォルダ）からは取り込めません")
            if is_link(p):
                raise ValueError("ショートカット（リンク）は取り込めません。元のファイル・フォルダを選んでください: %s" % p)
            if os.path.isfile(p):
                items.append((p, nfc(os.path.basename(p))))
                continue
            top = os.path.basename(p.rstrip("\\/"))
            for dp, dns, fns in os.walk(p):
                dns[:] = sorted(d for d in dns if not d.startswith((".", "$")) and d != "System Volume Information"
                                and not is_junk(d) and not is_link(os.path.join(dp, d)))
                for fn in sorted(fns):
                    sp = os.path.join(dp, fn)
                    if is_link(sp):
                        continue
                    rel = os.path.relpath(sp, p).replace("\\", "/")
                    items.append((sp, nfc((top + "/" + rel) if top else rel)))
                    if len(items) > MAX_FILES:
                        raise ValueError("ファイルが多すぎます（%d件以上）" % MAX_FILES)
        items = [(sp, rel) for sp, rel in items if not is_junk(rel)]
        if not items:
            raise ValueError("取り込むファイルがありません")
        total = 0
        for sp, _rel in items:
            try:
                total += os.path.getsize(sp)
            except OSError:
                pass
        fr = free_bytes(self.stage)
        if fr is not None and fr < total + 300 * 1024 * 1024:
            raise ValueError("この受付PCの空き容量が足りません（%s 必要）" % fmt_size(total))
        job = {"id": secrets.token_hex(6), "kind": "import", "state": "run", "total": total, "done": 0,
               "n": len(items), "i": 0, "cur": "", "errors": [], "cancel": False, "t0": time.time()}
        with self.lock:
            self.jobs[t.key] = job
        threading.Thread(target=self._import, args=(t, items, job), daemon=True, name="rx-import").start()
        return job

    def _import(self, t, items, job):
        try:
            for i, (sp, rel) in enumerate(items, 1):
                if job["cancel"]:
                    job["errors"].append("中止しました")
                    break
                job["i"], job["cur"] = i, rel
                try:
                    rel = clean_rel(rel)
                    dst = t.path_of(rel)
                    os.makedirs(os.path.dirname(dst), exist_ok=True)
                    tmp = dst + ".part~"
                    h = hashlib.sha256()
                    n = 0
                    with W.open_ro(sp) as src, open(tmp, "wb") as out:
                        while True:
                            b = src.read(CHUNK)
                            if not b:
                                break
                            out.write(b)
                            h.update(b)
                            n += len(b)
                            job["done"] += len(b)
                            if job["cancel"]:
                                break
                    if job["cancel"]:
                        os.remove(tmp)
                        continue
                    os.replace(tmp, dst)
                    with t.lock:
                        self._drop_ci(t, rel)
                        t.files[rel] = {"size": n, "sha": h.hexdigest(), "src": "USB", "t": time.time()}
                        t.ver += 1
                except (OSError, ValueError, W.UnsafeOpen) as e:
                    job["errors"].append("%s: %s" % (rel, W._err(e) if isinstance(e, OSError) else e))
        finally:
            with t.lock:
                t.save()
            job["state"] = "done"
            job["t1"] = time.time()

    def remove(self, rid, group, rels=None, all_=False):
        t = self.tray(rid, group)
        if not t:
            return
        if self._busy(t.key):
            raise ValueError("NASへの書き込み・取り込みの途中です")
        with t.lock:
            for rel in (list(t.files) if all_ else (rels or [])):
                if rel in t.files:
                    try:
                        os.remove(t.path_of(rel))
                    except OSError:
                        pass
                    del t.files[rel]
            t.ver += 1
            t.save()
            if not t.files:
                shutil.rmtree(t.dir, ignore_errors=True)
                with self.lock:
                    self.trays.pop(t.key, None)

    # ---- トレイの状態（事前解析・注意点）
    def _analyze(self, t, rel):
        a = t.ana.get(rel)
        if a and a["ver"] == t.ver:
            return a["res"]
        res = W.analyze_pptx(t.path_of(rel), self.M.coi)
        t.ana[rel] = {"ver": t.ver, "res": res}
        return res

    def tray_state(self, rid, group):
        missing = False
        try:
            w, _pdir = self.presenter(rid, group)
        except KeyError:
            w = self.M.watchers.get(rid)
            if not w:
                raise
            missing = True          # 演者フォルダが名前変更・削除された：受け取ったデータは見せる（移す・空にするため）
        t = self.tray(rid, group)
        out = {"files": [], "top": None, "total": 0, "warn": [], "busy": False, "missing": missing}
        if not t or not t.files:
            if missing:
                raise KeyError("演者フォルダがNAS上に見つかりません（削除・名前変更された可能性）")
            return out
        out["busy"] = self._busy(t.key)
        rels = sorted(t.files, key=W.nat_key)
        tops = {r.split("/")[0] for r in rels}
        if len(tops) == 1 and all("/" in r for r in rels):
            out["top"] = next(iter(tops))
        with w.lock:
            cur = w.current
        pre = group + "/"
        curcf = {k.casefold() for k in cur if k.startswith(pre)}     # NASは大文字小文字を区別しない
        warn = []
        if missing:
            warn.append(("bad", "この演者フォルダがNAS上に見つかりません（名前変更・削除された可能性）。受け取ったデータは残っています。"
                                "「別の演者へ移す」で移すか、トレイを空にしてください"))
        pres, ppts = 0, []
        for rel in rels:
            info = t.files[rel]
            name = rel.split("/")[-1]
            ext = W.ext_of(name)
            f = {"rel": rel, "size": info["size"], "src": info.get("src", ""), "c": W.file_cat(name),
                 "exists": (pre + rel).casefold() in curcf}
            if out["top"]:
                f["exists_strip"] = (pre + rel.split("/", 1)[1]).casefold() in curcf
            kind = W.ana_kind(rel)
            if ext in PRES_EXTS:
                pres += 1
            if kind == "key":
                f["na"] = "Keynote"
                warn.append(("warn", "%s：Keynoteです。会場のPCがMacか確認してください" % name))
            elif kind == "ppt":
                f["na"] = "旧形式(.ppt)"
                warn.append(("warn", "%s：旧形式（.ppt）です。会場PCで開けるか確認してください" % name))
            elif kind == "pptx":
                ppts.append(name)
                if not out["busy"]:
                    try:
                        res = self._analyze(t, rel)
                    except Exception as e:   # 解析の失敗で受付を止めない
                        res = {"ok": False, "error": "%s" % e}
                    f["sum"] = W.ana_sum(res)
                    warn += self._warnings(name, res)
            out["files"].append(f)
            out["total"] += info["size"]
        if not pres:
            warn.insert(0, ("warn", "発表ファイル（PowerPoint・PDF・Keynote）が見つかりません"))
        if len(ppts) > 1:
            warn.insert(0, ("warn", "PowerPointが%dつあります（%s）。どれを使うか演者に確認してください" % (len(ppts), "、".join(ppts[:4]))))
        out["warn"] = [{"lv": lv, "msg": m} for lv, m in warn][:60]
        return out

    @staticmethod
    def _warnings(name, res):
        if not res.get("ok"):
            return [("bad", "%s：%s" % (name, res.get("error") or "解析できません"))]
        w = []
        if not res["coi"]:
            w.append(("warn", "%s：COIの記載が見つかりません（画像で貼られている場合は検出できません）" % name))
        # 動画は100本以上あることもあるので、同じ種類の注意は1行にまとめる
        groups = {}

        def add(lv, key, msg, label):
            g = groups.setdefault(key, {"lv": lv, "msg": msg, "names": []})
            if label not in g["names"]:
                g["names"].append(label)
        for v in res["video"]:
            fmt = v.get("fmt") or {}
            label = v.get("target") or v.get("name") or ""
            if v.get("kind") == "link" and v.get("st") == "missing":
                add("bad", "missing", "リンク動画が受け取ったデータの中にありません（動画ファイルも受け取ってください）", label)
            elif v.get("st") == "abs":
                add("bad", "abs", "リンク動画が発表者PCの場所を指しているため、会場PCでは再生できません", label)
            elif v.get("st") == "unc":
                add("warn", "unc", "リンク動画がネットワーク上の場所を指しています", label)
            elif v.get("kind") == "online":
                add("info", "online", "ネット接続が必要な動画があります", label)
            if fmt.get("v") in ("bad", "warn", "unk"):
                desc = " / ".join(x for x in (fmt.get("video"), fmt.get("audio") and "音声 " + fmt["audio"]) if x)
                lv = fmt["v"] if fmt["v"] != "unk" else "warn"
                why = fmt.get("why", "")
                key = ("fmt", fmt["v"], desc if fmt["v"] != "unk" else "", why if fmt["v"] != "unk" else "")
                head = ("動画の形式が%s" % desc) if desc and fmt["v"] != "unk" else ("形式を確認できない動画があります" if fmt["v"] == "unk" else "動画の形式")
                add(lv, key, "%s — %s" % (head, why) if fmt["v"] != "unk" else head + "（試写で確認を）", v.get("name") or label)
        order = {"bad": 0, "warn": 1, "info": 2}
        for g in sorted(groups.values(), key=lambda g: order.get(g["lv"], 3)):
            ns = g["names"]
            shown = "、".join(ns[:4]) + ("ほか" if len(ns) > 4 else "")
            w.append((g["lv"], "%s：%s（%d本：%s）" % (name, g["msg"], len(ns), shown)))
        if res.get("kiosk"):
            w.append(("bad", "%s：「自動プレゼンテーション（キオスク）」設定のため、クリックで進めません" % name))
        elif res["noclick"]:
            auto = {s for s, _sec in res["auto"]} if res["use_timings"] else set()
            stuck = [s for s in res["noclick"] if s not in auto]
            if stuck:
                w.append(("bad", "%s：%d枚目などはクリックでも自動でも進みません" % (name, stuck[0])))
        if res["auto"] and res["use_timings"]:
            w.append(("info", "%s：自動で進むスライドが%d枚あります" % (name, len(res["auto"]))))
        return w

    # ---- NASへ書き込む
    def start_commit(self, rid, group, strip_top=False, exclude=None):
        w, pdir = self.presenter(rid, group, check=True)
        t = self.tray(rid, group)
        if not t or not t.files:
            raise ValueError("トレイが空です")
        if self._busy(t.key):
            raise ValueError("取り込み・書き込みの途中です")
        exclude = set(exclude or [])
        rels = [r for r in t.files if r not in exclude]
        if not rels:
            raise ValueError("書き込むファイルが選ばれていません")
        tops = {r.split("/")[0] for r in t.files}
        can_strip = len(tops) == 1 and all("/" in r for r in t.files)
        plan, seen = [], set()
        for rel in rels:
            drel = clean_rel(rel.split("/", 1)[1] if (strip_top and can_strip) else rel)
            k = drel.lower()
            if k in seen:
                raise ValueError("同じ名前になるファイルがあります: %s" % drel)
            seen.add(k)
            plan.append((rel, drel, dict(t.files[rel])))
        # 置き換える予定のファイルが会場PCで開かれていたら、何も書かずに止める
        # （動画だけ新しくなってPowerPointは古いまま、という中途半端な状態をNASに作らないため）
        busy = [drel for _r, drel, _i in plan if W.in_use_by_office(os.path.join(pdir, *drel.split("/")))]
        if busy:
            raise ValueError("会場PCで開かれているファイルがあるため、受付を始めませんでした（%s）。閉じてからもう一度「受付する」を押してください"
                             % "、".join(busy[:3]))
        # 動画などを先に、発表ファイルを最後に（会場側でPowerPointだけ先に届かないように）
        plan.sort(key=lambda x: (W.ext_of(x[1].split("/")[-1]) in PRES_EXTS, W.nat_key(x[1])))
        total = sum(x[2]["size"] for x in plan)
        fr = free_bytes(W.long_path(pdir))
        if fr is not None and fr < total + 50 * 1024 * 1024:
            raise ValueError("NASの空き容量が足りません（%s 必要、空き %s）" % (fmt_size(total), fmt_size(fr)))
        job = {"id": secrets.token_hex(6), "kind": "commit", "state": "run", "total": total, "done": 0,
               "n": len(plan), "i": 0, "cur": "", "errors": [], "cancel": False, "t0": time.time(), "result": None}
        with self.lock:
            self.jobs[t.key] = job
        threading.Thread(target=self._commit, args=(t, w, pdir, plan, job), daemon=True, name="rx-commit").start()
        return job

    def _commit(self, t, w, pdir, plan, job):
        results = []
        stamp = time.strftime("%Y%m%d-%H%M%S")
        st = self.settings
        safe_group = "/".join(p for p in t.group.split("/"))
        try:
            with self.wlock:
                self._sweep_tmp(pdir)
                done_bytes = 0
                for i, (rel, drel, info) in enumerate(plan, 1):
                    job["i"], job["cur"] = i, drel
                    r = {"rel": rel, "dest": drel, "size": info["size"]}
                    results.append(r)
                    if job["cancel"]:
                        r.update(st="skip", msg="中止しました")
                        continue
                    self._write_one(t, pdir, rel, drel, info, r, job, stamp, safe_group, st)
                    done_bytes += info["size"]
                    job["done"] = done_bytes      # 書いた・飛ばした分を合わせた進み具合
                # フォルダだけで運用している人にも分かるように、「受付済」の目印画像を入れる（設定でオフにできる）。
                # 1つでも書き込めなかったファイルがあるときは入れない（受付が終わっていないため）
                if st.get("auto_recv") and st.get("flag_dir") and results \
                        and all(r.get("st") in ("ok", "replaced", "same") for r in results) and not job["cancel"]:
                    tpl = self._template(None, "recv")
                    if tpl:
                        try:
                            fr = self._put_flag(w, pdir, t.group, tpl, skip_roles=("recv", "got", "done"))
                            job["flag"] = fr.get("added") or ""
                        except Exception as e:   # 目印を入れられなくても、受付（データ）は済んでいる
                            job["errors"].append("「受付済」の目印を入れられませんでした: %s" % (W._err(e) if isinstance(e, OSError) else e))
                    else:
                        job["errors"].append("目印画像のフォルダに「受付済」の画像がありません")
                elif st.get("auto_recv") and st.get("flag_dir") and any(r.get("st") in ("busy", "err") for r in results):
                    job["flag_skip"] = True
        except Exception as e:   # 想定外でも、トレイと記録は残す
            job["errors"].append("%s: %s" % (type(e).__name__, e))
        finally:
            self._finish(t, w, results, job, stamp, safe_group)

    def _write_one(self, t, pdir, rel, drel, info, r, job, stamp, safe_group, st):
        dest = os.path.join(pdir, *drel.split("/"))
        if not W.is_under(dest, pdir):
            r.update(st="err", msg="演者フォルダの外には書き込みません")
            return
        ld = W.long_path(dest)
        ddir = os.path.dirname(dest)
        tmp = None
        try:
            if not os.path.isdir(W.long_path(pdir)):
                # 演者フォルダが名前変更・削除された：作り直さない（古い名前のフォルダをNASに復活させないため）
                r.update(st="err", msg="演者フォルダがNAS上に見つかりません（名前変更・削除された可能性）。トレイに残しています")
                return
            # 演者フォルダの中のフォルダだけを1段ずつ作る（演者フォルダやその上は決して作らない）
            sub = drel.split("/")[:-1]
            for i in range(1, len(sub) + 1):
                d = os.path.join(pdir, *sub[:i])
                if not os.path.isdir(W.long_path(d)):
                    try:
                        os.mkdir(W.long_path(d))
                    except FileExistsError:
                        pass
            existed = os.path.lexists(ld)
            if existed and os.path.isdir(ld):
                r.update(st="err", msg="同じ名前のフォルダがNASにあります")
                return
            if existed:
                if W.in_use_by_office(dest):
                    r.update(st="busy", msg="会場PCで開かれているため置き換えません（閉じてからもう一度「受付する」）")
                    return
                try:
                    if os.path.getsize(ld) == info["size"] and sha256_of(ld, W.open_ro)[0] == info["sha"]:
                        r.update(st="same", msg="NASに同じ内容のファイルがあるため書き込みませんでした")
                        return
                except (OSError, W.UnsafeOpen):
                    pass
                if st["keep_local"]:
                    bak = os.path.join(self.bak_dir, t.rid, *safe_group.split("/"), stamp, *drel.split("/"))
                    os.makedirs(os.path.dirname(bak), exist_ok=True)
                    try:
                        with W.open_ro(ld) as src, open(bak, "wb") as out:
                            shutil.copyfileobj(src, out, CHUNK)
                    except (OSError, W.UnsafeOpen) as e:
                        r.update(st="busy" if isinstance(e, OSError) and is_busy_error(e) else "err",
                                 msg="前の版をこのPCに保存できないため置き換えません（%s）" % (W._err(e) if isinstance(e, OSError) else e))
                        return
                    r["backup"] = bak
            tmp = os.path.join(ddir, RX_TMP + secrets.token_hex(6) + ".part")
            src_path = t.path_of(rel)
            with open(src_path, "rb") as src, open(W.long_path(tmp), "xb") as out:
                W._hide(W.long_path(tmp))
                while True:
                    b = src.read(CHUNK)
                    if not b:
                        break
                    out.write(b)
                    job["done"] += len(b)
                out.flush()
                os.fsync(out.fileno())
            if st["verify"]:
                sha, n = sha256_of(W.long_path(tmp), W.open_ro)
                if sha != info["sha"] or n != info["size"]:
                    raise IOError("NASに書き込んだ内容が一致しません（もう一度「受付する」を押してください）")
            if existed and W.in_use_by_office(dest):
                r.update(st="busy", msg="会場PCで開かれたため置き換えませんでした（閉じてからもう一度）")
                return
            W._unhide(tmp)                  # 隠し属性のまま置き換えると、置いたファイルも隠しファイルになる
            os.replace(W.long_path(tmp), ld)
            tmp = None
            W._unhide(dest)
            r.update(st="replaced" if existed else "ok", sha=info["sha"])
        except W.UnsafeOpen as e:
            r.update(st="err", msg=str(e))
        except OSError as e:
            if is_busy_error(e):
                r.update(st="busy", msg="NAS上で使用中か、書き込む権限がないため書き込めません（%s）" % W._err(e))
            else:
                r.update(st="err", msg="書き込めません: %s" % W._err(e))
        except Exception as e:
            r.update(st="err", msg="%s: %s" % (type(e).__name__, e))
        finally:
            if tmp:
                try:
                    os.remove(W.long_path(tmp))     # 片付けるのは自分の一時ファイルだけ
                except OSError:
                    pass

    def _sweep_tmp(self, pdir):
        """前に異常終了（書き込み中にウィンドウを閉じた等）して残った自分の一時ファイル（.swnr_xxxx.part）を片付ける。
        この演者フォルダの中だけ。ほかの受付PCが書き込み中のものを消さないよう、15分以上更新されていないものに限る。"""
        pat = re.compile(r"^%s[0-9a-f]{12}\.part$" % re.escape(RX_TMP))
        cut = time.time() - 900
        try:
            for dp, _dns, fns in os.walk(W.long_path(pdir)):
                for fn in fns:
                    if pat.match(fn):
                        fp = os.path.join(dp, fn)
                        try:
                            if os.stat(fp).st_mtime < cut:
                                os.remove(fp)
                        except OSError:
                            pass
        except OSError:
            pass

    def _finish(self, t, w, results, job, stamp, safe_group):
        done = [r for r in results if r.get("st") in ("ok", "replaced", "same")]
        keep = self.settings["keep_local"]
        with t.lock:
            for r in done:
                rel = r["rel"]
                src = t.path_of(rel)
                try:
                    if keep:
                        dst = W.long_path(os.path.join(self.recv_dir, t.rid, *safe_group.split("/"), stamp, *r["dest"].split("/")))
                        os.makedirs(os.path.dirname(dst), exist_ok=True)
                        if os.path.exists(dst):
                            base_, ext_ = os.path.splitext(dst)
                            dst = "%s_%s%s" % (base_, secrets.token_hex(2), ext_)
                        shutil.move(src, dst)
                    else:
                        os.remove(src)
                except OSError as e:
                    # NASへの受付は済んでいる。このPCの予備に移せなかったので、トレイに残しておく（消さない）
                    r["msg"] = ((r.get("msg") or "") + "　このPCへの保存に失敗したため、トレイに残しています（%s）" % W._err(e)).strip()
                    continue
                t.files.pop(rel, None)
            t.ver += 1
            if t.files:
                t.save()
            else:
                shutil.rmtree(t.dir, ignore_errors=True)
                with self.lock:
                    if self.trays.get(t.key) is t:
                        del self.trays[t.key]
        cnt = {k: sum(1 for r in results if r.get("st") == k) for k in ("ok", "replaced", "same", "busy", "err", "skip")}
        rec = {"ts": time.time(), "pc": self.settings["pc_name"], "root": t.rid, "root_label": w.label, "group": t.group,
               "files": [{k: r.get(k) for k in ("dest", "size", "st", "msg", "sha")} for r in results][:500],
               "count": cnt, "flag": job.get("flag", "")}
        try:
            with open(self.log_path, "ab") as f:
                f.write(W.json_bytes(rec) + b"\n")
        except OSError as e:
            job["errors"].append("受付記録を保存できません: %s" % e)
        self.M.log("RECEPTION  %s / %s  書き込み%d 差し替え%d 同じ%d 使用中%d エラー%d" % (
            w.label, t.group, cnt["ok"], cnt["replaced"], cnt["same"], cnt["busy"], cnt["err"]))
        job["result"] = {"files": results, "count": cnt, "flag": job.get("flag", ""), "flag_skip": bool(job.get("flag_skip"))}
        job["state"] = "done"
        job["t1"] = time.time()
        self.M.poke()

    def move_tray(self, rid, group, to_group):
        """受け取ったデータを、別の演者（名前を変えた演者フォルダなど）のトレイへ移す。"""
        t = self.tray(rid, group)
        if not t or not t.files:
            raise ValueError("トレイが空です")
        if self._busy(t.key):
            raise ValueError("取り込み・書き込みの途中です")
        self.presenter(rid, to_group, check=True)
        nt = self.tray(rid, to_group)
        if nt and nt.files:
            raise ValueError("移す先の演者のトレイにもデータがあります。先に受付するか、空にしてください")
        new = Tray(self.stage, rid, to_group)
        with t.lock:
            if os.path.exists(new.dir):
                shutil.rmtree(new.dir, ignore_errors=True)
            shutil.move(t.dir, new.dir)
            new.files = dict(t.files)
            new.ver = t.ver + 1
            new.save()
            t.files = {}
        with self.lock:
            self.trays.pop(t.key, None)
            self.trays[new.key] = new
        self._log({"root": rid, "group": to_group, "tray_from": group})
        return {"ok": True}

    def list_trays(self):
        """トレイにデータが残っている演者の一覧（演者フォルダの名前が変わって見えなくなったものも含む）。"""
        with self.lock:
            ts = list(self.trays.values())
        out = []
        for t in ts:
            if not t.files:
                continue
            w = self.M.watchers.get(t.rid)
            out.append({"root": t.rid, "group": t.group, "n": len(t.files), "size": sum(i["size"] for i in t.files.values()),
                        "exists": bool(w) and w.current.get(t.group) == W.DIR})
        return sorted(out, key=lambda x: W.nat_key(x["group"]))

    # ---- 目印画像（現場で使っている 00_受付済.jpg などを、そのままコピーして入れる）
    def flag_templates(self):
        """目印画像のフォルダにある画像の一覧。SW NAS WATCH が目印として認識するものだけ使える。"""
        fd = self.settings.get("flag_dir") or ""
        out = {"dir": fd, "templates": [], "error": ""}
        if not fd:
            return out
        try:
            with os.scandir(W.long_path(fd)) as it:
                ents = [(de.name, de.stat().st_size) for de in it if de.is_file() and not de.name.startswith((".", "~$"))]
        except OSError as e:
            out["error"] = "目印画像のフォルダを読めません: %s" % W._err(e)
            return out
        for name, size in sorted(ents, key=lambda x: W.nat_key(x[0])):
            if W.ext_of(name) not in W.MARK_EXTS or is_junk(name):
                continue
            mk = self.M.marker_of(name, (size, 0))
            out["templates"].append({"name": nfc(name), "role": mk[0] if mk else None, "label": mk[1] if mk else None,
                                     "ok": bool(mk)})
        return out

    def _template(self, name, role=None):
        for t in self.flag_templates()["templates"]:
            if t["ok"] and (t["name"] == name if name else t["role"] == role):
                return t
        return None

    def _present_flags(self, w, group):
        with w.lock:
            cur = dict(w.current)
        pre = group + "/"
        out = []
        for k, sig in cur.items():
            if k.startswith(pre) and "/" not in k[len(pre):] and sig != W.DIR:
                mk = self.M.marker_of(k, sig)
                if mk:
                    out.append((k[len(pre):], mk))
        return out

    def _put_flag(self, w, pdir, group, t, skip_roles=()):
        """目印画像を演者フォルダへコピーする。同じ表示名の目印がすでにあれば何もしない（上書きしない）。"""
        for n, mk in self._present_flags(w, group):
            if mk[1] == t["label"] or mk[0] in skip_roles:
                return {"ok": True, "exists": n}
        if not os.path.isdir(W.long_path(pdir)):
            raise KeyError("演者フォルダがNAS上に見つかりません（名前変更・削除された可能性）")
        dest = os.path.join(pdir, t["name"])
        if os.path.lexists(W.long_path(dest)):
            return {"ok": True, "exists": t["name"]}
        src = os.path.join(self.settings["flag_dir"], t["name"])
        tmp = os.path.join(pdir, RX_TMP + secrets.token_hex(6) + ".part")
        try:
            with W.open_ro(W.long_path(src)) as f:
                data = f.read(W.MARK_MAX + 1)
            if len(data) > W.MARK_MAX:
                raise ValueError("目印画像が大きすぎます")
            with open(W.long_path(tmp), "xb") as out:
                W._hide(W.long_path(tmp))
                out.write(data)
                out.flush()
                os.fsync(out.fileno())
            with W.open_ro(W.long_path(tmp)) as f:
                if f.read() != data:
                    raise IOError("NASに書き込んだ内容が一致しません")
            W._unhide(tmp)
            if os.path.lexists(W.long_path(dest)):
                return {"ok": True, "exists": t["name"]}
            if W.IS_WIN:
                os.rename(W.long_path(tmp), W.long_path(dest))     # 同じ名前があれば失敗する（上書きしない）
            else:
                try:
                    os.link(tmp, dest)                             # 同じ名前があれば失敗する（上書きしない）
                    os.remove(tmp)
                except FileExistsError:
                    return {"ok": True, "exists": t["name"]}
                except OSError:                                    # SMBなど、リンクを作れない場所
                    if os.path.lexists(dest):
                        return {"ok": True, "exists": t["name"]}
                    os.rename(tmp, dest)
            tmp = None
            W._unhide(dest)
        finally:
            if tmp:
                try:
                    os.remove(W.long_path(tmp))
                except OSError:
                    pass
        self._log({"root": w.id, "group": group, "flag_add": t["name"]})
        return {"ok": True, "added": t["name"]}

    def add_flag(self, rid, group, name):
        w, pdir = self.presenter(rid, group, check=True)
        if not self.settings.get("flag_dir"):
            raise ValueError("［設定］で目印画像のフォルダを指定してください")
        t = self._template(str(name))
        if not t:
            raise ValueError("目印画像が見つからないか、目印として認識されません: %s" % name)
        with self.wlock:
            res = self._put_flag(w, pdir, group, t)
        self.M.poke()
        return res

    def remove_flag(self, rid, group, names):
        """目印画像だけを消す（データは消さない）。演者フォルダの直下にあり、目印として認識され、
        しかも目印画像のフォルダにある元画像と中身が同じものに限る（同じ名前のデータ画像を消さないため）。"""
        w, pdir = self.presenter(rid, group, check=True)
        present = {nfc(n): n for n, _mk in self._present_flags(w, group)}     # Macで作られた名前（NFD）も同じに扱う
        fd = self.settings.get("flag_dir") or ""
        tpl = {}
        for t in self.flag_templates()["templates"]:
            if t["ok"]:
                try:
                    with W.open_ro(W.long_path(os.path.join(fd, t["name"]))) as f:
                        b = f.read(W.MARK_MAX + 1)
                    tpl.setdefault(len(b), set()).add(hashlib.sha256(b).hexdigest())
                except (OSError, W.UnsafeOpen):
                    pass
        targets = []
        for n in names or []:
            n = nfc(str(n))
            if "/" in n or "\\" in n or n not in present:
                raise ValueError("目印として認識されるファイルではありません: %s" % n)
            real = present[n]
            p = os.path.join(pdir, real)
            st = os.stat(W.long_path(p))
            if st.st_size > W.MARK_MAX or self.M.marker_of(real, (st.st_size, 0)) is None:
                raise ValueError("目印として認識されるファイルではありません: %s" % n)
            with W.open_ro(W.long_path(p)) as f:
                h = hashlib.sha256(f.read(W.MARK_MAX + 1)).hexdigest()
            if h not in tpl.get(st.st_size, ()):
                raise ValueError("「%s」は目印画像のフォルダにある元画像と中身が違うため、アプリからは外せません"
                                 "（データの画像かもしれません。外すならExplorerで確認してから操作してください）" % n)
            targets.append(real)
        done = []
        with self.wlock:
            for real in targets:
                os.remove(W.long_path(os.path.join(pdir, real)))
                done.append(nfc(real))
        if done:
            self._log({"root": rid, "group": group, "flag_del": done})
        self.M.poke()
        return {"ok": True, "removed": done}

    def _log(self, rec):
        rec = dict(rec, ts=time.time(), pc=self.settings["pc_name"])
        try:
            with open(self.log_path, "ab") as f:
                f.write(W.json_bytes(rec) + b"\n")
        except OSError:
            pass

    # ---- 演者フォルダを作る
    def sessions(self, rid):
        w = self.M.watchers.get(rid)
        if not w:
            raise KeyError("監視フォルダが見つかりません")
        with w.lock:
            cur = dict(w.current)
        lvl = w.depth - 1
        out = set()
        if lvl == 0:
            out.add("")
        for k, v in cur.items():
            if v == W.DIR and k.count("/") + 1 == lvl:
                out.add(k)
        return sorted(out, key=W.nat_key)

    def mkdir(self, rid, parent, name):
        w = self.M.watchers.get(rid)
        if not w:
            raise KeyError("監視フォルダが見つかりません")
        if not isinstance(name, str) or not name.strip():
            raise ValueError("フォルダ名を入れてください")
        name = nfc(name).strip()
        if not safe_part(name) or name.startswith(RX_TMP):
            raise ValueError("フォルダ名に使えない文字があります（\\ / : * ? \" < > | など）")
        if name.startswith((".", "~$")) or W.is_ignored(self.M.ignore_re, name):
            raise ValueError("この名前のフォルダは一覧に表示されない（無視するファイル名に当たる）ため作れません: %s" % name)
        segs = [s for s in str(parent).split("/") if s] if parent else []
        if len(segs) != w.depth - 1 or any(x in (".", "..") or x.strip(" .") == "" or x.endswith((" ", "."))
                                           or "\\" in x or ":" in x for x in segs):
            raise ValueError("追加先のセッションを選んでください")
        pdir = os.path.join(w.path, *segs)
        if not os.path.isdir(W.long_path(pdir)):
            raise KeyError("セッションのフォルダがNAS上に見つかりません")
        target = os.path.join(pdir, name)
        if os.path.lexists(W.long_path(target)):
            raise ValueError("同じ名前のフォルダがすでにあります")
        os.mkdir(W.long_path(target))
        group = "/".join(segs + [name])
        self._log({"root": rid, "group": group, "mkdir": True})
        self.M.poke()
        return group

    def history(self, rid, group, limit=30):
        out = []
        try:
            with open(self.log_path, encoding="utf-8") as f:
                for ln in f:
                    try:
                        r = json.loads(ln)
                    except ValueError:
                        continue
                    if r.get("root") == rid and r.get("group") == group:
                        out.append(r)
        except OSError:
            pass
        return out[-limit:][::-1]

    # ---- USB・ドライブ
    def drives(self):
        out = []
        if W.IS_WIN:
            import ctypes
            k32 = ctypes.windll.kernel32
            mask = k32.GetLogicalDrives()
            sysd = (os.environ.get("SystemDrive") or "C:").upper()
            for i, L in enumerate(string.ascii_uppercase):
                if not mask & (1 << i):
                    continue
                root = L + ":\\"
                typ = k32.GetDriveTypeW(root)        # 2=リムーバブル 3=固定 4=ネットワーク 5=CD
                if typ not in (2, 3, 5) or root[:2].upper() == sysd:
                    continue
                buf = ctypes.create_unicode_buffer(261)
                k32.SetErrorMode(1)
                label = buf.value if k32.GetVolumeInformationW(root, buf, 261, None, None, None, None, 0) else ""
                try:
                    du = shutil.disk_usage(root)
                except OSError:
                    continue                          # カードリーダーにメディアがない など
                if any(W.is_under(root, nr) or W.is_under(nr, root) for nr in self.nas_roots()):
                    continue
                out.append({"path": root, "name": "%s (%s)" % (label or ("USBドライブ" if typ == 2 else "ドライブ"), L + ":"),
                            "type": "USB" if typ == 2 else ("CD/DVD" if typ == 5 else "ドライブ"),
                            "eject": typ in (2, 5), "total": du.total, "free": du.free})
        elif W.IS_MAC:
            net = set()
            try:        # ネットワーク上の共有（NASなど）は取り込み元に出さない
                mo = subprocess.run(["mount"], capture_output=True, text=True, timeout=5).stdout
                for ln in mo.splitlines():
                    m = re.match(r"^\S+ on (.+) \((smbfs|afpfs|nfs|webdav|cifs)\b", ln)
                    if m:
                        net.add(m.group(1))
            except (OSError, subprocess.SubprocessError):
                pass
            for n in sorted(os.listdir("/Volumes")):
                p = os.path.join("/Volumes", n)
                if p in net or any(W.is_under(p, nr) or W.is_under(nr, p) for nr in self.nas_roots()):
                    continue
                if os.path.ismount(p) and os.path.realpath(p) != "/":
                    try:
                        du = shutil.disk_usage(p)
                    except OSError:
                        continue
                    out.append({"path": p, "name": n, "type": "ドライブ", "eject": True, "total": du.total, "free": du.free})
        for p in self.extra:
            if os.path.isdir(p):
                du = shutil.disk_usage(p)
                out.append({"path": p, "name": os.path.basename(p) or p, "type": "フォルダ", "eject": False,
                            "total": du.total, "free": du.free})
        return out

    def browse(self, path):
        p = os.path.abspath(str(path))
        if not os.path.isdir(p):
            raise ValueError("フォルダが見つかりません: %s" % p)
        items = []
        with os.scandir(p) as it:
            for de in it:
                n = de.name
                if n.startswith((".", "$", "~$")) or n == "System Volume Information" or is_junk(n):
                    continue
                try:
                    isdir = de.is_dir()
                    stt = de.stat()
                except OSError:
                    continue
                items.append({"name": n, "path": de.path, "dir": isdir, "size": 0 if isdir else stt.st_size,
                              "m": stt.st_mtime, "c": "" if isdir else W.file_cat(n)})
                if len(items) >= 3000:
                    break
        items.sort(key=lambda x: (not x["dir"], W.nat_key(x["name"])))
        parent = os.path.dirname(p.rstrip("\\/")) if os.path.dirname(p.rstrip("\\/")) != p.rstrip("\\/") else None
        if parent and (len(p.rstrip("\\/")) <= 3 and W.IS_WIN):
            parent = None
        return {"path": p, "parent": parent, "items": items}

    def eject(self, path):
        p = str(path)
        with self.lock:
            if any(j["state"] == "run" and j["kind"] == "import" for j in self.jobs.values()):
                raise ValueError("取り込みの途中です。終わってから取り出してください")
        if W.IS_WIN:
            if not (len(p) >= 2 and p[0].isalpha() and p[1] == ":"):
                raise ValueError("ドライブを指定してください")
            L = p[0].upper() + ":"
            ps = "(New-Object -ComObject Shell.Application).Namespace(17).ParseName('%s').InvokeVerb('Eject')" % L
            subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", ps], timeout=30,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, creationflags=0x08000000)
            for _ in range(20):
                if not os.path.exists(L + "\\"):
                    return {"ok": True, "msg": "%s を取り外せます" % L}
                time.sleep(0.25)
            return {"ok": False, "msg": "%s を取り出せませんでした（使用中のファイルがないか確認してください）" % L}
        if W.IS_MAC:
            if not p.startswith("/Volumes/"):
                raise ValueError("ドライブを指定してください")
            r = subprocess.run(["diskutil", "eject", p], timeout=30, capture_output=True, text=True)
            return {"ok": r.returncode == 0, "msg": "取り外せます" if r.returncode == 0 else (r.stderr or r.stdout).strip()}
        raise ValueError("このOSでは取り出しに対応していません")


# ---------------------------------------------------------------- manager / http
class RxManager(W.Manager):
    def apply_config(self, new):
        new["op"] = dict(new.get("op") or {}, enabled=False)   # 受付アプリではコピーしない（SW NAS OPERATOR の役目）
        super().apply_config(new)


def build_page():
    if not W.LEGACY_UI and W.UI_PACK:
        return W.ui_page()     # 新しい画面（React）：どのアプリかは画面の側で切り替える
    h = W.HTML

    def sub(old, new):
        nonlocal h
        if h.count(old) != 1:
            raise RuntimeError("画面の組み立てに失敗しました: %r" % old[:40])
        h = h.replace(old, new)
    sub("<title>SW NAS WATCH</title>", "<title>SW NAS RECEPTION</title>")
    sub('+"SW NAS WATCH";if(ret)return t;', '+"SW NAS RECEPTION";if(ret)return t;')
    sub("SW NAS WATCH<small>SEVENTHWELL · READ ONLY</small>", "SW NAS RECEPTION<small>SEVENTHWELL · 受付</small>")
    sub("SW NAS WATCH v__VERSION__ · © SEVENTHWELL",
        "SW NAS RECEPTION v%s（SW NAS WATCH v__VERSION__ ベース） · © SEVENTHWELL" % VERSION)
    sub("</style>\n</head>", RX_CSS + "\n</style>\n</head>")
    sub("</script>\n</body>", RX_JS + "\n</script>\n</body>")
    return h


class RxHandler(W.Handler):
    server_version = "SWNasReception/" + VERSION

    @property
    def RX(self):
        return self.server.rx

    def send_page(self):
        body = self.server.page.replace("__TOKEN__", self.server.token).replace("__VERSION__", W.VERSION).replace(
            "__APPKIND__", "reception").encode("utf-8")
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
        q = parse_qs(u.query)

        def g(k):
            return (q.get(k) or [""])[0]
        try:
            if u.path in ("/", "/index.html"):
                return self.send_page()
            if u.path == "/api/ping":
                return self.send_json({"app": APP_NAME, "version": VERSION})
            if not u.path.startswith("/api/rx/"):
                return super().do_GET()
            RX = self.RX
            if u.path == "/api/rx/tray":
                self.send_json(RX.tray_state(g("root"), g("group")))
            elif u.path == "/api/rx/job":
                self.send_json({"job": RX.job_of(g("root") + "|" + g("group"))})
            elif u.path == "/api/rx/history":
                self.send_json({"items": RX.history(g("root"), g("group"))})
            elif u.path == "/api/rx/sessions":
                self.send_json({"sessions": RX.sessions(g("root"))})
            elif u.path == "/api/rx/drives":
                self.send_json({"drives": RX.drives()})
            elif u.path == "/api/rx/browse":
                self.send_json(RX.browse(g("path")))
            elif u.path == "/api/rx/settings":
                self.send_json({"settings": RX.settings, "data_dir": RX.data})
            elif u.path == "/api/rx/flags":
                self.send_json(RX.flag_templates())
            elif u.path == "/api/rx/trays":
                self.send_json({"trays": RX.list_trays()})
            else:
                self.deny(404, "not found")
        except KeyError as e:
            self.deny(404, str(e).strip("'\""))
        except ValueError as e:
            self.deny(400, str(e))
        except OSError as e:
            try:
                self.deny(500, W._err(e))
            except OSError:
                pass
        except Exception as e:
            try:
                self.deny(500, "%s: %s" % (type(e).__name__, e))
            except OSError:
                pass

    def do_POST(self):
        u = urlparse(self.path)
        if not u.path.startswith("/api/rx/"):
            return super().do_POST()
        if not self.is_local() or (self.headers.get("Host") or "").lower() not in self.server.allowed_hosts:
            return self.deny(403, "この操作はアプリを動かしているPCからのみ可能です")
        if self.headers.get("X-SW-Token") != self.server.token:
            return self.deny(403, "token")
        RX = self.RX
        try:
            if u.path == "/api/rx/upload":
                q = parse_qs(u.query)
                try:
                    n = int(self.headers.get("Content-Length") or -1)
                except ValueError:
                    n = -1
                if n < 0:
                    return self.deny(411, "Content-Length がありません")
                res = RX.upload((q.get("root") or [""])[0], (q.get("group") or [""])[0], (q.get("path") or [""])[0],
                                n, self.rfile)
                return self.send_json(res)
            try:
                n = int(self.headers.get("Content-Length") or 0)
                if n > 1_000_000:
                    return self.deny(413, "too large")
                body = json.loads(self.rfile.read(n).decode("utf-8") or "{}") if n else {}
            except (ValueError, UnicodeDecodeError):
                return self.deny(400, "bad json")
            rid, group = str(body.get("root") or ""), str(body.get("group") or "")
            if u.path == "/api/rx/import":
                self.send_json({"job": RX.start_import(rid, group, body.get("paths") or [])})
            elif u.path == "/api/rx/remove":
                RX.remove(rid, group, [str(x) for x in (body.get("rels") or [])], bool(body.get("all")))
                self.send_json({"ok": True})
            elif u.path == "/api/rx/commit":
                self.send_json({"job": RX.start_commit(rid, group, bool(body.get("strip_top")),
                                                       [str(x) for x in (body.get("exclude") or [])])})
            elif u.path == "/api/rx/cancel":
                j = RX.job_of(rid + "|" + group)
                if j and j["state"] == "run":
                    j["cancel"] = True
                self.send_json({"ok": True})
            elif u.path == "/api/rx/mkdir":
                self.send_json({"ok": True, "group": RX.mkdir(rid, str(body.get("parent") or ""), body.get("name"))})
            elif u.path == "/api/rx/eject":
                self.send_json(RX.eject(body.get("path") or ""))
            elif u.path == "/api/rx/move":
                self.send_json(RX.move_tray(rid, group, str(body.get("to") or "")))
            elif u.path == "/api/rx/flag":
                self.send_json(RX.add_flag(rid, group, body.get("name") or ""))
            elif u.path == "/api/rx/unflag":
                self.send_json(RX.remove_flag(rid, group, [str(x) for x in (body.get("names") or [])]))
            elif u.path == "/api/rx/pickdir":
                self.send_json({"ok": True, "path": W.pick_folder()})
            elif u.path == "/api/rx/settings":
                self.send_json({"ok": True, "settings": RX.save_settings(body)})
            else:
                self.deny(404, "not found")
        except KeyError as e:
            self.deny(404, str(e).strip("'\""))
        except (ValueError, RuntimeError) as e:
            self.deny(400, str(e))
        except OSError as e:
            try:
                self.deny(500, W._err(e))
            except OSError:
                pass
        except Exception as e:
            try:
                self.deny(500, "%s: %s" % (type(e).__name__, e))
            except OSError:
                pass


def main():
    for _s in (sys.stdout, sys.stderr):
        try:
            _s.reconfigure(errors="replace")
        except Exception:
            pass
    ap = argparse.ArgumentParser(description="%s — 学会の受付PC用：演者のデータをNASの演者フォルダへ入れる" % APP_NAME)
    ap.add_argument("--root", action="append", default=[], help="受付先の監視フォルダ（学会名フォルダ）")
    ap.add_argument("--label", default="", help="--root の表示名")
    ap.add_argument("--depth", type=int, default=3, help="演者フォルダの階層（学会/会場/セッション/演者 なら 3）")
    ap.add_argument("--port", type=int, default=DEFAULT_PORT)
    ap.add_argument("--no-browser", action="store_true", help="画面を自動で開かない")
    ap.add_argument("--browser", choices=["app", "default"], default="app")
    ap.add_argument("--data-dir", default="", help="設定・受付データの保存先（既定: このファイルの横）")
    ap.add_argument("--drive", action="append", default=[], help="取り込み元として一覧に出すフォルダ（任意・複数可）")
    ap.add_argument("--legacy-ui", action="store_true", help="旧画面（v1.13 まで）で表示する")
    a = ap.parse_args()
    W.use_legacy(a.legacy_ui)
    W.disable_quick_edit()

    data_dir = a.data_dir or pick_data_dir()
    os.makedirs(data_dir, exist_ok=True)
    store = W.LocalStore(data_dir)
    raw = store.read_json("config.json", None)
    first = raw is None
    cfg, cfg_msg = W.startup_config(store, data_dir, raw)
    if cfg_msg:
        print(cfg_msg)
    for p in a.root:
        if not any(W.norm_key(r["path"]) == W.norm_key(p) for r in cfg["roots"]):
            cfg["roots"].append({"path": p, "label": a.label, "depth": a.depth, "enabled": True})
    cfg["op"]["enabled"] = False
    if first:   # 受付PCは通知・音なしで始める（設定で変えられる）
        cfg["notify"] = {k: False for k in W.NOTIFY_KINDS}
        cfg["ui"]["sound"] = False
    try:
        cfg = W.validate_cfg(cfg, data_dir)
    except ValueError as e:
        raise SystemExit(str(e))

    url = "http://127.0.0.1:%d/" % a.port
    if not W.claim_port("127.0.0.1", a.port, url, APP_NAME, None if a.no_browser else (lambda: W.open_ui(url, data_dir, a.browser))):
        return
    store.roots = [r["path"] for r in cfg["roots"]]
    store.write_json("config.json", cfg)      # 2つ目の起動（すでに起動中）では設定ファイルに触れない

    mgr = RxManager(store, cfg)
    srv = W.Server(("127.0.0.1", a.port), RxHandler)
    srv.mgr = mgr
    srv.token = secrets.token_urlsafe(24)
    srv.lan = False
    srv.stopping = False
    srv.allowed_hosts = {"127.0.0.1:%d" % a.port, "localhost:%d" % a.port, "[::1]:%d" % a.port}
    srv.page = build_page()
    srv.rx = Rx(mgr, data_dir, a.drive)
    srv.quit_block = lambda: ("受け取り・NASへの書き込みの途中です。終わってから終了してください"
                              if any(j.get("state") == "run" for j in list(srv.rx.jobs.values())) else "")
    mgr.start()
    W.start_autoquit(srv, enabled=False)

    print("=" * 64)
    print(" %s v%s   (受付：NASの演者フォルダへ書き込みます)" % (APP_NAME, VERSION))
    print(" 画面: %s" % url)
    print(" 保存先: %s" % data_dir)
    for r in cfg["roots"]:
        print(" 受付先: [%s] %s  (階層%d)" % (r["label"] or W.default_label(r["path"]), r["path"], r["depth"]))
    if not cfg["roots"]:
        print(" 受付先が未設定 → 画面の［設定］から学会名フォルダを追加してください")
    print(" " + ("画面の［終了］（電源のボタン）で止まります。ウィンドウを閉じても裏で動いています（もう一度起動すると画面が開きます）" if W.AUTOQUIT else "このウィンドウを閉じると止まります（Ctrl+C で終了）"))
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
RX_CSS = r'''
/* ===== SW NAS RECEPTION ===== */
#rxpane{padding:16px 24px 0}
.rxbox{border:1px solid var(--border);border-radius:14px;background:var(--card);padding:16px 16px 14px;box-shadow:0 1px 2px rgba(0,0,0,.3)}
.rxh{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:12px;min-width:0}
.rxt{font-size:11px;font-weight:800;letter-spacing:.14em;color:#052e1a;background:var(--emerald);border-radius:6px;padding:2px 8px;flex:none}
.rxn{font-size:19px;font-weight:700;letter-spacing:-.01em;word-break:break-all}
.rxw{color:var(--muted-fg);font-size:12.5px}
.rxflags{display:flex;flex-wrap:wrap;gap:5px;align-items:center;margin:-2px 0 12px;font-size:12.5px}
.rxflags .lb{font-size:11.5px;font-weight:700;color:var(--muted-fg);margin-right:4px;letter-spacing:.06em}
.rxflags.none{color:var(--muted-fg)}
.rxflags .fb{height:26px;padding:0 9px;font-size:12px;font-weight:600;border-radius:999px;gap:4px;color:var(--muted-fg);background:transparent;box-shadow:none;border:1px dashed #3f3f46}
.rxflags .fb svg{width:13px;height:13px}
.rxflags .fb:hover{color:var(--foreground);border-color:#71717a}
.rxflags .fb.on{border-style:solid;color:#e4e4e7;background:rgba(255,255,255,.07);border-color:#52525b}
.rxflags .fb.on.r-recv{color:var(--emerald);border-color:rgba(16,185,129,.5);background:rgba(16,185,129,.1)}
.rxflags .fb.on.r-got{color:var(--sky);border-color:rgba(56,189,248,.5);background:rgba(56,189,248,.1)}
.rxflags .fb.on.r-warn{color:var(--amber);border-color:rgba(245,158,11,.5);background:rgba(245,158,11,.1)}
.rxflags .fb.on.r-direct{color:var(--violet);border-color:rgba(139,92,246,.5);background:rgba(139,92,246,.1)}
.rxflags .fb.on.r-drop{color:#fca5a5;border-color:rgba(239,68,68,.5);background:rgba(239,68,68,.1)}
.rxdrop{border:2px dashed #3f3f46;border-radius:12px;padding:18px 14px;text-align:center;transition:border-color .15s,background .15s}
#center.dragging .rxdrop,.rxdrop.over{border-color:var(--emerald);background:rgba(16,185,129,.08)}
.rxdrop .big{display:flex;gap:8px;justify-content:center;align-items:center;font-size:16px;font-weight:600}
.rxdrop .big svg{width:20px;height:20px;color:var(--emerald)}
.rxdrop .sub{color:var(--muted-fg);font-size:12.5px;margin:6px 0 12px}
.rxdrop .btns{display:flex;gap:8px;justify-content:center;flex-wrap:wrap}
.rxdrop.dis{opacity:.55}
.rxprog{margin-top:12px;border:1px solid rgba(245,158,11,.35);background:rgba(245,158,11,.06);border-radius:10px;padding:10px 12px;font-size:13px}
.rxprog .l1{display:flex;align-items:center;gap:8px}
.rxprog .l1 svg{width:15px;height:15px;color:var(--amber);animation:spin 1.1s linear infinite}
.rxprog .l1 .t{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.rxprog .bar{height:7px;border-radius:999px;background:rgba(0,0,0,.35);overflow:hidden;margin-top:8px}
.rxprog .bar i{display:block;height:100%;background:var(--amber);border-radius:999px;transition:width .2s}
.rxprog .l2{font:500 11.5px var(--mono);color:var(--muted-fg);margin-top:5px}
.rxtray{margin-top:14px}
.rxtray .th{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:8px}
.rxtray .th b{font-size:14.5px}
.rxtray .th .x{color:var(--muted-fg);font-size:12.5px}
.rxtray table{width:100%;border-collapse:collapse;font-size:13px;border:1px solid var(--border);border-radius:10px;overflow:hidden}
.rxtray td{padding:7px 10px;border-top:1px solid var(--border);vertical-align:middle}
.rxtray tr:first-child td{border-top:0}
.rxtray td.nm{word-break:break-all}
.rxtray td.nm .p{color:var(--dim)}
.rxtray td.num{text-align:right;white-space:nowrap;color:var(--muted-fg);font-variant-numeric:tabular-nums}
.rxtray td.tg{white-space:normal}
.rxtray td.tg .tag{margin:1px 2px}
.rxtray tr.off td{opacity:.45}
.rxtray .rm{width:26px;height:26px;padding:0;color:var(--muted-fg)}
.rxwarn{margin:10px 0 0;padding:0;list-style:none;font-size:13px;display:flex;flex-direction:column;gap:4px}
.rxwarn li{padding:6px 10px;border-radius:8px;border:1px solid var(--border);line-height:1.5}
.rxwarn li.bad{border-color:rgba(239,68,68,.45);background:rgba(239,68,68,.08);color:#fecaca}
.rxwarn li.warn{border-color:rgba(245,158,11,.4);background:rgba(245,158,11,.07);color:#fde68a}
.rxwarn li.info{color:var(--muted-fg)}
.rxgo{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-top:12px}
.rxgo .big{height:42px;padding:0 18px;font-size:14.5px;font-weight:700}
.rxgo label{display:flex;gap:7px;align-items:center;font-size:13px;color:var(--muted-fg);cursor:pointer}
.rxgo .note{font-size:12.5px;color:var(--amber)}
.rxres{margin-top:12px;border:1px solid var(--border);border-radius:10px;padding:10px 12px;font-size:13px}
.rxres.ok{border-color:rgba(16,185,129,.45);background:rgba(16,185,129,.07)}
.rxres.ng{border-color:rgba(239,68,68,.45);background:rgba(239,68,68,.07)}
.rxres .hd{display:flex;align-items:center;gap:8px;font-weight:700;font-size:14px}
.rxres ul{margin:6px 0 0;padding:0;list-style:none}
.rxres li{display:flex;gap:8px;padding:2px 0;align-items:baseline}
.rxres li .s{flex:none;font-size:11.5px;font-weight:700;width:84px}
.rxres li .f{word-break:break-all}
.rxres li .m{color:var(--muted-fg);font-size:12px}
.s-ok{color:var(--emerald)}.s-replaced{color:#c4b5fd}.s-same{color:var(--muted-fg)}.s-busy{color:var(--amber)}.s-err,.s-skip{color:var(--red)}
.rxhist{margin-top:12px;font-size:12.5px;color:var(--muted-fg)}
.rxhist b{color:var(--foreground);font-weight:600}
.rxhist li{padding:2px 0}
.rxhist ul{margin:4px 0 0;padding-left:18px}
.rxempty{display:flex;gap:14px;align-items:center;border:1px dashed var(--border);border-radius:12px;padding:16px;color:var(--muted-fg);font-size:13px;flex-wrap:wrap}
.rxempty>svg{width:22px;height:22px;flex:none}
.rxempty b{display:block;color:var(--foreground);font-size:14px;margin-bottom:2px}
.rxempty>div{flex:1;min-width:200px}
.rxdlg .drv{display:flex;gap:8px;flex-wrap:wrap;margin:12px 0}
.rxdlg .drv .d{display:inline-flex;align-items:center;gap:6px;border:1px solid var(--border);border-radius:10px;padding:6px 6px 6px 10px;font-size:13px}
.rxdlg .drv .d.on{border-color:var(--emerald);background:rgba(16,185,129,.08)}
.rxdlg .drv .d .s{font:11px var(--mono);color:var(--dim)}
.rxdlg .drv .d button{height:28px;padding:0 8px;font-size:12px}
.rxdlg .cur{display:flex;align-items:center;gap:8px;font:12px var(--mono);color:var(--muted-fg);margin:6px 0 8px;word-break:break-all}
.rxdlg .cur button{height:28px;font-size:12px;flex:none}
.rxdlg .lst{border:1px solid var(--border);border-radius:10px;max-height:46vh;overflow:auto}
.rxdlg .lst table{width:100%;border-collapse:collapse;font-size:13px}
.rxdlg .lst td{padding:6px 10px;border-top:1px solid var(--border)}
.rxdlg .lst tr:first-child td{border-top:0}
.rxdlg .lst td.nm{word-break:break-all}
.rxdlg .lst .dirlink{background:none;border:0;box-shadow:none;padding:0;height:auto;color:var(--foreground);font-weight:600;display:inline-flex;gap:6px;cursor:pointer}
.rxdlg .lst .dirlink:hover{color:var(--emerald);background:none}
.rxdlg .lst td.num{text-align:right;color:var(--muted-fg);white-space:nowrap}
.rxdlg .emp{padding:24px;text-align:center;color:var(--muted-fg)}
.rxdlg .grid2 select,.rxdlg .grid2 input{width:100%}
'''

RX_JS = r'''
/* ===================== SW NAS RECEPTION（受付）===================== */
const RX={key:"",tray:null,job:null,poll:0,up:null,strip:true,excl:new Set(),hist:[],res:null,lastJob:"",mine:{},settings:null,data:"",pendSel:null,
  usb:{path:"",parent:null,items:[],sel:new Set(),drives:[]}};
const enc=encodeURIComponent;
/* 受付では自動で切り替えない・テスト通知は使わない */
FOLLOW=false;
(()=>{const s=$("#swFollow");if(s)s.closest("label").style.display="none";const t=$("#bTest");if(t)t.style.display="none"})();
renderBanner=function(){const b=$("#banner");let h="",cls="";
  if(!S.roots.length)h=`受付先のNASフォルダ（学会名フォルダ）がまだ設定されていません。<button class="pri" onclick="openCfg()">設定を開く</button>`;
  const off=S.roots.filter(r=>r.enabled&&r.online===false);
  if(off.length){h=off.map(r=>`⚠ ${esc(nfc(r.label))}: ${esc(r.error)}`).join("　")+(h?"<br>"+h:"");cls="bad"}
  b.innerHTML=h?IC.alert+`<span style="flex:1">${h}</span>`:"";b.className=cls;b.style.display=h?"flex":"none"};
/* 中央：上に受付パネル、下にNASのフォルダの中身 */
(()=>{const f=$("#fold");f.innerHTML='<div id="rxpane"></div><div id="foldbody"></div>';
  const fi=document.createElement("input");fi.type="file";fi.multiple=true;fi.id="rxF";fi.style.display="none";
  const di=document.createElement("input");di.type="file";di.setAttribute("webkitdirectory","");di.id="rxD";di.style.display="none";
  document.body.appendChild(fi);document.body.appendChild(di)})();
const _rf=renderFolder;renderFolder=function(){_rf();rxSync()};
const _rfe=renderFolderEmpty;renderFolderEmpty=function(){_rfe();rxSync()};
const _ra=renderAll;renderAll=function(){_ra();
  if(RX.pendSel){const p=RX.pendSel,r=rootById(p.root);if(r&&(r.groups||[]).some(g=>g.key===p.group)){RX.pendSel=null;selectGroup(p.root,p.group)}}};
const _oe=onEvent;onEvent=function(ev){_oe(ev);const k=ev.root+"|"+ev.group;   /* 自分が書き込んだ変化は既読にする */
  if(RX.mine[k]&&Date.now()-RX.mine[k]<180000&&S.local)api("/api/seen",{root:ev.root,group:ev.group}).then(refresh).catch(()=>{})};
function rxSel(){if(!RX.key)return null;const i=RX.key.indexOf("|");return {root:RX.key.slice(0,i),group:RX.key.slice(i+1)}}
function rxSync(){const k=SEL&&SEL.group?SEL.root+"|"+SEL.group:"";
  if(k!==RX.key||!RX.inited){RX.inited=true;RX.key=k;RX.tray=null;RX.excl=new Set();RX.res=null;RX.hist=[];RX.job=null;renderRx();if(k){rxLoad();rxPoll()}}
  else{rxHead();rxFlagsUpdate()}}
async function rxLoad(){const s=rxSel();if(!s)return;const k=RX.key;
  try{const [t,h]=await Promise.all([api(`/api/rx/tray?root=${enc(s.root)}&group=${enc(s.group)}`),api(`/api/rx/history?root=${enc(s.root)}&group=${enc(s.group)}`)]);
    if(RX.key!==k)return;RX.tray=t;RX.hist=h.items||[]}
  catch(e){if(RX.key===k){RX.tray={files:[],warn:[{lv:"bad",msg:e.message}],total:0}}}
  renderRx()}
function rxWhere(){const s=rxSel();const r=s&&rootById(s.root);if(!r)return"";const p=parts(r,s.group);
  return [p.day,p.venue,p.ses].filter(Boolean).map(x=>esc(nfc(x))).join(" › ")}
function rxStateTag(){const s=rxSel();const r=s&&rootById(s.root);const g=r&&(r.groups||[]).find(x=>x.key===s.group);if(!g)return"";const st=recvState(g);
  return `<span class="rtag ${st}">${stIcon(st)}${STL[st]||""}</span>${flagChips(g)}`}
function rxHead(){const e=$("#rxst");if(e){const h=rxStateTag();if(e.innerHTML!==h)e.innerHTML=h}}
function rxBusy(){return !!(RX.up||(RX.job&&RX.job.state==="run"))}
function renderRx(){const el=$("#rxpane");if(!el)return;
  if(!RX.key){el.innerHTML=`<div class="rxempty">${IC.inbox}<div><b>受付する演者を選んでください</b>左の一覧（または会場ボード）で演者を選ぶと、ここでデータを受け取れます。</div><button data-act="addp">${IC.plus}演者フォルダを追加</button></div><div id="rxleft"></div>`;rxLeftovers();return}
  const s=rxSel();const name=s.group.split("/").pop();const busy=rxBusy();
  let h=`<div class="rxbox"><div class="rxh"><span class="rxt">受付</span><span class="rxn">${esc(nfc(name))}</span><span id="rxst">${rxStateTag()}</span><span class="rxw">${rxWhere()}</span><span style="flex:1"></span><button class="ghost" data-act="addp">${IC.plus}演者フォルダを追加</button></div>`;
  h+=`<div id="rxflags">${rxFlagsHtml()}</div>`;
  h+=`<div class="rxdrop ${busy?"dis":""}" id="rxdrop"><div class="big">${IC.inbox}ここにファイル・フォルダをドロップ</div><div class="sub">USBのフォルダごとドロップしてもOK。いったんこのPCに受け取って中身を確認してから、NASへ書き込みます。</div>
    <div class="btns"><button class="pri" data-act="usb" ${busy?"disabled":""}>${IC.hd}USB・ドライブから取り込む</button><button data-act="pickf" ${busy?"disabled":""}>${IC.file}ファイルを選ぶ</button><button data-act="pickd" ${busy?"disabled":""}>${IC.folder}フォルダを選ぶ</button></div></div>`;
  h+=`<div id="rxprog">${rxProgHtml()}</div>${rxTrayHtml()}${rxResHtml()}${rxHistHtml()}</div>`;
  el.innerHTML=h}
/* まだNASへ入れていないデータが残っている演者（フォルダ名が変わって見えなくなったものも） */
async function rxLeftovers(){let ts=[];try{ts=(await api("/api/rx/trays")).trays}catch(e){return}
  const el=$("#rxleft");if(!el||RX.key)return;if(!ts.length){el.innerHTML="";return}
  el.innerHTML=`<div class="rxhist" style="margin-top:12px"><b>まだNASへ入れていないデータ（トレイに残っているもの）</b><ul>${ts.map(t=>`<li><button class="ghost" data-left-r="${esc(t.root)}" data-left-g="${esc(t.group)}" style="height:26px;font-size:12.5px">${esc(nfc(t.group.split("/").join(" › ")))}</button>　${t.n}ファイル · ${fmtSize(t.size)}${t.exists?"":`　<span style="color:var(--amber)">演者フォルダが見つかりません</span>`}</li>`).join("")}</ul></div>`}
$("#rxpane").addEventListener("click",e=>{const b=e.target.closest("[data-left-g]");if(b)selectGroup(b.dataset.leftR,b.dataset.leftG)});
function rxProgHtml(){
  if(RX.up){const u=RX.up;const pct=u.total?Math.floor(u.done*100/u.total):0;
    return `<div class="rxprog"><div class="l1">${IC.spin}<span class="t">このPCへ受け取り中 ${u.i}/${u.n}：${esc(nfc(u.cur))}</span><button class="ghost" data-act="cancel">中止</button></div><div class="bar"><i style="width:${pct}%"></i></div><div class="l2">${fmtSize(u.done)} / ${fmtSize(u.total)}（${pct}%）${u.who!==RX.key?" · 受付先: "+esc(nfc(u.who.split("/").pop())):""}</div></div>`}
  const j=RX.job;if(!j||j.state!=="run")return"";const pct=j.total?Math.floor(j.done*100/j.total):0;
  const what=j.kind==="commit"?"NASの演者フォルダへ書き込み中":"USB・ドライブから受け取り中";
  const sp=(Date.now()/1000-j.t0)>1?fmtSize(j.done/Math.max(1,Date.now()/1000-j.t0))+"/s":"";
  return `<div class="rxprog"><div class="l1">${IC.spin}<span class="t">${what} ${j.i}/${j.n}：${esc(nfc(j.cur))}</span><button class="ghost" data-act="cancel">中止</button></div><div class="bar"><i style="width:${pct}%"></i></div><div class="l2">${fmtSize(j.done)} / ${fmtSize(j.total)}（${pct}%）${sp?" · "+sp:""}</div></div>`}
function rxProgUpdate(){const e=$("#rxprog");if(e)e.innerHTML=rxProgHtml()}
function rxChips(f){if(f.na)return `<span class="tag t-dim">${esc(f.na)}</span>`;const s=f.sum;if(!s)return"";
  if(s.err)return `<span class="tag t-bad">解析不可</span>`;
  return anaChips({n:1,done:1,err:0,video:s.video,vwarn:s.vbad||0,vfbad:s.vfbad||0,vfwarn:s.vfwarn||0,links:s.links,coi:s.coi?1:0,auto:s.auto,noclick:(s.noclick||0)+(s.kiosk?1:0)})}
function rxTrayHtml(){const t=RX.tray;if(!t)return `<div class="rxtray"><div class="th"><span class="x">読み込み中…</span></div></div>`;
  if(!t.files.length)return t.warn&&t.warn.length?`<ul class="rxwarn">${t.warn.map(w=>`<li class="${w.lv}">${esc(w.msg)}</li>`).join("")}</ul>`:"";
  const strip=!!(t.top&&RX.strip);const busy=rxBusy()||t.busy;const miss=!!t.missing;
  const inc=t.files.filter(f=>!RX.excl.has(f.rel));const size=inc.reduce((a,f)=>a+f.size,0);
  const rep=inc.filter(f=>strip?f.exists_strip:f.exists).length;
  let h=`<div class="rxtray"><div class="th"><b>受け取ったデータ（このPCのトレイ）</b><span class="x">${t.files.length}ファイル · ${fmtSize(t.total)}</span><span style="flex:1"></span><button class="ghost" data-act="clear" ${busy?"disabled":""}>${IC.x}トレイを空にする</button></div><table>`;
  h+=t.files.map(f=>{const off=RX.excl.has(f.rel);const ex=strip?f.exists_strip:f.exists;const shown=strip?f.rel.split("/").slice(1).join("/"):f.rel;
    const segs=shown.split("/");const nm=segs.pop();
    return `<tr class="${off?"off":""}"><td style="width:30px"><input type="checkbox" data-inc="${esc(f.rel)}" ${off?"":"checked"} ${busy?"disabled":""}></td><td class="nm">${segs.length?`<span class="p">${esc(nfc(segs.join("/")))}/</span>`:""}${esc(nfc(nm))}</td><td><span class="chip c-${esc(f.c)}">${esc(f.c)}</span></td><td class="num">${fmtSize(f.size)}</td><td class="tg">${rxChips(f)}${ex?`<span class="tag t-repl" title="NASに同じ名前のファイルがあります。前の版をこのPCに保存してから置き換えます（同じ内容なら書き込みません）">差し替え</span>`:""}</td><td style="width:34px"><button class="ghost rm" data-rm="${esc(f.rel)}" title="トレイから外す" ${busy?"disabled":""}>${IC.x}</button></td></tr>`}).join("");
  h+=`</table>`;
  if(t.warn&&t.warn.length)h+=`<ul class="rxwarn">${t.warn.map(w=>`<li class="${w.lv}">${w.lv==="bad"?"⚠ ":w.lv==="warn"?"! ":"・"}${esc(w.msg)}</li>`).join("")}</ul>`;
  if(miss){const s=rxSel(),r=rootById(s.root);const opts=(r&&r.groups||[]).filter(g=>g.key&&g.key!==s.group).sort((a,b)=>cmpPath(a.key,b.key));
    h+=`<div class="rxgo"><select id="rxMoveTo" style="max-width:420px"><option value="">移す先の演者を選ぶ…</option>${opts.map(g=>`<option value="${esc(g.key)}">${esc(nfc(g.key.split("/").join(" › ")))}</option>`).join("")}</select><button data-act="move" ${busy?"disabled":""}>別の演者へ移す</button></div></div>`;return h}
  h+=`<div class="rxgo"><button class="pri big" data-act="commit" ${busy||!inc.length?"disabled":""}>${IC.check2}${rep?"差し替えて受付する":"受付する"}（NASの演者フォルダへ ${inc.length}ファイル · ${fmtSize(size)}）</button>`;
  if(t.top)h+=`<label title="ドロップしたフォルダの名前を付けずに、中身だけを演者フォルダへ入れます"><input type="checkbox" data-act="strip" ${RX.strip?"checked":""} ${busy?"disabled":""}>「${esc(nfc(t.top))}」フォルダの中身だけ入れる</label>`;
  if(rep)h+=`<span class="note">同じ名前のファイル ${rep}件 は差し替えます（前の版はこのPCに保存）</span>`;
  h+=`</div></div>`;return h}
const RXST={ok:"書き込み済み",replaced:"差し替え済み",same:"同じ内容",busy:"使用中",err:"エラー",skip:"中止"};
function rxResHtml(){const r=RX.res;if(!r)return"";const c=r.count;const bad=c.busy+c.err+c.skip;
  const good=c.ok+c.replaced+c.same;
  let h=`<div class="rxres ${bad?"ng":"ok"}"><div class="hd">${bad?IC.alert:IC.check2}${bad?`${good}件は完了、${bad}件は書き込めませんでした（トレイに残してあります）`:`受付しました：${good}件をNASの演者フォルダへ入れました`}</div><ul>`;
  h+=r.files.map(f=>`<li><span class="s s-${f.st}">${RXST[f.st]||f.st}</span><span class="f">${esc(nfc(f.dest))}</span>${f.msg?`<span class="m">${esc(f.msg)}</span>`:""}</li>`).join("");
  if(r.flag)h+=`<li><span class="s s-ok">目印</span><span class="f">${esc(nfc(r.flag))}</span><span class="m">「受付済」の目印を入れました</span></li>`;
  if(r.flag_skip)h+=`<li><span class="s s-busy">目印</span><span class="f">—</span><span class="m">書き込めなかったファイルがあるため、「受付済」の目印は入れていません</span></li>`;
  return h+`</ul></div>`}
function rxHistHtml(){const hs=(RX.hist||[]).filter(x=>x.count);if(!hs.length)return"";
  return `<div class="rxhist"><b>この演者の受付履歴</b><ul>${hs.slice(0,8).map(x=>{const c=x.count||{};const n=(c.ok||0)+(c.replaced||0);
    return `<li>${dtm(x.ts)}　${esc(x.pc||"")}　${n}件${c.replaced?`（差し替え${c.replaced}）`:""}${c.busy||c.err?`　<span style="color:var(--amber)">未完了 ${(c.busy||0)+(c.err||0)}</span>`:""}${x.flag?`　目印「${esc(nfc(x.flag))}」`:""}</li>`}).join("")}</ul></div>`}
/* ---- 目印画像（現場の 00_受付済.jpg などをそのままコピーして付ける・外す） */
function rxFolderFlags(){const s=rxSel();if(!s||!F||F.root!==s.root||F.group!==s.group)return null;
  return (F.items||[]).filter(i=>i.mk&&!i.d&&!i.p.includes("/"))}
function rxFlagsHtml(){const fl=RX.flags;const pres=rxFolderFlags();if(!fl)return"";
  if(!fl.dir)return `<div class="rxflags none"><span class="lb">目印</span><span class="hint" style="margin:0">［設定］→「受付」で目印画像のフォルダ（00_受付済.jpg などの元画像）を指定すると、ここから目印を付けられます</span></div>`;
  if(fl.error)return `<div class="rxflags none"><span class="lb">目印</span><span style="color:var(--amber)">${esc(fl.error)}</span></div>`;
  const on=new Map();(pres||[]).forEach(i=>{if(!on.has(i.ml))on.set(i.ml,[]);on.get(i.ml).push(i.p)});
  const busy=RX.flagBusy||pres===null;
  let h=fl.templates.filter(t=>t.ok).map(t=>{const has=on.has(t.label);
    return `<button class="fb ${has?"on":""} r-${esc(t.role)}" ${busy?"disabled":""} ${has?`data-unflag="${esc(t.label)}" title="NASの演者フォルダから「${esc(nfc(on.get(t.label).join("、")))}」を消します（データは消しません）"`:`data-flag="${esc(t.name)}" title="「${esc(nfc(t.name))}」を演者フォルダへ入れます"`}>${has?IC.chk:""}${esc(nfc(t.label))}</button>`}).join("");
  const known=new Set(fl.templates.filter(t=>t.ok).map(t=>t.label));
  h+=[...on.keys()].filter(l=>!known.has(l)).map(l=>`<button class="fb on" ${busy?"disabled":""} data-unflag="${esc(l)}" title="NASの演者フォルダから「${esc(nfc(on.get(l).join("、")))}」を消します">${IC.chk}${esc(nfc(l))}</button>`).join("");
  const bad=fl.templates.filter(t=>!t.ok);
  return `<div class="rxflags"><span class="lb">目印</span>${h}${bad.length?`<span class="hint" style="margin:0" title="${esc(bad.map(t=>t.name).join("、"))}">（目印として認識されない画像 ${bad.length}件：［設定］→「目印のファイル」に文字を追加すると使えます）</span>`:""}</div>`}
function rxFlagsUpdate(){const e=$("#rxflags");if(e){const h=rxFlagsHtml();if(e.innerHTML!==h)e.innerHTML=h}}
async function rxLoadFlags(){try{RX.flags=await api("/api/rx/flags")}catch(e){RX.flags={dir:"",templates:[],error:e.message}}rxFlagsUpdate()}
rxLoadFlags();
$("#rxpane").addEventListener("click",async e=>{const b=e.target.closest("[data-flag],[data-unflag]");if(!b)return;const s=rxSel();if(!s)return;
  e.stopPropagation();
  if(b.dataset.flag){RX.flagBusy=true;rxFlagsUpdate();
    try{const j=await api("/api/rx/flag",{root:s.root,group:s.group,name:b.dataset.flag});toast(j.added?`目印「${nfc(j.added)}」を入れました`:`同じ目印がすでにあります（${nfc(j.exists||"")}）`,3500)}
    catch(err){toast(err.message,6000)}
    RX.flagBusy=false;refresh();return}
  const names=(rxFolderFlags()||[]).filter(i=>i.ml===b.dataset.unflag).map(i=>i.p);if(!names.length)return;
  if(!confirm(`目印「${nfc(b.dataset.unflag)}」を外します。\nNASの演者フォルダから ${names.map(nfc).join("、")} を削除します（データは消しません）。`))return;
  RX.flagBusy=true;rxFlagsUpdate();
  try{const j=await api("/api/rx/unflag",{root:s.root,group:s.group,names});toast(`目印を外しました（${j.removed.map(nfc).join("、")}）`,3500)}
  catch(err){toast(err.message,6000)}
  RX.flagBusy=false;refresh()},true);
/* ---- 受け取り（ブラウザから） */
function rxFilterList(list){return list.filter(x=>{const n=x.file.name;return !/^(\.ds_store|thumbs\.db|desktop\.ini)$/i.test(n)&&!n.startsWith("._")&&!n.startsWith("~$")})}
function upOne(s,file,rel,onp){return new Promise((res,rej)=>{const x=new XMLHttpRequest();RX.xhr=x;
  x.open("POST",`/api/rx/upload?root=${enc(s.root)}&group=${enc(s.group)}&path=${enc(rel)}`);x.setRequestHeader("X-SW-Token",TOKEN);
  x.upload.onprogress=e=>onp(e.loaded);
  x.onload=()=>{let j={};try{j=JSON.parse(x.responseText)}catch(e){}if(x.status===200)res(j);else rej(new Error(j.error||("HTTP "+x.status)))};
  x.onerror=()=>rej(new Error("送れませんでした"));x.onabort=()=>rej(new Error("中止しました"));x.send(file)})}
async function rxUpload(list){
  if(!RX.key){toast("先に演者を選んでください");return}
  if(rxBusy()){toast("受け取り・書き込みの途中です");return}
  list=rxFilterList(list);if(!list.length){toast("受け取るファイルがありません");return}
  const s=rxSel();const total=list.reduce((a,x)=>a+x.file.size,0);
  RX.up={i:0,n:list.length,done:0,total,cur:"",who:RX.key,cancel:false};RX.res=null;renderRx();
  let base=0;const errs=[];
  for(const [i,x] of list.entries()){if(RX.up.cancel)break;RX.up.i=i+1;RX.up.cur=x.rel;rxProgUpdate();
    try{await upOne(s,x.file,x.rel,l=>{RX.up.done=base+l;rxProgUpdate()})}
    catch(e){if(RX.up.cancel)break;errs.push(x.rel+"："+e.message)}     // 1つ受け取れなくても、残りは続ける
    base+=x.file.size;RX.up.done=base}
  const who=RX.up.who,canceled=RX.up.cancel;RX.up=null;
  if(errs.length)toast(`${errs.length}件を受け取れませんでした：${errs.slice(0,3).join(" / ")}${errs.length>3?" ほか":""}`,9000);
  else if(canceled)toast("中止しました",3000);
  if(RX.key===who)await rxLoad();else renderRx()}
async function collectDrop(dt){
  const ents=[...dt.items].filter(i=>i.kind==="file").map(i=>i.webkitGetAsEntry?i.webkitGetAsEntry():null);
  const files=[...dt.files];const out=[];
  if(!ents.length||ents.some(e=>!e)){files.forEach(f=>out.push({file:f,rel:f.name}));return out}
  async function walk(e,pre){
    if(e.isFile){const f=await new Promise((ok,ng)=>e.file(ok,ng));out.push({file:f,rel:pre+e.name})}
    else if(e.isDirectory){const rd=e.createReader();let batch;do{batch=await new Promise((ok,ng)=>rd.readEntries(ok,ng));for(const c of batch)await walk(c,pre+e.name+"/")}while(batch.length)}}
  for(const e of ents)await walk(e,"");return out}
["dragover","drop"].forEach(t=>window.addEventListener(t,e=>{e.preventDefault()}));   /* ドロップでページが開いてしまわないように */
let dragN=0;
$("#center").addEventListener("dragenter",e=>{if(!RX.key)return;dragN++;$("#center").classList.add("dragging")});
$("#center").addEventListener("dragleave",()=>{dragN=Math.max(0,dragN-1);if(!dragN)$("#center").classList.remove("dragging")});
$("#center").addEventListener("drop",e=>{e.preventDefault();dragN=0;$("#center").classList.remove("dragging");
  if(!RX.key){toast("先に左の一覧で演者を選んでください",4000);return}
  const p=collectDrop(e.dataTransfer);p.then(rxUpload).catch(err=>toast("読み込めませんでした: "+err.message,6000))});
$("#rxF").addEventListener("change",e=>{const l=[...e.target.files].map(f=>({file:f,rel:f.name}));e.target.value="";rxUpload(l)});
$("#rxD").addEventListener("change",e=>{const l=[...e.target.files].map(f=>({file:f,rel:f.webkitRelativePath||f.name}));e.target.value="";rxUpload(l)});
/* ---- 仕事（USBからの取り込み・NASへの書き込み）の進み具合 */
async function rxPoll(){clearTimeout(RX.poll);const s=rxSel();if(!s)return;const k=RX.key;
  let j=null;try{j=(await api(`/api/rx/job?root=${enc(s.root)}&group=${enc(s.group)}`)).job}catch(e){}
  if(RX.key!==k)return;
  const was=RX.job&&RX.job.state==="run";RX.job=j;
  if(j&&j.state==="run"){if(!was)renderRx();else rxProgUpdate();RX.poll=setTimeout(rxPoll,400);return}
  if(j&&j.state==="done"&&j.id!==RX.lastJob&&was){RX.lastJob=j.id;
    if(j.kind==="commit"&&j.result){RX.res=j.result;RX.mine[k]=Date.now();RX.excl=new Set();refresh()}
    if(j.errors&&j.errors.length)toast(j.errors.slice(0,3).join(" / "),7000);
    await rxLoad();return}
  if(was)renderRx()}
async function rxStart(path,body){try{const j=(await api(path,body)).job;RX.job=j;RX.lastJob="";renderRx();rxPoll()}catch(e){toast(e.message,7000)}}
/* ---- 受付パネルの操作 */
$("#rxpane").addEventListener("click",async e=>{const b=e.target.closest("[data-act],[data-rm]");if(!b)return;const s=rxSel();
  if(b.dataset.rm){try{await api("/api/rx/remove",{root:s.root,group:s.group,rels:[b.dataset.rm]});RX.excl.delete(b.dataset.rm);await rxLoad()}catch(err){toast(err.message,5000)}return}
  const a=b.dataset.act;
  if(a==="addp")return rxAddOpen();
  if(!s)return;
  if(a==="usb")return rxUsbOpen();
  if(a==="pickf")return $("#rxF").click();
  if(a==="pickd")return $("#rxD").click();
  if(a==="cancel"){if(RX.up){RX.up.cancel=true;if(RX.xhr)RX.xhr.abort()}else api("/api/rx/cancel",{root:s.root,group:s.group}).catch(()=>{});return}
  if(a==="clear"){try{await api("/api/rx/remove",{root:s.root,group:s.group,all:true});RX.excl=new Set();RX.res=null;await rxLoad()}catch(err){toast(err.message,5000)}return}
  if(a==="move"){const to=$("#rxMoveTo")&&$("#rxMoveTo").value;if(!to){toast("移す先の演者を選んでください");return}
    try{await api("/api/rx/move",{root:s.root,group:s.group,to});toast("移しました",3000);selectGroup(s.root,to)}catch(err){toast(err.message,6000)}return}
  if(a==="commit"){RX.res=null;const t=RX.tray;rxStart("/api/rx/commit",{root:s.root,group:s.group,strip_top:!!(t&&t.top&&RX.strip),exclude:[...RX.excl]})}});
$("#rxpane").addEventListener("change",e=>{const c=e.target;
  if(c.dataset.inc!==undefined){if(c.checked)RX.excl.delete(c.dataset.inc);else RX.excl.add(c.dataset.inc);renderRx();return}
  if(c.dataset.act==="strip"){RX.strip=c.checked;renderRx()}});
/* ---- USB・ドライブから取り込む */
async function rxUsbOpen(){if(!RX.key){toast("先に演者を選んでください");return}
  RX.usb.sel=new Set();RX.usb.items=[];RX.usb.path="";await rxDrives();
  if(RX.usb.drives.length===1)await rxBrowse(RX.usb.drives[0].path,true);
  rxUsbRender();$("#modal").classList.add("open")}
async function rxDrives(){try{RX.usb.drives=(await api("/api/rx/drives")).drives}catch(e){RX.usb.drives=[];toast(e.message,5000)}}
async function rxBrowse(p,quiet){try{const j=await api("/api/rx/browse?path="+enc(p));RX.usb.path=j.path;RX.usb.parent=j.parent;RX.usb.items=j.items;RX.usb.sel=new Set()}catch(e){toast(e.message,5000)}if(!quiet)rxUsbRender()}
function rxUsbRender(){const u=RX.usb;const s=rxSel();if(!s)return;
  const drv=u.drives.length?u.drives.map(d=>`<span class="d ${u.path&&u.path.startsWith(d.path)?"on":""}"><button class="ghost" data-u="drv" data-p="${esc(d.path)}">${IC.hd}${esc(d.name)}</button><span class="s">${esc(d.type)} · 空き ${fmtSize(d.free)}</span>${d.eject?`<button class="ghost" data-u="eject" data-p="${esc(d.path)}" title="安全に取り外す">取り出す</button>`:""}</span>`).join(""):`<span class="emp" style="padding:4px 0">USBメモリ・ドライブが見つかりません（差し込んだら［更新］）</span>`;
  let list="";
  if(u.path){const items=u.items;
    list=items.length?`<table>${items.map(it=>`<tr><td style="width:30px"><input type="checkbox" data-pick="${esc(it.path)}" ${u.sel.has(it.path)?"checked":""}></td><td class="nm">${it.dir?`<button class="dirlink" data-u="enter" data-p="${esc(it.path)}">${IC.folder}${esc(nfc(it.name))}</button>`:esc(nfc(it.name))}</td><td>${it.dir?"":`<span class="chip c-${esc(it.c)}">${esc(it.c)}</span>`}</td><td class="num">${it.dir?"":fmtSize(it.size)}</td><td class="num">${dtm(it.m)}</td></tr>`).join("")}</table>`:`<div class="emp">空のフォルダです</div>`}
  else list=`<div class="emp">上のドライブを選んでください</div>`;
  $("#modal").innerHTML=`<div class="dlg rxdlg"><h2>USB・ドライブから取り込む</h2><p class="desc">受付先：<b>${esc(nfc(s.group.split("/").pop()))}</b>　（いったんこのPCのトレイに受け取ります。NASへはまだ書き込みません）</p>
    <div class="drv">${drv}<span style="flex:1"></span><button class="ghost" data-u="reload">更新</button><button class="ghost" data-u="pickdir">フォルダを指定…</button></div>
    ${u.path?`<div class="cur">${u.parent?`<button class="ghost" data-u="enter" data-p="${esc(u.parent)}">↑ 上へ</button>`:""}<span>${esc(nfc(u.path))}</span></div>`:""}
    <div class="lst">${list}</div>
    <div class="foot"><span class="hint" style="margin:0">${u.sel.size?`${u.sel.size}件を選択中`:"取り込むファイル・フォルダにチェック"}</span><span style="display:flex;gap:8px"><button data-u="close">閉じる</button>${u.path?`<button data-u="all" title="いま開いているフォルダを、フォルダごと取り込みます">このフォルダごと</button>`:""}<button class="pri" data-u="imp" ${u.sel.size?"":"disabled"}>選んだものをトレイに入れる</button></span></div></div>`}
$("#modal").addEventListener("click",async e=>{if(!e.target.closest(".rxdlg"))return;const b=e.target.closest("[data-u]");if(!b)return;const u=RX.usb,s=rxSel(),a=b.dataset.u;
  if(a==="close")return closeCfg();
  if(a==="drv"||a==="enter")return rxBrowse(b.dataset.p);
  if(a==="reload"){await rxDrives();return rxUsbRender()}
  if(a==="pickdir"){try{const j=await api("/api/rx/pickdir",{});if(j.path)await rxBrowse(j.path)}catch(err){toast(err.message,5000)}return}
  if(a==="eject"){try{const j=await api("/api/rx/eject",{path:b.dataset.p});toast(j.msg||"取り出しました",5000);if(j.ok&&u.path.startsWith(b.dataset.p)){u.path="";u.items=[];u.sel=new Set()}}catch(err){toast(err.message,6000)}await rxDrives();return rxUsbRender()}
  if(a==="imp"||a==="all"){const paths=a==="all"?[u.path]:[...u.sel];if(!paths.length||!s)return;closeCfg();RX.res=null;rxStart("/api/rx/import",{root:s.root,group:s.group,paths})}});
$("#modal").addEventListener("change",e=>{const c=e.target;if(!c.closest(".rxdlg")||c.dataset.pick===undefined)return;
  if(c.checked)RX.usb.sel.add(c.dataset.pick);else RX.usb.sel.delete(c.dataset.pick);
  const f=$("#modal .rxdlg .foot .hint");if(f)f.textContent=RX.usb.sel.size?`${RX.usb.sel.size}件を選択中`:"取り込むファイル・フォルダにチェック";
  const bt=$('#modal [data-u="imp"]');if(bt)bt.disabled=!RX.usb.sel.size});
/* ---- 演者フォルダを追加 */
async function rxAddOpen(){if(!S||!S.roots.length){toast("先に［設定］で受付先を追加してください");return}
  const s=rxSel();const rid=s?s.root:(SEL&&SEL.root)||S.roots[0].id;
  let ses=[];try{ses=(await api("/api/rx/sessions?root="+enc(rid))).sessions}catch(e){toast(e.message,5000);return}
  const cur=s?s.group.split("/").slice(0,-1).join("/"):"";
  const r=rootById(rid);
  $("#modal").innerHTML=`<div class="dlg rxdlg" style="width:min(620px,100%)"><h2>演者フォルダを追加</h2><p class="desc">NASのセッションフォルダの中に、演者のフォルダを作ります（NASへ書き込みます）。</p>
    <div class="grid2" style="margin-top:16px">${S.roots.length>1?`<span>受付先</span><select id="rxaRoot">${S.roots.map(x=>`<option value="${esc(x.id)}" ${x.id===rid?"selected":""}>${esc(nfc(x.label))}</option>`).join("")}</select>`:""}
    <span>セッション</span>${ses.length&&ses[0]!==""?`<select id="rxaSes">${ses.map(x=>`<option value="${esc(x)}" ${x===cur?"selected":""}>${esc(nfc(x.split("/").join(" › ")))}</option>`).join("")}</select>`:`<span class="hint" style="margin:0">${r&&r.depth>1?"セッションのフォルダがありません":"監視フォルダの直下に作ります"}</span><input type="hidden" id="rxaSes" value="">`}
    <span>フォルダ名</span><input type="text" id="rxaName" placeholder="例: 012_架空演者" autocomplete="off"></div>
    <p class="hint">\\ / : * ? " &lt; &gt; | は使えません。</p>
    <div class="foot"><span></span><span style="display:flex;gap:8px"><button data-u="close">キャンセル</button><button class="pri" id="rxaGo">作成</button></span></div></div>`;
  $("#modal").classList.add("open");setTimeout(()=>{const n=$("#rxaName");if(n)n.focus()},50);
  const rs=$("#rxaRoot");if(rs)rs.onchange=()=>{closeCfg();SEL={root:rs.value,group:""};rxAddOpen()};
  $("#rxaGo").onclick=async()=>{const name=$("#rxaName").value.trim();if(!name){toast("フォルダ名を入れてください");return}
    try{const j=await api("/api/rx/mkdir",{root:rid,parent:$("#rxaSes").value,name});closeCfg();toast("作成しました: "+name,4000);RX.pendSel={root:rid,group:j.group};refresh()}
    catch(e){toast(e.message,6000)}}}
/* ---- 設定：受付の設定を足す（会場オペレーターの設定は SW NAS OPERATOR だけに出る） */
api("/api/rx/settings").then(j=>{RX.settings=j.settings;RX.data=j.data_dir}).catch(()=>{});
const _rcfg=renderCfg;renderCfg=function(){_rcfg();
  const foot=$("#modal .foot");const st=RX.settings||{verify:true,keep_local:true,pc_name:"",flag_dir:"",auto_recv:true};
  if(foot&&!$("#rxSet")){const d=document.createElement("div");d.id="rxSet";
    d.innerHTML=`<h3>受付</h3><div class="checks" style="flex-direction:column;gap:8px">
      <label><input type="checkbox" id="rxVerify" ${st.verify?"checked":""}>NASへ書き込んだあと、読み直して内容を照合する（おすすめ）</label>
      <label><input type="checkbox" id="rxKeep" ${st.keep_local?"checked":""}>受け取ったデータと、差し替える前の版をこのPCにも残す（おすすめ。オフのときは差し替え前の版を残さずに置き換えます）</label></div>
      <div class="grid2" style="margin-top:10px"><span>受付PCの名前</span><input type="text" id="rxPc" value="${esc(st.pc_name||"")}" placeholder="例: 受付1"></div>
      <p class="hint">受付履歴に記録されます。保存先: <span class="mono">${esc(RX.data||"")}</span>（received＝受け取ったデータ、backup＝差し替え前の版）</p>
      <div class="grid2" style="margin-top:10px"><span>目印画像のフォルダ</span><span style="display:flex;gap:6px;min-width:0"><input type="text" id="rxFlagDir" value="${esc(st.flag_dir||"")}" placeholder="例: \\\\192.168.0.10\\share\\目印" style="flex:1;min-width:0"><button class="ghost" id="rxFlagPick" type="button">選ぶ…</button></span></div>
      <p class="hint">現場で使っている目印の元画像（00_受付済.jpg 〜 18_発表終了.jpg など）を入れたフォルダを指定すると、受付パネルから目印を付けたり外したりできます。画像はそのままコピーします（アプリが画像を作ることはありません）。</p>
      <div class="checks" style="flex-direction:column;gap:8px;margin-top:6px"><label><input type="checkbox" id="rxAuto" ${st.auto_recv!==false?"checked":""}>受付したとき、「受付済」の目印画像を演者フォルダへ入れる（フォルダだけで確認している人にも受付済みが分かるように。すでに受付済・会場取得・発表終了の目印があれば入れません）</label></div>`;
    foot.parentNode.insertBefore(d,foot);
    $("#rxFlagPick").onclick=async()=>{try{const j=await api("/api/rx/pickdir",{});if(j.path)$("#rxFlagDir").value=j.path}catch(e){toast(e.message,5000)}}}};
const _sc=saveCfg;saveCfg=async function(){
  if($("#rxVerify")){try{const j=await api("/api/rx/settings",{verify:$("#rxVerify").checked,keep_local:$("#rxKeep").checked,pc_name:$("#rxPc").value.trim(),
      flag_dir:$("#rxFlagDir").value.trim().replace(/^"|"$/g,""),auto_recv:$("#rxAuto").checked});RX.settings=j.settings}
    catch(e){const c=$("#cerr");if(c)c.textContent=e.message;else toast(e.message,5000);return}}
  const r=await _sc();rxLoadFlags();return r};
'''

if __name__ == "__main__":
    main()
