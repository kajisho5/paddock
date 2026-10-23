/* RECEPTION：受付パネル（演者を選ぶと、ここでデータを受け取って NAS の演者フォルダへ入れる） */
import { useEffect, useRef, useState } from "react";
import { api, enc } from "../api";
import { refresh, rootById, selectGroup, store, toast, useApp } from "../store";
import { parts, recvState } from "../lib/layout";
import { cmpPath, cx, dtm, fmtSize, nfc } from "../lib/util";
import { AnaChips, FlagChips, StateTag, Tag } from "../components/Bits";
import { Icon } from "../components/Icons";
import { Modal } from "../components/Modal";
import { collectDrop, RX, rxBusy, rxLoad, rxSel, rxStart, rxSync, rxUpload, type TrayFile } from "./rxState";
import { Bar } from "../design/ui";

export function RxPanel() {
  useApp();
  rxSync();
  const fileRef = useRef<HTMLInputElement>(null), dirRef = useRef<HTMLInputElement>(null);
  const [left, setLeft] = useState<any[] | null>(null);
  // ドロップ（中央の画面全体で受ける）
  useEffect(() => {
    const c = document.getElementById("center"); if (!c) return; let n = 0;
    const en = () => { if (!RX.key) return; n++; c.classList.add("dragging"); };
    const lv = () => { n = Math.max(0, n - 1); if (!n) c.classList.remove("dragging"); };
    const dr = (e: DragEvent) => {
      e.preventDefault(); n = 0; c.classList.remove("dragging");
      if (!RX.key) { toast("先に左の一覧で演者を選んでください", 4000); return; }
      collectDrop(e.dataTransfer!).then(rxUpload).catch((err) => toast("読み込めませんでした: " + err.message, 6000));
    };
    c.addEventListener("dragenter", en); c.addEventListener("dragleave", lv); c.addEventListener("drop", dr);
    return () => { c.removeEventListener("dragenter", en); c.removeEventListener("dragleave", lv); c.removeEventListener("drop", dr); };
  }, []);
  useEffect(() => { if (!RX.key) api<any>("/api/rx/trays").then((j) => setLeft(j.trays)).catch(() => {}); }, [RX.key]);
  const inputs = <>
    <input ref={fileRef} type="file" multiple id="rxF" style={{ display: "none" }} onChange={(e) => { const l = [...(e.target.files || [])].map((f) => ({ file: f, rel: f.name })); e.target.value = ""; rxUpload(l); }} />
    <input ref={dirRef} type="file" id="rxD" style={{ display: "none" }} {...({ webkitdirectory: "" } as any)} onChange={(e) => { const l = [...(e.target.files || [])].map((f) => ({ file: f, rel: (f as any).webkitRelativePath || f.name })); e.target.value = ""; rxUpload(l); }} />
  </>;
  if (!RX.key) return <div id="rxpane">{inputs}
    <div className="rxempty"><Icon n="inbox" /><div><b>受付する演者を選んでください</b>左の一覧（または会場ボード）で演者を選ぶと、ここでデータを受け取れます。</div><button onClick={() => rxAddOpen()}><Icon n="plus" />演者フォルダを追加</button></div>
    {left && left.length > 0 && <div className="rxhist" style={{ marginTop: 12 }}><b>まだNASへ入れていないデータ（トレイに残っているもの）</b><ul>{left.map((t, i) =>
      <li key={i}><button className="ghost" style={{ height: 26, fontSize: 12.5 }} onClick={() => selectGroup(t.root, t.group)}>{nfc(t.group.split("/").join(" › "))}</button>　{t.n}ファイル · {fmtSize(t.size)}{!t.exists && <span className="amber">　演者フォルダが見つかりません</span>}</li>)}</ul></div>}
  </div>;
  const sel = rxSel()!; const name = sel.group.split("/").pop(); const busy = rxBusy();
  const r = rootById(sel.root); const g = r && (r.groups || []).find((x) => x.key === sel.group);
  const p = r ? parts(r, sel.group) : null;
  return <div id="rxpane">{inputs}<div className="rxbox">
    <div className="rxh"><span className="rxt">受付</span><span className="rxn">{nfc(name)}</span>
      <span id="rxst">{g && <><StateTag st={recvState(g)} /><FlagChips g={g} /></>}</span>
      <span className="rxw">{p ? [p.day, p.venue, p.ses].filter(Boolean).map((x) => nfc(x)).join(" › ") : ""}</span><span style={{ flex: 1 }} />
      <button className="ghost" onClick={() => rxAddOpen()}><Icon n="plus" />演者フォルダを追加</button></div>
    <RxFlags />
    <div className={cx("rxdrop", busy && "dis")} id="rxdrop"><div className="big"><Icon n="inbox" />ここにファイル・フォルダをドロップ</div>
      <div className="sub">USBのフォルダごとドロップしてもOK。いったんこのPCに受け取って中身を確認してから、NASへ書き込みます。</div>
      <div className="btns"><button className="pri" disabled={busy} onClick={rxUsbOpen}><Icon n="hd" />USB・ドライブから取り込む</button>
        <button disabled={busy} onClick={() => fileRef.current?.click()}><Icon n="file" />ファイルを選ぶ</button>
        <button disabled={busy} onClick={() => dirRef.current?.click()}><Icon n="folder" />フォルダを選ぶ</button></div></div>
    <div id="rxprog"><RxProg /></div><RxTray key={RX.key} /><RxRes /><RxHist />
  </div></div>;
}
function cancel() { const s = rxSel(); if (RX.up) { RX.up.cancel = true; if (RX.xhr) RX.xhr.abort(); } else if (s) api("/api/rx/cancel", { root: s.root, group: s.group }).catch(() => {}); }
function RxProg() {
  if (RX.up) {
    const u = RX.up; const pct = u.total ? Math.floor((u.done * 100) / u.total) : 0;
    return <div className="rxprog"><div className="l1"><Icon n="spin" className="spin" /><span className="t">このPCへ受け取り中 {u.i}/{u.n}：{nfc(u.cur)}</span><button className="ghost" onClick={cancel}>中止</button></div>
      <Bar pct={pct} className="bar block" /><div className="l2">{fmtSize(u.done)} / {fmtSize(u.total)}（{pct}%）{u.who !== RX.key ? " · 受付先: " + nfc(u.who.split("/").pop()) : ""}</div></div>;
  }
  const j = RX.job; if (!j || j.state !== "run") return null; const pct = j.total ? Math.floor((j.done * 100) / j.total) : 0;
  const what = j.kind === "commit" ? "NASの演者フォルダへ書き込み中" : "USB・ドライブから受け取り中";
  const el = Date.now() / 1000 - j.t0; const sp = el > 1 ? fmtSize(j.done / Math.max(1, el)) + "/s" : "";
  return <div className="rxprog"><div className="l1"><Icon n="spin" className="spin" /><span className="t">{what} {j.i}/{j.n}：{nfc(j.cur)}</span><button className="ghost" onClick={cancel}>中止</button></div>
    <Bar pct={pct} className="bar block" /><div className="l2">{fmtSize(j.done)} / {fmtSize(j.total)}（{pct}%）{sp ? " · " + sp : ""}</div></div>;
}
function RxChips({ f }: { f: TrayFile }) {
  if (f.na) return <Tag t="dim">{f.na}</Tag>; const s = f.sum; if (!s) return null;
  if (s.err) return <Tag t="bad">解析不可</Tag>;
  return <AnaChips a={{ n: 1, done: 1, err: 0, video: s.video, vwarn: s.vbad || 0, vfbad: s.vfbad || 0, vfwarn: s.vfwarn || 0, abad: 0, links: s.links, coi: s.coi ? 1 : 0, auto: s.auto, noclick: (s.noclick || 0) + (s.kiosk ? 1 : 0) }} />;
}
function RxTray() {
  const t = RX.tray; const sel = rxSel()!;
  const [to, setTo] = useState("");
  if (!t) return <div className="rxtray"><div className="th"><span className="x">読み込み中…</span></div></div>;
  if (!t.files.length) return t.warn && t.warn.length ? <ul className="rxwarn">{t.warn.map((w, i) => <li key={i} className={w.lv}>{w.msg}</li>)}</ul> : null;
  const strip = !!(t.top && RX.strip); const busy = rxBusy() || !!t.busy; const miss = !!t.missing;
  const inc = t.files.filter((f) => !RX.excl.has(f.rel)); const size = inc.reduce((a, f) => a + f.size, 0);
  const rep = inc.filter((f) => (strip ? f.exists_strip : f.exists)).length;
  const r = rootById(sel.root);
  return <div className="rxtray"><div className="th"><b>受け取ったデータ（このPCのトレイ）</b><span className="x">{t.files.length}ファイル · {fmtSize(t.total)}</span><span style={{ flex: 1 }} />
    <button className="ghost" disabled={busy} onClick={async () => { try { await api("/api/rx/remove", { root: sel.root, group: sel.group, all: true }); RX.excl = new Set(); RX.res = null; await rxLoad(); } catch (e: any) { toast(e.message, 5000); } }}><Icon n="x" />トレイを空にする</button></div>
    <table><tbody>{t.files.map((f) => {
      const off = RX.excl.has(f.rel); const ex = strip ? f.exists_strip : f.exists; const shown = strip ? f.rel.split("/").slice(1).join("/") : f.rel;
      const segs = shown.split("/"); const nm = segs.pop();
      return <tr key={f.rel} className={off ? "off" : ""}>
        <td style={{ width: 30 }}><input type="checkbox" checked={!off} disabled={busy} onChange={(e) => { if (e.target.checked) RX.excl.delete(f.rel); else RX.excl.add(f.rel); store.emit(); }} /></td>
        <td className="nm">{segs.length > 0 && <span className="p">{nfc(segs.join("/"))}/</span>}{nfc(nm)}</td><td><span className={"chip c-" + f.c}>{f.c}</span></td><td className="num">{fmtSize(f.size)}</td>
        <td className="tg"><RxChips f={f} />{ex && <Tag t="repl" title="NASに同じ名前のファイルがあります。前の版をこのPCに保存してから置き換えます（同じ内容なら書き込みません）">差し替え</Tag>}</td>
        <td style={{ width: 34 }}><button className="ghost rm icon" title="トレイから外す" disabled={busy} onClick={async () => { try { await api("/api/rx/remove", { root: sel.root, group: sel.group, rels: [f.rel] }); RX.excl.delete(f.rel); await rxLoad(); } catch (e: any) { toast(e.message, 5000); } }}><Icon n="x" /></button></td></tr>;
    })}</tbody></table>
    {t.warn && t.warn.length > 0 && <ul className="rxwarn">{t.warn.map((w, i) => <li key={i} className={w.lv}>{w.lv === "bad" ? "⚠ " : w.lv === "warn" ? "! " : "・"}{w.msg}</li>)}</ul>}
    {miss ? <div className="rxgo"><select id="rxMoveTo" style={{ maxWidth: 420 }} value={to} onChange={(e) => setTo(e.target.value)}><option value="">移す先の演者を選ぶ…</option>
      {(r && r.groups || []).filter((g) => g.key && g.key !== sel.group).sort((a, b) => cmpPath(a.key, b.key)).map((g) => <option key={g.key} value={g.key}>{nfc(g.key.split("/").join(" › "))}</option>)}</select>
      <button disabled={busy} onClick={async () => { if (!to) { toast("移す先の演者を選んでください"); return; } try { await api("/api/rx/move", { root: sel.root, group: sel.group, to }); toast("移しました", 3000); selectGroup(sel.root, to); } catch (e: any) { toast(e.message, 6000); } }}>別の演者へ移す</button></div>
      : <div className="rxgo"><button className="pri big" disabled={busy || !inc.length} onClick={() => { RX.res = null; rxStart("/api/rx/commit", { root: sel.root, group: sel.group, strip_top: !!(t.top && RX.strip), exclude: [...RX.excl] }); }}>
        <Icon n="check2" />{rep ? "差し替えて受付する" : "受付する"}（NASの演者フォルダへ {inc.length}ファイル · {fmtSize(size)}）</button>
        {t.top && <label title="ドロップしたフォルダの名前を付けずに、中身だけを演者フォルダへ入れます"><input type="checkbox" checked={RX.strip} disabled={busy} onChange={(e) => { RX.strip = e.target.checked; store.emit(); }} />「{nfc(t.top)}」フォルダの中身だけ入れる</label>}
        {rep > 0 && <span className="note">同じ名前のファイル {rep}件 は差し替えます（前の版はこのPCに保存）</span>}</div>}
  </div>;
}
const RXST: Record<string, string> = { ok: "書き込み済み", replaced: "差し替え済み", same: "同じ内容", busy: "使用中", err: "エラー", skip: "中止" };
function RxRes() {
  const r = RX.res; if (!r) return null; const c = r.count; const bad = c.busy + c.err + c.skip; const good = c.ok + c.replaced + c.same;
  return <div className={cx("rxres", bad ? "ng" : "ok")}><div className="hd"><Icon n={bad ? "alert" : "check2"} />{bad ? `${good}件は完了、${bad}件は書き込めませんでした（トレイに残してあります）` : `受付しました：${good}件をNASの演者フォルダへ入れました`}</div><ul>
    {r.files.map((f: any, i: number) => <li key={i}><span className={"s s-" + f.st}>{RXST[f.st] || f.st}</span><span className="f">{nfc(f.dest)}</span>{f.msg && <span className="m">{f.msg}</span>}</li>)}
    {r.flag && <li><span className="s s-ok">目印</span><span className="f">{nfc(r.flag)}</span><span className="m">「受付済」の目印を入れました</span></li>}
    {r.flag_skip && <li><span className="s s-busy">目印</span><span className="f">—</span><span className="m">書き込めなかったファイルがあるため、「受付済」の目印は入れていません</span></li>}</ul></div>;
}
function RxHist() {
  const hs = (RX.hist || []).filter((x: any) => x.count); if (!hs.length) return null;
  return <div className="rxhist"><b>この演者の受付履歴</b><ul>{hs.slice(0, 8).map((x: any, i: number) => {
    const c = x.count || {}; const n = (c.ok || 0) + (c.replaced || 0);
    return <li key={i}>{dtm(x.ts)}　{x.pc || ""}　{n}件{c.replaced ? `（差し替え${c.replaced}）` : ""}{(c.busy || c.err) ? <span className="amber">　未完了 {(c.busy || 0) + (c.err || 0)}</span> : null}{x.flag && <>　目印「{nfc(x.flag)}」</>}</li>;
  })}</ul></div>;
}
/* ---- 目印画像（現場の 00_受付済.jpg などをそのままコピーして付ける・外す） */
function RxFlags() {
  const fl = RX.flags; const sel = rxSel()!; const F = store.F;
  if (!fl) return null;
  if (!fl.dir) return <div className="rxflags none"><span className="lb">目印</span><span className="hint" style={{ margin: 0 }}>［設定］→「受付」で目印画像のフォルダ（00_受付済.jpg などの元画像）を指定すると、ここから目印を付けられます</span></div>;
  if (fl.error) return <div className="rxflags none"><span className="lb">目印</span><span className="amber">{fl.error}</span></div>;
  const pres = F && F.root === sel.root && F.group === sel.group ? F.items.filter((i) => i.mk && !i.d && !i.p.includes("/")) : null;
  const on = new Map<string, string[]>(); (pres || []).forEach((i) => { const k = i.ml || ""; if (!on.has(k)) on.set(k, []); on.get(k)!.push(i.p); });
  const busy = RX.flagBusy || pres === null;
  const add = async (name: string) => {
    RX.flagBusy = true; store.emit();
    try { const j: any = await api("/api/rx/flag", { root: sel.root, group: sel.group, name }); toast(j.added ? `目印「${nfc(j.added)}」を入れました` : `同じ目印がすでにあります（${nfc(j.exists || "")}）`, 3500); }
    catch (e: any) { toast(e.message, 6000); }
    RX.flagBusy = false; refresh();
  };
  const del = async (label: string) => {
    const names = on.get(label) || []; if (!names.length) return;
    if (!confirm(`目印「${nfc(label)}」を外します。\nNASの演者フォルダから ${names.map(nfc).join("、")} を削除します（データは消しません）。`)) return;
    RX.flagBusy = true; store.emit();
    try { const j: any = await api("/api/rx/unflag", { root: sel.root, group: sel.group, names }); toast(`目印を外しました（${j.removed.map(nfc).join("、")}）`, 3500); }
    catch (e: any) { toast(e.message, 6000); }
    RX.flagBusy = false; refresh();
  };
  const known = new Set(fl.templates.filter((t) => t.ok).map((t) => t.label)); const bad = fl.templates.filter((t) => !t.ok);
  return <div className="rxflags"><span className="lb">目印</span>
    {fl.templates.filter((t) => t.ok).map((t) => { const has = on.has(t.label);
      return <button key={t.name} className={cx("fb", has && "on", "r-" + t.role)} disabled={busy} onClick={() => (has ? del(t.label) : add(t.name))}
        title={has ? `NASの演者フォルダから「${nfc((on.get(t.label) || []).join("、"))}」を消します（データは消しません）` : `「${nfc(t.name)}」を演者フォルダへ入れます`}>{has && <Icon n="chk" />}{nfc(t.label)}</button>; })}
    {[...on.keys()].filter((l) => !known.has(l)).map((l) => <button key={l} className="fb on" disabled={busy} onClick={() => del(l)} title={`NASの演者フォルダから「${nfc((on.get(l) || []).join("、"))}」を消します`}><Icon n="chk" />{nfc(l)}</button>)}
    {bad.length > 0 && <span className="hint" style={{ margin: 0 }} title={bad.map((t) => t.name).join("、")}>（目印として認識されない画像 {bad.length}件：［設定］→「目印のファイル」に文字を追加すると使えます）</span>}
  </div>;
}

/* ---- USB・ドライブから取り込む */
async function rxDrives() { try { RX.usb.drives = (await api<any>("/api/rx/drives")).drives; } catch (e: any) { RX.usb.drives = []; toast(e.message, 5000); } }
async function rxBrowse(p: string) { try { const j: any = await api("/api/rx/browse?path=" + enc(p)); RX.usb.path = j.path; RX.usb.parent = j.parent; RX.usb.items = j.items; RX.usb.sel = new Set(); } catch (e: any) { toast(e.message, 5000); } store.emit(); }
export async function rxUsbOpen() {
  if (!RX.key) { toast("先に演者を選んでください"); return; }
  RX.usb.sel = new Set(); RX.usb.items = []; RX.usb.path = ""; await rxDrives();
  if (RX.usb.drives.length === 1) await rxBrowse(RX.usb.drives[0].path);
  store.modal = "usb"; store.emit();
}
export function UsbDialog() {
  const s = useApp(); if (s.modal !== "usb") return null; const u = RX.usb; const sel = rxSel(); if (!sel) return null;
  const close = () => { s.modal = null; s.emit(); };
  return <Modal onClose={close} wide><div className="dlg rxdlg"><h2>USB・ドライブから取り込む</h2><p className="desc">受付先：<b>{nfc(sel.group.split("/").pop())}</b>　（いったんこのPCのトレイに受け取ります。NASへはまだ書き込みません）</p>
    <div className="drv">{u.drives.length ? u.drives.map((d: any) => <span key={d.path} className={cx("d", u.path && u.path.startsWith(d.path) && "on")}>
      <button className="ghost" onClick={() => rxBrowse(d.path)}><Icon n="hd" />{d.name}</button><span className="s">{d.type} · 空き {fmtSize(d.free)}</span>
      {d.eject && <button className="ghost" title="安全に取り外す" onClick={async () => {
        try { const j: any = await api("/api/rx/eject", { path: d.path }); toast(j.msg || "取り出しました", 5000); if (j.ok && u.path.startsWith(d.path)) { u.path = ""; u.items = []; u.sel = new Set(); } } catch (e: any) { toast(e.message, 6000); }
        await rxDrives(); s.emit();
      }}>取り出す</button>}</span>) : <span className="emp" style={{ padding: "4px 0" }}>USBメモリ・ドライブが見つかりません（差し込んだら［更新］）</span>}
      <span style={{ flex: 1 }} /><button className="ghost" onClick={async () => { await rxDrives(); s.emit(); }}>更新</button>
      <button className="ghost" onClick={async () => { try { const j: any = await api("/api/rx/pickdir", {}); if (j.path) await rxBrowse(j.path); } catch (e: any) { toast(e.message, 5000); } }}>フォルダを指定…</button></div>
    {u.path && <div className="cur">{u.parent && <button className="ghost" onClick={() => rxBrowse(u.parent!)}>↑ 上へ</button>}<span>{nfc(u.path)}</span></div>}
    <div className="lst">{!u.path ? <div className="emp">上のドライブを選んでください</div> : !u.items.length ? <div className="emp">空のフォルダです</div> :
      <table><tbody>{u.items.map((it: any) => <tr key={it.path}><td style={{ width: 30 }}><input type="checkbox" checked={u.sel.has(it.path)} onChange={(e) => { if (e.target.checked) u.sel.add(it.path); else u.sel.delete(it.path); s.emit(); }} /></td>
        <td className="nm">{it.dir ? <button className="dirlink" onClick={() => rxBrowse(it.path)}><Icon n="folder" />{nfc(it.name)}</button> : nfc(it.name)}</td>
        <td>{!it.dir && <span className={"chip c-" + it.c}>{it.c}</span>}</td><td className="num">{it.dir ? "" : fmtSize(it.size)}</td><td className="num">{dtm(it.m)}</td></tr>)}</tbody></table>}</div>
    <div className="foot"><span className="hint" style={{ margin: 0 }}>{u.sel.size ? `${u.sel.size}件を選択中` : "取り込むファイル・フォルダにチェック"}</span>
      <span style={{ display: "flex", gap: 8 }}><button onClick={close}>閉じる</button>
        {u.path && <button title="いま開いているフォルダを、フォルダごと取り込みます" onClick={() => { close(); RX.res = null; rxStart("/api/rx/import", { root: sel.root, group: sel.group, paths: [u.path] }); }}>このフォルダごと</button>}
        <button className="pri" disabled={!u.sel.size} onClick={() => { const paths = [...u.sel]; close(); RX.res = null; rxStart("/api/rx/import", { root: sel.root, group: sel.group, paths }); }}>選んだものをトレイに入れる</button></span></div>
  </div></Modal>;
}

/* ---- 演者フォルダを追加（NASのセッションフォルダの中に作る） */
const ADD: { rid: string; ses: string[]; cur: string } = { rid: "", ses: [], cur: "" };
export async function rxAddOpen(rid0?: string) {
  const S = store.S; if (!S || !S.roots.length) { toast("先に［設定］で受付先を追加してください"); return; }
  const s = rxSel(); const rid = typeof rid0 === "string" ? rid0 : s ? s.root : (store.SEL && store.SEL.root) || S.roots[0].id;
  try { ADD.ses = (await api<any>("/api/rx/sessions?root=" + enc(rid))).sessions; } catch (e: any) { toast(e.message, 5000); return; }
  ADD.rid = rid; ADD.cur = s && s.root === rid ? s.group.split("/").slice(0, -1).join("/") : "";
  store.modal = "addp"; store.emit();
}
export function AddDialog() {
  const s = useApp(); const [name, setName] = useState(""); const [ses, setSes] = useState(ADD.cur);
  useEffect(() => { setSes(ADD.cur); setName(""); }, [s.modal, ADD.rid]);
  if (s.modal !== "addp") return null; const S = s.S!; const r = rootById(ADD.rid);
  const close = () => { s.modal = null; s.emit(); };
  const go = async () => {
    const n = name.trim(); if (!n) { toast("フォルダ名を入れてください"); return; }
    try { const j: any = await api("/api/rx/mkdir", { root: ADD.rid, parent: ADD.ses.length && ADD.ses[0] !== "" ? ses || ADD.ses[0] : "", name: n }); close(); toast("作成しました: " + n, 4000); RX.pendSel = { root: ADD.rid, group: j.group }; refresh(); }
    catch (e: any) { toast(e.message, 6000); }
  };
  return <Modal onClose={close}><div className="dlg rxdlg" style={{ width: "min(620px,100%)" }}><h2>演者フォルダを追加</h2><p className="desc">NASのセッションフォルダの中に、演者のフォルダを作ります（NASへ書き込みます）。</p>
    <div className="grid2" style={{ marginTop: 16 }}>
      {S.roots.length > 1 && <><span>受付先</span><select value={ADD.rid} onChange={(e) => rxAddOpen(e.target.value)}>{S.roots.map((x) => <option key={x.id} value={x.id}>{nfc(x.label)}</option>)}</select></>}
      <span>セッション</span>{ADD.ses.length && ADD.ses[0] !== "" ? <select id="rxaSes" value={ses || ADD.ses[0]} onChange={(e) => setSes(e.target.value)}>{ADD.ses.map((x) => <option key={x} value={x}>{nfc(x.split("/").join(" › "))}</option>)}</select>
        : <span className="hint" style={{ margin: 0 }}>{r && r.depth > 1 ? "セッションのフォルダがありません" : "監視フォルダの直下に作ります"}</span>}
      <span>フォルダ名</span><input type="text" id="rxaName" autoFocus value={name} placeholder="例: 012_架空演者" autoComplete="off" onChange={(e) => setName(e.target.value)} onKeyDown={(e) => { if (e.key === "Enter") go(); }} />
    </div>
    <p className="hint">\ / : * ? " &lt; &gt; | は使えません。</p>
    <div className="foot"><span /><span style={{ display: "flex", gap: 8 }}><button onClick={close}>キャンセル</button><button className="pri" id="rxaGo" onClick={go}>作成</button></span></div>
  </div></Modal>;
}
