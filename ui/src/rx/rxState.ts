/* RECEPTION：受付の状態（トレイ・仕事の進み具合・受け取り）とサーバーとのやりとり */
import { api, enc } from "../api";
import { IS_RX, TOKEN } from "../boot";
import { onEventHook, refresh, rootById, selectGroup, store, toast } from "../store";

export interface TrayFile { rel: string; size: number; c: string; exists?: boolean; exists_strip?: boolean; na?: string; sum?: any }
export interface Tray { files: TrayFile[]; total: number; warn?: { lv: string; msg: string }[]; top?: string; busy?: boolean; missing?: boolean }
export interface RxJob { id: string; kind: "commit" | "import"; state: "run" | "done" | "error"; i: number; n: number; done: number; total: number; cur: string; t0: number; result?: any; errors?: string[] }
export interface FlagT { name: string; label: string; role: string; ok: boolean }
export const RX = {
  key: "", tray: null as Tray | null, job: null as RxJob | null, poll: 0, up: null as null | { i: number; n: number; done: number; total: number; cur: string; who: string; cancel: boolean },
  strip: true, excl: new Set<string>(), hist: [] as any[], res: null as any, lastJob: "", mine: {} as Record<string, number>,
  settings: null as any, data: "", pendSel: null as null | { root: string; group: string },
  flags: null as null | { dir: string; templates: FlagT[]; error?: string }, flagBusy: false, xhr: null as XMLHttpRequest | null,
  usb: { path: "", parent: null as string | null, items: [] as any[], sel: new Set<string>(), drives: [] as any[] },
};
export const rxSel = () => { if (!RX.key) return null; const i = RX.key.indexOf("|"); return { root: RX.key.slice(0, i), group: RX.key.slice(i + 1) }; };
export const rxBusy = () => !!(RX.up || (RX.job && RX.job.state === "run"));
const emit = () => store.emit();

/* 選んでいる演者が変わったら、受付パネルを作り直す */
export function rxSync() {
  const s = store.SEL; const k = s && s.group ? s.root + "|" + s.group : "";
  if (k === RX.key) return;
  RX.key = k; RX.tray = null; RX.excl = new Set(); RX.res = null; RX.hist = []; RX.job = null;
  if (k) { rxLoad(); rxPoll(); }
}
export async function rxLoad() {
  const s = rxSel(); if (!s) return; const k = RX.key;
  try {
    const [t, h] = await Promise.all([api<Tray>(`/api/rx/tray?root=${enc(s.root)}&group=${enc(s.group)}`), api<any>(`/api/rx/history?root=${enc(s.root)}&group=${enc(s.group)}`)]);
    if (RX.key !== k) return; RX.tray = t; RX.hist = h.items || [];
  } catch (e: any) { if (RX.key === k) RX.tray = { files: [], warn: [{ lv: "bad", msg: e.message }], total: 0 }; }
  emit();
}
export async function rxPoll() {
  clearTimeout(RX.poll); const s = rxSel(); if (!s) return; const k = RX.key;
  let j: RxJob | null = null;
  try { j = (await api<any>(`/api/rx/job?root=${enc(s.root)}&group=${enc(s.group)}`)).job; } catch { /* */ }
  if (RX.key !== k) return;
  const was = RX.job && RX.job.state === "run"; RX.job = j;
  if (j && j.state === "run") { emit(); RX.poll = window.setTimeout(rxPoll, 400); return; }
  if (j && j.state === "done" && j.id !== RX.lastJob && was) {
    RX.lastJob = j.id;
    if (j.kind === "commit" && j.result) { RX.res = j.result; RX.mine[k] = Date.now(); RX.excl = new Set(); refresh(); }
    if (j.errors && j.errors.length) toast(j.errors.slice(0, 3).join(" / "), 7000);
    await rxLoad(); return;
  }
  if (was) emit();
}
export async function rxStart(path: string, body: any) {
  try { const j = (await api<any>(path, body)).job; RX.job = j; RX.lastJob = ""; emit(); rxPoll(); } catch (e: any) { toast(e.message, 7000); }
}
export async function rxLoadFlags() { try { RX.flags = await api("/api/rx/flags"); } catch (e: any) { RX.flags = { dir: "", templates: [], error: e.message }; } emit(); }

/* ---- 受け取り（ブラウザから。いったんこのPCのトレイへ） */
export interface UpItem { file: File; rel: string }
const filterList = (list: UpItem[]) => list.filter((x) => { const n = x.file.name; return !/^(\.ds_store|thumbs\.db|desktop\.ini)$/i.test(n) && !n.startsWith("._") && !n.startsWith("~$"); });
function upOne(s: { root: string; group: string }, file: File, rel: string, onp: (n: number) => void) {
  return new Promise<any>((res, rej) => {
    const x = new XMLHttpRequest(); RX.xhr = x;
    x.open("POST", `/api/rx/upload?root=${enc(s.root)}&group=${enc(s.group)}&path=${enc(rel)}`); x.setRequestHeader("X-SW-Token", TOKEN);
    x.upload.onprogress = (e) => onp(e.loaded);
    x.onload = () => { let j: any = {}; try { j = JSON.parse(x.responseText); } catch { /* */ } if (x.status === 200) res(j); else rej(new Error(j.error || "HTTP " + x.status)); };
    x.onerror = () => rej(new Error("送れませんでした")); x.onabort = () => rej(new Error("中止しました")); x.send(file);
  });
}
export async function rxUpload(list0: UpItem[]) {
  if (!RX.key) { toast("先に演者を選んでください"); return; }
  if (rxBusy()) { toast("受け取り・書き込みの途中です"); return; }
  const list = filterList(list0); if (!list.length) { toast("受け取るファイルがありません"); return; }
  const s = rxSel()!; const total = list.reduce((a, x) => a + x.file.size, 0);
  RX.up = { i: 0, n: list.length, done: 0, total, cur: "", who: RX.key, cancel: false }; RX.res = null; emit();
  let base = 0; const errs: string[] = [];
  for (const [i, x] of list.entries()) {
    if (RX.up.cancel) break; RX.up.i = i + 1; RX.up.cur = x.rel; emit();
    try { await upOne(s, x.file, x.rel, (l) => { RX.up!.done = base + l; emit(); }); }
    catch (e: any) { if (RX.up.cancel) break; errs.push(x.rel + "：" + e.message); }   // 1つ受け取れなくても、残りは続ける
    base += x.file.size; RX.up.done = base;
  }
  const who = RX.up.who, canceled = RX.up.cancel; RX.up = null;
  if (errs.length) toast(`${errs.length}件を受け取れませんでした：${errs.slice(0, 3).join(" / ")}${errs.length > 3 ? " ほか" : ""}`, 9000);
  else if (canceled) toast("中止しました", 3000);
  if (RX.key === who) await rxLoad(); else emit();
}
export async function collectDrop(dt: DataTransfer): Promise<UpItem[]> {
  const ents = [...dt.items].filter((i) => i.kind === "file").map((i) => (i.webkitGetAsEntry ? i.webkitGetAsEntry() : null));
  const files = [...dt.files]; const out: UpItem[] = [];
  if (!ents.length || ents.some((e) => !e)) { files.forEach((f) => out.push({ file: f, rel: f.name })); return out; }
  async function walk(e: any, pre: string): Promise<void> {
    if (e.isFile) { const f: File = await new Promise((ok, ng) => e.file(ok, ng)); out.push({ file: f, rel: pre + e.name }); }
    else if (e.isDirectory) {
      const rd = e.createReader(); let batch: any[];
      do { batch = await new Promise((ok, ng) => rd.readEntries(ok, ng)); for (const c of batch) await walk(c, pre + e.name + "/"); } while (batch.length);
    }
  }
  for (const e of ents) await walk(e, ""); return out;
}

if (IS_RX) {
  api<any>("/api/rx/settings").then((j) => { RX.settings = j.settings; RX.data = j.data_dir; }).catch(() => {});
  rxLoadFlags();
  /* 自分が書き込んだ変化は既読にする */
  onEventHook((ev) => {
    const k = ev.root + "|" + ev.group;
    if (RX.mine[k] && Date.now() - RX.mine[k] < 180000 && store.S?.local) api("/api/seen", { root: ev.root, group: ev.group }).then(refresh).catch(() => {});
  });
  /* 演者フォルダを作ったら、一覧に出たところで選ぶ */
  store.subscribe(() => {
    const p = RX.pendSel; if (!p) return; const r = rootById(p.root);
    if (r && (r.groups || []).some((g) => g.key === p.group)) { RX.pendSel = null; setTimeout(() => selectGroup(p.root, p.group), 0); }
  });
  /* ドロップでページが開いてしまわないように */
  ["dragover", "drop"].forEach((t) => window.addEventListener(t, (e) => e.preventDefault()));
}
