/* 画面全体の状態と操作。サーバーの状態（/api/state）＋ このPCだけの表示設定（localStorage）。
   変化したら emit() → 画面を描き直す（useApp）。旧画面の動作（通知・自動表示・既読・日の切り替えなど）をそのまま移す */
import { useSyncExternalStore } from "react";
import { api, enc } from "./api";
import { IS_OP, IS_RX, APP_TITLE } from "./boot";
import type { AppState, Ev, Folder, Group, Root } from "./types";
import { cmpDay, dayInfo, fuOf, lay, parts, ymd } from "./lib/layout";
import { cmpName, ls, nfc, whereText } from "./lib/util";

export type View = "list" | "board";
export type Modal = null | "cfg" | "net" | "usb" | "addp";
export interface Sel { root: string; group: string }

const VPAL = ["#38bdf8", "#a78bfa", "#34d399", "#fbbf24", "#f472b6", "#fb923c", "#2dd4bf", "#818cf8", "#f87171", "#a3e635"];
export const VPAL_ = VPAL;

class Store {
  S: AppState | null = null;
  F: Folder | null = null;
  folderErr = "";
  SEL: Sel | null = ls.get<Sel | null>("sel", null);
  VENUE: string = ls.get("venue", "");
  FOLLOW: boolean = IS_OP || IS_RX ? false : ls.get("follow", true);
  view: View = ls.get<string>("view", "list") === "board" ? "board" : "list";
  onlyU: boolean = ls.get("onlyU", false);
  onlyN: boolean = ls.get("onlyN", false);
  sort: "name" | "recent" | "unread" = ls.get<"name" | "recent" | "unread">("sort", "name");
  q = "";
  bq = "";
  DAYSEL: { v: string; at: string } | null = ls.get("day", null);
  FOLD: Record<string, 1> = ls.get("fold", {});
  VCOL: Record<string, string> = ls.get("vcol", {});
  logOpen = false;
  drawer = false;
  modal: Modal = null;
  toastMsg = "";
  toastSeq = 0;
  conn = true;
  flashKeys = new Set<string>();
  RATE: Record<string, { b: number; t: number; v: number | null }> = {};
  SKEW = 0;
  boot: string | null = null;
  lastId = 0;
  lastVer = -1;
  ready = false;
  lastInteract = 0;
  liveUnread = 0;
  followKey: string | null = null;
  tick = 0;
  appVersion = "";
  quit = false;
  version = 0;
  private ls = new Set<() => void>();

  subscribe = (f: () => void) => { this.ls.add(f); return () => { this.ls.delete(f); }; };
  snap = () => this.version;
  emit() { this.version++; this.ls.forEach((f) => f()); }
}
export const store = new Store();
export function useApp() { useSyncExternalStore(store.subscribe, store.snap); return store; }

/* ---------------------------------------------------------------- 小さな道具 */
let toastT = 0;
export function toast(msg: string, ms = 3200) {
  store.toastMsg = msg; store.toastSeq++; store.emit();
  clearTimeout(toastT); toastT = window.setTimeout(() => { store.toastMsg = ""; store.emit(); }, ms);
}
export const rootById = (id: string): Root | undefined => store.S?.roots.find((r) => r.id === id);
export const OPON = () => !!(store.S && store.S.op && store.S.op.enabled);
export const opDests = () => (OPON() ? store.S!.op.dests.filter((d) => d.enabled) : []);
export function effVenue() { const S = store.S!; return OPON() ? S.op.root + "|" + (S.op.venue || "") : store.VENUE; }
export function inVenue(root: string, group: string | null) {
  const V = effVenue(); if (!V) return true; const i = V.indexOf("|");
  if (root !== V.slice(0, i)) return false;
  if (group == null || group === "" || !V.slice(i + 1)) return true;
  const S = store.S!;
  if (OPON() && S.op.venue && root === S.op.root) return (group + "/").startsWith(S.op.venue + "/");
  const r = rootById(root); return r ? fuOf(r, group) === V.slice(i + 1) : group.split("/")[0] === V.slice(i + 1);
}
export function allDays(): string[] {
  const set = new Set<string>(); const EV = effVenue();
  for (const r of store.S ? store.S.roots : []) {
    if (EV && EV.slice(0, EV.indexOf("|")) !== r.id) continue;
    for (const g of r.groups || []) if (g.key) { const d = parts(r, g.key).day; if (d) set.add(d); }
  }
  return [...set].sort(cmpDay);
}
/* 表示する日（PCごとに保存）。「1日目」を選んだまま翌日になったら、自動で「2日目」に進める */
export function effDay(days?: string[]): string {
  const DS = store.DAYSEL; if (!DS || !DS.v) return ""; days = days || allDays();
  if (!days.length) return "";
  const d = dayInfo(DS.v);
  if (d && d.n != null && DS.at) {
    const diff = Math.round((+new Date(ymd() + "T00:00:00") - +new Date(DS.at + "T00:00:00")) / 864e5);
    if (diff > 0) { const hit = days.find((x) => { const e = dayInfo(x); return e && e.n === d.n! + diff; }); if (hit) return hit; }
  }
  return days.includes(DS.v) ? DS.v : "";
}
export function setDay(v: string) { store.DAYSEL = v ? { v, at: ymd() } : null; ls.set("day", store.DAYSEL); store.emit(); }
export function setVenue(v: string) { store.VENUE = v; ls.set("venue", v); store.emit(); }
export function setView(v: View) { store.view = v; ls.set("view", v); store.logOpen = false; if (v === "list") store.drawer = false; store.emit(); }
export function setPref<K extends "onlyU" | "onlyN" | "sort">(k: K, v: Store[K]) { (store as any)[k] = v; ls.set(k, v); store.emit(); }
export function setFollow(v: boolean) { store.FOLLOW = v; ls.set("follow", v); store.emit(); }

/* 会場の色（このPCに保存。会場が増えても今までの色は変えない） */
export function computeVenueColors() {
  let ch = false; const S = store.S; if (!S) return;
  for (const r of S.roots) {
    if (lay(r).vl < 0) continue;
    const vs = [...new Set((r.groups || []).filter((g) => g.key).map((g) => parts(r, g.key).venue).filter(Boolean))].sort(cmpName);
    const used = new Set(Object.keys(store.VCOL).filter((k) => k.startsWith(r.id + "|")).map((k) => store.VCOL[k]));
    for (const v of vs) {
      const k = r.id + "|" + v; if (store.VCOL[k]) continue;
      store.VCOL[k] = VPAL.find((c) => !used.has(c)) || VPAL[used.size % VPAL.length]; used.add(store.VCOL[k]); ch = true;
    }
  }
  if (ch) ls.set("vcol", store.VCOL);
}
export const venueOf = (root: string, group: string | null) => { const r = rootById(root); if (!r || !group) return null; return parts(r, group).venue || null; };
export const vColor = (root: string, v: string) => store.VCOL[root + "|" + v] || "#a1a1aa";

/* 開閉（会場＝「root|会場名」、セッション＝「root|演者フォルダの親のパス」） */
export const isFold = (k: string) => !!store.FOLD[k];
export function setFold(k: string, v: boolean) { if (v) store.FOLD[k] = 1; else delete store.FOLD[k]; ls.set("fold", store.FOLD); store.emit(); }
export function setFoldMany(keys: string[], v: boolean) { keys.forEach((k) => { if (v) store.FOLD[k] = 1; else delete store.FOLD[k]; }); ls.set("fold", store.FOLD); store.emit(); }
export function foldKeysOf(root: string, group: string) {
  const r = rootById(root); if (!r || !group || r.depth < 2) return [] as string[];
  const segs = group.split("/"); const ks: string[] = [];
  const v = parts(r, group).venue; if (v) ks.push(root + "|" + v);
  if (segs.length > 1) ks.push(root + "|" + segs.slice(0, -1).join("/"));
  return ks;
}
function unfold(root: string, group: string) {
  let ch = false; foldKeysOf(root, group).forEach((k) => { if (store.FOLD[k]) { delete store.FOLD[k]; ch = true; } });
  if (ch) ls.set("fold", store.FOLD);
}

/* ---------------------------------------------------------------- 状態の読み込み・SSE */
function updateRates() {
  const S = store.S; if (!S) return; store.SKEW = S.now - Date.now() / 1000; const live = new Set<string>();
  for (const r of S.roots) for (const g of r.groups || []) {
    if (!g.pending) continue; const k = r.id + "|" + g.key; live.add(k);
    const b = g.pbytes || 0, x = store.RATE[k];
    if (!x) { store.RATE[k] = { b, t: S.now, v: null }; continue; }
    const dt = S.now - x.t; if (dt < 1.5) continue;
    const dv = (b - x.b) / dt; x.v = dv > 0 ? (x.v ? x.v * 0.5 + dv * 0.5 : dv) : dt > 6 ? 0 : x.v; x.b = b; x.t = S.now;
  }
  Object.keys(store.RATE).forEach((k) => { if (!live.has(k)) delete store.RATE[k]; });
}
export async function loadState() {
  const st = await api<AppState>("/api/state");
  if (store.S && st.boot === store.S.boot && st.ver < store.S.ver) return;   // 遅れて届いた古い状態で上書きしない
  store.S = st; updateRates(); computeVenueColors();
  if (!store.ready) { store.ready = true; store.lastId = st.last_event_id; store.boot = st.boot; connect(); }
  if (store.SEL && !rootById(store.SEL.root)) { store.SEL = null; ls.set("sel", null); store.F = null; }
  setTitle();
  store.emit();
  if (store.SEL) loadFolder(false);
}
let rT = 0;
export function refresh() { clearTimeout(rT); rT = window.setTimeout(() => loadState().catch((e) => console.warn(e)), 200); }

const evHooks: ((ev: Ev) => void)[] = [];
export const onEventHook = (f: (ev: Ev) => void) => { evHooks.push(f); };

function connect() {
  const es = new EventSource("/api/stream?since=" + store.lastId);
  es.addEventListener("ev", (e) => { const ev = JSON.parse((e as MessageEvent).data) as Ev; store.lastId = Math.max(store.lastId, ev.id); onEvent(ev); });
  es.addEventListener("incoming", (e) => onIncoming(JSON.parse((e as MessageEvent).data)));
  es.addEventListener("status", (e) => {
    const st = JSON.parse((e as MessageEvent).data);
    if (store.boot && st.boot !== store.boot) { location.reload(); return; }
    if (!store.conn) { store.conn = true; }
    if (store.S) for (const r of st.roots) { const x = rootById(r.id); if (x) Object.assign(x, r); }
    if (st.ver !== store.lastVer) { store.lastVer = st.ver; refresh(); } else store.emit();
  });
  es.onerror = () => { store.conn = false; if (store.quit) es.close(); store.emit(); };
}
function onIncoming(x: any) {
  if (!store.S || !inVenue(x.root, x.group)) return;
  if (store.S.notify.incoming !== false) queueN("inc", x);
  maybeFollow(x); flashRow(x); refresh();
}
function onEvent(ev: Ev) {
  const S = store.S; if (!S) return;
  if (!S.events.some((e) => e.id === ev.id)) { S.events.push(ev); if (S.events.length > 400) S.events.shift(); }
  const live = ev.ts > Date.now() / 1000 - 120;
  if (live && inVenue(ev.root, ev.group)) {
    if (wantNotify(ev)) queueN("ev", ev);
    maybeFollow(ev); flashRow(ev);
    if (ev.group != null && (document.hidden || !document.hasFocus())) { store.liveUnread++; flashTitle(); }
  }
  evHooks.forEach((f) => f(ev));
  refresh();
}
const wantNotify = (ev: Ev) => { const ks = ev.kinds && ev.kinds.length ? ev.kinds : [ev.kind]; return ks.some((k) => store.S!.notify[k] !== false); };
function maybeFollow(x: { root: string; group: string | null }) {
  if (!store.FOLLOW || x.group == null || Date.now() - store.lastInteract < 15000) return;
  if (store.view === "board") { store.followKey = x.root + "|" + x.group; if (!store.drawer) return; }
  if (store.SEL && store.SEL.root === x.root && store.SEL.group === x.group) return;
  selectGroup(x.root, x.group, true);
}
function flashRow(x: { root: string; group: string | null }) {
  if (x.group == null) return; const k = x.root + "|" + x.group; store.flashKeys.add(k);
  setTimeout(() => { store.flashKeys.delete(k); store.emit(); }, 2600);
}

/* ---------------------------------------------------------------- 通知・音（OPERATOR では出さない） */
type NQ = { kind: "inc" | "ev"; x: any; tag: string; sound: boolean; re: boolean };
const nQ: NQ[] = []; const lastInc: Record<string, number> = {}; let nT = 0; let AC: AudioContext | null = null;
const tagOf = (x: any) => "sw-" + x.root + "|" + (x.group == null ? "#" : x.group);
export const anaWarn = (x: any) => (x.ana || []).some((a: any) => a.warn);
function queueN(kind: "inc" | "ev", x: any) {
  const tag = tagOf(x); let sound = true, re = true;
  if (kind === "ev" && x.kind === "copied") { sound = false; re = false; }
  else if (kind === "ev" && x.kind === "copy_err") { sound = true; re = true; }
  else if (kind === "ev") {
    const inc = lastInc[tag] && Date.now() - lastInc[tag] < 300000; delete lastInc[tag];
    if (inc) { const w = anaWarn(x) || ["del", "folder_del", "offline"].includes(x.kind); sound = w; re = w; }
  } else lastInc[tag] = Date.now();
  nQ.push({ kind, x, tag, sound, re }); if (!nT) nT = window.setTimeout(flushN, 450);
}
function bodyOf(x: any) {
  const L: string[] = []; if (x.where) L.push(whereText(x.where)); L.push(x.summary); if (x.detail) L.push(nfc(x.detail));
  (x.ana || []).forEach((a: any) => L.push(nfc(a.file) + ": " + (a.text || a.na || "解析中…")));
  if (store.S!.roots.length > 1 || x.group == null) L.push("[" + nfc(x.root_label) + "]"); return L.join("\n");
}
function flushN() {
  nT = 0; const L = nQ.splice(0); if (!L.length) return;
  if (OPON() || IS_OP) return;   // 会場の発表PC：スライドショーをしているので、通知も音も出さない
  const S = store.S!;
  const snd = L.filter((i) => i.sound);
  if (snd.length) chime(snd.some((i) => i.kind === "ev" && (anaWarn(i.x) || ["offline", "del", "folder_del", "copy_err"].includes(i.x.kind))));
  if (!("Notification" in window) || Notification.permission !== "granted") return;
  const m = new Map<string, NQ>(); L.forEach((i) => m.set(i.tag, i)); const items = [...m.values()];
  if (items.length > 3) {
    const n = new Notification(items.length + "件の変更", {
      body: items.slice(0, 4).map((i) => (i.x.where ? whereText(i.x.where) + " › " : "") + nfc(i.x.title) + "  " + (i.kind === "inc" ? "受信中" : i.x.summary)).join("\n") + (items.length > 4 ? "\n…" : ""),
      tag: "sw-batch", requireInteraction: !!S.ui.sticky, silent: !!S.ui.sound || !snd.length, ...({ renotify: true } as any),
    });
    n.onclick = (e) => { e.preventDefault(); window.focus(); showLog(); n.close(); }; return;
  }
  items.forEach((i) => {
    const x = i.x;
    const n = new Notification((x.while_stopped ? "[停止中の変更] " : "") + (i.kind === "inc" ? "受信中: " : "") + (x.repl ? "【差し替え" + x.repl + "回目】" : "") + nfc(x.title),
      { body: bodyOf(x), tag: i.tag, requireInteraction: !!S.ui.sticky, silent: !!S.ui.sound || !i.sound, ...({ renotify: i.re } as any) });
    n.onclick = (e) => {
      e.preventDefault(); window.focus();
      if (x.group != null) { selectGroup(x.root, x.group); if (S.ui.click === "both" && S.ui.os_open) openOS(x.root, x.group); } else showLog();
      n.close();
    };
  });
}
export function unlockAudio() {
  try { if (!AC) AC = new (window.AudioContext || (window as any).webkitAudioContext)(); if (AC!.state === "suspended") AC!.resume(); } catch { /* */ }
}
export function chime(bad: boolean) {
  if (!store.S?.ui.sound || OPON() || IS_OP) return; unlockAudio(); if (!AC) return;
  const ac = AC; const t = ac.currentTime + 0.02;
  const tone = (f: number, s: number, d: number, v?: number) => {
    const o = ac.createOscillator(), g = ac.createGain(); o.type = "sine"; o.frequency.value = f;
    g.gain.setValueAtTime(0.0001, t + s); g.gain.exponentialRampToValueAtTime(v || 0.22, t + s + 0.012); g.gain.exponentialRampToValueAtTime(0.0001, t + s + d);
    o.connect(g); g.connect(ac.destination); o.start(t + s); o.stop(t + s + d + 0.05);
  };
  if (bad) { tone(740, 0, 0.22); tone(494, 0.24, 0.38); } else { tone(988, 0, 0.16); tone(1319, 0.15, 0.3); }
}
let flT = 0;
function flashTitle() {
  if (flT || OPON() || IS_OP) return; let on = false;
  flT = window.setInterval(() => {
    if (!document.hidden && document.hasFocus()) { clearInterval(flT); flT = 0; store.liveUnread = 0; setTitle(); return; }
    on = !on; document.title = on ? "● 新着 " + store.liveUnread + "件" : titleText();
  }, 900);
}
const titleText = () => { const u = store.S ? store.S.unread_total : 0; return (u ? "(" + u + ") " : "") + APP_TITLE; };
export function setTitle() { if (!flT) document.title = titleText(); }
export async function askPerm() { try { await Notification.requestPermission(); } catch { /* */ } unlockAudio(); store.emit(); }
export async function testNotify() {
  if (OPON() || IS_OP) { toast("会場オペレーターモードでは、スライドショーの邪魔にならないよう通知と音は出しません", 6000); return; }
  unlockAudio();
  if ("Notification" in window && Notification.permission === "default") await askPerm();
  chime(false);
  if ("Notification" in window && Notification.permission === "granted") {
    const n = new Notification(APP_TITLE + " テスト通知", { body: "この通知が見えていれば設定OKです", tag: "sw-test", silent: !!store.S?.ui.sound });
    n.onclick = () => { window.focus(); n.close(); };
  } else toast("通知が許可されていません（音のみ再生）", 4000);
}

/* ---------------------------------------------------------------- 演者を選ぶ・中身 */
export function selectGroup(root: string, group: string, auto?: boolean) {
  store.SEL = { root, group }; ls.set("sel", store.SEL);
  unfold(root, group);
  if (store.view === "board") store.drawer = true;
  store.F = store.F && store.F.root === root && store.F.group === group ? store.F : null;
  store.folderErr = "";
  store.emit();
  loadFolder(true);
  if (store.S?.local && (!auto || document.hasFocus())) api("/api/seen", { root, group }).then(refresh).catch(() => {});
}
export let folderScrollTop = false;
export function consumeScrollTop() { const v = folderScrollTop; folderScrollTop = false; return v; }
export async function loadFolder(scrollTop: boolean) {
  const sel = store.SEL; if (!sel) return; const want = sel.root + "|" + sel.group;
  let res: Folder;
  try { res = await api<Folder>(`/api/folder?root=${enc(sel.root)}&group=${enc(sel.group)}`); }
  catch (e: any) { if (!store.SEL || store.SEL.root + "|" + store.SEL.group !== want) return; store.F = null; store.folderErr = e.message; store.emit(); return; }
  if (!store.SEL || store.SEL.root + "|" + store.SEL.group !== want) return;   // 速く続けて選んだとき、前の演者の結果で上書きしない
  store.F = res; store.folderErr = ""; if (scrollTop) folderScrollTop = true; store.emit();
}
export function closeDrawer() { store.drawer = false; store.emit(); }
export function showLog() { store.logOpen = true; store.emit(); }
export function openOS(root: string, group: string) { api("/api/open", { root, rel: group }).catch((e) => toast(e.message, 5000)); }

/* 演者をダブルクリック：WATCH・RECEPTION は Explorer / Finder で開く（設定でオンのときだけ）。OPERATOR は差し替え（op/opener） */
let dblHandler: ((root: string, group: string) => void) | null = null;
export const setDblHandler = (f: (root: string, group: string) => void) => { dblHandler = f; };
export function openFolderOS(root: string, group: string) {
  if (dblHandler) { dblHandler(root, group); return; }
  const S = store.S!;
  if (!S.local) { toast("フォルダを開くのは監視PCでのみできます", 4000); return; }
  if (!S.ui.os_open) { toast("ダブルクリックでフォルダを開くには、［設定］→「Explorer / Finder で開く」をオンにしてください（会場側への影響を避けるため、通常はオフです）", 7000); return; }
  openOS(root, group); toast("フォルダを開いています…", 1800);
}
/* 1回目のクリックで画面が書き換わっても判定できるよう、「同じ演者を0.45秒以内に2回クリック」でダブルクリックとみなす */
let LASTCLK: { r: string; g: string; t: number; x: number; y: number } | null = null;
export function clickRow(e: { clientX: number; clientY: number }, r: string, g: string) {
  const c = LASTCLK;
  if (c && c.r === r && c.g === g && Date.now() - c.t < 450 && Math.abs(e.clientX - c.x) < 8 && Math.abs(e.clientY - c.y) < 8) { LASTCLK = null; openFolderOS(r, g); return; }
  LASTCLK = { r, g, t: Date.now(), x: e.clientX, y: e.clientY };
  selectGroup(r, g);
}

export async function quitApp() {
  const msg = IS_OP ? "アプリを終了しますか？\nコピーも止まります（コピー中のファイルは次に起動したときにやり直します）。" : IS_RX ? "アプリを終了しますか？" : "アプリを終了しますか？\n監視と通知が止まります。";
  if (!confirm(msg)) return;
  try { await api("/api/quit", {}); }
  catch (e: any) { if (e instanceof TypeError) { /* 止まって応答がない */ } else { toast(e.message, 6000); return; } }
  store.quit = true; store.emit();
  setTimeout(() => { try { window.close(); } catch { /* */ } }, 600);
}
export function markAllSeen() { api("/api/seen", { all: true }).then(refresh).catch((e) => toast(e.message)); }

/* 受信中の進み具合（受信済みサイズ・速度・経過時間） */
export function rateOf(rid: string, g: Group) { const x = store.RATE[rid + "|" + g.key]; return x && x.v && x.v > 0 ? x.v : 0; }

/* 起動 */
export function startApp() {
  ["pointerdown", "keydown", "wheel"].forEach((t) => document.addEventListener(t, () => { store.lastInteract = Date.now(); }, { passive: true, capture: true }));
  document.addEventListener("pointerdown", unlockAudio);
  window.addEventListener("focus", () => {
    store.liveUnread = 0; setTitle();
    const sel = store.SEL;
    if (sel && store.S?.local && (store.view === "list" || store.drawer)) api("/api/seen", sel).then(refresh).catch(() => {});
  });
  setInterval(() => { store.tick++; store.emit(); }, 30000);   // セッションの進行状況・「◯分前」の表示を更新
  api("/api/ping").then((j: any) => { store.appVersion = j.version || ""; store.emit(); }).catch(() => {});
  loadState().catch((e) => { store.folderErr = "起動できません: " + e.message; store.emit(); });
}
