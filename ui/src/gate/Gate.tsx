/* PADDOCK GATE の本番画面（会場の発表PC）。
   左：その日のセッション（DAY の切り替えつき）／中央：残り時間・発表中の人・発表順／右：選んだ演者の本番用の情報。
   発表中・発表済みは このPC の記録だけ（/api/op/stage）。NAS には何も書かない */
import { Fragment, useEffect, useLayoutEffect, useRef, useState } from "react";
import { api } from "../api";
import type { CpState, Folder, Group, Root } from "../types";
import { cmpDay, dayInfo, dayOK, fmtT, isTodayLabel, parts, sesStatus, sesTime, todayDay, type SStat, type STime } from "../lib/layout";
import { ago, cmpPath, copyText, cx, dtm, fmtSize, hms, mss, nfc } from "../lib/util";
import { allDays, effDay, inVenue, loadState, opDests, quitApp, rateOf, rootById, selectGroup, setDay, store, toast, useApp } from "../store";
import { Icon } from "../components/Icons";
import { LogButton } from "../components/Header";
import { LogPane } from "../components/LogPane";
import { AnaCard } from "../components/Folder";
import { openCfg } from "../components/Settings";
import { netBadge, netOpen } from "../op/Net";
import { OPEN, opOpen } from "../op/Opener";
import { CPL, KindPill, OPS } from "../components/Bits";
import { Bar, Segmented } from "../design/ui";
import { APP_ICON } from "../lib/appIcon";
import "./gate.css";

/* ---------------------------------------------------------------- 発表中・発表済み（このPCの記録） */
type Stage = "now" | "done";
const STG: { st: Record<string, { st: Stage; ts: number }>; loaded: boolean } = { st: {}, loaded: false };
/* 保存は1つずつ順番に送る（速く続けて押しても、サーバーで順番が入れ替わらない）。送っている間は読み直しの結果で上書きしない */
let stQ: Promise<void> = Promise.resolve(); let stPending = 0; let stWrites = 0;
async function stageLoad() {
  if (stPending) return; const w0 = stWrites;
  try { const j: any = await api("/api/op/stage"); if (stPending || stWrites !== w0) return; STG.st = j.st || {}; STG.loaded = true; store.emit(); } catch { /* 古いサーバー */ }
}
export function setStage(root: string, group: string, st: Stage | "") {
  const k = root + "|" + group; const n = { ...STG.st };
  if (st === "now") for (const x of Object.keys(n)) if (n[x].st === "now" && x !== k) n[x] = { st: "done", ts: Date.now() / 1000 };
  if (st) n[k] = { st, ts: Date.now() / 1000 }; else delete n[k];
  STG.st = n; store.emit();   // 先に画面を変えて、保存はあとから
  stPending++; stWrites++;
  stQ = stQ.then(async () => {
    try { const j: any = await api("/api/op/stage", { root, group, st }); if (stPending === 1 && j.st) { STG.st = j.st; store.emit(); } }
    catch (e: any) { toast("発表の状態を保存できませんでした：" + e.message, 6000); stPending--; await stageLoad(); stPending++; }
    finally { stPending--; }
  });
}
const stageOf = (root: string, g: string, gr?: Group): Stage | "" => STG.st[root + "|" + g]?.st || ((gr ?? (rootById(root)?.groups || []).find((x) => x.key === g))?.mk_done ? "done" : "");

/* ---------------------------------------------------------------- データの組み立て */
interface Ses { key: string; name: string; day: string; t: STime | null; list: Group[]; custom?: boolean }
/* 当日の発表順の変更（このPCに保存。NAS のフォルダ名は変えない） */
let ORDER: Record<string, string[]> = {};
try { ORDER = JSON.parse(localStorage.getItem("gate.order") || "{}") || {}; } catch { ORDER = {}; }
function saveOrder(rootId: string, ses: Ses, keys: string[] | null) {
  const k = rootId + "|" + ses.key; if (keys) ORDER[k] = keys; else delete ORDER[k];
  try { localStorage.setItem("gate.order", JSON.stringify(ORDER)); } catch { /* */ }
  store.emit();
}
function moveRow(rootId: string, ses: Ses, key: string, to: number) {
  const keys = ses.list.map((g) => g.key); const from = keys.indexOf(key); if (from < 0) return;
  keys.splice(from, 1); keys.splice(Math.max(0, Math.min(keys.length, to)), 0, key); saveOrder(rootId, ses, keys);
}
interface Model { r: Root; days: string[]; day: string; dayMode: "op" | "path" | ""; sessions: Ses[]; tl: Map<string, SStat> }
function build(): Model | null {
  const S = store.S; if (!S) return null; const o = S.op; const r = rootById(o.root || ""); if (!r) return null;
  let dayMode: Model["dayMode"] = ""; let days: string[] = []; let day = "";
  if ((o.days || []).length) { dayMode = "op"; days = o.days!.slice(); day = o.day || days[0]; }
  else {
    days = allDays();
    if (days.length) { dayMode = "path"; day = effDay(days) || days.find(isTodayLabel) || days[0]; }
  }
  const gs = (r.groups || []).filter((g) => g.key && inVenue(r.id, g.key) && (dayMode !== "path" || dayOK(r, g.key, day)));
  const m = new Map<string, Ses>();
  for (const g of gs) {
    const p = parts(r, g.key); const k = p.sesKey;
    if (!m.has(k)) m.set(k, { key: k, name: p.ses || k.split("/").pop() || "（セッションなし）", day: p.day, t: sesTime(p.ses), list: [] });
    m.get(k)!.list.push(g);
  }
  // 並び：全部に時刻があれば時刻順、時刻のないセッションが混じるときは名前順（S01・S02… の番号順）
  const all = [...m.values()]; const timed = all.every((x) => x.t);
  const sessions = all.sort((a, b) => cmpDay(a.day, b.day) || (timed ? a.t!.s - b.t!.s : 0) || cmpPath(a.name, b.name));
  sessions.forEach((x) => {
    x.list.sort((a, b) => cmpPath(a.key, b.key));
    const o = ORDER[r.id + "|" + x.key];   // 当日の順番変更（このPCだけ）
    if (o && o.length) { const pos = new Map(o.map((k, i) => [k, i])); const base = new Map(x.list.map((g, i) => [g.key, i]));
      x.list.sort((a, b) => (pos.has(a.key) && pos.has(b.key) ? pos.get(a.key)! - pos.get(b.key)! : base.get(a.key)! - base.get(b.key)!)); x.custom = true; }
  });
  // 進行中・次：選んでいる日が「今日」のときだけ（日付の名前でなければ、選んでいる日を今日とみなす）
  const today = dayMode === "op" ? (days.find(isTodayLabel) || day) : todayDay(days, day);
  const tl = !days.length || day === today ? sesStatus(sessions.filter((x) => x.t).map((x) => ({ key: x.key, t: x.t! })).sort((a, b) => a.t.s - b.t.s)) : new Map<string, SStat>();
  return { r, days, day, dayMode, sessions, tl };
}
/* セッション名から時刻（0900-1030 / 9:00〜10:30 など）を除いた表示名。時刻は別に出す */
const T_RE = /\s*(?:\d{1,2}:?\d{2}\s*[-~〜ー−–—]+\s*\d{1,2}:?\d{2}|\d{1,2}時(?:\d{1,2}分?)?\s*[-~〜ー−–—]+\s*\d{1,2}時(?:\d{1,2}分?)?)\s*/;
const sesLabel = (x: { name: string; t: STime | null }) => {
  const n = nfc(x.name.split("/").pop()); if (!x.t) return n;
  return n.replace(T_RE, " ").replace(/[【\[(（「『〔<＜]\s*[】\])）」』〕>＞]/g, " ").replace(/\s{2,}/g, " ").replace(/^[\s_\-]+|[\s_\-]+$/g, "") || n;   // 時刻を抜いて空になった【】も消す
};
/* 演者フォルダ名「001 架空演者A」「S02-01_架空 演者B」→ 番号と名前 */
function splitName(seg: string) {
  const n = nfc(seg); const m = /^([A-Za-z]*\d[\w-]*)[\s_.、]+(.+)$/.exec(n);
  return m ? { no: m[1], name: m[2] } : { no: "", name: n };
}
const nameOf = (g: Group) => splitName(g.key.split("/").pop() || "");

/* 受付の状態（行の左） */
type RC = "received" | "got" | "direct" | "byo" | "pending" | "error" | "drop";
function needCheck(g: Group) {
  const a = g.ana; const cp = Object.values(g.cp || {});
  return !!(a && (a.vfbad || a.abad || a.noclick || a.err)) || cp.includes("err") || (g.fl || []).some((f) => f[1] === "warn");
}
/* 受付済みか：目印（受付済・取得済・発表終了・会場直）があるか、発表に使うデータがあるか（メモの .txt だけでは受付済みにしない） */
const isRecvG = (g: Group) => !!(g.mk_recv || g.mk_got || g.mk_done || g.mk_direct) || hasData(g);
function rcOf(g: Group): RC {
  if (g.mk_drop) return "drop"; if (needCheck(g)) return "error";
  if (g.mk_got || g.mk_done) return "got"; if (g.mk_direct && !hasData(g) && !g.mk_recv) return "direct";
  if (isRecvG(g)) return "received";
  return isBYO(g) ? "byo" : "pending";   // PC持込でデータなし：未受付ではない
}
/* 受付の数（左の一覧・発表順の見出しで同じ数え方） */
const recvCount = (L: Group[]) => L.filter((g) => isRecvG(g) || isBYO(g)).length;
const RCL: Record<RC, string> = { received: "受付済", got: "取得済", direct: "会場直", byo: "持込", pending: "未受付", error: "要確認", drop: "取下げ" };
const RCT: Record<RC, string> = { received: "受付済み", got: "会場取得済（「取得済」の目印あり）", direct: "会場直（データは会場で受け取る）", byo: "PC持込（本人のPCで発表。データなしでもよい）", pending: "まだ受付していません", error: "要確認（下のラベル・右の注意を見てください）", drop: "演題取り下げ" };
function RIcon({ k }: { k: RC | "done" | "live" | "progress" }) {
  if (k === "got" || k === "direct" || k === "byo") k = "received";
  if (k === "received") return <svg className="ri" viewBox="0 0 14 14" aria-hidden="true"><circle cx="7" cy="7" r="6" fill="none" stroke="var(--g-received)" strokeWidth="1.5" /><path d="M4.4 7.1 6.2 8.9 9.6 5.3" fill="none" stroke="var(--g-received)" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" /></svg>;
  if (k === "error") return <svg className="ri" viewBox="0 0 14 14" aria-hidden="true"><circle cx="7" cy="7" r="6" fill="none" stroke="var(--g-error)" strokeWidth="1.5" /><path d="M7 4v3.6" stroke="var(--g-error)" strokeWidth="1.6" strokeLinecap="round" /><circle cx="7" cy="9.9" r=".9" fill="var(--g-error)" /></svg>;
  if (k === "done") return <svg className="ri" viewBox="0 0 14 14" aria-hidden="true"><circle cx="7" cy="7" r="7" fill="var(--g-done)" /><path d="M4.3 7.1 6.1 8.9 9.7 5.2" fill="none" stroke="#fff" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" /></svg>;
  if (k === "live") return <svg className="ri" viewBox="0 0 14 14" aria-hidden="true"><circle cx="7" cy="7" r="4" fill="var(--g-error)" /></svg>;
  if (k === "progress") return <svg className="ri" viewBox="0 0 14 14" aria-hidden="true"><circle cx="7" cy="7" r="6" fill="none" stroke="var(--g-progress)" strokeWidth="1.5" /><path d="M7 3.2A3.8 3.8 0 0 1 7 10.8Z" fill="var(--g-progress)" /></svg>;
  if (k === "drop") return <svg className="ri" viewBox="0 0 14 14" aria-hidden="true"><circle cx="7" cy="7" r="6" fill="none" stroke="var(--g-text-3)" strokeWidth="1.5" /><path d="m3 11 8-8" stroke="var(--g-text-3)" strokeWidth="1.5" /></svg>;
  return <svg className="ri" viewBox="0 0 14 14" aria-hidden="true"><circle cx="7" cy="7" r="6" fill="none" stroke="var(--g-pending)" strokeWidth="1.5" strokeDasharray="2.2 2" /></svg>;
}

/* このPCのコピー（行の右） */
const mainDest = () => OPEN.dest?.id || opDests()[0]?.id || "";
function copyOf(g: Group): { k: "ok" | "run" | "wait" | "bad" | "none"; t: string; pct?: number; tip?: string } {
  const S = store.S!; const a = S.op.active;
  if (a && a.rel.startsWith(g.key + "/") && (!a.dests || a.dests.includes(mainDest()))) { const pct = a.total ? Math.floor((a.done * 100) / a.total) : 0; return { k: "run", t: "コピー中 " + pct + "%", pct }; }
  if (g.pending) {   // NASへ書き込み中：受信済みサイズ・速度・経過時間
    const r = rootById(S.op.root || ""); const v = r ? rateOf(r.id, g) : 0;
    return { k: "run", t: (canOpen(g) ? "DL済・差し替えを受信中" : "NASに受信中") + (g.pbytes ? " " + fmtSize(g.pbytes) : ""),
      tip: "NASに受信中" + (g.pbytes ? " " + fmtSize(g.pbytes) : "") + (v ? " · " + fmtSize(v) + "/s" : "") + (g.pstart ? " · 経過 " + mss(Date.now() / 1000 + store.SKEW - g.pstart) : "") };
  }
  if (!hasData(g)) return { k: "none", t: isBYO(g) ? "PC持込（データなし）" : g.files ? "データなし（メモだけ）" : "データなし" };
  const st: CpState | undefined = g.cp?.[mainDest()];
  if (!st) return { k: "wait", t: "確認中" };
  if (st === "ok") return { k: "ok", t: isBYO(g) ? "DL済（バックアップ）" : "DL済" };
  if (st === "edited") return { k: "ok", t: "DL済（このPCで変更あり）" };
  const ps = g.cpp?.[mainDest()];
  if (ps === "old" || st === "old") return { k: "run", t: "前の版あり・新しい版はまだ" };
  if (st === "copying") return { k: "run", t: "コピー中" };
  if (st === "err" || st === "off") return { k: "bad", t: CPL[st][0] };
  return { k: "wait", t: CPL[st]?.[0] || st };
}

/* このPCのコピーから開けるか：メインのコピー先の状態だけで決める（バックアップへのコピー中・差し替えの受信中でも、前の版は開ける） */
const OPENABLE = ["ok", "edited", "old"];
/* 開けるか：発表ファイルの状態で決める（大きな動画のコピー中・差し替えの受信中でも、コピー済みのスライドは開ける）。サーバーの判定と同じ */
const canOpen = (g: Group) => { const st = (g.cpp || g.cp)?.[mainDest()]; return hasData(g) && !!st && OPENABLE.includes(st); };
/* 発表に使うデータがあるか（メモの .txt などだけなら「データなし」） */
const hasData = (g: Group) => g.files > 0 && Object.keys(g.cats || {}).some((c) => c !== "他");
/* PC持込（本人のPCで発表）：入っているデータは「バックアップ」として扱う */
const BYO_RE = /^(?:PC|Win|Mac)?持込(?:リモプレ)?$/i;   // 既定の目印（PC持込・Mac持込・持込…）だけ。「持込不可」などは含めない
const isBYO = (g: Group) => (g.fl || []).some((f) => BYO_RE.test(nfc(f[0]).replace(/[\s　]/g, "")));

/* ほかのコピー先（バックアップPCなど）の状態：小さな点で */
function OtherDests({ g }: { g: Group }) {
  const ds = opDests().filter((d) => d.id !== mainDest()); if (!ds.length || !g.files) return null;
  return <span className="odots">{ds.map((d) => {
    const st = d.online === false ? "off" : g.cp?.[d.id]; const x = st ? CPL[st] : null;
    const k = !x ? "wait" : x[1] === "ok" ? "ok" : x[1] === "run" ? "run" : x[1] === "bad" ? "bad" : "wait";
    return <i key={d.id} className={"pc " + k} title={d.label + "：" + (x ? x[0] : "確認中")} aria-label={d.label + "：" + (x ? x[0] : "確認中")} />;
  })}</span>;
}

/* ラベル：多くても2つまで（赤い注意 → オペの対応 → 差し替え → そのほか）。残りは「+N」 */
interface TagX { t: string; k: "bad" | "warn" | "op" | "repl" | "info"; p: number }
function tagsOf(g: Group): TagX[] {
  const out: TagX[] = []; const a = g.ana;
  for (const [l, role] of g.fl || []) out.push(role === "warn" ? { t: nfc(l), k: "bad", p: 0 } : role === "op" ? { t: nfc(l), k: "op", p: 1 } : { t: nfc(l), k: "info", p: 3 });
  if (a) {
    if (a.vfbad) out.push({ t: "動画の形式", k: "bad", p: 0 });
    else if (a.vfwarn || a.vwarn) out.push({ t: "動画 要試写", k: "warn", p: 1.5 });
    if (a.abad) out.push({ t: "音声リンク切れ", k: "bad", p: 0 });
    if (a.noclick) out.push({ t: "クリック無効", k: "bad", p: 0 });
    if (a.err) out.push({ t: "解析できない", k: "bad", p: 0 });
    if (a.video) out.push({ t: "動画", k: "info", p: 3 });
    if (a.coi) out.push({ t: "COI", k: "info", p: 3 });
    if (a.auto) out.push({ t: "自動送り", k: "info", p: 3 });
  }
  if (Object.values(g.cp || {}).includes("err")) out.push({ t: "コピーエラー", k: "bad", p: 0 });
  if (g.repl) out.push({ t: "差替 " + g.repl, k: "repl", p: 2 });
  return out.map((x, i) => ({ ...x, i })).sort((x, y) => x.p - y.p || x.i - y.i);
}
function Tags({ g, max = 2, fresh }: { g: Group; max?: number; fresh?: Set<string> }) {
  const all = tagsOf(g); const sh = all.slice(0, max); const rest = all.slice(max);
  return <>{sh.map((x) => <span key={x.t} className={cx("gt", fresh?.has(x.t) && "a-new")} data-k={x.k}>{x.k === "repl" && g.repl ? <>差替 <span className="roll" key={g.repl}>{g.repl}</span></> : x.t}</span>)}{rest.length > 0 && <span className="gt" data-k="more" title={rest.map((x) => x.t).join("・")}>+{rest.length}</span>}</>;
}

/* ---------------------------------------------------------------- 選んでいるセッション（このPCに保存） */
const GS: { ses: string; auto: boolean } = { ses: "", auto: true };
try { const v = localStorage.getItem("gate.ses"); if (v) { GS.ses = v; GS.auto = false; } } catch { /* */ }
/* いま本番で進んでいるセッション（発表中の人がいる／時刻が進行中） */
function liveSes(M: Model): Ses | null {
  return M.sessions.find((x) => x.list.some((g) => STG.st[M.r.id + "|" + g.key]?.st === "now")) || M.sessions.find((x) => M.tl.get(x.key)?.st === "live") || null;
}
function pickSes(k: string, manual = true) { GS.ses = k; GS.auto = !manual; try { manual ? localStorage.setItem("gate.ses", k) : localStorage.removeItem("gate.ses"); } catch { /* */ } store.emit(); }
function curSes(M: Model): Ses | null {
  const ss = M.sessions; if (!ss.length) return null;
  const hit = !GS.auto && ss.find((x) => x.key === GS.ses); if (hit) return hit;
  const now = ss.find((x) => x.list.some((g) => STG.st[M.r.id + "|" + g.key]?.st === "now"));   // 発表中の人がいるセッション（時間が延びていても）
  if (now) return now;
  const live = ss.find((x) => M.tl.get(x.key)?.st === "live") || ss.find((x) => M.tl.get(x.key)?.st === "next");
  if (live) return live;
  return M.tl.size && [...M.tl.values()].every((x) => x.st === "done") ? ss[ss.length - 1] : ss[0];
}

/* ---------------------------------------------------------------- 画面 */
export function GateApp() {
  const s = useApp(); const M = build();
  useEffect(() => { stageLoad(); const t = window.setInterval(stageLoad, 15000); return () => clearInterval(t); }, []);
  const ses = M ? curSes(M) : null;
  const [menu, setMenu] = useState<{ x: number; y: number; g: string } | null>(null);
  useEffect(() => { setMenu(null); }, [ses?.key, M?.day, s.q]);
  /* 本番で進んでいるセッションの「発表中」と「次」 */
  const live = M ? (liveSes(M) || ses) : null;
  const pair = live && M ? nowNext(M, live) : { cur: undefined, nx: undefined };
  /* 5. 発表中・次の人に差し替えが届いたら大きく知らせる */
  const replSeen = useRef(new Map<string, number>());
  const [alert, setAlert] = useState<{ key: string; who: string; role: string; n: number } | null>(null);
  useEffect(() => {
    for (const [g, role] of [[pair.cur, "発表中"], [pair.nx, "次"]] as [Group | undefined, string][]) {
      if (!g) continue; const n = g.repl || 0; const p = replSeen.current.get(g.key);
      if (p != null && n > p) setAlert({ key: g.key, who: nameOf(g).name, role, n });
      replSeen.current.set(g.key, n);
    }
  });
  /* 6. Stream Deck・Companion から（このPCの中だけ）：受けた操作を順に実行し、いまの状態を知らせる */
  const ref = useRef({ M, ses, live, pair }); ref.current = { M, ses, live, pair };
  useEffect(() => {
    let since = -1, stop = false, last = "";
    const tick = async () => {
      if (stop) return;
      try {
        const j: any = await api("/api/op/remote?since=" + Math.max(0, since));
        if (since < 0) since = j.seq;   // 開いた時より前の操作は実行しない
        for (const c of j.cmds || []) { if (c.seq <= since) continue; since = c.seq; runRemote(c.cmd, ref.current); }
        const { M: m, live: lv, pair: pr } = ref.current;
        const st = JSON.stringify({ now: pr.cur ? nameOf(pr.cur).name : "", next: pr.nx ? nameOf(pr.nx).name : "", session: lv ? sesLabel(lv) : "", venue: m ? nfc(store.S?.op.venue || "") : "" });
        if (st !== last) { last = st; api("/api/op/remote/status", JSON.parse(st)).catch(() => { last = ""; }); }
      } catch { /* 古いサーバー */ }
      if (!stop) window.setTimeout(tick, 600);
    };
    tick(); return () => { stop = true; };
  }, []);
  /* キーボード：N＝次の人へ、Enter＝選んでいる人を発表中に、↑↓＝選ぶ、Esc＝メニュー・ログを閉じる */
  useEffect(() => {
    const k = (e: KeyboardEvent) => {
      if (store.modal || (e.target as HTMLElement).closest("input,textarea,select")) return;
      if (e.key === "Escape") { if (menu) { setMenu(null); e.preventDefault(); e.stopImmediatePropagation(); } else if (store.q) { store.q = ""; store.emit(); e.preventDefault(); e.stopImmediatePropagation(); } return; }
      if (e.repeat) return;   // 押しっぱなしで何人も進めない
      if (!M || !ses || e.ctrlKey || e.metaKey || e.altKey || menu) return;   // メニューを開いている間は、後ろの一覧を動かさない
      const sel = store.SEL && store.SEL.root === M.r.id ? ses.list.findIndex((g) => g.key === store.SEL!.group) : -1;
      if (e.key === "n" || e.key === "N") { e.preventDefault(); nextUpGuard(M, ses); }
      else if (e.key === "Enter" && sel >= 0 && !ses.list[sel].mk_drop && !menu && !store.q && !(e.target as HTMLElement).closest("button,a,[role=menu],[role=tab]")) { e.preventDefault(); rowFx(ses.list[sel].key); setStage(M.r.id, ses.list[sel].key, "now"); }
      else if ((e.key === "ArrowDown" || e.key === "ArrowUp") && !store.q && !menu) {
        e.preventDefault(); const d = e.key === "ArrowDown" ? 1 : -1; let n = sel + d;
        while (ses.list[n] && ses.list[n].mk_drop) n += d;   // 取り下げは飛ばす
        if (ses.list[n]) selectGroup(M.r.id, ses.list[n].key);
      }
    };
    document.addEventListener("keydown", k, true); return () => document.removeEventListener("keydown", k, true);   // 先に受ける（Esc を二重に使わない）
  });
  return <div className={cx("gate", s.logOpen && "showlog")}>
    <Side M={M} ses={ses} />
    <TopBar M={M} ses={ses} />
    <main className="gmain">
      {alert && M && <ReplAlert M={M} a={alert} close={() => setAlert(null)} />}
      {M && ses ? <>
        <NowBlock M={M} ses={ses} />
        {s.q.trim() ? <Found M={M} onMenu={(x, y, g) => setMenu({ x, y, g })} /> : <List M={M} ses={ses} onMenu={(x, y, g) => setMenu({ x, y, g })} />}
      </> : <div className="gempty"><Icon n="shoe" /><b>{M ? "この日の演者フォルダはまだありません" : "会場が設定されていません"}</b>
        <span>{M ? "NASに演者フォルダができると、ここに発表順で並びます。" : "［設定］で NAS の学会フォルダと、このPCの会場を選んでください。"}</span></div>}
    </main>
    <Detail />
    {s.logOpen && <div className="glog"><LogPane /></div>}
    {menu && M && <RowMenu M={M} at={menu} close={() => setMenu(null)} />}
  </div>;
}

/* 発表中の人と次の人（取り下げ・発表済みは飛ばす） */
function nowNext(M: Model, ses: Ses) {
  const L = ses.list.filter((g) => !g.mk_drop);
  const cur = L.find((g) => stageOf(M.r.id, g.key, g) === "now"); const ci = cur ? L.indexOf(cur) : -1;
  const nx = ci >= 0 ? L[ci + 1] : L.find((g) => stageOf(M.r.id, g.key, g) !== "done");
  return { cur, nx };
}
/* Stream Deck・Companion からの操作 */
function runRemote(cmd: string, c: { M: Model | null; ses: Ses | null; live: Ses | null; pair: { cur?: Group; nx?: Group } }) {
  const { M, live } = c; if (!M || !live) return;
  if (cmd === "next") { pressFx("bNext"); nextUp(M.r, live); return; }
  if (cmd === "prev") {   // 1人戻す：いまの人を未発表に戻し、前の人を発表中に
    const L = live.list.filter((g) => !g.mk_drop); const i = L.findIndex((g) => stageOf(M.r.id, g.key, g) === "now");
    const p = i > 0 ? L[i - 1] : i < 0 ? [...L].reverse().find((g) => stageOf(M.r.id, g.key, g) === "done") : undefined;
    if (!p) return; const cur = i >= 0 ? L[i] : undefined;
    setStage(M.r.id, p.key, "now"); if (cur) setStage(M.r.id, cur.key, ""); selectGroup(M.r.id, p.key); return;
  }
  const g = c.pair.cur || c.pair.nx; if (!g) { toast("開く演者がいません（発表中の人がいません）", 3000); return; }
  opOpen(M.r.id, g.key, "", cmd === "file" ? "file" : cmd === "folder" ? "folder" : "show");
}
let lastN = 0; let warnN = 0;
function pressFx(id: string) {   // キーで押したときも、ボタンが押されたように見せる
  const el = document.getElementById(id); if (!el) return;
  el.classList.remove("kpress"); void el.offsetWidth; el.classList.add("kpress");
}
function nextUpGuard(M: Model, ses: Ses) {
  if (Date.now() - lastN < 400) return;   // 連打・ダブルクリックで2人進めない
  lastN = Date.now(); pressFx("bNext");
  const lv = liveSes(M);
  if (lv && lv.key !== ses.key && Date.now() - warnN > 4000) {   // 進行中ではないセッションを見ているとき：もう一度押したら進める
    warnN = Date.now(); toast("いま表示しているのは進行中のセッションではありません（進行中：" + sesLabel(lv) + "）。このセッションで進めるなら、もう一度押してください", 4000); return;
  }
  warnN = 0; nextUp(M.r, ses);
}
function nextUp(r: Root, ses: Ses) {
  const L = ses.list.filter((g) => !g.mk_drop);
  const i = L.findIndex((g) => stageOf(r.id, g.key, g) === "now");
  const nx = i >= 0 ? L[i + 1] : L.find((g) => stageOf(r.id, g.key, g) !== "done");
  if (i >= 0 && !nx) { setStage(r.id, L[i].key, "done"); toast("このセッションの最後の演者でした（発表済みにしました）", 4000); return; }
  if (!nx) { toast("このセッションは全員発表済みです", 3000); return; }
  setStage(r.id, nx.key, "now"); selectGroup(r.id, nx.key);
}

/* ---- 左：会場・DAY・セッション */
function Side({ M, ses }: { M: Model | null; ses: Ses | null }) {
  const s = store; const S = s.S!; const o = S.op;
  const venue = nfc((o.venue || "").split("/").filter(Boolean).filter((x) => !dayInfo(x)).pop() || (M ? M.r.label : ""));
  const nb = netBadge();
  const daySet = async (v: string) => {
    if (!M) return;
    if (M.dayMode === "path") { setDay(v); pickSes("", false); return; }
    if (!S.local) return;
    try { const j: any = await api("/api/opday", { day: v }); pickSes("", false); toast("「" + v + "」にしました（" + nfc(j.venue) + " を監視・コピーします）", 4000); await loadState(); }
    catch (e: any) { toast(e.message, 6000); }
  };
  return <aside className="gside">
    <div className="gws"><img src={APP_ICON} alt="" width={20} height={20} /><b>PADDOCK GATE</b><span className="sub" title={rootTip(M)}>{M && <i className={"pc " + (M.r.online === false ? "bad" : M.r.online ? "ok" : "run")} />}{venue}</span></div>
    <div className="gsearch"><Icon n="search" /><input id="q" type="text" aria-label="演者・セッションを検索" placeholder="演者・セッションを検索" autoComplete="off" value={s.q}
      onChange={(e) => { s.q = e.target.value; s.emit(); }} onKeyDown={(e) => { if (e.key === "Escape") { s.q = ""; s.emit(); (e.target as HTMLInputElement).blur(); } }} />
      {s.q && <button className="x" title="検索をやめる（Esc）" onClick={() => { s.q = ""; s.emit(); }}><Icon n="x" /></button>}</div>
    {M && M.days.length > 0 && <div className="gdays">
      <Segmented label="日の切り替え" value={M.day} onChange={daySet} className="gseg"
        items={M.days.map((d) => ({ v: d, id: "gday-" + d, title: isTodayLabel(d) ? "今日" : d, label: <>{nfc(dayInfo(d)?.tok || d)}{isTodayLabel(d) && <i className="today" aria-label="今日" />}</> }))} />
    </div>}
    <div className="gh">セッション{M ? " · " + M.sessions.length : ""}</div>
    <nav className="gses" id="gses">{M && M.sessions.map((x) => {
      const st = M.tl.get(x.key); const n = x.list.filter((g) => !g.mk_drop); const rc = recvCount(n);
      const ic = st?.st === "done" ? "done" : st?.st === "live" ? "live" : st?.st === "next" ? "progress" : "pending";
      return <button key={x.key} aria-current={ses?.key === x.key ? "true" : undefined} className={cx("gs", ses?.key === x.key && "on")} data-ses={x.key} onClick={() => pickSes(x.key)} title={nfc(x.name)}>
        <RIcon k={ic as any} /><span className="nm">{sesLabel(x)}</span><span className="c">{rc}/{n.length}</span>
        <span className="tm">{x.t ? fmtT(x.t.s) + (x.t.e != null ? "–" + fmtT(x.t.e) : "〜") : ""}
          {st?.st === "live" && <span className="live">進行中{st.rem != null ? " 残り" + st.rem + "分" : ""}</span>}
          {st?.st === "next" && <span className="nxt">次 · あと{Math.max(0, st.until)}分</span>}
          {st?.st === "done" && <span>終了</span>}</span>
      </button>;
    })}</nav>
    <div className="gfoot">
      <button className="gb" id="bCfg" onClick={() => openCfg()}><Icon n="cog" />設定</button>
      <button className={cx("gb", nb.has && "has")} id="bNet" title={nb.title} onClick={() => netOpen()}><Icon n="net" />共有</button>
      {S.local && <button className="gb icon" id="bQuit" title="アプリを終了（ウィンドウを閉じても、コピーは裏で続けます）" onClick={quitApp}><Icon n="power" /></button>}
    </div>
  </aside>;
}

/* NAS（監視フォルダ）の状態：会場名にマウスを乗せると出す */
function rootTip(M: Model | null) {
  if (!M) return ""; const r = M.r;
  const st = !r.enabled ? "停止中" : r.online === false ? "接続できません" : r.online === null ? "確認中…" : r.pending ? "変化を確認中 " + r.pending : "監視中";
  return nfc(store.S!.op.venue || "") + "\n" + nfc(r.label) + "　" + st + (r.online ? `\n${(r.count || 0).toLocaleString()}件${r.scan_ms != null ? " · " + (r.scan_ms / 1000).toFixed(1) + "s" : ""}${r.last_scan ? " · " + hms(r.last_scan) : ""}` : "") + "\n" + r.path + (r.error ? "\n" + r.error : "") + (r.n_warns ? "\n読めないフォルダ " + r.n_warns + "件" : "");
}

/* ---- 上：セッション名とコピーの状況 */
function TopBar({ M, ses }: { M: Model | null; ses: Ses | null }) {
  const S = store.S!; const L = ses ? ses.list.filter((g) => !g.mk_drop) : [];
  const ds = opDests();
  return <div className="gbar">
    {ses ? <><b className="st-t">{sesLabel(ses)}</b>{ses.t && <span className="st-tm">{fmtT(ses.t.s)}{ses.t.e != null ? "–" + fmtT(ses.t.e) : ""}</span>}</> : <b className="st-t">{M ? nfc(M.r.label) : "PADDOCK GATE"}</b>}
    {!store.conn && <span className="gchip bad">アプリに再接続中…</span>}
    {M && M.r.online === false && <span className="gchip bad" title={nfc(M.r.path) + (M.r.error ? "\n" + M.r.error : "")}><RIcon k="error" /><b>NASに接続できません</b>{M.r.last_scan ? <span>最終確認 {hms(M.r.last_scan).slice(0, 5)}・表示は古い可能性</span> : null}</span>}
    {M && ses && (() => { const lv = liveSes(M); return lv && lv.key !== ses.key ? <button className="gchip btn warnc" onClick={() => pickSes("", false)} title="自動で進行中のセッションを表示するように戻します">進行中のセッションではありません<b>進行中へ戻る</b></button> : null; })()}
    <span className="sp" />
    {ds.map((d) => {
      if (d.online === false) return <button key={d.id} className="gchip bad btn" title={d.path + (d.error ? "\n" + d.error : "") + "\nクリックで原因を調べます（つながったら自動でコピーします）"} onClick={() => netOpen()}><RIcon k="error" />{d.label}<b>接続できません</b><span className="lnk">原因を調べる</span></button>;
      const has = L; const ok = L.filter((g) => hasData(g) && (g.cp?.[d.id] === "ok" || g.cp?.[d.id] === "edited")).length;   // 分母は演者の人数（データのない人も数える）
      const nod = L.filter((g) => !hasData(g)).length;
      const c = d.count || {}; const busy = (c.busy || 0) + (c.srcbusy || 0); const bad = c.err || 0;
      return <span key={d.id} className={cx("gchip", ok > 0 && ok === has.length - nod && "full", bad && "bad")}
        title={d.path + `\nこのセッション：DL済 ${ok}/${has.length}人` + (nod ? `（データなし ${nod}人）` : "") + `\n会場全体：コピー済み ${(c.ok || 0) + (c.edited || 0)}/${d.total || 0}` + (busy ? `\n差し替え待ち ${busy}（コピー先で開かれているため、閉じたら差し替えます）` : "") + (bad ? `\nエラー ${bad}` : "")}>
        <i className="pc ok" />{d.label}<b>{ok}/{has.length}</b>DL済<Bar pct={has.length ? (ok * 100) / has.length : 0} className="gtrack" />
        {busy > 0 && <span className="sub2">差し替え待ち {busy}</span>}{bad > 0 && <b className="e">エラー {bad}</b>}</span>;
    })}
    {(() => { const n = L.filter((g) => copyOf(g).k === "run").length; return n > 0 && <span className="gchip"><i className="pc run" />コピー中<b>{n}</b></span>; })()}
    {(() => { const n = L.filter((g) => rcOf(g) === "error").length; return n > 0 && <span className="gchip bad pop" key={"w" + n}><RIcon k="error" />要確認<b>{n}</b></span>; })()}
    {S.op.active && (() => {   // いまコピーしているファイル・進み具合・残り
      const a = S.op.active!; const pct = a.total ? Math.floor((a.done * 100) / a.total) : 0; const here = L.some((g) => a.rel.startsWith(g.key + "/"));
      return <span className="gchip act" title={nfc(a.rel)}><Icon n="spin" className="spin" /><span className="fn">{here ? "" : "ほかのセッション · "}{nfc(a.rel.split("/").pop())}</span><b>{pct}%</b>{(S.op.queue || 0) > 1 && <span className="sub2">残り {(S.op.queue || 0) - 1}</span>}</span>;
    })()}
    <LogButton />
  </div>;
}

/* 中身が変わったとき：前のものが上へ抜け、新しいものが下から入る（最初の表示では動かさない） */
function Swap({ k, children }: { k: string; children: React.ReactNode }) {
  const [gone, setGone] = useState<{ k: string; n: React.ReactNode }[]>([]);   // 抜けていく途中の前の中身
  const last = useRef<{ k: string; n: React.ReactNode; moved: boolean }>({ k, n: children, moved: false });
  if (last.current.k !== k) {   // 描くときに入れ替えを決める（effect で毎回 state を変えない）
    const old = last.current; last.current = { k, n: children, moved: true };
    queueMicrotask(() => setGone((a) => [...a.filter((x) => x.k !== k && x.k !== old.k), { k: old.k, n: old.n }]));
  } else last.current.n = children;
  useEffect(() => { if (!gone.length) return; const t = setTimeout(() => setGone([]), 260); return () => clearTimeout(t); }, [gone]);
  return <div className="swap">
    {gone.filter((x) => x.k !== k).map((x) => <div key={"o" + x.k} className="sw out" aria-hidden="true">{x.n}</div>)}
    <div key={k} className={cx("sw", last.current.moved && "in")}>{children}</div>
  </div>;
}

/* ---- 中央の上：発表中の人・次の人へ */
function NowBlock({ M, ses }: { M: Model; ses: Ses }) {
  const cur = ses.list.find((g) => stageOf(M.r.id, g.key, g) === "now");
  const L = ses.list.filter((g) => !g.mk_drop); const ci = cur ? L.indexOf(cur) : -1;
  const nx = ci >= 0 ? L[ci + 1] : L.find((g) => stageOf(M.r.id, g.key, g) !== "done");
  return <div className="gnow">
    <div className="cur">
      <div className="lb">発表中</div>
      <Swap k={cur ? cur.key : "-"}>{cur ? <div className="who"><span className="o">{ci + 1}</span>{nameOf(cur).name}<span className="no">{nameOf(cur).no}</span></div>
        : <div className="tt">まだいません（右クリック「発表中にする」か ［次の人へ］）</div>}</Swap>
    </div>
    <div className="cur nxb">
      <div className="lb">次</div>
      <Swap k={nx ? nx.key : "-"}>{nx ? <div className="who dim2"><span className="o">{L.indexOf(nx) + 1}</span>{nameOf(nx).name}<span className="no">{nameOf(nx).no}</span></div> : <div className="tt">—</div>}</Swap>
    </div>
    <button className="gb big" id="bNext" onMouseUp={(e) => e.currentTarget.blur()} onClick={() => nextUpGuard(M, ses)} title="いまの人を発表済みにして、次の人を発表中にします（キー N）">
      {cur ? "次の人へ" : "最初の人を発表中に"}<Icon n="chev" /><kbd>N</kbd></button>
    <div className="keys">↑↓ 選ぶ・Enter 発表中にする・右クリック メニュー</div>
  </div>;
}

/* ---- 中央：発表順の一覧 */
function List({ M, ses, onMenu }: { M: Model; ses: Ses; onMenu: (x: number, y: number, g: string) => void }) {
  const s = store; const box = useRef<HTMLDivElement>(null);
  // セッションを切り替えた向き：後ろのセッションなら右から、前なら左から
  const sv = useRef({ key: ses.key, idx: M.sessions.indexOf(ses), dir: "" });
  if (sv.current.key !== ses.key) { const idx = M.sessions.findIndex((x) => x.key === ses.key); sv.current = { key: ses.key, idx, dir: idx >= sv.current.idx ? "from-r" : "from-l" }; }
  // 行が増えた・減ったとき：残る行はもとの位置から すっと移動、新しい行はふわっと入る（FLIP。transform だけ）
  const pos = useRef<{ key: string; m: Map<string, number> }>({ key: "", m: new Map() });
  useLayoutEffect(() => {
    const el = box.current; if (!el) return;
    const rows = [...el.querySelectorAll<HTMLElement>(".grows > .grow")]; const prev = pos.current; const same = prev.key === ses.key;
    const m = new Map<string, number>();
    for (const r of rows) {
      const g = r.dataset.g || ""; const y = r.offsetTop; m.set(g, y);
      if (!same || !prev.m.size) continue;
      const py = prev.m.get(g);
      if (py == null) { r.classList.remove("a-new"); void r.offsetWidth; r.classList.add("a-new"); continue; }
      if (py !== y) { r.style.transition = "none"; r.style.transform = `translateY(${py - y}px)`; void r.offsetWidth; r.style.transition = ""; r.style.transform = ""; r.classList.add("flip"); }
    }
    pos.current = { key: ses.key, m };
  });
  const [ind, setInd] = useState<{ y: number; h: number } | null>(null);
  const curKey = ses.list.find((g) => stageOf(M.r.id, g.key, g) === "now")?.key || "";
  useLayoutEffect(() => {   // 発表中の帯：行から行へすべって移動する
    const el = curKey ? box.current?.querySelector<HTMLElement>(`.grow[data-g="${CSS.escape(curKey)}"]`) : null;
    const v = el ? { y: el.offsetTop, h: el.offsetHeight } : null;
    setInd((o) => (o && v && o.y === v.y && o.h === v.h) || (!o && !v) ? o : v);
  });
  const L = ses.list.filter((g) => !g.mk_drop);
  const r = recvCount(L); const cnt = { r, p: L.length - r, e: L.filter((g) => rcOf(g) === "error").length };
  return <div className="glist scroll" id="groups" ref={box}>
    <div className="ghd">発表順 · {L.length}人{ses.custom && <button className="reorder" onClick={() => { saveOrder(M.r.id, ses, null); toast("発表順を元に戻しました（フォルダ名の順）"); }} title="ドラッグで変えた発表順をやめて、フォルダ名の順に戻します">順番を変更中 · 元に戻す</button>}<span className="legend"><span><RIcon k="received" />受付済 {cnt.r}</span><span><RIcon k="pending" />未受付 {cnt.p}</span>{cnt.e > 0 && <span><RIcon k="error" />要確認 {cnt.e}</span>}</span></div>
    <div className={cx("grows", sv.current.dir)} key={ses.key}>
      {ind && <span className="nowind" style={{ transform: `translateY(${ind.y}px)`, height: ind.h }} aria-hidden="true" />}
      {ses.list.map((g, i) => <Row key={g.key} r={M.r} g={g} ord={g.mk_drop ? 0 : L.indexOf(g) + 1} i={i} sel={!!s.SEL && s.SEL.root === M.r.id && s.SEL.group === g.key} onMenu={onMenu}
        drag={{ start: () => { DRAG.key = g.key; }, over: (before) => { DRAG.to = before ? i : i + 1; }, drop: () => { if (DRAG.key) { const from = ses.list.findIndex((x) => x.key === DRAG.key); let to = DRAG.to; if (from < to) to--; moveRow(M.r.id, ses, DRAG.key, to); DRAG.key = ""; } } }} />)}
    </div>
  </div>;
}
/* 検索：その日の全セッションから（演者名・番号・セッション名） */
function Found({ M, onMenu }: { M: Model; onMenu: (x: number, y: number, g: string) => void }) {
  const s = store; const q = nfc(s.q).toLowerCase().trim();
  const hits = M.sessions.flatMap((x) => x.list.filter((g) => nfc(g.key.split("/").slice(-2).join("/")).toLowerCase().includes(q) || sesLabel(x).toLowerCase().includes(q)).map((g) => ({ x, g })));
  return <div className="glist scroll" id="groups">
    <div className="ghd">検索「{s.q.trim()}」 · {hits.length}人<span className="legend"><span>Esc で戻る</span></span></div>
    {!hits.length ? <div className="gempty sm"><span>見つかりません</span></div>
      : <div className="grows">{hits.map(({ x, g }, i) => <Fragment key={g.key}>
        {(i === 0 || hits[i - 1].x !== x) && <div className="gsesh"><button onClick={() => { s.q = ""; pickSes(x.key); }}>{sesLabel(x)}{x.t ? "　" + fmtT(x.t.s) : ""}<Icon n="chev" /></button></div>}
        <Row r={M.r} g={g} ord={x.list.filter((y) => !y.mk_drop).indexOf(g) + 1} i={i} sel={!!s.SEL && s.SEL.root === M.r.id && s.SEL.group === g.key} onMenu={onMenu} /></Fragment>)}</div>}
  </div>;
}
const DRAG = { key: "", to: 0 };
type DragH = { start: () => void; over: (before: boolean) => void; drop: () => void };
function Row({ r, g, ord, i, sel, onMenu, drag }: { r: Root; g: Group; ord: number; i: number; sel: boolean; onMenu: (x: number, y: number, g: string) => void; drag?: DragH }) {
  const [dz, setDz] = useState<"" | "top" | "bot">("");
  const st = stageOf(r.id, g.key, g); const rc = rcOf(g); const cp = copyOf(g); const nm = nameOf(g);
  const prev = useRef(cp.k); const [pop, setPop] = useState(false);
  useEffect(() => { if (prev.current !== cp.k && cp.k === "ok" && prev.current === "run") { setPop(true); const t = setTimeout(() => setPop(false), 700); prev.current = cp.k; return () => clearTimeout(t); } prev.current = cp.k; }, [cp.k]);
  const ref = useRef<HTMLDivElement>(null);
  useEffect(() => { if (sel) ref.current?.scrollIntoView({ block: "nearest" }); }, [sel]);
  // 差し替えが届いた：行が一瞬光る
  const pr = useRef(g.repl || 0);
  useEffect(() => { const n = g.repl || 0; if (n > pr.current && ref.current) { const el = ref.current; el.classList.remove("rflash"); void el.offsetWidth; el.classList.add("rflash"); } pr.current = n; }, [g.repl]);
  // 新しく出た赤いラベル（要確認）：小さく弾んで輪が一度広がる
  const bad = tagsOf(g).filter((x) => x.k === "bad").map((x) => x.t).join("|");
  const pb = useRef(new Set(bad ? bad.split("|") : [])); const [fresh, setFresh] = useState<Set<string>>(new Set());
  useEffect(() => {
    const now = new Set(bad ? bad.split("|") : []); const nw = new Set([...now].filter((x) => !pb.current.has(x))); pb.current = now;
    if (nw.size) { setFresh(nw); const t = setTimeout(() => setFresh(new Set()), 1200); return () => clearTimeout(t); }
  }, [bad]);
  return <div ref={ref} className={cx("grow grp", sel && "sel", st === "done" && "past", st === "now" && "now", g.mk_drop && "drop", store.flashKeys.has(r.id + "|" + g.key) && "flash")}
    data-r={r.id} data-g={g.key} style={{ ["--i" as any]: Math.min(i, 12) }}
    onClick={(e) => rowClick(e, r.id, g.key)}
    onContextMenu={(e) => { e.preventDefault(); selectGroup(r.id, g.key); onMenu(e.clientX, e.clientY, g.key); }}
    draggable={!!drag} onDragStart={(e) => { e.dataTransfer.effectAllowed = "move"; try { e.dataTransfer.setData("text/plain", g.key); } catch { /* */ } drag?.start(); }}
    onDragOver={(e) => { if (!drag) return; e.preventDefault(); const rc = e.currentTarget.getBoundingClientRect(); const b = e.clientY < rc.top + rc.height / 2; setDz(b ? "top" : "bot"); drag.over(b); }}
    onDragLeave={() => setDz("")} onDrop={(e) => { e.preventDefault(); setDz(""); drag?.drop(); }} onDragEnd={() => setDz("")}
    data-dz={dz || undefined}>
    {drag && <span className="grip" aria-hidden="true"><Icon n="grip" /></span>}<span className="ord">{ord || ""}</span><RIcon k={rc} /><span className={"rcv " + rc} title={RCT[rc]}>{RCL[rc]}</span>
    {nm.no && <span className="no">{nm.no}</span>}<span className="nm">{nm.name}</span>
    <span className="tags"><Tags g={g} fresh={fresh} /></span><span className="gap" />
    <span className="state">{st === "now" ? <span className="pill now">発表中</span>
      : st === "done" ? <><RIcon k="done" />発表済み</>
        : <><i className={cx("pc", cp.k, pop && "pop")} /><span title={cp.tip}>{cp.t}</span>{cp.pct != null && <Bar pct={cp.pct} className="gtrack sm" />}<OtherDests g={g} /></>}</span>
  </div>;
}

/* 同じ行を 0.45 秒以内に2回クリック＝ダブルクリック（1回目で画面が描き直されても確実に判定する） */
let LAST: { g: string; t: number; x: number; y: number } | null = null;
function rowClick(e: React.MouseEvent, root: string, group: string) {
  const c = LAST; const k = root + "|" + group;
  if (c && c.g === k && Date.now() - c.t < 450 && Math.abs(e.clientX - c.x) < 8 && Math.abs(e.clientY - c.y) < 8) { LAST = null; dblOpen(root, group); return; }
  LAST = { g: k, t: Date.now(), x: e.clientX, y: e.clientY }; selectGroup(root, group);
}
/* ダブルクリック：設定（［設定］→ 演者のスライドを開く）に合わせて開く */
function rowFx(key: string) {   // 行が押されたように一瞬沈む
  const el = document.querySelector<HTMLElement>(`.grow[data-g="${CSS.escape(key)}"]`); if (!el) return;
  el.classList.remove("kpress"); void el.offsetWidth; el.classList.add("kpress");
}
function dblOpen(root: string, group: string) {
  rowFx(group);
  if (!OPEN.settings.enabled) { toast("ダブルクリックで開くには、［設定］→「演者のスライドを開く」をオンにしてください", 7000); return; }
  opOpen(root, group, "", OPEN.settings.dbl);
}
const SHOWX = /\.(pptx?|ppsx?|pptm|ppsm)$/i, PRESX = /\.(pptx?|ppsx?|pptm|ppsm|key|pdf)$/i;

/* ---- 右クリックのメニュー */
function RowMenu({ M, at, close }: { M: Model; at: { x: number; y: number; g: string }; close: () => void }) {
  const ref = useRef<HTMLDivElement>(null); const [pos, setPos] = useState({ x: at.x, y: at.y });
  const g = (M.r.groups || []).find((x) => x.key === at.g); const st = stageOf(M.r.id, at.g);
  useLayoutEffect(() => {   // 画面からはみ出さないように
    const el = ref.current; if (!el) return; const w = el.offsetWidth, h = el.offsetHeight;
    // 画面が広いと .gate を 1.08 倍にしているので、座標を倍率で割って合わせる
    const z = parseFloat(getComputedStyle(el.closest(".gate") || el).zoom || "1") || 1;
    const W = window.innerWidth / z, H = window.innerHeight / z;
    setPos({ x: Math.max(8, Math.min(at.x / z, W - w - 8)), y: Math.max(8, Math.min(at.y / z, H - h - 8)) });
    el.querySelector<HTMLElement>("button")?.focus();
  }, [at.x, at.y]);
  useEffect(() => {
    const c = (e: MouseEvent) => { if (!ref.current?.contains(e.target as Node)) close(); };
    const w = () => close();
    const sc = (e: Event) => { if (!ref.current?.contains(e.target as Node)) close(); };
    document.addEventListener("mousedown", c); window.addEventListener("blur", w); window.addEventListener("resize", w); document.addEventListener("scroll", sc, true);
    return () => { document.removeEventListener("mousedown", c); window.removeEventListener("blur", w); window.removeEventListener("resize", w); document.removeEventListener("scroll", sc, true); };
  }, []);
  useEffect(() => { if (!g) close(); }, [g]);
  if (!g) return null;
  const has = g.files > 0 && OPEN.settings.enabled; const ok = canOpen(g); const s0 = store;
  const it = (label: React.ReactNode, f: () => void, opt: { k?: string; dis?: boolean; ic?: React.ReactNode; id?: string } = {}) =>
    <button className="it" id={opt.id} disabled={opt.dis} onClick={(e) => { e.currentTarget.classList.add("hit"); setTimeout(() => { close(); f(); }, 90); }}>{opt.ic}{label}{opt.k && <kbd>{opt.k}</kbd>}</button>;
  const onKey = (e: React.KeyboardEvent) => {
    const bs = [...(ref.current?.querySelectorAll<HTMLButtonElement>("button:not(:disabled)") || [])]; const i = bs.indexOf(document.activeElement as HTMLButtonElement);
    if (e.key === "ArrowDown" || e.key === "ArrowUp") { e.preventDefault(); e.stopPropagation(); bs[(i + (e.key === "ArrowDown" ? 1 : bs.length - 1)) % bs.length]?.focus(); }
    if (e.key === "Escape") { e.preventDefault(); e.stopPropagation(); close(); }
  };
  return <div className="gmenu" ref={ref} role="menu" style={{ left: pos.x, top: pos.y }} onKeyDown={onKey} id="gmenu">
    <div className="hd">{nameOf(g).no} {nameOf(g).name}</div>
    {st !== "now" && it("発表中にする", () => setStage(M.r.id, g.key, "now"), { k: "Enter", ic: <RIcon k="live" />, id: "mNow" })}
    {st !== "done" && it("発表済みにする", () => setStage(M.r.id, g.key, "done"), { ic: <RIcon k="done" />, id: "mDone" })}
    {STG.st[M.r.id + "|" + g.key] && it("未発表に戻す", () => setStage(M.r.id, g.key, ""), { ic: <Icon n="chevL" />, id: "mReset" })}
    {!s0.q && (() => { const ss = curSes(M); const ix = ss ? ss.list.findIndex((x) => x.key === g.key) : -1; return ss && ix >= 0 ? <>
      {ix > 0 && it("1つ上へ（発表順）", () => moveRow(M.r.id, ss, g.key, ix - 1), { ic: <Icon n="up" /> })}
      {ix < ss.list.length - 1 && it("1つ下へ（発表順）", () => moveRow(M.r.id, ss, g.key, ix + 1), { ic: <Icon n="down" /> })}</> : null; })()}
    <div className="sep" />
    {it(isBYO(g) ? "バックアップを開く（スライドショー）" : "スライドショーで開く", () => opOpen(M.r.id, g.key, "", "show"), { dis: !has || !ok, ic: <Icon n="play" />, id: "mShow" })}
    {it("発表ファイルを開く", () => opOpen(M.r.id, g.key, "", "file"), { dis: !has || !ok, ic: <Icon n="file" /> })}
    {it("フォルダを開く", () => opOpen(M.r.id, g.key, "", "folder"), { dis: !has, ic: <Icon n="folder" /> })}
    <div className="sep" />
    {it("NASのパスをコピー", () => copyText(nfc(M.r.path.replace(/[\\/]+$/, "") + (M.r.path.includes("\\") ? "\\" + g.key.split("/").join("\\") : "/" + g.key))).then(() => toast("パスをコピーしました"), () => toast("コピーできませんでした")), { ic: <Icon n="copy" /> })}
  </div>;
}

/* 準備用：ファイルの一覧（大きさ・更新・NASで追加/更新・コピー先ごとの状態・開く） */
function FileTable({ F }: { F: Folder }) {
  const rows = F.items.filter((i) => !i.d).sort((a, b) => cmpPath(a.p, b.p)); const ds = (F.op?.dests || []).filter((d) => d.enabled); const on = OPEN.settings.enabled;
  if (!rows.length) return <div className="dim" style={{ padding: "4px 0 8px" }}>空のフォルダです</div>;
  return <table className="gft"><tbody>{rows.map((i) => {
    const c = i.cp?.[mainDest()]?.[0]; const ok = on && !i.mk && !!c && OPENABLE.includes(c);
    return <tr key={i.p} className={cx(i.st === "pending" && "pend")}>
      <td className="fn" title={nfc(i.p)}>{nfc(i.p)}{i.mk && <span className="gt" data-k="info">{i.mk === "meta" ? "付帯情報" : "目印"}</span>}{i.st && i.st !== "pending" && <span className="gt" data-k="repl">{i.st === "add" ? "追加" : i.st === "mod" ? "更新" : "名前変更"}</span>}{i.st === "pending" && <span className="gt" data-k="warn">受信中</span>}</td>
      <td className="num">{i.mk ? "" : fmtSize(i.s)}</td><td className="tm">{i.m ? dtm(i.m) : ""}</td>
      <td className="cps">{!i.mk && ds.map((d) => { const x = i.cp?.[d.id]; const y = x ? CPL[x[0]] : null; const k = !y ? "wait" : y[1] === "ok" ? "ok" : y[1] === "run" ? "run" : y[1] === "bad" ? "bad" : "wait";
        return <i key={d.id} className={"pc " + k} title={d.label + "：" + (y ? y[0] : "確認中") + (x && x[1] ? " — " + x[1] : "")} />; })}</td>
      <td className="op">{!i.mk && <>{SHOWX.test(i.p) && <OpenBtn cls="gb icon sm" how="show" F={F} rel={i.p} disabled={!ok} title="スライドショーで開く"><Icon n="play" /></OpenBtn>}
        <OpenBtn cls="gb icon sm" how="file" F={F} rel={i.p} disabled={!ok} title="開く"><Icon n="file" /></OpenBtn></>}</td></tr>;
  })}</tbody></table>;
}

/* 差し替えが届いた（発表中・次の人）：上に大きく。開いている前の版を閉じると新しい版に入れ替わる */
function ReplAlert({ M, a, close }: { M: Model; a: { key: string; who: string; role: string; n: number }; close: () => void }) {
  const g = (M.r.groups || []).find((x) => x.key === a.key); if (!g) return null;
  const st = g.cp?.[mainDest()]; const ps = (g.cpp || g.cp)?.[mainDest()];
  const msg = st === "busy" ? "PowerPoint などで開いている前の版を閉じると、新しい版に入れ替わります"
    : ps === "ok" || ps === "edited" ? "新しい版はこのPCにコピー済みです。開いているなら開き直してください"
      : "新しい版をコピーしています";
  return <div className="galert" role="alert"><RIcon k="error" /><div><b>差し替えが届きました：{a.role}の {a.who}（{a.n}回目）</b><span>{msg}</span></div>
    {(ps === "ok" || ps === "edited") && <button className="gb" onClick={() => { opOpen(M.r.id, g.key, "", "show"); close(); }}><Icon n="play" />開き直す</button>}
    <button className="gb icon" title="閉じる" onClick={close}><Icon n="x" /></button></div>;
}

/* 押した手ごたえ：押す → 「開いています…」（くるくる）→ 開けたら「開きました」✓ を一瞬、だめなら軽く揺れる */
function OpenBtn({ id, cls, how, F, rel = "", disabled, title, children, done }: {
  id?: string; cls: string; how: "show" | "file" | "folder"; F: Folder; rel?: string; disabled?: boolean; title?: string; children: React.ReactNode; done?: string;
}) {
  const [st, setSt] = useState<"" | "run" | "ok" | "ng">("");
  const t = useRef(0);
  useEffect(() => () => clearTimeout(t.current), []);
  const go = async () => {
    if (st === "run") return;
    setSt("run"); const ok = await opOpen(F.root, F.group, rel, how);
    setSt(ok ? "ok" : "ng"); clearTimeout(t.current); t.current = window.setTimeout(() => setSt(""), ok ? 1400 : 600);
  };
  return <button id={id} className={cx(cls, "ob", st && "is-" + st)} disabled={disabled} title={title} onClick={go} aria-busy={st === "run" || undefined}>
    <span className="ob-in">{st === "run" ? <><Icon n="spin" className="spin" />{done ? "開いています…" : null}</> : st === "ok" ? <><Icon n="chk" />{done || null}</> : children}</span>
  </button>;
}

/* ---- 右：選んだ演者（本番で使うものだけ。解析の詳細はたたんでおく） */
function Detail() {
  const s = store; const F = s.F; const r = F ? rootById(F.root) : null;
  const g = F && r ? (r.groups || []).find((x) => x.key === F.group) : null;
  if (!F || !g || !s.SEL || F.group === "" || !inVenue(F.root, F.group)) return <aside className="gdet"><div className="gempty sm"><Icon n="shoe" /><span>演者を選ぶと、ここにスライドショーのボタンと注意点が出ます。</span></div></aside>;
  return <aside className="gdet" key={F.root + "|" + F.group}><DetailBody F={F} r={r!} g={g} /></aside>;
}
function warnsOf(F: Folder) {
  const out: [string, string][] = [];
  for (const it of F.items) {
    const a = it.a; if (!a || !a.ok) { if (a && a.error) out.push(["解析できません", nfc(it.p) + "：" + a.error]); continue; }
    const fn = nfc(it.p.split("/").pop());
    for (const v of a.video || []) {
      if (v.kind !== "embed" && (v.st === "missing" || v.st === "abs")) out.push([(v.av === "audio" ? "音声" : "動画") + "のリンク切れ", fn + "：スライド " + v.s.join(",") + "　" + nfc(v.target || v.name)]);
      else if (v.fmt && v.fmt.v === "bad") out.push(["再生できない可能性のある動画", fn + "：スライド " + v.s.join(",") + (v.fmt.why ? "　" + v.fmt.why : "")]);
    }
    for (const v of a.audio || []) if (v.kind !== "embed" && (v.st === "missing" || v.st === "abs")) out.push(["音声のリンク切れ", fn + "：スライド " + v.s.join(",") + "　" + nfc(v.target || v.name)]);
    if (a.kiosk) out.push(["クリックで進めません", fn + "：自動プレゼンテーション（キオスク）設定"]);
    else if ((a.noclick || []).length) out.push(["クリック無効のスライド", fn + "：スライド " + a.noclick!.join(",")]);
  }
  for (const d of F.op?.dests || []) if (d.enabled && (d.state === "err" || d.state === "off")) out.push(["コピーできていません", d.label + "：" + CPL[d.state][0]]);
  return out.slice(0, 6);
}
function DetailBody({ F, r, g }: { F: Folder; r: Root; g: Group }) {
  const [more, setMore] = useState(false);
  const nm = nameOf(g); const ses = parts(r, g.key).ses; const st = stageOf(r.id, g.key, g);
  const ws = warnsOf(F); const memo = (F.memo || []).filter((m) => !m.more);
  const fl = g.fl || []; const ops = fl.filter((f) => f[1] === "op"); const oth = fl.filter((f) => f[1] !== "op");
  const pres = F.op?.pres; const d = F.op?.dests.find((x) => x.id === mainDest()) || F.op?.dests[0];
  const cp = copyOf(g); const on = OPEN.settings.enabled; const canShow = on && canOpen(g); const byo = isBYO(g);
  const ana = F.items.filter((i) => i.a);
  const shows = F.items.filter((i) => !i.d && !i.mk && PRESX.test(i.p)).sort((a, b) => cmpPath(a.p, b.p));
  const presFile = pres && pres.newest && OPEN.settings.multi !== "folder" ? pres.newest : shows.length === 1 ? shows[0].p : "";
  return <>
    <div className="dhd">
      <div className="no">{nm.no}{st === "now" && <span className="pill now">発表中</span>}{st === "done" && <span className="pill">発表済み</span>}</div>
      <h2 id="gdName">{nm.name}</h2><div className="by">{sesLabel({ name: ses, t: sesTime(ses) })}</div>
      <div className="go">
        <OpenBtn cls="gb pri" id="bShow" how="show" F={F} done="開きました" disabled={!canShow} title={!on ? "［設定］→「演者のスライドを開く」がオフです" : !canShow ? (g.files ? "このPCへのコピーが終わると開けます" : "データがありません") : byo ? "PC持込の演者です。本人のPCが使えないときに、入っているデータ（バックアップ）をスライドショーで開きます" : "発表ファイルをスライドショーで開きます（このPCのコピーから）"}><Icon n="play" />{byo && hasData(g) ? "バックアップを開く" : "スライドショー"}</OpenBtn>
        <OpenBtn cls="gb" id="bOpenF" how="file" F={F} disabled={!canShow} title="発表ファイルを開く（PowerPoint など）"><Icon n="file" /></OpenBtn>
        <OpenBtn cls="gb" id="bFold" how="folder" F={F} disabled={!on || !g.files} title="この演者のフォルダを開く（このPCのコピー）"><Icon n="folder" /></OpenBtn>
      </div>
    </div>
    {!canShow && g.files > 0 && <div className="gwhy">{!on ? "開けません：［設定］→「演者のスライドを開く」がオフです" : "開けません：" + (hasData(g) ? cp.t : "発表に使うファイルがありません（メモだけ）")}</div>}
    {canShow && (g.cpp || g.cp)?.[mainDest()] === "old" && <div className="gwhy warn">前の版を開きます（新しい版はまだこのPCにありません）</div>}
    {byo && <div className="gbyo"><b>PC持込</b><span>{hasData(g) ? "本人のPCで発表します。入っているデータはバックアップです（本人のPCが使えないときに［バックアップを開く］）。" : "本人のPCで発表します。バックアップのデータは入っていません。"}</span></div>}
    {!F.exists && <div className="gwarn" role="alert"><RIcon k="error" /><div><div><b>NAS にこのフォルダが見つかりません</b><span>削除・名前変更された可能性があります。このPCにコピーしたファイルは消していません。</span></div></div></div>}
    {ws.length > 0 && <div className="gwarn" role="alert"><RIcon k="error" /><div>{ws.map((w, i) => <div key={i}><b>{w[0]}</b><span>{w[1]}</span></div>)}</div></div>}
    {memo.length > 0 && <><div className="sec">メモ</div>{memo.map((m, i) => <div key={i} className="gmemo"><small>{nfc(m.p)}</small>
      {m.pending ? <span className="dim">受信中</span> : m.error != null ? <span className="dim">読めませんでした</span> : <pre>{m.text || "（空のファイル）"}</pre>}</div>)}</>}
    {(fl.length > 0 || g.repl || g.ana) && <><div className="sec">会場での対応</div><div className="gmarks">
      {ops.length > 0 && <div className="g"><b>オペ</b>{ops.map((f) => <span key={f[0]} className="gt" data-k="op">{nfc(f[0])}</span>)}</div>}
      {(oth.length > 0 || g.repl || (g.ana && (g.ana.video || g.ana.coi || g.ana.auto))) && <div className="g"><b>ファイル</b>
        {g.repl ? <span className="gt" data-k="repl">差替 {g.repl}</span> : null}
        {oth.map((f) => <span key={f[0]} className="gt" data-k={f[1] === "warn" ? "bad" : "info"}>{nfc(f[0])}</span>)}
        {g.ana?.video ? <span className="gt">動画 {g.ana.video}</span> : null}{g.ana?.coi ? <span className="gt">COI</span> : null}{g.ana?.auto ? <span className="gt">自動送り</span> : null}</div>}
    </div></>}
    <div className="sec">このPC</div>
    <dl className="gdl">
      <div className="r"><dt>発表ファイル</dt><dd className="mono" title={presFile}>{presFile ? nfc(presFile.split("/").pop()) : pres && pres.n > 1 ? `${pres.n}個（フォルダから選ぶ）` : g.files ? "—" : "データなし"}</dd></div>
      {(F.op?.dests || []).filter((x) => x.enabled).map((x) => {
        const c = x.id === mainDest() ? cp : (() => { const y = x.state ? CPL[x.state] : null; return { k: !y ? "wait" : y[1] === "ok" ? "ok" : y[1] === "run" ? "run" : y[1] === "bad" ? "bad" : "wait", t: y ? y[0] : g.files ? "確認中" : "ファイルなし" }; })();
        return <div className="r" key={x.id}><dt>{x.id === mainDest() ? "コピー" : x.label}</dt><dd><i className={"pc " + c.k} />{c.t}{x.id === mainDest() && <span className="dim"> · {x.label}</span>}
          <button className="gb icon sm cpy" title={"コピー先のパスをコピー\n" + nfc(x.path)} onClick={() => copyText(nfc(x.path)).then(() => toast("コピー先のパスをコピーしました"), () => toast("コピーできませんでした"))}><Icon n="copy" /></button></dd></div>;
      })}
      {!(F.op?.dests || []).length && <div className="r"><dt>コピー</dt><dd><i className={"pc " + cp.k} />{cp.t}{d ? <span className="dim"> · {d.label}</span> : null}</dd></div>}
      {shows.length > 1 && <div className="r files"><dt>ファイル</dt><dd><ul className="gfiles">{shows.map((it) => {
        const c = it.cp?.[mainDest()]?.[0]; const ok = on && !!c && OPENABLE.includes(c);
        return <li key={it.p} data-p={it.p}><span className="fn" title={nfc(it.p)}>{nfc(it.p.split("/").pop())}{pres && pres.newest === it.p && <span className="gt" data-k="info">後から入った</span>}</span>
          {SHOWX.test(it.p) && <OpenBtn cls="gb icon sm" how="show" F={F} rel={it.p} disabled={!ok} title="スライドショーで開く"><Icon n="play" /></OpenBtn>}
          <OpenBtn cls="gb icon sm" how="file" F={F} rel={it.p} disabled={!ok} title="開く"><Icon n="file" /></OpenBtn></li>;
      })}</ul></dd></div>}
      {g.repl ? <div className="r"><dt>差し替え</dt><dd>{g.repl}回{g.repl_ts ? `（最終 ${dtm(g.repl_ts)}）` : ""}</dd></div> : null}
      {g.recv_ts ? <div className="r"><dt>受付</dt><dd>{hms(g.recv_ts)}</dd></div> : null}
    </dl>
    <button className={cx("gmore", more && "open")} id="bMore" aria-expanded={more} onClick={() => setMore(!more)}><span>準備用の詳細（ファイル{ana.length ? "・PowerPoint 解析" : ""}{F.events.length ? "・変更" : ""}）</span><Icon n="chev" /></button>
    {more && <div className="ganalysis">
      {ana.length > 0 && <><div className="sub">PowerPoint 解析</div>{ana.map((it) => <AnaCard key={it.p} it={it} />)}</>}
      <div className="sub">ファイル（{F.items.filter((i) => !i.d && !i.mk).length}）</div><FileTable F={F} />
      {F.events.length > 0 && <><div className="sub">最近の変更</div><div className="gev">{F.events.slice(0, 8).map((e) => <div key={e.id} className="e">
        <div className="t"><span className="mono">{dtm(e.ts)}</span><span className="dim">（{ago(e.ts)}）</span><KindPill k={e.kind} />{e.repl ? <span className="gt" data-k="repl">差替 {e.repl}回目</span> : null}</div>
        <div className="sm">{e.summary}</div>
        {(e.items || []).slice(0, 12).map((it, i) => { const o = OPS[it.op] || ["", "", ""]; return <div key={i} className="it"><span className={"o o-" + o[1]} title={o[2]}>{o[0] && <Icon n={o[0]} />}</span><span className="fn">{it.op === "rename" || it.op === "folder_rename" ? nfc(it.path) + " → " + nfc(it.to) : nfc(it.path)}</span></div>; })}
      </div>)}</div></>}
      <div className="path"><span className="mono">{nfc(F.path)}</span><button className="gb icon sm" title="NASのパスをコピー" onClick={() => copyText(F.path).then(() => toast("パスをコピーしました"), () => toast("コピーできませんでした"))}><Icon n="copy" /></button></div>
    </div>}
    <div style={{ height: 24 }} />
  </>;
}
