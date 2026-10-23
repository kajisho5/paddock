/* 階層の読み取り：日（day1・1日目・10月11日など）／会場／セッション、受付状況、セッションの時刻（旧画面から移植） */
import type { Group, Root } from "../types";
import { cmpName, nameKey, p2 } from "./util";

const DAY_RE = /^(?:\d{1,3}[_\-\s.]+)?(?:day\s*[-_.]?\s*(\d{1,2})|(\d{1,2})\s*日目|第\s*(\d{1,2})\s*日目?|(\d{1,2})\s*月\s*(\d{1,2})\s*日|(\d{4})\s*[-_.年]\s*(\d{1,2})\s*[-_.月]\s*(\d{1,2})\s*日?)/i;
export interface DayInfo { tok: string; rest: string; n?: number; date?: { y?: number; m: number; d: number } }
export function dayInfo(name: string): DayInfo | null {
  const t = nameKey(name); const m = DAY_RE.exec(t); if (!m) return null;
  const o: DayInfo = { tok: m[0].replace(/^\d{1,3}[_\-\s.]+/, "").trim(), rest: t.slice(m[0].length) };
  if (m[1] || m[2] || m[3]) o.n = +(m[1] || m[2] || m[3]);
  else if (m[4]) o.date = { m: +m[4], d: +m[5] };
  else if (m[6]) o.date = { y: +m[6], m: +m[7], d: +m[8] };
  return o;
}

export interface Lay { ref: unknown; depth: number; dl: number; vl: number; sl: number[]; sd: boolean; L: number }
const LAYC: Record<string, Lay> = {};
export function lay(r: Root): Lay {
  const c = LAYC[r.id]; if (c && c.ref === r.groups && c.depth === r.depth) return c;
  const L = Math.max(0, (r.depth || 1) - 1); const keys = (r.groups || []).map((g) => g.key).filter(Boolean);
  let dl = -1;
  for (let i = 0; i < L && dl < 0; i++) {
    const vals = new Set<string>(); for (const k of keys) { const x = k.split("/")[i]; if (x != null) vals.add(x); }
    const tokN = new Map<string, number>();
    if (vals.size && vals.size <= 31 && [...vals].every((v) => {
      const d = dayInfo(v); if (d) tokN.set(d.tok, (tokN.get(d.tok) || 0) + 1);
      return d && d.rest.replace(/[\s_\-.()（）［］[\]・,、曜月火水木金土日]/g, "").length <= 8;
    }) && [...tokN.values()].every((n) => n === 1)) dl = i;   // 「day1_第1会場」「day1_第2会場」のように同じ日が並ぶなら日の階層ではない
  }
  const others: number[] = []; for (let i = 0; i < L; i++) if (i !== dl) others.push(i);
  const vl = others.length >= 2 ? others[0] : -1, sl = others.length >= 2 ? others.slice(1) : others;
  let sd = false;
  if (dl < 0 && sl.length) {
    const vals = new Set(keys.map((k) => k.split("/")[sl[0]])); let hit = 0;
    vals.forEach((v) => { if (v && dayInfo(v)) hit++; }); sd = hit > 0 && hit * 2 >= vals.size;
  }
  const o: Lay = { ref: r.groups, depth: r.depth, dl, vl, sl, sd, L }; LAYC[r.id] = o; return o;
}
export interface Parts { venue: string; day: string; ses: string; sesKey: string; name: string }
export function parts(r: Root, key: string): Parts {
  const y = lay(r); const segs = String(key).split("/");
  const venue = y.vl >= 0 ? segs[y.vl] || "" : "";
  const sesSegs = y.sl.map((i) => segs[i]).filter((x) => x != null && x !== "");
  let day = y.dl >= 0 ? segs[y.dl] || "" : "";
  if (!day && y.sd && sesSegs.length) { const d = dayInfo(sesSegs[0]); if (d) day = d.tok; }
  return { venue, day, ses: sesSegs.join("/"), sesKey: segs.slice(0, -1).join("/"), name: segs[segs.length - 1] };
}
/* 「この会場だけ」の単位：会場（会場の階層がなければ最初のフォルダ。階層2ならセッション＝従来どおり） */
export function fuOf(r: Root, key: string) {
  const y = lay(r); const segs = String(key).split("/");
  if (y.vl >= 0) return segs[y.vl] || "";
  const i = y.dl === 0 && y.sl.length ? y.sl[0] : 0; return segs[i] || "";
}
export function dayOrd(label: string) {
  const d = label ? dayInfo(label) : null; if (!d) return 1e9;
  if (d.date) return (d.date.y || new Date().getFullYear()) * 10000 + d.date.m * 100 + d.date.d;
  return d.n != null ? d.n : 1e9 - 1;
}
export const cmpDay = (a: string, b: string) => (a ? 0 : 1) - (b ? 0 : 1) || dayOrd(a) - dayOrd(b) || cmpName(a, b);
export function isTodayLabel(label: string) {
  const d = label && dayInfo(label); if (!d || !d.date) return false; const t = new Date();
  return d.date.m === t.getMonth() + 1 && d.date.d === t.getDate() && (!d.date.y || d.date.y === t.getFullYear());
}
export const ymd = (t?: Date) => { t = t || new Date(); return t.getFullYear() + "-" + p2(t.getMonth() + 1) + "-" + p2(t.getDate()); };
export function dayOK(r: Root, key: string, ed: string) { if (!ed) return true; const y = lay(r); if (y.dl < 0 && !y.sd) return true; return parts(r, key).day === ed; }
export const todayDay = (days: string[], ed: string) => days.find(isTodayLabel) || ed || null;

/* セッション名の時刻：0900-1030 / 9:00〜10:30 / 9時30分 / 先頭の0900_ など */
const TMS = String.raw`(\d{1,2})(?::([0-5]\d)|時(?!間)(?:([0-5]?\d)分?)?)`, SEPS = String.raw`\s*[-~〜ー−–—]+\s*`;
const RE_TR = new RegExp(String.raw`(?<!\d)` + TMS + SEPS + TMS), RE_T = new RegExp(String.raw`(?<!\d)` + TMS);
const RE_HR = /(?<!\d)([01]\d|2[0-3])([0-5]\d)\s*[-~〜ー−–—]+\s*([01]\d|2[0-3])([0-5]\d)(?!\d)/, RE_HH = /(?:^|[_\s])([01]\d|2[0-3])([0-5]\d)(?=[_\s\-.]|$)/;
export interface STime { s: number; e: number | null }
export function sesTime(path: string): STime | null {
  if (!path) return null; const t = nameKey(path); let m: RegExpExecArray | null; let a: number | null = null, b: number | null = null;
  const tm = (h: string, mm?: string, m2?: string) => { const hh = +h; const mi = mm != null && mm !== "" ? +mm : m2 != null && m2 !== "" ? +m2 : 0; return hh <= 24 && mi < 60 ? hh * 60 + mi : null; };
  if ((m = RE_TR.exec(t))) { a = tm(m[1], m[2], m[3]); b = tm(m[4], m[5], m[6]); }
  else if ((m = RE_HR.exec(t))) { a = +m[1] * 60 + +m[2]; b = +m[3] * 60 + +m[4]; }
  else if ((m = RE_T.exec(t))) a = tm(m[1], m[2], m[3]);
  else for (const seg of t.split("/")) { if ((m = RE_HH.exec(seg)) && +m[2] % 5 === 0) { a = +m[1] * 60 + +m[2]; break; } }   // 「1101_一般演題」「2026」などの番号は時刻にしない
  if (a == null) return null; if (b != null && b <= a) b = null; return { s: a, e: b };
}
export const fmtT = (m: number) => Math.floor(m / 60) + ":" + p2(m % 60);
export const fmtDur = (m: number) => (m >= 60 ? Math.floor(m / 60) + "時間" + (m % 60 ? (m % 60) + "分" : "") : m + "分");
export interface SStat { st: "done" | "live" | "next" | "later"; s: number; end: number | null; rem: number | null; until: number; pct: number | null }
/* 同じ会場・同じ日のセッション（開始順）から、終了／進行中／次 を決める。終わりの時刻がなければ次のセッションの開始まで */
export function sesStatus(list: { key: string; t: STime }[]): Map<string, SStat> {
  const now = new Date(); const nm = now.getHours() * 60 + now.getMinutes() + now.getSeconds() / 60;
  const out = new Map<string, SStat>(); let nextSet = false;
  list.forEach((x, i) => {
    const end = x.t.e != null ? x.t.e : list[i + 1] ? list[i + 1].t.s : null; let st: SStat["st"];
    if (nm < x.t.s) { st = nextSet ? "later" : "next"; nextSet = true; }
    else if (end != null ? nm < end : nm < x.t.s + 180) st = "live"; else st = "done";
    out.set(x.key, {
      st, s: x.t.s, end, rem: end != null ? Math.max(0, Math.ceil(end - nm)) : null, until: Math.ceil(x.t.s - nm),
      pct: end != null && end > x.t.s ? Math.min(100, Math.max(0, ((nm - x.t.s) * 100) / (end - x.t.s))) : null,
    });
  });
  return out;
}

/* 受付状況：「取得済」の目印＝会場側が受け取った。「受付済」の目印 か データがあれば受付済み。
   目印：「演題取り下げ」→取り下げ（受付の数に入れない）、「発表終了」→発表終了、「会場直」→データがなくても未受付にしない */
export type RState = "copying" | "drop" | "done" | "got" | "recv" | "direct" | "none";
export const recvState = (g: Group): RState =>
  g.pending ? "copying" : g.mk_drop ? "drop" : g.mk_done ? "done" : g.mk_got ? "got" : g.files > 0 || g.mk_recv ? "recv" : g.mk_direct ? "direct" : "none";
const RECV_OK = new Set(["recv", "got", "done", "direct"]);
/* 差し替えを受信中（コピー中）でも、もともと受付済みなら受付済みとして数える */
export const isRecv = (g: Group) => { const s = recvState(g); return RECV_OK.has(s) || (s === "copying" && !!(g.files > 0 || g.mk_recv || g.mk_got || g.mk_done || g.mk_direct)); };
export const isGot = (g: Group) => { const s = recvState(g); return s === "got" || s === "done" || (s === "copying" && !!(g.mk_got || g.mk_done)); };
export const actv = (list: Group[]) => list.filter((g) => !g.mk_drop);
export const isTodo = (g: Group) => !g.mk_drop && !isRecv(g);
export const STL: Record<string, string> = { got: "会場取得済", recv: "受付済み", copying: "コピー中", none: "未受付", done: "発表終了", drop: "演題取り下げ", direct: "会場直" };
