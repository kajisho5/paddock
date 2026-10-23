/* 小さな部品：状態のチップ・進み具合・コピー状況など（一覧・会場ボード・演者画面で共通） */
import { useEffect, useState } from "react";
import type { AnaSum, CpState, Group, Root } from "../types";
import { Icon } from "./Icons";
import { actv, fmtDur, fmtT, isGot, isRecv, isTodo, recvState, STL, type RState, type SStat, type STime } from "../lib/layout";
import { cx, dtm, fmtSize, mss, nfc } from "../lib/util";
import { OPON, rateOf, store } from "../store";

export const KIND: Record<string, [string, string]> = {
  incoming: ["受信中", "mod"], folder_new: ["新規フォルダ", "acc"], add: ["追加", "add"], mod: ["更新", "mod"], rename: ["名前変更", "ren"],
  del: ["削除", "del"], folder_rename: ["フォルダ名変更", "ren"], folder_del: ["フォルダ削除", "del"], offline: ["接続断", "del"], online: ["復帰", "add"],
  copied: ["コピー完了", "add"], copy_err: ["コピー要確認", "del"],
};
export const OPS: Record<string, [string, string, string]> = {
  add: ["＋", "add", "追加"], mod: ["✎", "mod", "更新"], rename: ["↔", "ren", "名前変更"], del: ["−", "del", "削除"], dir_add: ["＋", "add", "フォルダ追加"],
  dir_del: ["−", "del", "フォルダ削除"], folder_rename: ["↔", "ren", "フォルダ名変更"], copy: ["⇢", "add", "コピー"],
};
export const CPL: Record<string, [string, string]> = {
  ok: ["コピー済み", "ok"], todo: ["コピー待ち", "dim"], copying: ["コピー中", "run"], wait: ["受信完了待ち", "dim"], srcbusy: ["NAS側で使用中", "warn"],
  busy: ["差し替え待ち", "warn"], edited: ["コピー先で変更あり", "warn"], err: ["エラー", "bad"], off: ["接続できません", "bad"],
};
export const MKC: Record<string, string> = { recv: "ok", got: "got", done: "done", drop: "drop", direct: "direct", warn: "warn", info: "dim" };
export const MKR: Record<string, string> = { recv: "受付済", got: "会場取得済", done: "発表終了", drop: "演題取り下げ", direct: "会場直", warn: "注意", info: "表示だけ" };
export const ST: Record<string, [string, string]> = { add: ["追加", "add"], mod: ["更新", "mod"], ren: ["名前変更", "ren"], pending: ["コピー中…", "mod"] };

export function Tag({ t, children, title, className }: { t: string; children: React.ReactNode; title?: string; className?: string }) {
  return <span className={cx("tag", "t-" + t, className)} title={title}>{children}</span>;
}
export function KindPill({ k }: { k: string }) { const x = KIND[k] || [k, "acc"]; return <span className={"kind k-" + x[1]}>{x[0]}</span>; }
export function CpPill({ label, st, msg }: { label: string; st: CpState; msg?: string }) {
  const x = CPL[st] || [st, "dim"];
  return <span className={"cp cp-" + x[1]} title={label + ": " + x[0] + (msg ? " — " + msg : "")}>
    {st === "ok" ? <Icon n="chk" /> : st === "copying" ? <Icon n="spin" className="spin" /> : null}{label}</span>;
}
export const stIconName = (st: string) => (st === "got" ? "check2" : st === "recv" ? "ok" : st === "copying" ? "spin" : st === "done" ? "flag" : st === "drop" ? "ban" : st === "direct" ? "direct" : "todo");
export function StIcon({ st }: { st: string }) { return <span className="sti" title={STL[st] || ""}><Icon n={stIconName(st)} className={st === "copying" ? "spin" : ""} /></span>; }
export function StateTag({ st }: { st: RState }) { return <span className={"rtag " + st}><Icon n={stIconName(st)} className={st === "copying" ? "spin" : ""} />{STL[st] || ""}</span>; }

export function AnaChips({ a }: { a?: AnaSum }) {
  if (!a || !a.n) return null;
  return <>
    {a.done < a.n && <Tag t="dim">解析中</Tag>}
    {!!a.err && <Tag t="bad">解析不可</Tag>}
    {!!a.video && <>
      {!!a.vwarn && <Tag t="bad">外部動画⚠</Tag>}
      {a.vfbad ? <Tag t="bad" title="会場のWindows PCで再生できない可能性が高い形式の動画があります">動画形式NG</Tag>
        : a.vfwarn ? <Tag t="warn" title="形式の確認が必要な動画があります（試写推奨）">動画要試写</Tag> : null}
      {!a.vwarn && !a.vfbad && !a.vfwarn && <Tag t="info">動画あり</Tag>}
    </>}
    {!!a.abad && <Tag t="bad" title="リンクされた音声ファイルが見つからない、または発表者PCの場所を指しています">音声リンク⚠</Tag>}
    {!!a.links && <Tag t="info">リンクあり</Tag>}
    {a.done === a.n && a.done > a.err && (a.coi ? <Tag t="ok">COI</Tag> : <Tag t="warn">COIなし</Tag>)}
    {!!a.auto && <Tag t="warn">自動送り</Tag>}
    {!!a.noclick && <Tag t="bad">クリック無効</Tag>}
  </>;
}
/* 目印のチップ（注意 → 会場直 → 表示だけ の順。max を超えた分は「+n」） */
const FLO: Record<string, number> = { warn: 0, direct: 1, info: 2 };
export function FlagChips({ g, max }: { g: Group; max?: number }) {
  const f = (g.fl || []).map((x, i) => [x[0], x[1], i] as [string, string, number]).sort((a, b) => (FLO[a[1]] ?? 3) - (FLO[b[1]] ?? 3) || a[2] - b[2]);
  if (!f.length) return null;
  const sh = max && f.length > max ? f.slice(0, max - 1) : f;
  return <>{sh.map(([l, r]) => <span key={l} className={"fl fl-" + r} title={"目印：" + nfc(l)}>{nfc(l)}</span>)}
    {sh.length < f.length && <span className="fl fl-more" title={f.slice(sh.length).map((x) => nfc(x[0])).join("、")}>+{f.length - sh.length}</span>}</>;
}
export function ReplTag({ g }: { g?: Group }) {
  if (!g || !g.repl) return null;
  return <Tag t="repl" title={`受付後に${g.repl}回変更されています${g.repl_ts ? "（最終 " + dtm(g.repl_ts) + (g.repl_sum ? "：" + g.repl_sum : "") + "）" : ""}`}>差替 {g.repl}</Tag>;
}
export function Prog({ list, suffix }: { list: Group[]; suffix?: string }) {
  const l = actv(list); const t = l.length, n = l.filter(isRecv).length; const pct = t ? Math.round((n * 100) / t) : 0;
  return <span className={cx("prog", t && n === t ? "done" : n ? "" : "zero")} title={`受付 ${n}/${t}`}>
    <span className="bar"><i style={{ width: pct + "%" }} /></span>{n}/{t}{suffix || ""}</span>;
}
export function GotProg({ list }: { list: Group[] }) {
  const anyGot = !!store.S?.roots.some((r) => (r.groups || []).some((g) => g.mk_got || g.mk_done));
  if (!anyGot) return null; const l = actv(list); const t = l.length, n = l.filter(isGot).length;
  return <span className={cx("gotc", t && n === t && "done")} title="会場取得済（「取得済」の目印あり）">取得 {n}/{t}</span>;
}
/* 受信中（NASへ書き込み中）・このPCへのコピー中の進み具合 */
/* 受信の経過時間（1秒ごとに進める） */
function Elapsed({ since }: { since: number }) {
  const [, f] = useState(0);
  useEffect(() => { const t = window.setInterval(() => f((n) => n + 1), 1000); return () => clearInterval(t); }, []);
  return <>{mss(Date.now() / 1000 + store.SKEW - since)}</>;
}
export function RowProg({ r, g }: { r: Root; g: Group }) {
  const S = store.S!;
  const a = OPON() && r.id === S.op.root && S.op.active && S.op.active.rel.startsWith(g.key + "/") ? S.op.active : null;
  if (!g.pending && !a) return null;
  return <>
    {!!g.pending && <div className="rx" title="NASへの書き込み中（全体のサイズはNASの一覧からは分からないため、受信済みサイズと速度を表示）">
      <span className="rbar ind"><i /></span>
      <span className="rt">受信中{g.pending > 1 ? " " + g.pending + "件" : ""}{g.pbytes ? " " + fmtSize(g.pbytes) : ""}{rateOf(r.id, g) ? " · " + fmtSize(rateOf(r.id, g)) + "/s" : ""}{g.pstart ? <> · <Elapsed since={g.pstart} /></> : ""}</span></div>}
    {a && (() => {
      const pct = a.total ? Math.floor((a.done * 100) / a.total) : 0;
      const lb = (S.op.dests || []).filter((d) => (a.dests || []).includes(d.id)).map((d) => d.label).join("・");
      return <div className="rx op" title={nfc(a.rel)}><span className="rbar"><i style={{ width: pct + "%" }} /></span>
        <span className="rt">{lb}へコピー {pct}% · {nfc(a.rel.split("/").pop())}</span></div>;
    })()}
  </>;
}
export function TimeChip({ t }: { t: STime | null }) { return t ? <span className="stime">{fmtT(t.s)}{t.e != null ? "–" + fmtT(t.e) : "〜"}</span> : null; }
export function SesStatus({ st, list }: { st?: SStat; list: Group[] }) {
  if (!st) return null; const un = list.filter(isTodo).length;
  const soon = st.st === "live" || ((st.st === "next" || st.st === "later") && st.until <= 30);
  const warn = un && soon ? <span className="sw-un" title="開始前・進行中なのに未受付の演者がいます">未受付 {un}</span> : null;
  if (st.st === "done") return <><span className="sst done">終了</span>{warn}</>;
  if (st.st === "live") return <><span className="sst live">進行中{st.rem != null ? " · 残り" + fmtDur(st.rem) : ""}</span>{warn}</>;
  if (st.st === "next") return <><span className={cx("sst next", st.until <= 30 && "soon")}>次 · あと{fmtDur(Math.max(0, st.until))}</span>{warn}</>;
  return warn;
}
export const catsOf = (g: Group, n: number) =>
  Object.entries(g.cats || {}).filter(([c]) => !(g.ana && c === "PPT")).sort((a, b) => b[1] - a[1]).slice(0, n);
export function Cats({ g, n }: { g: Group; n: number }) {
  return <>{catsOf(g, n).map(([c, k]) => <span key={c} className={"chip c-" + c}>{c}{k > 1 ? " " + k : ""}</span>)}</>;
}
export { recvState };
