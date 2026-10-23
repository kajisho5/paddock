/* リスト表示（左）：監視フォルダ → 会場 → （日）→ セッション → 演者 のツリー */
import { Fragment, useEffect, useRef } from "react";
import type { Group, Root } from "../types";
import { cmpDay, dayOK, isTodayLabel, isTodo, lay, parts, recvState, sesStatus, sesTime, todayDay, type SStat } from "../lib/layout";
import { ago, cmpName, cmpPath, cx, fmtSize, nfc, whereText } from "../lib/util";
import {
  allDays, clickRow, effDay, effVenue, foldKeysOf, inVenue, isFold, OPON, opDests, setDay, setFold, setFoldMany,
  setPref, setVenue, store, useApp, venueOf, vColor,
} from "../store";
import { AnaChips, Cats, CpPill, FlagChips, KindPill, Prog, GotProg, ReplTag, RowProg, SesStatus, StIcon, Tag, TimeChip } from "./Bits";
import { Icon } from "./Icons";
import { fuOf } from "../lib/layout";

export function VenueSelect({ id }: { id: string }) {
  const s = useApp(); const S = s.S!;
  if (OPON()) return null;   // 会場の発表PC：自分の会場だけなので、会場の切り替えは出さない
  const opts: [string, string][] = [];
  for (const r of S.roots) {
    if (r.depth < 2) continue;
    const segs = [...new Set((r.groups || []).filter((g) => g.key).map((g) => fuOf(r, g.key)).filter(Boolean))].sort(cmpName);
    segs.forEach((x) => opts.push([r.id + "|" + x, (S.roots.length > 1 ? nfc(r.label) + " / " : "") + nfc(x)]));
  }
  if (s.VENUE && !opts.some((o) => o[0] === s.VENUE)) opts.push([s.VENUE, s.VENUE.slice(s.VENUE.indexOf("|") + 1) + "（現在なし）"]);
  if (!opts.length) return null;
  return <select id={id} title="この会場だけ表示・通知" value={s.VENUE} onChange={(e) => setVenue(e.target.value)}>
    <option value="">すべての会場</option>{opts.map((o) => <option key={o[0]} value={o[0]}>{o[1]}</option>)}</select>;
}
export function DaySelect({ id }: { id: string }) {
  useApp(); const days = allDays(); const ed = effDay(days); if (!days.length) return null;
  return <select id={id} title="表示する日（日ごとのフォルダがあるとき）" value={ed} onChange={(e) => setDay(e.target.value)}>
    <option value="">すべての日</option>
    {days.map((d) => <option key={d} value={d}>{nfc(d)}{isTodayLabel(d) ? "（今日）" : ""}</option>)}
    {ed && !days.includes(ed) && <option value={ed}>{nfc(ed)}（現在なし）</option>}
  </select>;
}

export function ListPane() {
  const s = useApp(); const S = s.S;
  return <section id="left" className="pane left">
    <div className="ph"><div className="search"><Icon n="search" /><input id="q" type="text" placeholder="演者・セッションを検索" autoComplete="off" value={s.q} onChange={(e) => { s.q = e.target.value; s.emit(); }} /></div></div>
    {S && <div className="tools">
      <VenueSelect id="venue" /><DaySelect id="lday" />
      <label><input type="checkbox" id="onlyU" checked={s.onlyU} onChange={(e) => setPref("onlyU", e.target.checked)} />未確認のみ</label>
      <label><input type="checkbox" id="onlyN" checked={s.onlyN} onChange={(e) => setPref("onlyN", e.target.checked)} />未受付のみ</label>
      <span style={{ flex: 1 }} />
      <select id="sort" value={s.sort} onChange={(e) => setPref("sort", e.target.value as any)}><option value="name">会場・セッション順</option><option value="recent">変更が新しい順</option><option value="unread">未確認を上に</option></select>
    </div>}
    <div className="scroll" id="groups">{S && <Groups />}</div>
  </section>;
}

function Groups() {
  const s = useApp(); const S = s.S!;
  if (!S.roots.length) return <div className="empty"><div className="ico"><Icon n="folder" /></div><b>監視フォルダがありません</b>［設定］から学会名フォルダを追加してください。<br /><span className="mono" style={{ fontSize: 11.5, color: "var(--dim)" }}>例: \\192.168.0.10\share\学会名</span></div>;
  const q = nfc(s.q).toLowerCase().trim(); const filtering = !!(q || s.onlyU || s.onlyN); const out: React.ReactNode[] = [];
  const EV = effVenue(); const ED = effDay();
  for (const r of S.roots) {
    if (EV && EV.slice(0, EV.indexOf("|")) !== r.id) continue;
    let gs = (r.groups || []).filter((g) => inVenue(r.id, g.key) && (g.key === "" || dayOK(r, g.key, ED)));
    if (q) gs = gs.filter((g) => nfc(g.key).toLowerCase().includes(q));
    if (s.onlyU) gs = gs.filter((g) => g.unread);
    if (s.onlyN) gs = gs.filter((g) => g.key !== "" && isTodo(g));
    gs.sort((a, b) => {
      if (a.key === "") return 1; if (b.key === "") return -1;
      if (s.sort === "recent") return (b.last_ts || 0) - (a.last_ts || 0) || cmpPath(a.key, b.key);
      if (s.sort === "unread") return (b.unread ? 1 : 0) - (a.unread ? 1 : 0) || (b.last_ts || 0) - (a.last_ts || 0) || cmpPath(a.key, b.key);
      return cmpPath(a.key, b.key);
    });
    const all = (r.groups || []).filter((g) => g.key !== "" && inVenue(r.id, g.key) && dayOK(r, g.key, ED)); const un = all.filter((g) => g.unread).length;
    const hier = s.sort === "name" && r.depth >= 2;
    out.push(<div className="rhead" key={"rh" + r.id}>
      <div className="r1"><span className={"dot " + (r.online === false ? "off" : r.online ? "on" : "busy")} /><span className="rl">{nfc(r.label)}</span>
        {hier && <span className="tb">
          <button className="ghost icon" title="すべて開く" onClick={() => setFoldAll(r, false)}><Icon n="expand" /></button>
          <button className="ghost icon" title="すべてたたむ" onClick={() => setFoldAll(r, true)}><Icon n="collapse" /></button></span>}</div>
      <div className="r2"><Prog list={all} suffix=" 受付" /><GotProg list={all} />{un > 0 && <span className="cnt">未確認 {un}</span>}</div>
      <span className="p" title={r.path}><bdi>{nfc(r.path)}</bdi></span></div>);
    if (!gs.length) { out.push(<div className="empty" style={{ padding: 18 }} key={"e" + r.id}>{r.online === false ? "接続できません" : filtering ? "該当なし" : "フォルダがありません"}</div>); continue; }
    if (!hier) { gs.forEach((g) => out.push(<Row key={r.id + "|" + g.key} r={r} g={g} hier={false} />)); continue; }
    // 会場 → （日）→ セッション → 演者（見出しの数は、絞り込みに関係なく全員で数える）
    const tree = new Map<string, Map<string, Group[]>>(); const rest: Group[] = []; const SI: Record<string, { day: string; ses: string }> = {};
    const FV = new Map<string, Map<string, Group[]>>(), FS = new Map<string, Group[]>();
    for (const g of all) {
      const pp = parts(r, g.key); if (!FV.has(pp.venue)) FV.set(pp.venue, new Map()); const m = FV.get(pp.venue)!;
      if (!m.has(pp.sesKey)) m.set(pp.sesKey, []); m.get(pp.sesKey)!.push(g); if (!FS.has(pp.sesKey)) FS.set(pp.sesKey, m.get(pp.sesKey)!);
      if (!SI[pp.sesKey]) SI[pp.sesKey] = { day: pp.day, ses: pp.ses };
    }
    for (const g of gs) {
      if (g.key === "") { rest.push(g); continue; }
      const pp = parts(r, g.key);
      if (!tree.has(pp.venue)) tree.set(pp.venue, new Map()); const m = tree.get(pp.venue)!;
      if (!m.has(pp.sesKey)) m.set(pp.sesKey, []); m.get(pp.sesKey)!.push(g);
      if (!SI[pp.sesKey]) SI[pp.sesKey] = { day: pp.day, ses: pp.ses };
    }
    for (const v of [...tree.keys()].sort(cmpName)) {
      const sessions = new Map([...tree.get(v)!.entries()].sort((a, b) => cmpDay(SI[a[0]].day, SI[b[0]].day) || cmpPath(SI[a[0]].ses, SI[b[0]].ses)));
      const vfull = FV.get(v) ? [...FV.get(v)!.values()].flat() : [...sessions.values()].flat();
      const vk = r.id + "|" + v;
      if (v) {
        const vfold = !filtering && isFold(vk); const vun = vfull.filter((g) => g.unread).length; const vpend = vfull.some((g) => g.pending);
        const vflash = vfold && vfull.some((g) => s.flashKeys.has(r.id + "|" + g.key));
        out.push(<div key={"v" + vk} className={cx("vhead", vfold && "fold", vflash && "flashh")} data-fold={vk} tabIndex={0} role="button" aria-expanded={!vfold}
          style={{ ["--vc" as any]: vColor(r.id, v) }} onClick={() => setFold(vk, !isFold(vk))} onKeyDown={(e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); setFold(vk, !isFold(vk)); } }}>
          <span className="vic"><Icon n="building" /></span><span className="vn">{nfc(v)}</span>{vpend && <span className="pdot" title="コピー中" />}<Prog list={vfull} />{vun > 0 && <span className="badge">{vun}</span>}<span className="chev"><Icon n="down" /></span></div>);
        if (vfold) continue;
      }
      const TL = listTimeline(FV.get(v) || sessions, SI);
      for (const [skey, list] of sessions) {
        const info = SI[skey] || { day: "", ses: "" }; const ses = info.ses; const sall = FS.get(skey) || list;
        if (ses || info.day) {
          const sk = r.id + "|" + skey; const sfold = !filtering && isFold(sk);
          const sun = sall.filter((g) => g.unread).length; const spend = sall.some((g) => g.pending);
          const sflash = sfold && list.some((g) => s.flashKeys.has(r.id + "|" + g.key));
          const tt = sesTime(ses); const st = TL.get(skey);
          out.push(<div key={"s" + sk} className={cx("shead", sfold && "fold", sflash && "flashh", st && "st-" + st.st)} data-fold={sk} tabIndex={0} role="button" aria-expanded={!sfold}
            onClick={() => setFold(sk, !isFold(sk))} onKeyDown={(e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); setFold(sk, !isFold(sk)); } }}>
            <span className="chev"><Icon n="down" /></span>
            <span className="sn">{info.day && lay(r).dl >= 0 && <span className="dchip">{nfc(info.day)}</span>}{(ses || "").split("/").map((x, i) => <Fragment key={i}>{i > 0 && <span className="sep"> › </span>}{nfc(x)}</Fragment>)}</span>
            {spend && <span className="pdot" title="コピー中" />}<Prog list={sall} />{sun > 0 && <span className="badge">{sun}</span>}
            {tt && <span className="tl"><TimeChip t={tt} /><SesStatus st={st} list={sall} /></span>}</div>);
          if (sfold) continue;
        }
        list.forEach((g) => out.push(<Row key={r.id + "|" + g.key} r={r} g={g} hier />));
      }
    }
    rest.forEach((g) => out.push(<Row key={r.id + "|" + g.key} r={r} g={g} hier={false} />));
  }
  return <>{out}</>;
}
function setFoldAll(r: Root, close: boolean) {
  const keys = new Set<string>(); (r.groups || []).forEach((g) => foldKeysOf(r.id, g.key).forEach((k) => keys.add(k)));
  setFoldMany([...keys], close);
}
/* 会場ごと・日ごとの進行状況（今日の分だけ） */
function listTimeline(sessions: Map<string, Group[]>, SI: Record<string, { day: string; ses: string }>): Map<string, SStat> {
  const days = allDays(), ed = effDay(days), td = todayDay(days, ed);
  if (days.length && !td) return new Map();
  const arr: { key: string; t: NonNullable<ReturnType<typeof sesTime>> }[] = [];
  for (const [skey] of sessions) { const info = SI[skey]; if (!info) continue; if (days.length && info.day !== td) continue; const t = sesTime(info.ses); if (t) arr.push({ key: skey, t }); }
  arr.sort((a, b) => a.t.s - b.t.s); return sesStatus(arr);
}

function Row({ r, g, hier }: { r: Root; g: Group; hier: boolean }) {
  const s = store;
  const segs = g.key.split("/"); const name = g.key === "" ? (r.depth > 1 ? "（演者フォルダより上のファイル）" : "（直下のファイル）") : segs[segs.length - 1];
  const where = segs.length > 1 ? segs.slice(0, -1).join("/") : "";
  const v = venueOf(r.id, g.key);
  const isSel = !!s.SEL && s.SEL.root === r.id && s.SEL.group === g.key;
  const ref = useRef<HTMLDivElement>(null);
  useEffect(() => {
    if (!isSel || !ref.current) return;
    const go = () => ref.current?.scrollIntoView({ block: "nearest" });
    go(); const t1 = setTimeout(go, 400), t2 = setTimeout(go, 1500);   // 中身が読み込まれて行の高さが変わっても隠れないように
    return () => { clearTimeout(t1); clearTimeout(t2); };
  }, [isSel]);   // 自動表示・通知・ログから選んだときも見える位置へ
  const st = g.key === "" ? "" : recvState(g);
  const cps = OPON() && g.cp ? opDests().map((d) => (g.cp![d.id] ? <CpPill key={d.id} label={d.label} st={g.cp![d.id]} /> : null)) : null;
  const stTag = st === "drop" ? <Tag t="drop">演題取り下げ</Tag> : st === "done" ? <Tag t="done">発表終了</Tag> : st === "none" ? <Tag t="dim">未受付</Tag> : null;
  return <div ref={ref} className={cx("grp", hier && "hier", st && "st-" + st, g.unread > 0 && "unread", isSel && "sel", s.flashKeys.has(r.id + "|" + g.key) && "flash")} data-r={r.id} data-g={g.key}
    onClick={(e) => clickRow(e, r.id, g.key)}>
    <div className="n">{st && <StIcon st={st} />}<span className="nm">{!hier && where && <span className="pre">{v && <span className="vdot" style={{ ["--vc" as any]: vColor(r.id, v) }} />}{whereText(where)} › </span>}{nfc(name)}</span>
      {g.unread > 0 && <span className="badge">{g.unread}</span>}<span className="ago">{g.last_ts ? ago(g.last_ts) : ""}</span></div>
    <div className="meta">{!g.files && !g.pending ? <>
      {stTag}{(st === "recv" || st === "got" || st === "done") && g.key !== "" && <Tag t="dim">データなし</Tag>}<FlagChips g={g} />{g.last_kind && st !== "none" && <KindPill k={g.last_kind} />}<RowProg r={r} g={g} />
    </> : <>
      {stTag}{cps}<ReplTag g={g} /><FlagChips g={g} /><span>{g.files}ファイル</span><span>{fmtSize(g.size)}</span><AnaChips a={g.ana} /><Cats g={g} n={3} />{g.last_kind && <KindPill k={g.last_kind} />}<RowProg r={r} g={g} />
    </>}</div>
  </div>;
}
