/* 会場ボード：全会場を横に並べて受付状況を一覧（演者をクリックすると右に中身） */
import { Fragment, useEffect, useLayoutEffect, useRef } from "react";
import type { Group, Root } from "../types";
import { actv, cmpDay, dayOK, fmtDur, fmtT, isRecv, isTodo, lay, parts, recvState, sesStatus, sesTime, STL, todayDay, type STime } from "../lib/layout";
import { cmpName, cmpPath, cx, dtm, fmtSize, nfc } from "../lib/util";
import { allDays, clickRow, effDay, effVenue, inVenue, isFold, OPON, opDests, selectGroup, setFold, setFoldMany, setPref, store, useApp, vColor, VPAL_ } from "../store";
import { AnaChips, Cats, CpPill, FlagChips, Prog, GotProg, ReplTag, RowProg, SesStatus, StIcon, Tag, TimeChip } from "./Bits";
import { Icon } from "./Icons";
import { DaySelect, VenueSelect } from "./ListView";

interface Col { key: string; r: Root; v: string; vname: string; vc: string; sub: string; full: Group[]; gs: Group[] }

export function BoardPane() {
  const s = useApp(); const S = s.S;
  const boardRef = useRef<HTMLDivElement>(null);
  const navRef = useRef<HTMLDivElement>(null);
  if (!S) return <section id="boardpane" className="pane board" />;
  const q = nfc(s.bq).toLowerCase().trim(); const filtering = !!(q || s.onlyU || s.onlyN);
  const DAYS = allDays(), ED = effDay(DAYS), TD = todayDay(DAYS, ED);
  const EV = effVenue(); let scope: Group[] = []; const cols: (Col | { empty: true; r: Root; ri: number })[] = [];
  S.roots.forEach((r, ri) => {
    if (EV && EV.slice(0, EV.indexOf("|")) !== r.id) return;
    const y = lay(r);
    const base = (r.groups || []).filter((g) => g.key !== "" && inVenue(r.id, g.key) && dayOK(r, g.key, ED)); scope = scope.concat(base);
    const byV = new Map<string, Group[]>();
    for (const g of base) { const v = parts(r, g.key).venue; if (!byV.has(v)) byV.set(v, []); byV.get(v)!.push(g); }
    if (!byV.size) { if (!q) cols.push({ empty: true, r, ri }); return; }
    for (const v of [...byV.keys()].sort(cmpName)) {
      const full = byV.get(v)!; let gs = full;
      if (q) gs = gs.filter((g) => nfc(g.key).toLowerCase().includes(q));
      if (s.onlyU) gs = gs.filter((g) => g.unread);
      if (s.onlyN) gs = gs.filter(isTodo);
      if (q && !gs.length) continue;
      cols.push({ key: r.id + "|" + v, r, v, vname: y.vl >= 0 ? v : r.label, vc: y.vl >= 0 ? vColor(r.id, v) : VPAL_[ri % VPAL_.length], sub: y.vl >= 0 && S.roots.length > 1 ? r.label : "", full, gs });
    }
  });
  const scp = actv(scope); const n = scp.filter(isRecv).length, t = scp.length, pct = t ? Math.round((n * 100) / t) : 0;
  const cpn = scp.filter((g) => g.pending).length, unn = scp.filter((g) => g.unread).length;
  const real = cols.filter((c): c is Col => !("empty" in c));
  const sesKeysAll: string[] = [];
  let anyT = false;
  if (DAYS.length && !TD) outer: for (const r of S.roots) for (const g of r.groups || []) if (g.key && sesTime(parts(r, g.key).ses)) { anyT = true; break outer; }

  return <section id="boardpane" className="pane board">
    <div className="bbar">
      <span className="st" id="bTot">全体 <b>受付 {n}/{t}</b><span className={cx("prog", t && n === t ? "done" : n ? "" : "zero")}><span className="bar"><i style={{ width: pct + "%" }} /></span>{pct}%</span></span>
      <span className="st scp" id="bCp">コピー中 <b>{cpn}</b></span>
      <span className="st sun" id="bUn">未確認 <b>{unn}</b></span>
      <div className="flt">
        <span style={{ display: "inline-flex", gap: 2 }}>
          <button className="ghost fb" id="bOpenAll" title="すべてのセッションを開く" onClick={() => setFoldMany(sesKeysAll, false)}><Icon n="expand" />開く</button>
          <button className="ghost fb" id="bCloseAll" title="すべてのセッションを閉じる（演者を隠してコンパクトに）" onClick={() => setFoldMany(sesKeysAll, true)}><Icon n="collapse" />閉じる</button></span>
        <div className="search"><Icon n="search" /><input id="bq" type="text" placeholder="演者・セッションを検索" autoComplete="off" value={s.bq} onChange={(e) => { s.bq = e.target.value; s.emit(); }} /></div>
        <DaySelect id="bday" />
        {anyT && <span id="bdayhint" className="dhint">← 今日の日を選ぶと進行状況が出ます</span>}
        <VenueSelect id="bvenue" />
        <label><input type="checkbox" id="bOnlyU" checked={s.onlyU} onChange={(e) => setPref("onlyU", e.target.checked)} />未確認のみ</label>
        <label><input type="checkbox" id="bOnlyN" checked={s.onlyN} onChange={(e) => setPref("onlyN", e.target.checked)} />未受付のみ</label>
      </div>
    </div>
    <div className="bleg"><span><i className="sw recv" />受付済み</span><span><i className="sw got" />会場取得済</span><span><i className="sw copying" />コピー中</span><span><i className="sw none" />未受付</span><span><i className="sw direct" />会場直</span><span style={{ opacity: .6 }}><i className="sw done" />発表終了</span><span style={{ opacity: .7, textDecoration: "line-through" }}>取り下げ</span><span><i className="sw unread" />未確認（新着）</span><span className="dim">演者をクリックすると中身と解析結果を表示</span></div>
    <Nav cols={real} boardRef={boardRef} navRef={navRef} />
    <div className="boardcols" id="board" ref={boardRef}>
      {!S.roots.length ? <div className="empty"><div className="ico"><Icon n="folder" /></div><b>監視フォルダがありません</b>［設定］から学会名フォルダを追加してください。</div>
        : !cols.length ? <div className="empty"><div className="ico"><Icon n="search" /></div><b>該当なし</b>検索の文字や絞り込みを変えてください。</div>
          : cols.map((c) => "empty" in c
            ? <section key={"e" + c.r.id} className="col" data-col={c.r.id + "|"} style={{ ["--vc" as any]: VPAL_[c.ri % VPAL_.length] }}><div className="vh"><div className="n"><Icon n="building" /><span className="vn">{nfc(c.r.label)}</span></div></div>
              <div className="list"><div className="empty">{c.r.online === false ? "接続できません" : c.r.online == null ? "確認中…" : "演者フォルダがありません"}</div></div></section>
            : <Column key={c.key} c={c} filtering={filtering} DAYS={DAYS} TD={TD} sesKeysAll={sesKeysAll} />)}
    </div>
  </section>;
}

function Column({ c, filtering, DAYS, TD, sesKeysAll }: { c: Col; filtering: boolean; DAYS: string[]; TD: string | null; sesKeysAll: string[] }) {
  const s = store; const r = c.r; const y = lay(r);
  const vun = c.full.filter((g) => g.unread).length, vcp = c.full.filter((g) => g.pending).length;
  const sessions = new Map<string, { all: Group[]; vis: Group[]; day: string; ses: string }>();
  for (const g of c.full) { const pp = parts(r, g.key); if (!sessions.has(pp.sesKey)) sessions.set(pp.sesKey, { all: [], vis: [], day: pp.day, ses: pp.ses }); sessions.get(pp.sesKey)!.all.push(g); }
  for (const g of c.gs) sessions.get(parts(r, g.key).sesKey)!.vis.push(g);
  const order = [...sessions.keys()].sort((a, b) => { const A = sessions.get(a)!, B = sessions.get(b)!; return cmpDay(A.day, B.day) || cmpPath(A.ses, B.ses); });
  const tl: { key: string; t: STime }[] = [];
  for (const k of order) { const x = sessions.get(k)!; if (DAYS.length && (!TD || x.day !== TD)) continue; const t = sesTime(x.ses); if (t) tl.push({ key: k, t }); }
  tl.sort((a, b) => a.t.s - b.t.s); const STS = sesStatus(tl);
  const multiDay = new Set(order.map((k) => sessions.get(k)!.day)).size > 1;
  const fks: string[] = []; let lastDay: string | null = null; const body: React.ReactNode[] = [];
  for (const k of order) {
    const x = sessions.get(k)!; if (!x.vis.length) continue;
    x.vis.sort((a, b) => cmpPath(a.key, b.key));
    if (multiDay && x.day !== lastDay) { lastDay = x.day; body.push(<div key={"d" + k} className={cx("dsep", x.day && x.day === TD && "today")}>{nfc(x.day || "日の指定なし")}{x.day && x.day === TD && <span>今日</span>}</div>); }
    if (x.ses || x.day) {
      const fk = r.id + "|" + k; fks.push(fk);
      const sf = !filtering && isFold(fk); const sun = x.all.filter((g) => g.unread).length;
      const sflash = sf && x.all.some((g) => s.flashKeys.has(r.id + "|" + g.key));
      const tt = sesTime(x.ses), st = STS.get(k); const label = x.ses || x.day;
      body.push(<div key={"s" + k} className={cx("ses", sf && "fold", sflash && "flashh", st && "st-" + st.st)} data-fold={fk} tabIndex={0} role="button" aria-expanded={!sf}
        title={nfc((x.day && !multiDay && y.dl >= 0 ? x.day + " / " : "") + label) + `（クリックで${sf ? "開く" : "閉じる"}）`}
        onClick={() => setFold(fk, !isFold(fk))} onKeyDown={(e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); setFold(fk, !isFold(fk)); } }}>
        <span className="chev"><Icon n="down" /></span>
        <span className="sn">{label.split("/").map((t, i) => <Fragment key={i}>{i > 0 && <span className="sep"> › </span>}{nfc(t)}</Fragment>)}</span>
        {x.all.some((g) => g.pending) && <span className="pdot" title="コピー中" />}{sun > 0 && <span className="badge" title="未確認の演者">{sun}</span>}<Prog list={x.all} />
        {tt && <span className="tl"><TimeChip t={tt} /><SesStatus st={st} list={x.all} /></span>}
        {st && st.st === "live" && st.pct != null && <span className="tbar"><i style={{ width: st.pct.toFixed(1) + "%" }} /></span>}</div>);
      if (sf) continue;
    }
    x.vis.forEach((g) => body.push(<BRow key={r.id + "|" + g.key} r={r} g={g} />));
  }
  sesKeysAll.push(...fks);
  const live = tl.find((z) => STS.get(z.key)!.st === "live"), nx = tl.find((z) => STS.get(z.key)!.st === "next");
  const nm = (z: { key: string }) => nfc(sessions.get(z.key)!.ses.split("/").pop());
  const allF = fks.length > 0 && fks.every(isFold);
  return <section className="col" data-col={c.key} style={{ ["--vc" as any]: c.vc }}>
    <div className="vh">
      <div className="n"><Icon n="building" /><span className="vn" title={nfc(c.vname)}>{nfc(c.vname)}</span>{vun > 0 && <span className="badge" title="未確認の演者">{vun}</span>}
        {fks.length > 0 && !filtering && <button className="ghost cf icon" title={`この会場のセッションを${allF ? "すべて開く" : "すべて閉じる"}`} onClick={() => setFoldMany(fks, !allF)}><Icon n={allF ? "expand" : "collapse"} /></button>}</div>
      {c.sub && <div className="rl">{nfc(c.sub)}</div>}
      <div className="s"><span>受付</span><Prog list={c.full} /><GotProg list={c.full} />{vcp > 0 && <span className="cpg"><Icon n="spin" className="spin" />コピー中 {vcp}</span>}</div>
      {live ? (() => { const a = STS.get(live.key)!; return <div className="nowl live"><b>いま</b><span className="nn">{nm(live)}</span>{a.rem != null && <span className="nr">残り{fmtDur(a.rem)}</span>}</div>; })()
        : nx ? (() => { const a = STS.get(nx.key)!; return <div className="nowl"><b>次</b><span className="nn">{nm(nx)}</span><span className="nr">{fmtT(a.s)}〜（あと{fmtDur(Math.max(0, a.until))}）</span></div>; })()
          : tl.length ? <div className="nowl done"><b>本日のセッションは終了</b></div> : null}
    </div>
    <div className="list">{c.gs.length ? body : <div className="empty">{s.onlyN && !s.onlyU ? "全員受付済み" : s.onlyU && !s.onlyN ? "未確認はありません" : "該当なし"}</div>}</div>
  </section>;
}

function BRow({ r, g }: { r: Root; g: Group }) {
  const s = store; const ref = useRef<HTMLDivElement>(null);
  const name = g.key.split("/").pop() || ""; const st = recvState(g);
  const isSel = s.drawer && !!s.SEL && s.SEL.root === r.id && s.SEL.group === g.key;
  const cps = OPON() && g.cp ? opDests().map((d) => (g.cp![d.id] ? <CpPill key={d.id} label={d.label} st={g.cp![d.id]} /> : null)) : null;
  const tags = st === "none" ? <><Tag t="dim">未受付</Tag><FlagChips g={g} max={3} /></>
    : st === "drop" ? <><Tag t="drop">取り下げ</Tag><FlagChips g={g} max={3} /></>
      : st === "done" ? <><Tag t="done">発表終了</Tag><ReplTag g={g} /><FlagChips g={g} max={3} /></>
        : <>{!g.files && !g.pending && st !== "direct" && <Tag t="dim">データなし</Tag>}<ReplTag g={g} />{cps}<FlagChips g={g} max={3} /><AnaChips a={g.ana} /><Cats g={g} n={2} /></>;
  const S = s.S!;
  const tip = nfc(name) + "\n" + (STL[st] || "") + (g.files ? ` · ${g.files}ファイル · ${fmtSize(g.size)}` : "") + (g.recv_ts ? ` · 受付 ${dtm(g.recv_ts)}` : "") + (g.repl ? ` · 差し替え ${g.repl}回` : "")
    + (g.last_ts ? ` · 最終変更 ${dtm(g.last_ts)}` : "") + (g.unread ? ` · 未確認 ${g.unread}` : "") + (g.fl && g.fl.length ? "\n目印: " + g.fl.map((x) => nfc(x[0])).join("、") : "")
    + ((S.ui.os_open && S.local) || OPON() ? "\nダブルクリックで開く" : "");
  useEffect(() => { if (isSel && ref.current) revealInBoard(ref.current); }, [isSel]);
  useEffect(() => { if (s.followKey === r.id + "|" + g.key && ref.current) { s.followKey = null; revealInBoard(ref.current); } });
  return <div ref={ref} className={cx("bp", "st-" + st, g.unread > 0 && "unread", isSel && "sel", s.flashKeys.has(r.id + "|" + g.key) && "flash")} data-r={r.id} data-g={g.key} tabIndex={0} role="button" title={tip}
    onClick={(e) => clickRow(e, r.id, g.key)} onKeyDown={(e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); selectGroup(r.id, g.key); } }}>
    <StIcon st={st} /><span className="nm">{nfc(name)}</span>{g.unread > 0 && <span className="badge">{g.unread}</span>}<span className="tg">{tags}</span><RowProg r={r} g={g} /></div>;
}
/* 右パネルに隠れないよう、演者の列を左側へスクロールして見せる */
function revealInBoard(row: HTMLElement) {
  row.scrollIntoView({ block: "nearest", inline: "nearest" });
  const bd = document.getElementById("board"); if (!bd) return;
  const c = (row.closest(".col") as HTMLElement) || row; const br = bd.getBoundingClientRect();
  const center = document.getElementById("center");
  const lim = store.drawer && center ? innerWidth - center.offsetWidth - 12 : br.right - 12, rr = c.getBoundingClientRect();
  if (rr.right > lim) bd.scrollLeft += Math.ceil(rr.right - lim);
  else if (rr.left < br.left + 12) bd.scrollLeft -= Math.ceil(br.left + 12 - rr.left);
}

/* 会場ナビ（横にはみ出したときだけ）・ホイールで横スクロール・←→キー */
function Nav({ cols, boardRef, navRef }: { cols: Col[]; boardRef: React.RefObject<HTMLDivElement>; navRef: React.RefObject<HTMLDivElement> }) {
  const upd = () => {
    const bd = boardRef.current, nv = navRef.current; if (!bd || !nv) return;
    const over = bd.scrollWidth > bd.clientWidth + 4 && cols.length > 1; nv.classList.toggle("on", over); if (!over) return;
    const br = bd.getBoundingClientRect(); const center = document.getElementById("center");
    const lim = store.drawer && center ? Math.min(br.right, innerWidth - center.offsetWidth) : br.right;
    const vis = new Set<string>(); bd.querySelectorAll<HTMLElement>(".col").forEach((c) => { const r = c.getBoundingClientRect(); if (r.right > br.left + 40 && r.left < lim - 40) vis.add(c.dataset.col || ""); });
    nv.querySelectorAll<HTMLElement>(".vchip").forEach((b) => b.classList.toggle("vis", vis.has(b.dataset.goto || "")));
    (nv.querySelector("#bPrev") as HTMLButtonElement).disabled = bd.scrollLeft <= 2;
    (nv.querySelector("#bNext") as HTMLButtonElement).disabled = bd.scrollLeft + bd.clientWidth >= bd.scrollWidth - 2;
  };
  useLayoutEffect(upd);
  useEffect(() => {
    const bd = boardRef.current; if (!bd) return; let raf = 0;
    const onScroll = () => { if (raf) return; raf = requestAnimationFrame(() => { raf = 0; upd(); }); };
    const onWheel = (e: WheelEvent) => {
      if (e.ctrlKey || (e.target as HTMLElement).closest(".list")) return;
      if (Math.abs(e.deltaY) > Math.abs(e.deltaX) && bd.scrollWidth > bd.clientWidth) { bd.scrollLeft += e.deltaY; e.preventDefault(); }
    };
    const onKey = (e: KeyboardEvent) => {
      if (e.ctrlKey || e.altKey || e.metaKey || (e.key !== "ArrowLeft" && e.key !== "ArrowRight")) return;
      if ((e.target as HTMLElement).closest("input,textarea,select,#center") || store.modal) return;
      e.preventDefault(); scrollCols(e.key === "ArrowLeft" ? -1 : 1);
    };
    bd.addEventListener("scroll", onScroll, { passive: true }); bd.addEventListener("wheel", onWheel, { passive: false });
    window.addEventListener("resize", upd); document.addEventListener("keydown", onKey);
    return () => { bd.removeEventListener("scroll", onScroll); bd.removeEventListener("wheel", onWheel); window.removeEventListener("resize", upd); document.removeEventListener("keydown", onKey); };
  });
  const scrollCols = (dir: number) => { const bd = boardRef.current; const c = bd?.querySelector(".col"); bd?.scrollBy({ left: dir * (c ? c.getBoundingClientRect().width + 12 : 300), behavior: "smooth" }); };
  return <div className="bnav" id="bnav" ref={navRef}>
    <button className="ghost nv icon" id="bPrev" title="前の会場へ（←キー）" onClick={() => scrollCols(-1)}><Icon n="chevL" /></button>
    <div className="chips" id="bchips">{cols.length > 1 && cols.map((c) => {
      const a = actv(c.full); const n = a.filter(isRecv).length, t = a.length, un = c.full.filter((g) => g.unread).length;
      return <button key={c.key} className="vchip" data-goto={c.key} style={{ ["--vc" as any]: c.vc }} title={nfc(c.vname) + " へ移動"} onClick={() => {
        const bd = boardRef.current; const el = bd && [...bd.querySelectorAll<HTMLElement>(".col")].find((x) => x.dataset.col === c.key);
        if (bd && el) bd.scrollTo({ left: Math.max(0, el.offsetLeft - bd.offsetLeft - 16), behavior: "smooth" });
      }}><i />{nfc(c.vname)}<span className={cx("c", t && n === t && "done")}>{n}/{t}</span>{un > 0 && <span className="badge">{un}</span>}</button>;
    })}</div>
    <button className="ghost nv icon" id="bNext" title="次の会場へ（→キー）" onClick={() => scrollCols(1)}><Icon n="chev" /></button>
  </div>;
}
