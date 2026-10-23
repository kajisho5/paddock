import { APP_ICON } from "../lib/appIcon";
import { useEffect, useLayoutEffect, useRef, useState } from "react";
import { api } from "../api";
import type { Root } from "../types";
import { APP_SUB, APP_TITLE, IS_OP, IS_RX } from "../boot";
import { hms, nfc, cx } from "../lib/util";
import { askPerm, loadState, quitApp, markAllSeen, OPON, opDests, setFollow, setView, testNotify, toast, useApp } from "../store";
import { Icon } from "./Icons";
import { openCfg } from "./Settings";
import { netBadge, netOpen } from "../op/Net";

/* 監視フォルダの状態。並びきらないときは「監視フォルダ 4」の1つにまとめ、クリックで一覧を出す */
function rootInfo(r: Root) {
  const st = !r.enabled ? ["", "停止中"] : r.online === false ? ["off", "接続できません"] : r.online === null ? ["busy", "確認中…"] : r.pending ? ["busy", "変化を確認中 " + r.pending] : ["on", "監視中"];
  const m = r.online ? `${(r.count || 0).toLocaleString()}件 · ${r.scan_ms != null ? (r.scan_ms / 1000).toFixed(1) + "s" : ""}${r.last_scan ? " · " + hms(r.last_scan) : ""}` : "";
  return { st, m };
}
function Roots() {
  const s = useApp(); const S = s.S;
  const ref = useRef<HTMLDivElement>(null); const need = useRef(0);
  const [collapsed, setCollapsed] = useState(false); const [open, setOpen] = useState(false);
  const sig = S ? S.roots.map((r) => r.id + r.label).join("|") : "";
  useEffect(() => { setCollapsed(false); need.current = 0; }, [sig]);
  useLayoutEffect(() => {
    const el = ref.current; if (!el || collapsed) return;
    if (el.scrollWidth > el.clientWidth + 1) { need.current = el.scrollWidth; setCollapsed(true); }
  });
  useEffect(() => {
    const el = ref.current; if (!el || typeof ResizeObserver === "undefined") return;
    const ro = new ResizeObserver(() => {
      if (collapsed && need.current && el.clientWidth >= need.current) setCollapsed(false);
      else if (!collapsed && el.scrollWidth > el.clientWidth + 1) { need.current = el.scrollWidth; setCollapsed(true); }
    });
    ro.observe(el); return () => ro.disconnect();
  }, [collapsed]);
  useEffect(() => {
    if (!open) return; const c = (e: MouseEvent) => { if (!(e.target as HTMLElement).closest(".rootpop,.rchip.agg")) setOpen(false); };
    document.addEventListener("mousedown", c); return () => document.removeEventListener("mousedown", c);
  }, [open]);
  if (!S) return <div className="roots" ref={ref} />;
  const many = S.roots.length > 1;
  const chip = (r: Root) => {
    const { st, m } = rootInfo(r);
    const tip = nfc(r.label) + "　" + st[1] + (m ? "\n" + m : "") + "\n" + r.path + (r.error ? "\n" + r.error : "") + (r.n_warns ? "\n読めないフォルダ " + r.n_warns + "件" : "");
    return <span key={r.id} className={cx("rchip", many && "compact", r.online === false && "off")} title={tip}>
      <span className={"dot " + st[0]} /><span className="t"><b>{nfc(r.label)}</b>{!many && " " + st[1]}</span>
      <span className="m">{many ? (r.online === false ? "接続できません" : r.online ? (r.count || 0).toLocaleString() + "件" : st[1]) : m}{r.n_warns ? " · ⚠" + r.n_warns : ""}</span></span>;
  };
  let body: React.ReactNode;
  if (!S.roots.length) body = <span className="rchip"><span className="dot" />監視フォルダ未設定</span>;
  else if (!collapsed || !many) body = S.roots.map(chip);
  else {
    const off = S.roots.filter((r) => r.enabled && r.online === false).length, busy = S.roots.filter((r) => r.enabled && (r.online === null || r.pending)).length;
    const total = S.roots.reduce((a, r) => a + (r.count || 0), 0);
    body = <span className={cx("rchip agg", off && "off")} role="button" tabIndex={0} onClick={() => setOpen(!open)} title="クリックで監視フォルダの一覧">
      <span className={"dot " + (off ? "off" : busy ? "busy" : "on")} /><span className="t"><b>監視フォルダ {S.roots.length}</b>{off ? `（${off}つ接続できません）` : ""}</span>
      <span className="m">{total.toLocaleString()}件</span><Icon n="down" /></span>;
  }
  return <div className="rootsw">
    <div className="roots" ref={ref}>{body}{!s.conn && <span className="conn">再接続中…</span>}</div>
    {open && collapsed && <div className="rootpop">{S.roots.map((r) => {
      const { st, m } = rootInfo(r);
      return <div key={r.id} className={cx("rp", r.online === false && "off")}><span className={"dot " + st[0]} /><div><b>{nfc(r.label)}</b><span className="st">{st[1]}</span>
        <div className="m">{m}{r.n_warns ? " · 読めないフォルダ " + r.n_warns : ""}</div><div className="p">{nfc(r.path)}</div>{r.error && <div className="e">{r.error}</div>}</div></div>;
    })}</div>}
  </div>;
}

export function Header() {
  const s = useApp();
  return <header className="hdr">
    <div className="logo"><img className="mark" src={APP_ICON} alt="" width={34} height={34} />
      <span className="lt">{APP_TITLE}<small>SEVENTHWELL · {APP_SUB}</small></span></div>
    {IS_OP && OPON() ? <div className="rootsw">{!s.conn && <span className="conn">再接続中…</span>}</div> : <Roots />}
    <div className="seg" role="tablist" aria-label="表示の切り替え">
      <button type="button" role="tab" id="vList" aria-selected={s.view === "list"} onClick={() => setView("list")} title="会場・セッション・演者の一覧と、フォルダの中身"><Icon n="list" /><span className="lb">リスト</span></button>
      <button type="button" role="tab" id="vBoard" aria-selected={s.view === "board"} onClick={() => setView("board")} title="全会場を横に並べて受付状況を一覧"><Icon n="cols" /><span className="lb">会場ボード</span></button>
    </div>
    <div className="hbtns">
      {!IS_OP && !IS_RX && <label className="switch" title="更新があったフォルダを自動で表示（操作中の15秒間は切り替えない）">
        <input type="checkbox" id="swFollow" checked={s.FOLLOW} onChange={(e) => setFollow(e.target.checked)} /><span className="track"><span className="thumb" /></span>自動表示</label>}
      <button className="ghost" id="bLog" onClick={() => { s.logOpen = !s.logOpen; s.emit(); }}><Icon n="list" />ログ</button>
      {!IS_OP && !IS_RX && <button className="ghost" id="bTest" title="デスクトップ通知が出るか確認" onClick={testNotify}><Icon n="bell" />テスト通知</button>}
      <button className="ghost" id="bAll" onClick={markAllSeen}><Icon n="check2" />すべて既読</button>
      {IS_OP && <NetButton />}
      <button id="bCfg" onClick={() => openCfg()}><Icon n="cog" />設定</button>
      {s.S?.local && <button className="ghost icon" id="bQuit" title={IS_OP ? "アプリを終了（ウィンドウを閉じても、コピーは裏で続けます）" : IS_RX ? "アプリを終了（ウィンドウを閉じても裏で動いています）" : "アプリを終了（このウィンドウを閉じても終了します）"} onClick={quitApp}><Icon n="power" /></button>}
    </div>
  </header>;
}
function NetButton() {
  const b = netBadge();
  return <button className={cx("ghost", b.has && "has")} id="bNet" title={b.title} onClick={() => netOpen()}><Icon n="net" />ネットワーク共有</button>;
}

/* 会場オペレーター：自分の会場・いまの日・コピー先ごとの状況・コピー中 */
export function OpStrip() {
  const s = useApp(); const S = s.S; if (!S || !OPON()) return null; const o = S.op;
  return <div className="opstrip" id="opbar">
    {(() => {   // 自分の会場（監視フォルダの状態もここに。ほかの監視フォルダは見ない）
      const r = S.roots.find((x) => x.id === o.root); const ri = r ? rootInfo(r) : null;
      return <span className={cx("opt", r && r.online === false && "off")} title={"自分の会場だけを監視し、受信が完了した演者フォルダをコピー先へコピーします（NASには書き込みません）" + (r ? "\n" + nfc(r.label) + "　" + ri!.st[1] + (ri!.m ? "\n" + ri!.m : "") + "\n" + r.path + (r.error ? "\n" + r.error : "") : "")}>
        {ri ? <span className={"dot " + ri.st[0]} /> : <Icon n="hd" />}<span className="k">会場</span><b>{nfc(o.venue || (r ? r.label : "監視フォルダ全体"))}</b>
        {ri && <span className="m">{r!.online === false ? "接続できません" : ri.st[1]}{r!.online ? " · " + (r!.count || 0).toLocaleString() + "件" : ""}</span>}</span>;
    })()}
    {(o.days || []).length > 0 && <span className="opday" title="日ごとに分かれている学会：いまの日を選ぶと、その日の会場フォルダを監視・コピーします">
      <span className="k">いまの日</span>
      <select id="opDaySel" disabled={!S.local} value={o.day} onChange={async (e) => {
        const v = e.target.value;
        try { const j: any = await api("/api/opday", { day: v }); toast("いまの日を「" + v + "」にしました（" + j.venue + " を監視・コピーします）", 5000); await loadState(); }
        catch (err: any) { toast(err.message, 6000); }
      }}>{o.days!.map((d) => <option key={d} value={d}>{d}</option>)}</select></span>}
    {opDests().map((d) => {
      const c = d.count || {}; const okn = (c.ok || 0) + (c.edited || 0); const bad = (c.err || 0) + (c.off || 0); const busy = (c.busy || 0) + (c.srcbusy || 0);
      const dot = d.online === false || bad ? "off" : busy || c.copying || c.todo || c.wait ? "busy" : d.online ? "on" : "";
      const txt = d.online === false ? "接続できません" : `コピー済み ${okn}/${d.total || 0}${busy ? " · 差し替え待ち " + busy : ""}${bad ? " · エラー " + bad : ""}`;
      return <span key={d.id} className={cx("od", d.online === false && "off")} title={d.path + (d.error ? "\n" + d.error : "")}>
        <span className={"dot " + dot} /><span className="l">{d.label}</span><span className="m">{txt}</span><span className="p"><bdi>{nfc(d.path)}</bdi></span></span>;
    })}
    {o.active && (() => {
      const pct = o.active!.total ? Math.floor((o.active!.done * 100) / o.active!.total) : 0;
      return <span className="act"><Icon n="spin" className="spin" />コピー中 {nfc(o.active!.rel.split("/").pop())}<span className="bar"><i style={{ width: pct + "%" }} /></span>{pct}%{(o.queue || 0) > 1 ? " · 残り " + ((o.queue || 0) - 1) : ""}</span>;
    })()}
  </div>;
}

export function Banner() {
  const s = useApp(); const S = s.S; if (!S) return null;
  let body: React.ReactNode[] = []; let cls = "";
  const off = S.roots.filter((r) => r.enabled && r.online === false);
  const offd = opDests().filter((d) => d.online === false);
  if (IS_OP) {
    if (!S.roots.length || !OPON()) body.push(<span key="n">このPCで見る会場と、データのコピー先がまだ設定されていません。<button className="pri" onClick={() => openCfg()}>設定を開く</button> <button className="ghost" onClick={() => netOpen()}>ネットワーク共有</button></span>);
    if (offd.length) { body.unshift(<span key="d">{offd.map((d) => `コピー先「${d.label}」に接続できません（つながったら自動でコピーします）`).join("　")} <button className="pri" onClick={() => netOpen()}>原因を調べる</button></span>); cls = "warn"; }
    if (off.length) { body.unshift(<span key="o">{off.map((r) => `${nfc(r.label)}: ${r.error}`).join("　")}</span>); cls = "bad"; }
  } else if (IS_RX) {
    if (!S.roots.length) body.push(<span key="n">受付先のNASフォルダ（学会名フォルダ）がまだ設定されていません。<button className="pri" onClick={() => openCfg()}>設定を開く</button></span>);
    if (off.length) { body.unshift(<span key="o">{off.map((r) => `⚠ ${nfc(r.label)}: ${r.error}`).join("　")}</span>); cls = "bad"; }
  } else {
    let warn = false;
    if (!S.roots.length) body.push(<span key="n">監視するNASのフォルダがまだ設定されていません。<button className="pri" onClick={() => openCfg()}>設定を開く</button></span>);
    else if (!("Notification" in window)) { body.push(<span key="n">このブラウザはデスクトップ通知に対応していません。Chrome / Edge で開いてください。</span>); warn = true; }
    else if (Notification.permission === "default") body.push(<span key="n">デスクトップ通知がまだ許可されていません。<button className="pri" onClick={askPerm}>通知を許可</button></span>);
    else if (Notification.permission === "denied") { body.push(<span key="n">デスクトップ通知がブロックされています。Chrome / Edge のサイト設定で 127.0.0.1 の「通知」を許可してください（音とログ表示は動作します）</span>); warn = true; }
    else if (!S.local) { body.push(<span key="n">閲覧専用で表示中（別端末）。既読・設定などの操作は監視PC側で行ってください。</span>); warn = true; }
    if (S.op_moved) { body.unshift(<span key="m">このPCでは「会場オペレーターモード」（発表PCへのコピー）を使っていました。コピーは <b>PADDOCK GATE</b> に分かれたため、このアプリではコピーしません。発表PCでは PADDOCK GATE を使ってください（このアプリと同じ場所にZIPを展開すれば、はじめて起動したときに会場・コピー先の設定を引き継ぎます）。</span>); warn = true; }
    if (offd.length) { body.unshift(<span key="d">{offd.map((d) => `⚠ コピー先「${d.label}」に接続できません（つながったら自動でコピーします）`).join("　")}</span>); warn = true; }
    if (off.length) { body.unshift(<span key="o">{off.map((r) => `⚠ ${nfc(r.label)}: ${r.error}`).join("　")}</span>); }
    cls = off.length ? "bad" : warn ? "warn" : "";
  }
  if (!body.length) return null;
  body = body.flatMap((b, i) => (i ? [<br key={"br" + i} />, b] : [b]));
  return <div id="banner" className={cx("banner", cls)}><Icon n={cls ? "alert" : "info"} /><span className="bt">{body}</span></div>;
}
