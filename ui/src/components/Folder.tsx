/* 演者フォルダの中身：見出し・状態・メモ・コピー先・PowerPoint解析・最近の変更・ファイル一覧 */
import { EmptyState } from "../design/ui";
import { useEffect, useRef, useState } from "react";
import type { Analysis, FolderItem, VideoInfo } from "../types";
import { IS_OP, IS_RX } from "../boot";
import { lay, recvState } from "../lib/layout";
import { ago, cmpKeys, cmpPath, copyText, cx, dtm, fmtSize, hms, nfc, sl, sortKey } from "../lib/util";
import { closeDrawer, consumeScrollTop, openOS, rootById, store, toast, useApp, venueOf, vColor } from "../store";
import { CPL, CpPill, FlagChips, KindPill, MKC, MKR, OPS, RowProg, ST, StateTag, Tag } from "./Bits";
import { Icon } from "./Icons";
import { OpFileButtons, OpFolderButton, opNewest, OpOpenHead } from "../op/Opener";
import { RxPanel } from "../rx/RxPanel";

export function CenterPane() {
  const s = useApp();
  const ref = useRef<HTMLDivElement>(null);
  useEffect(() => { if (consumeScrollTop() && ref.current) ref.current.scrollTop = 0; });
  return <section id="center" className="pane center">
    {s.view === "board" && <div id="dhead"><span className="t">フォルダの中身</span><button className="ghost" id="bDClose" title="閉じる（Esc）" onClick={closeDrawer}><Icon n="x" />閉じる</button></div>}
    <div className="scroll" id="fold" ref={ref}>
      {IS_RX && <RxPanel />}
      <div id="foldbody"><div className="fswap" key={s.SEL ? s.SEL.root + "|" + s.SEL.group : "-"}><FolderBody /></div></div>
    </div>
  </section>;
}

function FolderBody() {
  const s = store; const S = s.S; const F = s.F;
  if (s.folderErr && !F) return <div className="empty">{s.folderErr}</div>;
  if (!s.SEL || !S) return IS_RX ? null : <EmptyState style={{ paddingTop: 90 }} title="演者フォルダを選択">左の一覧か通知をクリックすると、<br />その演者フォルダの中身と解析結果がここに表示されます。<br /><br /><span className="dim" style={{ fontSize: 12.5 }}>NAS上のファイルは書き換えません（一覧・属性の取得と、PowerPoint解析のための読み取りのみ）</span></EmptyState>;
  if (!F) return <div className="empty">読み込み中…</div>;
  const segs = F.group.split("/"); const r = rootById(F.root);
  const name = F.group === "" ? (r && r.depth > 1 ? "（演者フォルダより上のファイル）" : "（直下のファイル）") : segs[segs.length - 1];
  const files = F.items.filter((i) => !i.d && !i.mk); const size = files.reduce((a, i) => a + (i.s || 0), 0); const latest = files.reduce((a, i) => Math.max(a, i.m || 0), 0);
  const pend = F.items.filter((i) => i.st === "pending" && !i.mk).length;
  const cats: Record<string, number> = {}; files.forEach((i) => { cats[i.c || "他"] = (cats[i.c || "他"] || 0) + 1; });
  const osName = S.os === "win" ? "Explorer" : S.os === "mac" ? "Finder" : "ファイラー";
  const fv = venueOf(F.root, F.group);
  const gg = r && (r.groups || []).find((x) => x.key === F.group);
  const st = pend ? "copying" : gg ? recvState(gg) : files.length ? "recv" : "none";
  const fd = F.op ? F.op.dests.filter((d) => d.enabled) : [];
  const memo = F.memo || [];
  const ana = F.items.filter((i) => i.a).sort((a, b) => cmpPath(a.p, b.p));
  const rows = F.items.map((i) => ({ k: sortKey(i.p, i.d), i })).sort((a, b) => cmpKeys(a.k, b.k)).map((x) => x.i);
  const nmk = F.items.filter((i) => i.mk).length;
  const now = Date.now() / 1000;
  const newest = IS_OP ? opNewest(F) : "";
  return <>
    <div className="fh">
      <div className="crumb"><span>{nfc(F.label)}</span>{segs.length > 1 && segs.slice(0, -1).map((x, i) => r && i === lay(r).vl && fv
        ? <span key={i} className="cseg"><Icon n="chev" /><span className="vbadge" style={{ ["--vc" as any]: vColor(F.root, fv) }}><Icon n="building" />{nfc(x)}</span></span>
        : <span key={i} className="cseg"><Icon n="chev" /><b>{nfc(x)}</b></span>)}</div>
      <h1>{nfc(name)}</h1>
      <div className="facts">
        {F.group !== "" && <><StateTag st={st} />{gg && <FlagChips g={gg} />}</>}
        <span>{files.length} ファイル</span><span>{fmtSize(size)}</span>{latest > 0 && <span>最終更新 {dtm(latest)}</span>}
        {F.track && F.track.recv && <span>受付 {dtm(F.track.recv)}</span>}
        {F.track && F.track.n ? <Tag t="repl">差し替え {F.track.n}回（最終 {dtm(F.track.last!)}）</Tag> : null}
        {pend > 0 && <span className="copying">● コピー中/確定待ち {pend}</span>}
        {r && gg && <RowProg r={r} g={gg} />}
      </div>
      {IS_OP && <OpOpenHead F={F} />}
      <div className="acts">
        {IS_OP && <OpFolderButton F={F} />}
        {S.local && S.ui.os_open && !IS_OP && <button id="bOpen" title={`NAS上のフォルダを${osName}で開く`} onClick={() => openOS(F.root, F.group)}><Icon n="ext" />{osName}で開く</button>}
        <button id="bCopy" onClick={() => copyText(F.path).then(() => toast("パスをコピーしました"), () => toast("コピーできませんでした"))}><Icon n="copy" />パスをコピー</button>
        {Object.entries(cats).sort((a, b) => b[1] - a[1]).map(([c, n]) => <span key={c} className={"chip c-" + c}>{c} {n}</span>)}
      </div>
      <div className="pathline">{nfc(F.path)}</div>
    </div>
    {!F.exists && F.group !== "" && <div className="gone">このフォルダは現在NAS上に見つかりません（削除・名前変更された可能性）。{F.op ? "コピー先のファイルは消していません。" : ""}</div>}
    {memo.length > 0 && <div className="sec"><h3><Icon n="memo" />メモ<small>演者フォルダの中のテキスト（.txt）</small></h3>
      {memo.map((m, i) => m.more ? <div key={i} className="memo-more">ほか {m.more}個の .txt（表示を省略）</div>
        : <div key={i} className="memo"><div className="mh"><b>{nfc(m.p)}</b><span>{m.m ? dtm(m.m) : ""}</span></div>
          {m.pending ? <div className="mb dim">受信中（受け取りが終わると表示します）</div>
            : m.error != null ? <div className="mb dim">読めませんでした：{m.error}</div>
              : <><pre className="mb">{m.text || <span className="dim">（空のファイル）</span>}</pre>{m.trunc && <div className="mb dim">長いため途中まで表示しています</div>}</>}</div>)}</div>}
    {fd.length > 0 && <div className="sec"><h3>コピー先<small>受信が完了したら自動でコピーします（NASには書き込みません）</small></h3><div className="evlist">
      {fd.map((d) => {
        const x = d.state ? CPL[d.state] : null;
        return <div key={d.id} className="evc dest"><b>{d.label}</b>
          {x ? <Tag t={x[1] === "ok" ? "ok" : x[1] === "bad" ? "bad" : x[1] === "dim" ? "dim" : "warn"} className={x[1] === "run" ? "copying" : ""}>{x[0]}</Tag> : <Tag t="dim">{files.length ? "確認中" : "ファイルなし"}</Tag>}
          <span style={{ flex: 1 }} /><button className="ghost" onClick={() => copyText(d.path).then(() => toast("コピー先のパスをコピーしました"), () => toast("コピーできませんでした"))}><Icon n="copy" />パスをコピー</button>
          <div className="pathline">{nfc(d.path)}</div></div>;
      })}</div></div>}
    {ana.length > 0 && <div className="sec"><h3>PowerPoint 解析<small>動画・リンク・COI・自動送り・クリック無効</small></h3>{ana.map((it) => <AnaCard key={it.p} it={it} />)}</div>}
    {F.events.length > 0 && <div className="sec"><h3>最近の変更</h3><div className="evlist">{F.events.slice(0, 8).map((e) => {
      const items = (e.items || []).slice(0, 30);
      return <div key={e.id} className={cx("evc", e.u && "u")}><div className="top"><KindPill k={e.kind} />{e.repl ? <span className="kind k-repl">差し替え {e.repl}回目</span> : null}
        <span className="t">{dtm(e.ts)} ({ago(e.ts)})</span>{e.while_stopped && <span className="ws">停止中の変更</span>}<span style={{ fontSize: 12 }}>{e.summary}</span></div>
        {(items.length > 0 || (e.n_items || 0) > 30) && <ul>{items.map((it, i) => {
          const o = OPS[it.op] || ["", "", ""];
          const sz = it.op === "mod" && it.old_size != null ? `${fmtSize(it.old_size)} → ${fmtSize(it.size)}` : it.size != null ? fmtSize(it.size) : "";
          return <li key={i}><span className={"op o-" + o[1]} title={o[2]} aria-label={o[2]}>{o[0] && <Icon n={o[0]} />}</span><span className="fn">{it.op === "rename" || it.op === "folder_rename" ? <>{nfc(it.path)} <span className="x">→</span> {nfc(it.to)}</> : nfc(it.path)}</span><span className="x">{sz}</span></li>;
        })}{(e.n_items || 0) > 30 && <li><span className="op" /><span className="x">ほか {(e.n_items || 0) - 30} 件</span></li>}</ul>}</div>;
    })}</div></div>}
    <div className="sec"><h3>ファイル<small>{files.length}件{nmk ? `（ほかに目印 ${nmk}）` : ""}</small></h3>
      {!rows.length ? <div className="tcard"><div className="empty" style={{ padding: 28 }}>空のフォルダです</div></div>
        : <div className="tcard"><table className="files"><thead><tr><th>名前</th><th>種類</th><th style={{ textAlign: "right" }}>サイズ</th><th>更新日時</th><th>状態</th>{fd.length > 0 && <th>コピー</th>}{IS_OP && <OpFileButtons.Head F={F} />}</tr></thead>
          <tbody>{rows.map((i) => {
            const dep = i.p.split("/").length - 1; const nm = i.p.split("/").pop();
            const s2 = i.st ? ST[i.st] : null; const fresh = i.ct && now - i.ct < 1800;
            return <tr key={i.p} className={cx(i.d && "dir", i.mk && "mkrow", i.st === "pending" ? "pend" : s2 && fresh ? "hl-" + i.st : "")}>
              <td className="nm" style={{ paddingLeft: 8 + dep * 16 }}>{i.d ? "▸ " : ""}{nfc(nm)}
                {i.mk && <> <Tag t={MKC[i.mk] || "dim"} title={`ファイル名から判断した目印（${MKR[i.mk] || ""}）。データとしては数えません`}>目印：{nfc(i.ml || "")}</Tag></>}
                {newest === i.p && <> <Tag t="info" title="発表ファイルが2つ以上あります。これがいちばん後からNASに入ったものです">後から入った</Tag></>}</td>
              <td>{i.d ? "" : i.mk ? <span className="chip">目印</span> : <span className={"chip c-" + i.c}>{i.c}</span>}</td>
              <td className="num">{i.d ? "" : fmtSize(i.s)}</td><td className="tm">{i.m ? dtm(i.m) : ""}</td>
              <td>{s2 && <span className={cx("stl", "o-" + s2[1], i.st === "pending" && "copying")}>{s2[0]}{i.ct ? " " + hms(i.ct) : ""}</span>}</td>
              {fd.length > 0 && <td style={{ whiteSpace: "nowrap" }}>{!i.d && fd.map((d) => (i.cp && i.cp[d.id] ? <CpPill key={d.id} label={d.label} st={i.cp[d.id][0]} msg={i.cp[d.id][1]} /> : null))}</td>}
              {IS_OP && <OpFileButtons.Cell F={F} it={i} />}
            </tr>;
          })}</tbody></table></div>}
    </div>
    <div style={{ height: 32 }} />
  </>;
}

/* ---- PowerPoint 解析の結果 */
function VFmt({ v }: { v: VideoInfo }) {
  const f = v.fmt; if (!f) return null;
  const p = [f.container, f.video, f.audio && "音声 " + f.audio, f.res].filter(Boolean).join(" · ");
  const cls = f.v === "bad" ? "o-del" : f.v === "warn" ? "o-mod" : f.v === "unk" ? "" : "o-add";
  const lab = f.v === "bad" ? "再生できない可能性大" : f.v === "warn" ? "要試写" : f.v === "unk" ? "形式不明" : "再生OK（H.264等）";
  return <span className="vfmt">形式：{p || "—"}　<b className={cls}>{lab}</b>{f.why && <><br /><span className={cls}>{f.why}</span></>}</span>;
}
const VST: Record<string, [string, string]> = { here: ["同じフォルダにあり", "o-add"], missing: ["見つかりません", "o-del"], abs: ["発表者PCのパス（会場PCでは再生できない可能性大）", "o-del"], unc: ["ネットワーク上のパス", "o-mod"], online: ["ネット接続が必要", "o-mod"] };
function VLine({ v }: { v: VideoInfo }) {
  if (v.kind === "embed") return <span className="sub">{sl(v.s)}　埋め込み {v.name}{v.size ? " · " + fmtSize(v.size) : ""}<VFmt v={v} /></span>;
  const x = VST[v.st || ""] || ["外部リンク", "o-mod"];
  return <span className="sub">{sl(v.s)}　<b className={x[1]}>{v.kind === "online" ? (v.av === "audio" ? "オンライン音声" : "オンライン動画") : v.av === "audio" ? "リンク音声" : "リンク動画"}</b> {nfc(v.target || v.name)} — <span className={x[1]}>{x[0]}</span><VFmt v={v} /></span>;
}
const vProb = (v: VideoInfo) => !!((v.fmt && v.fmt.v !== "ok") || (v.kind === "embed" && !v.fmt) || (v.kind !== "embed" && v.st !== "here"));
type ARow = [string, string, string, React.ReactNode];
function VideoRow(a: Analysis, open: boolean, setOpen: (v: boolean) => void): ARow {
  const vs = a.video || [], nv = a.n_video != null ? a.n_video : vs.length;
  if (!nv) return ["動画", "dim", "なし", null];
  const cnt = (k: string) => vs.filter((v) => v.fmt && v.fmt.v === k).length; const nb = cnt("bad"), nw = cnt("warn"), nu = cnt("unk");
  const nl = vs.filter((v) => v.kind !== "embed").length, nlb = vs.filter((v) => v.kind !== "embed" && (v.st === "missing" || v.st === "abs")).length;
  const sum = [nb && `再生できない形式 ${nb}`, nw && `要試写 ${nw}`, nu && `形式不明 ${nu}`, nlb && `リンク切れ ${nlb}`].filter(Boolean).join("・");
  const cls = nb || nlb ? "bad" : nw || nu || nl ? "warn" : "info";
  const prob = vs.filter(vProb), ok = vs.filter((v) => !vProb(v));
  const body = vs.length <= 10 ? vs.map((v, i) => <VLine key={i} v={v} />) : <>
    {prob.map((v, i) => <VLine key={i} v={v} />)}
    {ok.length > 0 && <details className="vok" open={open || !prob.length} onToggle={(e) => setOpen((e.target as HTMLDetailsElement).open)}>
      <summary>{prob.length ? `問題のない動画 ${ok.length}本（再生OK）を表示` : `すべて再生OK（${ok.length}本）`}</summary>{ok.map((v, i) => <VLine key={i} v={v} />)}</details>}
  </>;
  return ["動画", cls, `あり ${nv}${sum ? "（" + sum + "）" : ""}`, <>{body}{nv > vs.length && <span className="sub">ほか {nv - vs.length}本（表示を省略）</span>}</>];
}
const autoText = (auto: [number, number][]) => { const m = new Map<number, number[]>(); auto.forEach(([s2, sec]) => { if (!m.has(sec)) m.set(sec, []); m.get(sec)!.push(s2); }); return [...m].map(([sec, ss]) => `${sl(ss)}：${sec}秒`).join("　"); };
function AnaCard({ it }: { it: FolderItem }) {
  const [open, setOpen] = useState(false);
  const a = it.a!; const chip = <span className={"chip c-" + it.c}>{it.c}</span>; const nm = nfc(it.p);
  if (a.na) return <div className="ana"><div className="hd">{chip}<span className="fn">{nm}</span><Tag t="dim">{a.na}</Tag></div></div>;
  if (a.pending) return <div className="ana"><div className="hd">{chip}<span className="fn">{nm}</span><Tag t="dim" className={a.inuse ? "" : "copying"}>{a.copying ? "コピー完了後に解析" : a.inuse ? "PowerPointで開かれているため解析待ち（閉じたら自動で解析）" : "解析中…"}</Tag></div></div>;
  if (!a.ok) return <div className="ana"><div className="hd">{chip}<span className="fn">{nm}</span><Tag t="bad">解析できません</Tag></div><div className="msg">{a.error || ""}</div></div>;
  const rows: ARow[] = [VideoRow(a, open, setOpen)];
  if (a.audio && a.audio.length) {
    const ab = a.audio.filter((v) => v.kind !== "embed" && (v.st === "missing" || v.st === "abs")).length;
    rows.push(["音声", ab ? "bad" : "info", `あり ${a.n_audio != null ? a.n_audio : a.audio.length}${ab ? `（リンク切れ ${ab}）` : ""}`, a.audio.slice(0, 40).map((v, i) => <VLine key={i} v={v} />)]);
  }
  const links = a.links || []; const nl = a.n_links != null ? a.n_links : links.length; const other = a.other || [];
  rows.push(nl || other.length ? ["ハイパーリンク", "info", `あり ${nl}`, <>
    {links.slice(0, 8).map((l, i) => <span key={i} className="sub">{sl(l.s)}　{l.url}</span>)}{nl > 8 && <span className="sub">ほか {nl - 8} 件</span>}
    {other.slice(0, 5).map((o, i) => <span key={"o" + i} className="sub">{sl(o.s)}　<b className="o-mod">外部リンク({o.type})</b> {o.target}</span>)}</>] : ["ハイパーリンク", "dim", "なし", null]);
  const coi = a.coi || [];
  rows.push(coi.length ? ["COI", "ok", "あり", coi.map((c, i) => <span key={i} className="sub">{sl([c.s])}　「{nfc(c.text)}」</span>)]
    : ["COI", "warn", "なし", <span className="sub">COI・利益相反・ディスクロージャー等の文字が見つかりません（画像で貼られている場合は検出できません）</span>]);
  const auto = a.auto || [];
  if (!auto.length) rows.push(["自動送り", "dim", "なし", null]);
  else if (a.use_timings) rows.push(["自動送り", "warn", `あり ${auto.length}枚`, <span className="sub">{autoText(auto)}</span>]);
  else rows.push(["自動送り", "dim", `設定あり ${auto.length}枚（無効）`, <span className="sub">「タイミングを使用」がオフのため、スライドショーでは自動で進みません</span>]);
  const noclick = a.noclick || [];
  if (a.kiosk) rows.push(["クリック無効", "bad", "全スライド", <span className="sub">「自動プレゼンテーション（キオスク）」設定のため、クリックで進めません</span>]);
  else if (noclick.length) {
    const autoSet = new Set(a.use_timings ? auto.map((x) => x[0]) : []); const stuck = noclick.filter((x) => !autoSet.has(x));
    rows.push(["クリック無効", stuck.length ? "bad" : "warn", `あり ${noclick.length}枚`, <span className="sub">{sl(noclick)}{stuck.length ? <><br /><b className="o-del">{sl(stuck)}は自動送りもないため、クリックで先に進めません</b></> : "（自動送りで進みます）"}</span>]);
  } else rows.push(["クリック無効", "dim", "なし", null]);
  const head = `${a.slides}枚${a.hidden && a.hidden.length ? `（非表示 ${sl(a.hidden)}）` : ""}`;
  return <div className="ana"><div className="hd">{chip}<span className="fn">{nm}</span><span className="x">{head}</span></div>
    <table><tbody>{rows.map((r) => <tr key={r[0]}><td className="k">{r[0]}</td><td className="v"><Tag t={r[1]}>{r[2]}</Tag>{r[3]}</td></tr>)}</tbody></table></div>;
}
