/* OPERATOR の設定：このPCの会場（日ごとに分かれている学会にも対応）とコピー先 */
import { Fragment, useEffect, useState } from "react";
import { api, enc } from "../api";
import type { Config } from "../types";
import { dayInfo } from "../lib/layout";
import { copyText, nfc } from "../lib/util";
import { OPON, store, toast } from "../store";
import { Icon } from "../components/Icons";
import { netOpen } from "./Net";

export const opReady = () => OPON();
export let OP_DEST = "";   // コピー先の初期値（デスクトップ\講演資料）
export function opPrepare(c: Config, defDest = "") {
  OP_DEST = defDest;
  c.op = c.op || { enabled: false, root: "", venue: "", dests: [], max_mbps: 0 };
  if (!c.op.dests.length) c.op.dests = [{ label: "このPC", path: "", enabled: true }];   // バックアップPCは、そのPCにも PADDOCK GATE を入れて自分でコピーする
  // はじめて（コピー先がどれも空）：メインはこのPCのデスクトップの「講演資料」フォルダ（コピーのときに自動で作る）
  if (OP_DEST && !c.op.dests.some((d) => String(d.path || "").trim())) c.op.dests[0].path = OP_DEST;
  c.op._dm = !!(c.op.days || []).length;
  const ids = c.roots.map((r, i) => r.id || "#" + i);
  if (!c.op.root || !ids.includes(c.op.root)) c.op.root = ids[0] || "";
}

/* メインPCとバックアップPCで「発表中・発表済み」をそろえる */
function PairSettings() {
  const [p, setP] = useState<any>(null); const [code, setCode] = useState(""); const [busy, setBusy] = useState("");
  const load = () => api<any>("/api/op/pair").then(setP).catch(() => {});
  useEffect(() => { load(); const t = window.setInterval(load, 4000); return () => clearInterval(t); }, []);
  if (!p) return null;
  const save = async (over: any = {}) => {
    setBusy("save");
    try { const j = await api<any>("/api/op/pair", { enabled: p.enabled, peer: p.peer, code: code || undefined, ...over }); setP(j); setCode(""); toast(j.enabled ? "連携を保存しました" : "連携を止めました"); }
    catch (e: any) { toast(e.message, 7000); }
    setBusy("");
  };
  const fw = async () => { setBusy("fw"); try { setP(await api<any>("/api/op/pair/fw", {})); toast("ファイアウォールの許可を追加しました"); } catch (e: any) { toast(e.message, 8000); } setBusy(""); };
  const ok = p.last_rx && Date.now() / 1000 - p.last_rx < 15;
  return <><h3>バックアップPCと発表中をそろえる</h3>
    <p className="hint" style={{ margin: "0 0 8px" }}>メインPCとバックアップPCの両方で設定すると、片方で［次の人へ］や「発表中にする」をしたとき、もう片方も同じ人になります。送るのは「どの演者を発表中・発表済みにしたか」だけです（NAS には触りません）。2台とも同じ会場・同じ合言葉にしてください。</p>
    <div className="grid2" id="pairSet">
      <span>そろえる</span><span><label className="lbl"><input type="checkbox" id="pairOn" checked={!!p.enabled} onChange={(e) => setP({ ...p, enabled: e.target.checked })} />このPCで使う</label></span>
      <span>相手のPC</span><span><input type="text" id="pairPeer" value={p.peer} placeholder="BACKUP-PC または 192.168.0.12" onChange={(e) => setP({ ...p, peer: e.target.value })} /> <span className="hint">このPCは「{p.me}」</span></span>
      <span>合言葉</span><span><input type="text" id="pairCode" value={code} placeholder={p.code_set ? "（設定済み。変えるときだけ入れる）" : "6文字以上。2台で同じもの"} onChange={(e) => setCode(e.target.value)} /></span>
      <span /><span style={{ display: "flex", gap: 8, flexWrap: "wrap" }}>
        <button className="pri" id="pairSave" disabled={!!busy} onClick={() => save()}>連携を保存</button>
        {store.S?.os === "win" && <button id="pairFw" disabled={!!busy} onClick={fw} title="相手のPCからの知らせを受け付けるよう、Windows ファイアウォールに許可を足します（管理者の確認が出ます。1回だけ）">ファイアウォールの許可を追加…</button>}</span>
      <span>状態</span><span id="pairSt" className={ok ? "" : "dim"}>{!p.enabled ? "使っていません" : ok ? "連携中（" + p.rx_from + " から届いています）" : "相手のPCから届いていません" + (p.err ? "：" + p.err : "（相手のPCでも設定し、両方でファイアウォールの許可を追加してください）")}{p.fw === "ok" ? "　· ファイアウォール許可済み" : ""}</span>
    </div></>;
}

/* Stream Deck・Companion から操作するときのURL（このPCの中だけ） */
function RemoteInfo() {
  const [info, setInfo] = useState<{ key: string; port: number } | null>(null);
  useEffect(() => { api<any>("/api/op/remote/info").then(setInfo).catch(() => {}); }, []);
  if (!info) return null;
  const base = "http://127.0.0.1:" + info.port + "/api/remote/";
  const rows: [string, string][] = [["next", "次の人へ（いまの人を発表済みに）"], ["prev", "1人戻す"], ["show", "発表中の人をスライドショーで開く"], ["file", "発表中の人の発表ファイルを開く"], ["folder", "発表中の人のフォルダを開く"], ["status", "いまの状態（発表中・次の人の名前。JSON）"]];
  return <><h3>Stream Deck・Companion から操作</h3>
    <p className="hint" style={{ margin: "0 0 8px" }}>Companion の「Generic HTTP」→「GET」に、下のURLを入れてボタンに割り当てます。<b>このPCの中から</b>だけ使えます（Companion はこのPCで動かしてください）。GATE の画面を開いているときに動きます。</p>
    <div className="grid2" id="remoteUrls">{rows.map(([k, l]) => { const u = base + k + "?key=" + info.key; return <Fragment key={k}><span>{l}</span>
      <span style={{ display: "flex", gap: 6, alignItems: "center", minWidth: 0 }}><code className="mono" style={{ fontSize: 11.5, overflow: "hidden", textOverflow: "ellipsis", whiteSpace: "nowrap" }}>{u}</code>
        <button className="ghost sm" onClick={() => copyText(u).then(() => toast("URLをコピーしました"), () => toast("コピーできませんでした"))}><Icon n="copy" />コピー</button></span></Fragment>; })}</div></>;
}

export function OpSetupGuide() {
  return <div className="opsetup"><b>はじめに、上から順に ①〜③ を入れて［保存］してください。</b>
    <div className="alt"><b>バックアップPC</b>にも PADDOCK GATE を入れて、同じように ①〜③（同じ会場）を設定してください。それぞれのPCが、NASから自分のデスクトップの「講演資料」へコピーします（PCどうしのファイル共有は不要です）。</div></div>;
}

const opJoin = (a: string, b: string) => { const sep = a.includes("\\") || /^[A-Za-z]:/.test(a) ? "\\" : "/"; return a.replace(/[\\/]+$/, "") + sep + b; };
const opList = async (path: string) => (await api<{ venues: string[] }>("/api/venues?root=&path=" + enc(path))).venues;
type Sub = string[] | { err: string };
const OPD: { root: string; dirs: string[] | null; sub: Record<string, Sub>; err: string } = { root: "", dirs: null, sub: {}, err: "" };

export function OpSection({ c, up, part }: { c: Config; up: () => void; part: "venue" | "dests" | "adv" }) {
  const op = c.op;
  {   // 監視フォルダを追加・削除したときも、選べる監視フォルダにそろえる（はじめての設定で会場が読み込めなくならないように）
    const ids = c.roots.map((r, i) => r.id || "#" + i);
    if (!ids.includes(op.root)) { op.root = ids[0] || ""; op.venue = ""; }
  }
  const rootIdx = c.roots.findIndex((r, i) => (r.id || "#" + i) === op.root);
  const rr = rootIdx >= 0 ? c.roots[rootIdx] : null;
  const rp = rr ? rr.path : "";
  const [venues, setVenues] = useState<{ list: string[]; err: string; root: string } | null>(null);
  const [, setTick] = useState(0); const re = () => setTick((n) => n + 1);

  // 会場の候補（監視フォルダのすぐ下のフォルダ）
  useEffect(() => {
    if (!rp || part !== "venue") return; let alive = true;
    api<{ venues: string[] }>("/api/venues?root=" + enc(rr?.id || "") + "&path=" + enc(rp)).then((j) => { if (alive) setVenues({ list: j.venues, err: "", root: rp }); })
      .catch((e) => { if (alive) setVenues({ list: [], err: e.message, root: rp }); });
    return () => { alive = false; };
  }, [rp]);
  // 日ごとの会場（DAY1 → その下の会場）
  useEffect(() => {
    if (!op._dm || !rp || part !== "venue") return; let alive = true;
    (async () => {
      if (OPD.root !== rp) { OPD.root = rp; OPD.dirs = null; OPD.sub = {}; OPD.err = ""; }
      if (!OPD.dirs) { try { OPD.dirs = await opList(rp); } catch (e: any) { OPD.err = e.message; if (alive) re(); return; } }
      if (!(op.days || []).length) {   // はじめて：日らしいフォルダ（DAY1・1日目・10月23日 など）を並べる
        const ds = OPD.dirs.filter((n) => dayInfo(n)); op.days = (ds.length ? ds : OPD.dirs.slice(0, 4)).map((n) => ({ label: n, venue: n + "/" }));
      }
      await Promise.all((op.days || []).map(async (d) => { const f = d.venue.split("/")[0]; if (f && !OPD.sub[f]) { try { OPD.sub[f] = await opList(opJoin(rp, f)); } catch (e: any) { OPD.sub[f] = { err: e.message }; } } }));
      if (!op.day || !(op.days || []).some((d) => d.label === op.day)) op.day = (op.days || [])[0]?.label || "";
      if (alive) { re(); up(); }
    })();
    return () => { alive = false; };
  }, [op._dm, rp]);

  const setMode = (dm: boolean) => {
    if (dm === !!op._dm) return;
    op._dm = dm;
    if (dm && rr && rr.depth < 4) { rr.depth = rr.depth + 1; (rr as any)._bump = true; toast("日のフォルダが1段増えるため、監視フォルダの「階層」を " + rr.depth + " にしました", 6000); }
    else if (!dm && rr && (rr as any)._bump) { rr.depth = rr.depth - 1; delete (rr as any)._bump; toast("監視フォルダの「階層」を " + rr.depth + " に戻しました", 5000); }   // 自動で増やした分を戻す
    up();
  };
  const days = op.days || [];
  const setDayFolder = async (i: number, f: string) => {
    const d = days[i]; const old = d.venue.split("/").slice(1).join("/"); d.label = f; d.venue = f + "/";
    if (f && !OPD.sub[f]) { try { OPD.sub[f] = await opList(opJoin(rp, f)); } catch (e: any) { OPD.sub[f] = { err: e.message }; } }
    const sub = OPD.sub[f]; if (old && Array.isArray(sub) && sub.includes(old)) d.venue = f + "/" + old; up();
  };
  const setDayVenue = (i: number, v: string) => {
    const d = days[i]; d.venue = d.venue.split("/")[0] + "/" + v;
    if (v) days.forEach((o) => { const f = o.venue.split("/")[0]; const sub = OPD.sub[f]; if (o !== d && f && !o.venue.split("/")[1] && Array.isArray(sub) && sub.includes(v)) o.venue = f + "/" + v; });
    up();
  };
  const vl = venues && venues.root === rp ? venues : null;
  // 学会フォルダのすぐ下が DAY1・DAY2…（日のフォルダ）なら、はじめての設定のときは自動で「日ごと」にする
  useEffect(() => {
    if (part !== "venue" || !vl || op._dm || op.venue || (op.days || []).length) return;
    const ds = vl.list.filter((n) => dayInfo(n));
    if (ds.length && ds.length * 2 >= vl.list.length) { setMode(true); toast("学会フォルダの下に日のフォルダ（" + ds.slice(0, 3).map(nfc).join("・") + (ds.length > 3 ? "…" : "") + "）があるので、「日ごとに分かれている」にしました", 7000); }
  }, [vl]);
  if (part === "adv") return <>
    <h3>コピーの速度</h3>
    <div className="grid2"><span>速度の上限</span><span><input type="number" id="opMbps" min={0} max={1000} step={1} value={op.max_mbps || 0} onChange={(e) => { op.max_mbps = Math.max(0, +e.target.value || 0); up(); }} /> MB/秒（0 = 制限なし）</span></div>
    <p className="hint">コピーの決まり（安全のため）<br />
      ・コピー先には、会場より下（セッション／演者フォルダ）を同じ構成で作ります。<br />
      ・<b>NASには一切書き込みません</b>（読むだけ）。受信中の演者フォルダはコピーせず、NAS上で開かれているファイルにも触れません。<br />
      ・コピー先で<b>開かれているファイル（発表中など）は上書きしません</b>。閉じられてから新しい版に差し替えます。<br />
      ・差し替えた旧版はコピー先の「_差し替え前」フォルダに残します。<b>コピー先のファイルを消すことはありません</b>（NAS側で消えても残します）。<br />
      ・コピー先で編集したファイルは、NAS側が更新されない限り上書きしません。</p>
    <PairSettings />
    <RemoteInfo />
  </>;
  if (part === "dests") {
    const main = op.dests[0];
    return <>
      <p className="hint" style={{ margin: "0 0 10px" }}>NASに演者のデータが入り終わったら、ここへ演者フォルダごと自動でコピーします。初期値は、このPCのデスクトップの「講演資料」フォルダです（無ければ自動で作ります）。バックアップPCは、そのPCに入れた PADDOCK GATE が自分でコピーするので、ここに入れる必要はありません。</p>
      <div id="dlist">{op.dests.map((d, i) => <div className="drow" key={i} data-i={i}>
        <input type="text" data-k="label" value={d.label} placeholder="名前（例: メイン）" onChange={(e) => { d.label = e.target.value; up(); }} />
        <input type="text" data-k="path" className="pth mono" value={d.path} placeholder={i === 0 ? "デスクトップ\\講演資料" : "D:\\講演資料  /  \\\\別のPC\\共有\\講演資料"} onChange={(e) => { d.path = e.target.value; up(); }} />
        <button className="ghost" onClick={async () => { try { const j: any = await api("/api/pick", { dest: true }); if (j.path) { d.path = j.path; up(); } } catch (e: any) { toast(e.message, 5000); } }}>参照…</button>
        <label><input type="checkbox" data-k="enabled" checked={d.enabled} onChange={(e) => { d.enabled = e.target.checked; up(); }} />有効</label>
        <button className="ghost danger" onClick={() => { op.dests.splice(i, 1); up(); }}>削除</button></div>)}</div>
      <p className="hint" style={{ marginTop: 0 }}>
        {op.dests.length < 4 && <button className="ghost" id="bDAdd" onClick={() => { op.dests.push({ label: "", path: "", enabled: true }); up(); }}><Icon n="plus" />コピー先を追加（USBなど）</button>}
        {OP_DEST && main && main.path !== OP_DEST && <button className="ghost" id="bDDef" onClick={() => { main.path = OP_DEST; up(); }}>デスクトップ\講演資料に戻す</button>}
        <button className="ghost" id="bNetCfg" onClick={() => netOpen()}><Icon n="net" />別のPCへコピーするとき（接続・共有）…</button></p>
    </>;
  }
  return <>
    {c.roots.length ? <div className="grid2">
      {c.roots.length > 1 && <><span>学会フォルダ</span><span><select id="opRoot" value={op.root} onChange={(e) => { if (op._dm) setMode(false); op.root = e.target.value; op.venue = ""; op.days = []; OPD.dirs = null; up(); }}>
        {c.roots.map((r, i) => <option key={i} value={r.id || "#" + i}>{r.label || r.path}</option>)}</select></span></>}
      <span>フォルダの分け方</span><span className="checks col">
        <label><input type="radio" name="opDm" value="0" checked={!op._dm} onChange={() => setMode(false)} />学会 → 会場 → セッション → 演者</label>
        <label><input type="radio" name="opDm" value="1" checked={!!op._dm} onChange={() => setMode(true)} />学会 → 日（DAY1・DAY2…） → 会場 → …（日ごとに分かれている）</label></span>
      {!op._dm ? <>
        <span>自分の会場</span><span><select id="opVenue" value={op.venue} onChange={(e) => { op.venue = e.target.value; up(); }}>
          {!vl ? <option value={op.venue}>{op.venue || "読み込み中…"}</option> : <>
            <option value="">（選んでください）</option>
            {vl.list.map((v) => <option key={v} value={v}>{nfc(v)}</option>)}
            {op.venue && !vl.list.includes(op.venue) && <option value={op.venue}>{nfc(op.venue)}（現在見つかりません）</option>}
            {vl.err && <option disabled>{vl.err}</option>}</>}</select></span>
      </> : <>
        <span>日ごとの会場</span><span><div id="opDays">{OPD.err ? <span className="hint">{OPD.err}</span> : !OPD.dirs ? <span className="hint">読み込み中…</span> :
          <table className="optab"><thead><tr><th>日のフォルダ</th><th>その日の自分の会場</th><th /></tr></thead><tbody>{days.map((d, i) => {
            const f = d.venue.split("/")[0], v = d.venue.split("/").slice(1).join("/"); const sub = OPD.sub[f];
            const fo = (OPD.dirs || []).slice(); if (f && !fo.includes(f)) fo.push(f);
            const vo = Array.isArray(sub) ? sub.slice() : []; if (v && !vo.includes(v)) vo.push(v);
            return <tr key={i} data-i={i}><td><select data-k="f" value={f} onChange={(e) => setDayFolder(i, e.target.value)}><option value="">（選ぶ）</option>{fo.map((x) => <option key={x} value={x}>{nfc(x)}</option>)}</select></td>
              <td><select data-k="v" value={v} onChange={(e) => setDayVenue(i, e.target.value)}><option value="">（選ぶ）</option>{vo.map((x) => <option key={x} value={x}>{nfc(x)}{Array.isArray(sub) && !sub.includes(x) ? "（現在見つかりません）" : ""}</option>)}
                {sub && !Array.isArray(sub) && <option disabled>{sub.err}</option>}</select></td>
              <td><button className="ghost danger" onClick={() => { days.splice(i, 1); up(); }}>削除</button></td></tr>;
          })}</tbody></table>}</div>
          <p className="hint" style={{ margin: "6px 0 0" }}><button className="ghost" id="bDayAdd" onClick={() => { op.days = [...days, { label: "", venue: "" }]; up(); }}><Icon n="plus" />日を追加</button>　1つの日で会場を選ぶと、ほかの日にも同じ名前の会場があれば自動で入ります。</p>
          <p className="hint" style={{ margin: "8px 0 0" }}><label><input type="checkbox" id="opDayDir" checked={op.day_dir !== false} onChange={(e) => { op.day_dir = e.target.checked; up(); }} />コピー先に日のフォルダ（DAY1 など）を作って分ける</label>（おすすめ）</p></span>
        <span>いまの日</span><span><select id="opDay" value={op.day || ""} onChange={(e) => { op.day = e.target.value; up(); }}>{days.filter((d) => d.label).map((d) => <option key={d.label} value={d.label}>{d.label}</option>)}</select><span className="hint">　メイン画面の左上の DAY タブからも切り替えられます</span></span>
      </>}
    </div> : <p className="hint" style={{ margin: 0 }}>先に ① で学会フォルダを追加してください（追加すると、ここで会場を選べます）。DAY1・DAY2… のように日ごとに分かれている学会も、追加したあとここで「日ごと」を選べます（日のフォルダがあれば自動で選びます）。</p>}
  </>;
}
