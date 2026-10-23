/* OPERATOR の設定：このPCの会場（日ごとに分かれている学会にも対応）とコピー先 */
import { useEffect, useState } from "react";
import { api, enc } from "../api";
import type { Config } from "../types";
import { dayInfo } from "../lib/layout";
import { nfc } from "../lib/util";
import { OPON, toast } from "../store";
import { Icon } from "../components/Icons";
import { closeModal } from "../components/Settings";
import { netOpen } from "./Net";

export const opReady = () => OPON();
export function opPrepare(c: Config) {
  c.op = c.op || { enabled: false, root: "", venue: "", dests: [], max_mbps: 0 };
  if (!c.op.dests.length) c.op.dests = [{ label: "メイン", path: "", enabled: true }, { label: "バックアップ", path: "", enabled: true }];
  c.op._dm = !!(c.op.days || []).length;
  const ids = c.roots.map((r, i) => r.id || "#" + i);
  if (!c.op.root || !ids.includes(c.op.root)) c.op.root = ids[0] || "";
}

export function OpSetupGuide() {
  return <div className="opsetup"><b>はじめに設定してください</b><ol>
    <li>「監視フォルダ」に、NASの学会名フォルダを追加（［参照…］→［追加］）</li>
    <li>「このPCの会場とコピー先」で、自分の会場を選ぶ</li>
    <li>コピー先（この発表PCのフォルダ、バックアップPCの共有フォルダ）を入れて［保存］</li></ol>
    <div className="alt">このPCが<b>バックアップPC（コピーされる側）</b>なら、ここの設定は不要です。<button className="ghost" onClick={() => { closeModal(); netOpen(); }}>ネットワーク共有</button> で［このPCを設定する］だけ押してください。</div></div>;
}

const opJoin = (a: string, b: string) => { const sep = a.includes("\\") || /^[A-Za-z]:/.test(a) ? "\\" : "/"; return a.replace(/[\\/]+$/, "") + sep + b; };
const opList = async (path: string) => (await api<{ venues: string[] }>("/api/venues?root=&path=" + enc(path))).venues;
type Sub = string[] | { err: string };
const OPD: { root: string; dirs: string[] | null; sub: Record<string, Sub>; err: string } = { root: "", dirs: null, sub: {}, err: "" };

export function OpSection({ c, up }: { c: Config; up: () => void }) {
  const op = c.op;
  const rootIdx = c.roots.findIndex((r, i) => (r.id || "#" + i) === op.root);
  const rr = rootIdx >= 0 ? c.roots[rootIdx] : null;
  const rp = rr ? rr.path : "";
  const [venues, setVenues] = useState<{ list: string[]; err: string; root: string } | null>(null);
  const [, setTick] = useState(0); const re = () => setTick((n) => n + 1);

  // 会場の候補（監視フォルダのすぐ下のフォルダ）
  useEffect(() => {
    if (!rp) return; let alive = true;
    api<{ venues: string[] }>("/api/venues?root=" + enc(rr?.id || "") + "&path=" + enc(rp)).then((j) => { if (alive) setVenues({ list: j.venues, err: "", root: rp }); })
      .catch((e) => { if (alive) setVenues({ list: [], err: e.message, root: rp }); });
    return () => { alive = false; };
  }, [rp]);
  // 日ごとの会場（DAY1 → その下の会場）
  useEffect(() => {
    if (!op._dm || !rp) return; let alive = true;
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
    op._dm = dm;
    if (dm && rr && rr.depth < 4) { rr.depth = rr.depth + 1; toast("日のフォルダが1段増えるため、監視フォルダの「階層」を " + rr.depth + " にしました", 6000); }
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
  return <>
    <h3>このPCの会場とコピー先</h3>
    <p className="hint" style={{ margin: "0 0 6px" }}>自分の会場だけを監視し、NASへの受信が完了した演者フォルダを、下のコピー先（この発表PC・バックアップPCなど）へコピーします。</p>
    {c.roots.length ? <div className="grid2" style={{ marginTop: 12 }}>
      <span>監視フォルダ</span><span><select id="opRoot" disabled={c.roots.length < 2} value={op.root} onChange={(e) => { op.root = e.target.value; op.venue = ""; op.days = []; OPD.dirs = null; up(); }}>
        {c.roots.map((r, i) => <option key={i} value={r.id || "#" + i}>{r.label || r.path}</option>)}</select></span>
      <span>フォルダの分け方</span><span className="checks col">
        <label><input type="radio" name="opDm" value="0" checked={!op._dm} onChange={() => setMode(false)} />学会 → 会場 → …（会場フォルダが直下にある）</label>
        <label><input type="radio" name="opDm" value="1" checked={!!op._dm} onChange={() => setMode(true)} />学会 → 日（DAY1・DAY2…） → 会場 → …（日ごとに分かれている）</label></span>
      {!op._dm ? <>
        <span>自分の会場</span><span><select id="opVenue" value={op.venue} onChange={(e) => { op.venue = e.target.value; up(); }}>
          {!vl ? <option value={op.venue}>{op.venue || "読み込み中…"}</option> : <>
            <option value="">（監視フォルダ全体）</option>
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
          <p className="hint" style={{ margin: "8px 0 0" }}><label><input type="checkbox" id="opDayDir" checked={op.day_dir !== false} onChange={(e) => { op.day_dir = e.target.checked; up(); }} />コピー先に日のフォルダ（DAY1 など）を作って分ける</label>（日が違う同じ名前のセッションが混ざらないように。おすすめ）</p></span>
        <span>いまの日</span><span><select id="opDay" value={op.day || ""} onChange={(e) => { op.day = e.target.value; up(); }}>{days.filter((d) => d.label).map((d) => <option key={d.label} value={d.label}>{d.label}</option>)}</select><span className="hint">　メイン画面の上の帯からも切り替えられます</span></span>
      </>}
      <span>速度の上限</span><span><input type="number" id="opMbps" min={0} max={1000} step={1} value={op.max_mbps || 0} onChange={(e) => { op.max_mbps = Math.max(0, +e.target.value || 0); up(); }} /> MB/秒（0 = 制限なし）</span>
    </div> : <p className="hint">先に「監視フォルダ」に学会名フォルダを追加してください（追加すると、ここで会場を選べます）。</p>}
    <p className="hint" style={{ marginTop: 14 }}>コピー先（最大4か所。メインPC・バックアップPCなど。バックアップPCは共有フォルダのパス \\PC名\共有名\… で指定）</p>
    <div id="dlist">{op.dests.map((d, i) => <div className="drow" key={i} data-i={i}>
      <input type="text" data-k="label" value={d.label} placeholder="名前（例: メイン）" onChange={(e) => { d.label = e.target.value; up(); }} />
      <input type="text" data-k="path" className="pth mono" value={d.path} placeholder="D:\発表データ  /  \\BACKUP-PC\共有\発表データ" onChange={(e) => { d.path = e.target.value; up(); }} />
      <button className="ghost" onClick={async () => { try { const j: any = await api("/api/pick", { dest: true }); if (j.path) { d.path = j.path; up(); } } catch (e: any) { toast(e.message, 5000); } }}>参照…</button>
      <label><input type="checkbox" data-k="enabled" checked={d.enabled} onChange={(e) => { d.enabled = e.target.checked; up(); }} />有効</label>
      <button className="ghost danger" onClick={() => { op.dests.splice(i, 1); up(); }}>削除</button></div>)}</div>
    {op.dests.length < 4 && <p className="hint" style={{ marginTop: 0 }}><button className="ghost" id="bDAdd" onClick={() => { op.dests.push({ label: "", path: "", enabled: true }); up(); }}><Icon n="plus" />コピー先を追加</button></p>}
    <p className="hint"><button className="ghost" id="bNetCfg" onClick={() => netOpen()}><Icon n="net" />接続を確認・共有を設定…</button>　バックアップPCにつながらないときは、ここからファイル共有をまとめて設定できます（保存してから確認してください）</p>
    <p className="hint">・コピー先には、会場より下（セッション／演者フォルダ）を同じ構成で作ります。<br />
      ・<b>NASには一切書き込みません</b>（読むだけ）。受信中の演者フォルダはコピーせず、NAS上で開かれているファイルにも触れません。<br />
      ・コピー先で<b>開かれているファイル（発表中など）は上書きしません</b>。閉じられてから新しい版に差し替えます。<br />
      ・差し替えた旧版はコピー先の「_差し替え前」フォルダに残します。<b>コピー先のファイルを消すことはありません</b>（NAS側で消えても残します）。<br />
      ・コピー先で編集したファイルは、NAS側が更新されない限り上書きしません。</p>
  </>;
}
