/* 設定（監視フォルダ・検出・解析・目印・通知・無視するファイル ＋ OPERATOR／RECEPTION の設定） */
import { useState } from "react";
import { api } from "../api";
import { APP_TITLE, BASE_VERSION, IS_OP, IS_RX } from "../boot";
import type { Config, Mark } from "../types";
import { refresh, store, toast, useApp } from "../store";
import { Icon } from "./Icons";
import { Modal } from "./Modal";
import { OpSection, opPrepare, opReady, OpSetupGuide } from "../op/OpSettings";
import { OpenSettings, openSettingsSave } from "../op/Opener";
import { RxSettings, rxSettingsSave } from "../rx/RxSettings";

export interface Defaults { ignore: string[]; coi: string[]; marks: Mark[] }
export let CFG: Config | null = null;
let DEF: Defaults | null = null;
let DATA = "";

export async function openCfg() {
  if (!store.S?.local) { toast("設定は監視PCでのみ変更できます"); return; }
  try {
    const j: any = await api("/api/config");
    CFG = JSON.parse(JSON.stringify(j.config)); DEF = j.defaults; DATA = j.data_dir || "";
    if (IS_OP) opPrepare(CFG!);
    store.modal = "cfg"; store.emit();
  } catch (e: any) { toast(e.message, 5000); }
}
export function closeModal() { store.modal = null; store.emit(); }

const MKROLES: [string, string][] = [["recv", "受付済にする"], ["got", "会場取得済にする"], ["done", "発表終了にする"], ["drop", "取り下げ（数に入れない）"], ["direct", "会場直（未受付にしない）"], ["warn", "注意（黄色のチップ）"], ["info", "チップで表示するだけ"]];
const NK: [string, string][] = [["incoming", "受信開始（コピー中にすぐ知らせる）"], ["folder_new", "新しい演者フォルダ"], ["add", "ファイル追加"], ["mod", "ファイル更新（差し替え）"], ["rename", "ファイル名変更"], ["del", "ファイル削除"], ["folder_rename", "フォルダ名変更"], ["folder_del", "フォルダ削除"], ["offline", "NAS接続断"], ["online", "NAS復帰"]];

function DepthSel({ v, on }: { v: number; on: (n: number) => void }) {
  return <select value={v} onChange={(e) => on(+e.target.value)} title="演者フォルダの階層" data-k="depth">{[1, 2, 3, 4, 5, 6].map((n) => <option key={n} value={n}>階層 {n}</option>)}</select>;
}

export function SettingsDialog() {
  const s = useApp();
  if (s.modal !== "cfg" || !CFG) return null;
  return <Modal onClose={closeModal} wide><SettingsBody /></Modal>;
}

function SettingsBody() {
  const [, setN] = useState(0);
  const c = CFG!; const up = () => setN((n) => n + 1);
  const [np, setNp] = useState({ p: "", l: "", d: 3 });
  const [ig, setIg] = useState(c.ignore.join("\n"));
  const [coi, setCoi] = useState((c.coi_keywords || []).join("\n"));
  const [err, setErr] = useState("");
  const [busy, setBusy] = useState(false);

  const save = async () => {
    if (np.p.trim()) { toast("入力中のパスは［追加］を押してから保存してください", 4500); return; }
    c.ignore = ig.split("\n").map((x) => x.trim()).filter(Boolean);
    c.coi_keywords = coi.split("\n").map((x) => x.trim()).filter(Boolean);
    c.marks = (c.marks || []).map((m) => ({ w: m.w.trim(), role: m.role })).filter((m) => m.w);
    delete (c as any).mark_recv; delete (c as any).mark_got;
    // コピーするのは PADDOCK GATE だけ。コピー先が1つ以上あれば有効
    c.op.enabled = IS_OP && c.op.dests.some((d) => d.enabled && String(d.path || "").trim());
    if (IS_OP && c.op._dm) {   // 日ごとに分かれているとき：会場を選んでいない日があると保存しない（全体をコピーしてしまわないように）
      const days = (c.op.days || []).filter((d) => d.label || d.venue);
      const bad = days.filter((d) => !d.venue.split("/")[1]);
      if (!days.length) { setErr("日ごとの会場を1つ以上選んでください"); return; }
      if (bad.length) { setErr("会場を選んでいない日があります: " + bad.map((d) => d.label || "（日のフォルダ未選択）").join("、")); return; }
      if (!c.op.day || !days.some((d) => d.label === c.op.day)) c.op.day = days[0].label;
    }
    setBusy(true); setErr("");
    try {
      if (IS_OP) await openSettingsSave();
      if (IS_RX) await rxSettingsSave();
      const body: any = JSON.parse(JSON.stringify(c));
      if (IS_OP) {
        if (body.op._dm) body.op.days = (body.op.days || []).filter((d: any) => d.label && d.venue.split("/")[1]).map((d: any) => ({ label: d.label, venue: d.venue }));
        else body.op.days = [];
        delete body.op._dm;
      }
      if (body.op && String(body.op.root || "").startsWith("#")) body.op.root = "";   // 保存前の監視フォルダ（1つだけなら自動でそれを使う）
      const j: any = await api("/api/config", body);
      closeModal();
      if (j.warnings && j.warnings.length) toast(j.warnings.join(" / "), 7000); else toast("保存しました");
      setTimeout(refresh, 300);
    } catch (e: any) { setErr(e.message); }
    setBusy(false);
  };

  return <div className="dlg settings">
    <div className="dlg-h"><div><h2>設定</h2><p className="desc">{IS_OP ? "見るNASのフォルダ、この発表PCの会場とコピー先、解析の動作を設定します。" : IS_RX ? "受付先のNASフォルダ、受付の動作、解析・目印を設定します。" : "監視するNASのフォルダ、検出のタイミング、通知と解析の動作を設定します。"}</p></div>
      <button className="ghost" onClick={closeModal}><Icon n="x" />閉じる</button></div>
    {IS_OP && !opReady() && <OpSetupGuide />}

    <h3>監視フォルダ</h3>
    <div id="rlist">{c.roots.length ? c.roots.map((r, i) => <div className="rrow" key={i} data-i={i}>
      <input type="text" data-k="label" value={r.label} placeholder="表示名（例: 学会名）" onChange={(e) => { r.label = e.target.value; up(); }} />
      <input type="text" data-k="path" className="pth mono" value={r.path} onChange={(e) => { r.path = e.target.value; up(); }} />
      <DepthSel v={r.depth} on={(n) => { r.depth = n; up(); }} />
      <label><input type="checkbox" data-k="enabled" checked={r.enabled} onChange={(e) => { r.enabled = e.target.checked; up(); }} />有効</label>
      <button className="ghost" title="今の状態を基準にし、未確定の変化を捨てる（通知しない）" onClick={() => {
        if (!r.id) { toast("保存後に使えます"); return; }
        api("/api/rebaseline", { root: r.id }).then(() => toast("次の確認で今の状態を基準にします")).catch((e) => toast(e.message));
      }}>基準リセット</button>
      <button className="ghost danger" onClick={() => { if (confirm(`「${r.label || r.path}」を監視対象から外しますか？（NAS上のファイルには何もしません）`)) { c.roots.splice(i, 1); up(); } }}>削除</button>
    </div>) : <div className="hint" style={{ margin: "0 0 8px" }}>まだありません</div>}</div>
    <div className="addrow"><input type="text" id="nPath" className="mono" value={np.p} onChange={(e) => setNp({ ...np, p: e.target.value })} placeholder="\\NASのIP\共有名\学会名  /  Z:\学会名  /  /Volumes/共有名/学会名" />
      <button id="bPick" onClick={async () => { try { const j: any = await api("/api/pick", {}); if (j.path) setNp({ ...np, p: j.path }); } catch (e: any) { toast(e.message, 5000); } }}>参照…</button></div>
    <div className="addrow2"><input type="text" id="nLabel" value={np.l} onChange={(e) => setNp({ ...np, l: e.target.value })} placeholder="表示名（任意）" /><DepthSel v={np.d} on={(n) => setNp({ ...np, d: n })} />
      <button className="pri" id="bAdd" onClick={() => {
        const p = np.p.trim().replace(/^"|"$/g, ""); if (!p) { toast("パスを入力してください"); return; }
        c.roots.push({ path: p, label: np.l.trim(), depth: np.d, enabled: true }); setNp({ p: "", l: "", d: 3 }); up();
      }}><Icon n="plus" />追加</button></div>
    <p className="hint">「階層」= 監視フォルダから見て演者フォルダが何段目にあるか。<br />
      <b>階層3</b>: 学会名フォルダ／会場／セッション／<b>001_演者名</b>／…（学会名フォルダを登録）<br />
      階層2: 会場フォルダ／セッション／<b>演者</b>　　階層1: セッションフォルダ／<b>演者</b><br />
      NAS側で「読み取り専用のユーザー」を作り、そのユーザーで接続しておくと、誤操作でも書き込めないので確実です。</p>

    {IS_OP && <OpSection c={c} up={up} />}
    {IS_OP && <OpenSettings c={c} />}

    <h3>検出</h3>
    <div className="grid2">
      <span>確認する間隔</span><span><input type="number" id="poll" min={1} max={60} step={1} value={c.poll_sec} onChange={(e) => { c.poll_sec = +e.target.value; up(); }} /> 秒</span>
      <span>確定待ち時間</span><span><input type="number" id="settle" min={0} max={300} step={1} value={c.settle_sec} onChange={(e) => { c.settle_sec = +e.target.value; up(); }} /> 秒</span>
      <span /><span className="hint" style={{ margin: 0 }}>コピーが始まった時点で「受信中」をすぐ通知し、サイズ・更新日時がこの秒数変わらなくなったら「追加・更新」に差し替えます（解析結果つき）</span>
    </div>
    <p style={{ margin: "10px 0 0" }}><label className="lbl"><input type="checkbox" id="rws" checked={c.report_while_stopped} onChange={(e) => { c.report_while_stopped = e.target.checked; up(); }} />アプリを止めていた間の変更も、起動時に通知する</label></p>

    <h3>PowerPoint 解析</h3>
    <p style={{ margin: 0 }}><label className="lbl"><input type="checkbox" id="ana" checked={c.analyze} onChange={(e) => { c.analyze = e.target.checked; up(); }} />動画・ハイパーリンク・COI・自動送り・クリック無効を解析する</label></p>
    <p className="hint">解析のため .pptx / .ppsx などの中身を「読み取り」ます（書き込みはしません）。Keynote・旧形式(.ppt)は対象外です。</p>
    <p className="hint" style={{ marginTop: 10 }}>COIとみなす文字（1行1つ・大文字小文字/全角半角は区別しない。「Conflicts of Interest」の複数形・改行・ハイフンも同じとみなします）</p>
    <textarea id="coi" spellCheck={false} value={coi} onChange={(e) => setCoi(e.target.value)} />
    <p className="hint"><button className="ghost" onClick={() => setCoi((DEF?.coi || []).join("\n"))}>初期値に戻す</button></p>

    <h3>目印のファイル（00_受付済.jpg・17_会場取得.jpg など）</h3>
    <p className="hint" style={{ margin: "0 0 8px" }}>演者フォルダの画像（またはテキスト）ファイルの名前がこの文字で始まっていれば、データではなく<b>目印</b>として扱います。全角半角・大文字小文字・空白や「_」・括弧（【】など）・送り仮名の違い（持ち込み／持込 など）は区別せず、先頭の番号（00_ など）があってもかまいません。2つ以上に当てはまるときは長い文字のほうを使います。</p>
    <table className="mkt" id="mkt"><tbody>{(c.marks || []).map((m, i) => <tr key={i}>
      <td><input type="text" className="mkw" value={m.w} maxLength={40} spellCheck={false} placeholder="ファイル名に入る文字（例: 動画有）" onChange={(e) => { m.w = e.target.value; up(); }} /></td>
      <td style={{ width: 240 }}><select className="mkr" value={m.role} onChange={(e) => { m.role = e.target.value; up(); }}>{MKROLES.map(([k, l]) => <option key={k} value={k}>{l}</option>)}</select></td>
      <td><button className="ghost x icon" title="この行を削除" onClick={() => { c.marks.splice(i, 1); up(); }}><Icon n="x" /></button></td></tr>)}</tbody></table>
    <p className="hint"><button className="ghost" onClick={() => { c.marks.push({ w: "", role: "info" }); up(); }}><Icon n="plus" />行を追加</button> <button className="ghost" onClick={() => { c.marks = JSON.parse(JSON.stringify(DEF?.marks || [])); up(); }}>初期値に戻す</button></p>

    {IS_OP ? <><h3>通知</h3><p className="hint" style={{ margin: 0 }}>このアプリはスライドショーをしている発表PCで使うため、<b>通知も音も出しません</b>（画面の表示だけ更新します）。</p></> : <>
      <h3>通知する変化</h3>
      <div className="checks">{NK.map(([k, l]) => <label key={k}><input type="checkbox" checked={c.notify[k] !== false} onChange={(e) => { c.notify[k] = e.target.checked; up(); }} />{l}</label>)}</div>
      <h3>通知の動作</h3>
      <div className="checks col">
        <label><input type="checkbox" id="snd" checked={c.ui.sound} onChange={(e) => { c.ui.sound = e.target.checked; up(); }} />通知音を鳴らす（アプリ独自の音。OSの通知音は鳴らさない）</label>
        <label><input type="checkbox" id="stk" checked={c.ui.sticky} onChange={(e) => { c.ui.sticky = e.target.checked; up(); }} />通知を自動で消さない（クリックするまで残す）</label>
        <label><input type="checkbox" id="osOpen" checked={c.ui.os_open} onChange={(e) => { c.ui.os_open = e.target.checked; if (!c.ui.os_open) c.ui.click = "app"; up(); }} />「Explorer / Finder で開く」を使えるようにする（通常はオフ推奨）</label>
        <label style={{ paddingLeft: 23 }}><input type="radio" name="clk" checked={c.ui.click !== "both"} onChange={() => { c.ui.click = "app"; up(); }} />通知クリック → アプリ内でフォルダの中身を表示（NASに一切触れない）</label>
        <label style={{ paddingLeft: 23 }}><input type="radio" name="clk" checked={c.ui.click === "both"} disabled={!c.ui.os_open} onChange={() => { c.ui.click = "both"; up(); }} />通知クリック → アプリ内表示 ＋ Explorer / Finder でも開く</label>
      </div>
      <p className="hint">※ Explorer / Finder はこのアプリの管理外です。表示設定によってはサムネイル作成のためにファイルを読みに行ったり、Thumbs.db（Windows）や .DS_Store（Mac）をNASに作ったりすることがあります。会場側への影響を完全になくすため、通常はオフのままにしてください。<br />※ 会場の絞り込みと「自動表示」は画面上部・左上で切り替えます（このPCだけの設定）。</p>
    </>}

    {IS_RX && <RxSettings />}

    <h3>無視するファイル名（1行1パターン、* と ? が使えます）</h3>
    <textarea id="ig" spellCheck={false} value={ig} onChange={(e) => setIg(e.target.value)} />
    <p className="hint"><button className="ghost" onClick={() => setIg((DEF?.ignore || []).join("\n"))}>初期値に戻す</button>　設定の保存先: <span className="mono">{DATA}</span></p>
    <div className="err" id="cerr">{err}</div>
    <div className="foot"><span className="hint" style={{ margin: 0 }}>{APP_TITLE} v{store.appVersion}{IS_OP || IS_RX ? `（PADDOCK SCOUT v${BASE_VERSION} ベース）` : ""} · © SEVENTHWELL</span>
      <span style={{ display: "flex", gap: 8 }}><button id="bCancel" onClick={closeModal}>キャンセル</button><button className="pri" id="bSave" disabled={busy} onClick={save}>保存</button></span></div>
  </div>;
}
