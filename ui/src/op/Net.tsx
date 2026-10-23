/* OPERATOR：メインPC⇄バックアップPCのネットワーク共有（接続の確認・ワンボタン設定・元に戻す） */
import { useEffect, useRef, useState } from "react";
import { api } from "../api";
import { IS_OP } from "../boot";
import { store, toast, useApp } from "../store";
import { Icon } from "../components/Icons";
import { Modal } from "../components/Modal";
import { cx } from "../lib/util";

interface Step { k?: string; label?: string; ok: boolean | null; msg?: string; hint?: string; raw?: string; need?: string }
interface Job { state: "running" | "done" | "error" | "canceled"; action: "setup" | "undo"; ok?: boolean; elevate?: boolean; msg?: string; steps: Step[] }
interface NetInfo {
  error?: string; computer?: string; ips?: string[]; supported?: boolean; job?: Job | null; creds?: string[]; links?: string[];
  record?: { unc?: string; path?: string; share?: string; updated?: string } | null;
  defaults?: { folder?: string; share?: string; user?: string; password?: string; peers?: string; nosleep?: boolean };
}
interface Form { share_this: boolean; folder: string; share: string; user: string; password: string; peers: string; nosleep: boolean; set_password: boolean; wifi: boolean; restrict: boolean; agree: boolean }
const NET: { info: NetInfo | null; chk: any; busy: boolean; job: Job | null; timer: number; form: Form | null; cred: Record<string, { user: string; password: string }> } =
  { info: null, chk: null, busy: false, job: null, timer: 0, form: null, cred: {} };

export function netBadge() {
  const I = NET.info; if (!I) return { has: false, title: "コピー先（バックアップPCなど）への接続を確認し、ファイル共有をまとめて設定します" };
  const R = I.record; const has = !!(R || (I.creds || []).length || (I.links || []).length);
  return { has, title: has ? `このPCには共有の設定（${R && R.unc ? R.unc + "・" : ""}接続情報・ショートカット）が残っています。イベントが終わったら、ここから［元に戻す］を押してください` : "コピー先（バックアップPCなど）への接続を確認し、ファイル共有をまとめて設定します" };
}
if (IS_OP) setTimeout(() => { if (!NET.info) api<NetInfo>("/api/op/net").then((j) => { if (!NET.info) { NET.info = j; store.emit(); } }).catch(() => {}); }, 4000);

async function netLoad() {
  try { NET.info = await api<NetInfo>("/api/op/net"); if (NET.info.job && !NET.job) NET.job = NET.info.job; if (NET.job && NET.job.state === "running") netPoll(); }
  catch (e: any) { NET.info = { error: e.message }; }
  store.emit();
}
async function netCheck() {
  if (NET.busy) return; NET.busy = true; store.emit();
  try { NET.chk = await api("/api/op/net/check", {}); } catch (e: any) { NET.chk = { error: e.message }; }
  NET.busy = false; store.emit();
}
function netPoll() {
  clearTimeout(NET.timer);
  NET.timer = window.setTimeout(async () => {
    try { const j: any = await api("/api/op/net/job"); NET.job = j.job; } catch { /* */ }
    if (NET.job && NET.job.state === "running") { store.emit(); netPoll(); return; }
    await netLoad(); if (NET.job && NET.job.state === "done") setTimeout(netCheck, 800);
  }, 1000);
}
export function netOpen() { store.modal = "net"; NET.form = null; NET.chk = null; store.emit(); netLoad().then(() => netCheck()); }
const netClose = () => { store.modal = null; store.emit(); };

function StepRow({ s }: { s: Step }) {
  const k = s.ok === true ? "ok" : s.ok === false ? "ng" : "na";
  return <div className={"nst " + k}><span className="ni"><Icon n={k === "ok" ? "chk" : k === "ng" ? "x" : "info"} /></span><div>
    <div>{s.label && <><b>{s.label}</b>　</>}{s.msg || ""}</div>{s.hint && <div className="nh">→ {s.hint}</div>}{s.raw && s.raw !== s.msg && <div className="nr mono">{s.raw}</div>}</div></div>;
}

export function NetDialog() {
  const s = useApp(); if (s.modal !== "net") return null;
  return <Modal onClose={netClose} wide id="netov"><NetBody /></Modal>;
}
function NetBody() {
  useApp();
  const I = NET.info || {}; const D = I.defaults || {}; const R = I.record; const job = NET.job; const running = !!(job && job.state === "running");
  const [f, setF] = useState<Form | null>(NET.form);
  const [undoArm, setUndoArm] = useState(0);
  const armT = useRef(0);
  useEffect(() => {   // 既定値は情報を読み込んでから入れる
    if (!f && NET.info && NET.info.defaults) {
      const d: any = D;
      const n: Form = { share_this: d.share_this !== false, folder: d.folder || "", share: d.share || "", user: d.user || "", password: d.password || "", peers: d.peers || "", nosleep: d.nosleep !== false, set_password: !!d.set_password, wifi: !!d.wifi, restrict: !!d.restrict, agree: false };
      NET.form = n; setF(n);
    }
  });
  useEffect(() => { const k = (e: KeyboardEvent) => { if (e.key === "Escape") { e.stopImmediatePropagation(); netClose(); } }; document.addEventListener("keydown", k, true); return () => document.removeEventListener("keydown", k, true); }, []);
  const F = f || { share_this: true, folder: "", share: D.share || "", user: "", password: "", peers: "", nosleep: true, set_password: false, wifi: false, restrict: false, agree: false };
  const set = (p: Partial<Form>) => { const n = { ...F, ...p }; NET.form = n; setF(n); };
  const hasUndo = !!(R || (I.creds || []).length || (I.links || []).length);
  const shareOn = F.share_this !== false; const ip0 = (I.ips || [])[0];
  const C = NET.chk;
  const run = async () => {
    try {
      const j: any = await api("/api/op/net/setup", { share_this: F.share_this, folder: F.folder, share: F.share, user: F.user, password: F.password, peers: F.peers, nosleep: F.nosleep, set_password: F.set_password, wifi: F.wifi, restrict: F.restrict });
      NET.job = j.job; set({ agree: false }); store.emit(); netPoll();
    } catch (e: any) { toast(e.message, 7000); }
  };
  const undo = async () => {
    if (undoArm < Date.now()) { setUndoArm(Date.now() + 5000); clearTimeout(armT.current); armT.current = window.setTimeout(() => setUndoArm(0), 5100); return; }
    setUndoArm(0);
    try { const j: any = await api("/api/op/net/undo", {}); NET.job = j.job; store.emit(); netPoll(); } catch (e: any) { toast(e.message, 7000); }
  };
  return <div className="dlg netdlg">
    <div className="dlg-h"><div style={{ flex: 1 }}><h2>ネットワーク共有（メインPC・バックアップPC・タイトルPC など）</h2>
      <p className="desc">コピー先（バックアップPCなど）につながるかを調べます。つながらないときは、ファイル共有に必要な設定をまとめて行えます。</p></div>
      <button className="ghost" id="nsClose" onClick={netClose}><Icon n="x" />閉じる</button></div>
    {I.error && <p className="err">{I.error}</p>}
    <div className="nsme">
      <div><span className="k">このPCの名前</span><b className="mono">{I.computer || "…"}</b></div>
      <div><span className="k">IPアドレス</span><span className="mono">{(I.ips || []).join("　") || "—"}</span></div>
      {R && R.unc ? <div><span className="k">このPCの共有</span><b className="mono">{R.unc}</b>（{R.path}）<br /><span className="k" /><span className="dim">ほかのPCのコピー先にはこのパス（の中のフォルダ）を指定します{ip0 && <>。名前で見つからないときは <span className="mono">\\{ip0}\{R.share}</span></>}</span></div>
        : <div><span className="k">このPCの共有</span><span className="dim">まだ設定していません</span></div>}
    </div>
    <h3>① コピー先への接続<button className="ghost sm" id="nsRe" disabled={NET.busy} onClick={netCheck}>{NET.busy ? "確認中…" : "もう一度確認"}</button></h3>
    {!C ? <p className="hint">{NET.busy ? "確認しています…（つながらない場合は1分ほどかかることがあります）" : "—"}</p>
      : C.error ? <p className="err">{C.error}</p>
        : !C.dests.length ? <p className="hint" style={{ marginTop: 0 }}>コピー先がまだ設定されていません（［設定］→「このPCの会場とコピー先」）。<br />このPCが<b>バックアップPC（コピーされる側）</b>なら、下の ② で［このPCを設定する］を押すだけでOKです。</p>
          : C.dests.map((d: any, di: number) => {
            const bad = d.steps.find((x: Step) => x.ok === false); const need = bad && bad.need === "cred" && d.host; const skip = !bad && d.steps.some((x: Step) => x.k === "nas");
            const cr = NET.cred[d.host] || { user: D.user || "share", password: D.password || "share" };
            return <div key={di} className={cx("nsd", bad ? "bad" : skip ? "" : "good")}>
              <div className="nsdh"><b>{d.label}</b><span className="mono">{d.path}</span><span className="tag">{bad ? "つながりません" : skip ? "確認しません" : "OK"}</span></div>
              {d.steps.map((x: Step, i: number) => <StepRow key={i} s={x} />)}
              {need && <CredBox host={d.host} init={cr} supported={!!I.supported} />}
            </div>;
          })}
    <h3>② ファイル共有の設定（ワンボタン）</h3>
    {!I.supported && <p className="err" style={{ marginTop: 0 }}>この機能は Windows だけで使えます。</p>}
    <div id="nsForm" className={shareOn ? "" : "noshare"}>
      <div className="checks col" style={{ margin: "0 0 4px" }}>
        <label><input type="radio" name="nsMode" value="1" checked={shareOn} onChange={() => set({ share_this: true })} /><span><b>このPCのフォルダを共有する</b>（メインPC・バックアップPCなど、コピーされるPC。それぞれで1回）</span></label>
        <label><input type="radio" name="nsMode" value="0" checked={!shareOn} onChange={() => set({ share_this: false })} /><span><b>このPCは共有しない</b>（タイトルPCなど、ほかのPCを開くだけ。管理者の確認は出ません）</span></label>
      </div>
      <div className="grid2" style={{ marginTop: 12 }}>
        {shareOn && <><span>共有するフォルダ</span><span className="nsrow"><input type="text" id="nsFolder" className="mono" value={F.folder} data-ready={I.defaults ? 1 : 0} spellCheck={false} onChange={(e) => set({ folder: e.target.value })} />
          <button className="ghost" id="nsPick" onClick={async () => { try { const j: any = await api("/api/pick", { dest: true }); if (j.path) set({ folder: j.path }); } catch (e: any) { toast(e.message, 5000); } }}>参照…</button></span></>}
        <span>{shareOn ? "共有名" : "相手の共有名"}</span><span className="nsrow"><input type="text" id="nsShare" value={F.share} style={{ maxWidth: 220 }} spellCheck={false} onChange={(e) => set({ share: e.target.value })} />
          {shareOn && <span className="dim">→ ほかのPCからは <b className="mono" id="nsUnc">{"\\\\" + (I.computer || "このPC") + "\\" + (F.share.trim() || "共有名")}</b>（共有名はどのPCでも同じにします）</span>}</span>
        <span>共有用アカウント</span><span className="nsrow"><input type="text" id="nsUser" value={F.user} style={{ maxWidth: 150 }} spellCheck={false} onChange={(e) => set({ user: e.target.value })} /><span>パスワード</span>
          <input type="text" id="nsPass" value={F.password} style={{ maxWidth: 150 }} spellCheck={false} onChange={(e) => set({ password: e.target.value })} /><span className="dim">どのPCでも同じにする</span></span>
        <span>開く相手のPC</span><span className="nsrow"><input type="text" id="nsPeers" className="mono" value={F.peers} placeholder="例: MAIN-PC, BACKUP-PC（名前かIPアドレス。複数はカンマ区切り）" spellCheck={false} onChange={(e) => set({ peers: e.target.value })} /></span>
        <span /><span className="hint" style={{ margin: 0 }}>入れたPCの接続情報をこのPCに登録し、<b>デスクトップにショートカット</b>「（PC名） の{F.share || "共有名"}」を作ります。コピーしているPCが落ちたときなどに、手で開いてコピーできます。{shareOn && "空欄でも共有の設定はできます。"}</span>
      </div>
      {shareOn && <div className="checks col" style={{ marginTop: 12 }}>
        <label><input type="checkbox" id="nsSleep" checked={F.nosleep} onChange={(e) => set({ nosleep: e.target.checked })} />電源につないでいる間は、このPCをスリープさせない（スリープ中は相手のPCから使えないため）</label>
        <label><input type="checkbox" id="nsSetPw" checked={F.set_password} onChange={(e) => set({ set_password: e.target.checked })} />同じ名前のアカウントがすでにあるときは、パスワードを上の内容に変える（管理者・ログイン中のアカウントは使えません）</label>
        <label><input type="checkbox" id="nsRestrict" checked={F.restrict} onChange={(e) => set({ restrict: e.target.checked })} />このPCに入れるのを、上の「開く相手のPC」からだけに限る（IPアドレスが変わるとつながらなくなります。タイトルPCなど、このPCを開くPCも全部入れてください）</label>
        <label><input type="checkbox" id="nsWifi" checked={F.wifi} onChange={(e) => set({ wifi: e.target.checked })} />Wi-Fi でも共有する（おすすめしません。ふつうは有線LANだけ。会場のWi-Fiにつないでいる人からも見えてしまうため）</label>
      </div>}
      {shareOn && <p className="hint" style={{ margin: "8px 0 0" }}>パスワードの既定（share）は、閉じた現場LAN向けです。ほかの人もつなぐネットワークでは、すべてのPCで別のパスワードにしてください。</p>}
      <details className="nschg" open><summary>このPCで変更する内容</summary>
        {shareOn ? <ul>
          <li>Windowsファイアウォールに、<b>有線LANの、同じネットワーク内のPCからだけ</b>（「相手のPCからだけ」にチェックしたときは、そのPCからだけ）、ファイル共有（SMB）・PC名の検索・ping を許可する規則を追加する（グループ名「SW NAS OPERATOR」。ネットワークの種類「パブリック／プライベート」は変えません）</li>
          <li>ファイル共有のサービス（Server・Workstation など）を自動で起動するようにする</li>
          <li>共有用アカウントを作る（管理者ではない普通のアカウント。30日で使えなくなります（もう一度押すと延びる）。すでにあればそのまま使う。ログイン画面にも表示されます）</li>
          <li>上のフォルダを作って共有し、そのアカウントに読み書き（変更）の権限を付ける</li>
          <li>スリープさせない（チェックしたとき。電源接続時だけ）</li>
          <li>開く相手のPCの接続情報を、このPCのWindowsの資格情報に登録し、デスクトップにショートカットを作る（上の設定がすべてうまくいったとき。NASのサーバーには登録しません）</li>
        </ul> : <ul>
          <li>開く相手のPCの接続情報を、このPCのWindowsの資格情報に登録する（NASのサーバーには登録しません）</li>
          <li>デスクトップに、相手のPCの共有フォルダへのショートカットを作る</li>
          <li>このPCの共有・ファイアウォール・アカウントなどは変えません</li>
        </ul>}
        <p className="hint" style={{ margin: "6px 0 0" }}>［元に戻す］で戻せます（作ったショートカット・登録した接続情報も消します。フォルダとデータは消しません。レンタルPCは返す前に押してください）。{shareOn && "変更前の状態は変更のたびに記録します。SMB1・パスワードなしの共有（ゲスト）は使いません。経過は、管理者の確認のあとに開くウィンドウにも表示されます。"}</p></details>
      <label className="lbl nsagree"><input type="checkbox" id="nsAgree" checked={F.agree} onChange={(e) => set({ agree: e.target.checked })} />上の内容で、このPCの設定を変更する</label>
      <div className="nsbtns">
        <button className="pri" id="nsRun" disabled={!I.supported || running || !F.agree} onClick={run}>{running && job!.action === "setup" ? "実行中…" : shareOn ? "このPCを設定する（管理者の確認が出ます）" : "接続情報とショートカットを作る"}</button>
        {hasUndo && <button className="ghost danger" id="nsUndo" disabled={!I.supported || running} onClick={undo}>{running && job!.action === "undo" ? "元に戻しています…" : undoArm > Date.now() ? "もう一度押すと元に戻します" : "元に戻す"}</button>}
        {R && R.updated && <span className="dim">前回の設定: {String(R.updated).replace("T", " ")}</span>}
      </div>
    </div>
    {job && <div className="nsjob">{job.msg && <p className={job.state === "error" || job.state === "canceled" ? "err" : "hint"} style={{ marginTop: 0 }}>{job.msg}</p>}
      {(job.steps || []).map((x, i) => <StepRow key={i} s={x} />)}
      {job.state === "done" && <p className="hint">{job.ok ? "✓ 終わりました。" : "一部うまくいきませんでした（✕の項目を確認してください）。"}{job.action === "setup" && job.elevate ? "ほかのPCでも同じように押してから、① の［もう一度確認］でつながるか確かめてください。" : ""}</p>}</div>}
  </div>;
}
function CredBox({ host, init, supported }: { host: string; init: { user: string; password: string }; supported: boolean }) {
  const [c, setC] = useState(init); const [busy, setBusy] = useState(false);
  const upd = (p: Partial<typeof c>) => { const n = { ...c, ...p }; NET.cred[host] = n; setC(n); };
  return <div className="nscred" data-credhost={host}><span>「{host}」のアカウント</span>
    <input type="text" className="cu" value={c.user} placeholder="ユーザー名" spellCheck={false} onChange={(e) => upd({ user: e.target.value })} />
    <input type="text" className="cp2" value={c.password} placeholder="パスワード" spellCheck={false} onChange={(e) => upd({ password: e.target.value })} />
    <button className="pri" data-cred={host} disabled={!supported || busy} onClick={async () => {
      setBusy(true);
      try {
        const j: any = await api("/api/op/net/cred", { host, user: c.user, password: c.password });
        toast((j.targets.length ? "接続情報を登録しました: " + j.targets.join("・") : "") + (j.errors.length ? "　登録できませんでした: " + j.errors.join("・") : "") + (j.skipped && j.skipped.length ? "　" + j.skipped.join("・") + " はほかで登録した接続情報があるため変えていません（Windowsの資格情報マネージャーで確認してください）" : ""), 9000);
      } catch (e: any) { toast(e.message, 6000); }
      setBusy(false); NET.busy = false; netCheck();
    }}>このPCに登録して確認</button></div>;
}
