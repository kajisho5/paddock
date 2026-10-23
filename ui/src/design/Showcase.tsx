/* デザインシステムの見本ページ（開発用。アプリには含めない）：npm run design → dist-design/design.html */
import { useState } from "react";
import { createRoot } from "react-dom/client";
import "./tailwind.css";
import "./tokens.css";
import "../styles.css";
import "./motion.css";
import { Icon } from "../components/Icons";
import { Bar, Chip, EmptyState, Segmented, StatusDot } from "./ui";

const COLORS: [string, string][] = [["bg", "背景"], ["card", "カード"], ["card2", "カード2"], ["border", "線"], ["fg", "文字"], ["muted", "補助の文字"], ["accent", "主ボタン"],
  ["ok", "受付済・正常"], ["got", "会場取得"], ["warn", "注意・コピー中"], ["bad", "未着・エラー"], ["vio", "会場直"], ["info", "情報"]];
const MOTION: [string, string, string][] = [["--dur-1", "120ms", "押した反応・ホバー"], ["--dur-2", "200ms", "トースト・ポップオーバー・タブ"], ["--dur-3", "320ms", "ダイアログ・ドロワー・進捗"], ["--dur-4", "2400ms", "更新した行の光"]];

function Sec({ t, d, children }: { t: string; d?: string; children: React.ReactNode }) {
  return <section className="mb-10"><h2 className="text-[15px] font-bold m-0 mb-1 text-fg">{t}</h2>{d && <p className="text-[12.5px] text-muted m-0 mb-4">{d}</p>}{children}</section>;
}

function Page() {
  const [theme, setTheme] = useState<"light" | "dark">("light");
  const [seg, setSeg] = useState<"list" | "board">("list");
  const [tab, setTab] = useState<"base" | "open" | "adv">("base");
  const [pct, setPct] = useState(38);
  const [replay, setReplay] = useState(0);
  const [toast, setToast] = useState(false);
  const [dlg, setDlg] = useState(false);
  const [flash, setFlash] = useState(0);
  document.documentElement.dataset.theme = theme;
  return <div className="min-h-full bg-bg text-fg font-sans px-10 py-8" style={{ minHeight: "100vh" }}>
    <header className="flex items-center gap-4 mb-8">
      <div><h1 className="m-0 text-[22px] font-bold">PADDOCK デザインシステム</h1>
        <p className="m-0 text-muted text-[13px]">SCOUT（監視）・SADDLE（受付）・GATE（会場PC）共通。トークン → Tailwind → 部品 → 動き</p></div>
      <div className="ml-auto"><Segmented label="テーマ" value={theme} onChange={setTheme} items={[{ v: "light", label: "ライト（SCOUT・SADDLE）" }, { v: "dark", label: "ダーク（GATE）" }]} /></div>
    </header>

    <Sec t="色（意味で使う）" d="値を直接書かず、変数名（Tailwind では bg-ok / text-warn-fg など）で使う。色だけで状態を伝えず、文字やアイコンも添える。">
      <div className="grid gap-3" style={{ gridTemplateColumns: "repeat(auto-fill,minmax(150px,1fr))" }}>
        {COLORS.map(([k, l]) => <div key={k} className="rounded-card border border-line bg-card overflow-hidden shadow-elev-1">
          <div style={{ height: 54, background: `var(--${k})` }} />
          <div className="px-3 py-2"><b className="text-[13px]">{l}</b><div className="font-mono text-[11px] text-muted">--{k}</div></div></div>)}
      </div>
    </Sec>

    <Sec t="文字" d="本文 14px・補助 12.5px・最小 11px。細いウェイトは使わない。">
      <div className="rounded-pane border border-line bg-card p-6 shadow-elev-1 grid gap-2">
        <div className="text-[30px] font-bold leading-tight">001 架空演者A</div>
        <div className="text-[19px] font-bold">ダイアログの見出し</div>
        <div className="text-[14px]">本文：NASに演者のデータが入り終わったら、このPCへ自動でコピーします。</div>
        <div className="text-[12.5px] text-muted">補助：NASには書き込みません（読むだけ）。</div>
        <div className="font-mono text-[12px] text-muted">\\NAS\共有\架空学会2030\第1会場</div>
      </div>
    </Sec>

    <Sec t="部品">
      <div className="rounded-pane border border-line bg-card p-6 shadow-elev-1 grid gap-6">
        <div className="flex flex-wrap items-center gap-2"><button className="pri"><Icon n="ok" />保存</button><button>キャンセル</button><button className="ghost"><Icon n="cog" />設定</button><button className="ghost danger">削除</button><button disabled>使えない</button><button className="sm">小さいボタン</button></div>
        <div className="flex flex-wrap items-center gap-2"><Chip tone="ok">受付済み</Chip><Chip tone="got">会場取得</Chip><Chip tone="warn">コピー中</Chip><Chip tone="bad">未着</Chip><Chip tone="vio">会場直</Chip><Chip tone="info">COI</Chip><Chip>他 3</Chip></div>
        <div className="flex flex-wrap items-center gap-6 text-[13px]"><span className="flex items-center gap-2"><StatusDot state="on" />監視中</span><span className="flex items-center gap-2"><StatusDot state="busy" />コピー中</span><span className="flex items-center gap-2"><StatusDot state="off" />つながらない</span><span className="flex items-center gap-2"><StatusDot />停止</span></div>
        <div className="flex flex-wrap items-center gap-4"><Segmented label="表示" value={seg} onChange={setSeg} items={[{ v: "list", label: <><Icon n="list" />リスト</> }, { v: "board", label: <><Icon n="cols" />会場ボード</> }]} />
          <Segmented label="設定" value={tab} onChange={setTab} items={[{ v: "base", label: "① 会場とコピー先" }, { v: "open", label: "スライドを開く" }, { v: "adv", label: "詳細" }]} /></div>
        <div className="flex items-center gap-3 text-[12px] font-mono text-muted"><span className="prog"><Bar pct={pct} />{pct}%</span>
          <button className="sm" onClick={() => setPct((p) => (p >= 100 ? 0 : Math.min(100, p + 22)))}>進める</button>
          <span className="rx" style={{ width: 200 }}><span className="rbar ind"><i /></span>読み込み中</span></div>
        <div className="grid gap-2" style={{ gridTemplateColumns: "repeat(3,1fr)" }}>
          <div className="bp st-recv"><b className="nm">001 架空演者A</b><Chip tone="ok">受付済み</Chip></div>
          <div className="bp st-copying"><b className="nm">002 架空演者B</b><Chip tone="warn">コピー中</Chip></div>
          <div className="bp st-none"><b className="nm">003 架空演者C</b><Chip tone="bad">未着</Chip></div>
        </div>
        <div className="rounded-card border border-line"><EmptyState title="演者フォルダを選択">左の一覧をクリックすると、ここに中身が表示されます。</EmptyState></div>
      </div>
    </Sec>

    <Sec t="動き" d="動かすのは位置と透明度だけ。速さは4段階、カーブは「入る＝ease-out」「出る＝ease-in」「移動＝ease-inout」「弾む＝ease-spring」。OSの「動きを減らす」で止まる。">
      <div className="grid gap-3 mb-4" style={{ gridTemplateColumns: "repeat(4,1fr)" }}>{MOTION.map(([k, v, d]) => <div key={k} className="rounded-card border border-line bg-card p-3"><div className="font-mono text-[12px] text-muted">{k}</div><b>{v}</b><div className="text-[12px] text-muted">{d}</div></div>)}</div>
      <div className="flex flex-wrap gap-2 mb-4"><button onClick={() => setReplay((n) => n + 1)}>出てくる動きを再生</button><button onClick={() => { setToast(false); setTimeout(() => setToast(true), 10); setTimeout(() => setToast(false), 2600); }}>トースト</button><button onClick={() => setDlg(true)}>ダイアログ</button><button onClick={() => setFlash((n) => n + 1)}>更新した行が光る</button></div>
      <div key={replay} className="grid gap-3" style={{ gridTemplateColumns: "repeat(4,1fr)" }}>
        {[["animate-fade-in", "fade-in"], ["animate-fade-up", "fade-up"], ["animate-pop", "pop"], ["animate-slide-left", "slide-left"]].map(([c, l]) => <div key={c} className={"rounded-card border border-line bg-card2 p-5 text-center " + c}><b>{l}</b><div className="font-mono text-[11px] text-muted">.{c}</div></div>)}
      </div>
      <div className="mt-3 grid gap-0 rounded-card border border-line overflow-hidden bg-card">
        <div key={"f" + flash} className={"grp " + (flash ? "flash" : "")}><span className="nm"><b>011 架空演者K</b></span> <span className="text-muted text-[12px]">差し替えが届いた行は一瞬光る</span></div>
        <div className="grp"><span className="nm"><b>012 架空演者L</b></span></div>
      </div>
    </Sec>
    {toast && <div className="toast on">保存しました</div>}
    {dlg && <div className="modal" onMouseDown={(e) => { if (e.target === e.currentTarget) setDlg(false); }}><div className="dlg"><h2>ダイアログ</h2><p className="desc">開くときは下から少し浮き上がる（320ms・ease-out）。</p><div className="foot" style={{ marginTop: 20, display: "flex", justifyContent: "flex-end", gap: 8 }}><button onClick={() => setDlg(false)}>閉じる</button></div></div></div>}
  </div>;
}
createRoot(document.getElementById("root")!).render(<Page />);
