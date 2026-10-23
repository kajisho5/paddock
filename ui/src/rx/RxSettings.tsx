/* RECEPTION の設定：受付（照合・このPCに残す・受付PCの名前・目印画像のフォルダ） */
import { useState } from "react";
import { api } from "../api";
import { toast } from "../store";
import { RX, rxLoadFlags } from "./rxState";

interface RxCfg { verify: boolean; keep_local: boolean; pc_name: string; flag_dir: string; auto_recv: boolean }
let draft: RxCfg | null = null;
export function RxSettings() {
  const [st, setSt] = useState<RxCfg>(() => (draft = { verify: true, keep_local: true, pc_name: "", flag_dir: "", auto_recv: true, ...(RX.settings || {}) }));
  const set = (p: Partial<RxCfg>) => { const n = { ...st, ...p }; draft = n; setSt(n); };
  return <div id="rxSet"><h3>受付</h3>
    <div className="checks col">
      <label><input type="checkbox" id="rxVerify" checked={st.verify} onChange={(e) => set({ verify: e.target.checked })} />NASへ書き込んだあと、読み直して内容を照合する（おすすめ）</label>
      <label><input type="checkbox" id="rxKeep" checked={st.keep_local} onChange={(e) => set({ keep_local: e.target.checked })} />受け取ったデータと、差し替える前の版をこのPCにも残す（おすすめ。オフのときは差し替え前の版を残さずに置き換えます）</label></div>
    <div className="grid2" style={{ marginTop: 10 }}><span>受付PCの名前</span><input type="text" id="rxPc" value={st.pc_name} placeholder="例: 受付1" onChange={(e) => set({ pc_name: e.target.value })} /></div>
    <p className="hint">受付履歴に記録されます。保存先: <span className="mono">{RX.data}</span>（received＝受け取ったデータ、backup＝差し替え前の版）</p>
    <div className="grid2" style={{ marginTop: 10 }}><span>目印画像のフォルダ</span><span style={{ display: "flex", gap: 6, minWidth: 0 }}>
      <input type="text" id="rxFlagDir" value={st.flag_dir} placeholder="例: \\192.168.0.10\share\目印" style={{ flex: 1, minWidth: 0 }} onChange={(e) => set({ flag_dir: e.target.value })} />
      <button className="ghost" type="button" onClick={async () => { try { const j: any = await api("/api/rx/pickdir", {}); if (j.path) set({ flag_dir: j.path }); } catch (e: any) { toast(e.message, 5000); } }}>選ぶ…</button></span></div>
    <p className="hint">現場で使っている目印の元画像（00_受付済.jpg 〜 18_発表終了.jpg など）を入れたフォルダを指定すると、受付パネルから目印を付けたり外したりできます。画像はそのままコピーします（アプリが画像を作ることはありません）。</p>
    <div className="checks col" style={{ marginTop: 6 }}><label><input type="checkbox" id="rxAuto" checked={st.auto_recv !== false} onChange={(e) => set({ auto_recv: e.target.checked })} />受付したとき、「受付済」の目印画像を演者フォルダへ入れる（フォルダだけで確認している人にも受付済みが分かるように。すでに受付済・会場取得・発表終了の目印があれば入れません）</label></div>
  </div>;
}
export async function rxSettingsSave() {
  if (!draft) return;
  const j: any = await api("/api/rx/settings", { ...draft, pc_name: draft.pc_name.trim(), flag_dir: draft.flag_dir.trim().replace(/^"|"$/g, "") });
  RX.settings = j.settings; draft = null; rxLoadFlags();
}
