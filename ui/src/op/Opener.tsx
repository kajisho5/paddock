/* OPERATOR：演者のスライドを開く（このPCのコピーから。NASのファイルは開かない） */
import { useState } from "react";
import { api } from "../api";
import { IS_OP } from "../boot";
import type { Config, Folder, FolderItem } from "../types";
import { setDblHandler, store, toast, useApp } from "../store";
import { CPL } from "../components/Bits";
import { Icon } from "../components/Icons";
import { cx } from "../lib/util";

export interface OpenCfg { enabled: boolean; dest: string; dbl: "file" | "show" | "folder"; multi: "newest" | "folder" }
export const OPEN: { settings: OpenCfg; dest: { id: string; label: string } | null } = { settings: { enabled: true, dest: "", dbl: "file", multi: "newest" }, dest: null };
export function openLoad() { return api<any>("/api/op/open/settings").then((j) => { OPEN.settings = j.settings; OPEN.dest = j.dest; store.emit(); }).catch(() => {}); }

export async function opOpen(root: string, group: string, rel: string, how: "file" | "show" | "folder") {
  if (!store.S?.local) { toast("開くのは、このアプリを動かしているPCでのみできます", 4000); return; }
  try {
    const j: any = await api("/api/op/open", { root, group, rel: rel || "", how });
    toast((j.what === "folder" ? "フォルダを開いています（" + j.dest + "）" : j.what === "show" ? "スライドショーで開いています: " + j.name + "（" + j.dest + "）" : "開いています: " + j.name + "（" + j.dest + "）") + (j.msg ? "\n" + j.msg : ""), j.msg ? 7000 : 3000);
  } catch (e: any) { toast(e.message, 8000); }
}
if (IS_OP) {
  openLoad();
  /* 演者をダブルクリック → 設定に合わせて、発表ファイル（またはフォルダ）をこのPCのコピーから開く */
  setDblHandler((root, group) => {
    if (!OPEN.settings.enabled) { toast("ダブルクリックで開くには、［設定］→「演者のスライドを開く」をオンにしてください", 7000); return; }
    opOpen(root, group, "", OPEN.settings.dbl);
  });
}
export const opNewest = (F: Folder) => (OPEN.settings.enabled && F.op && F.op.pres ? F.op.pres.newest : "");

/* 演者画面の上：大きな［スライドショー］［開く］（発表ファイルが決まるとき） */
export function OpOpenHead({ F }: { F: Folder }) {
  useApp(); const st = OPEN.settings; const d = OPEN.dest;
  if (!st.enabled || !F.group || !F.op || !d) return null;
  return <div className="opbig">
    <button className="big go" onClick={() => opOpen(F.root, F.group, "", "show")} title="発表ファイルをスライドショーで開きます（このPCのコピーから）"><Icon n="play" /><span><b>スライドショー</b><small>{d.label}のコピーから</small></span></button>
    <button className="big" onClick={() => opOpen(F.root, F.group, "", "file")} title="発表ファイルを開きます（PowerPoint など）"><Icon n="file" /><span><b>発表ファイルを開く</b><small>{st.multi === "newest" ? "2つ以上なら後から入ったほう" : "2つ以上ならフォルダ"}</small></span></button>
  </div>;
}
export function OpFolderButton({ F }: { F: Folder }) {
  const st = OPEN.settings; const d = OPEN.dest;
  if (!st.enabled || !F.group || !F.op || !d) return null;
  return <button className="pri" data-oo="folder" title={"この演者のフォルダを、このPCのコピー（" + d.label + "）から Explorer で開きます"} onClick={() => opOpen(F.root, F.group, "", "folder")}><Icon n="folder" />フォルダを開く（{d.label}）</button>;
}
const SHOW = [".pptx", ".ppsx", ".pptm", ".ppsm", ".ppt", ".pps"];
export const OpFileButtons = {
  Head({ F }: { F: Folder }) { const d = OPEN.dest; return OPEN.settings.enabled && F.op && d ? <th>開く（{d.label}）</th> : null; },
  Cell({ F, it }: { F: Folder; it: FolderItem }) {
    const d = OPEN.dest; if (!OPEN.settings.enabled || !F.op || !d) return null;
    if (it.d || it.mk) return <td />;
    const st = it.cp && it.cp[d.id] ? it.cp[d.id][0] : ""; const ok = st === "ok" || st === "edited" || st === "old";
    const ext = (it.p.match(/\.[^./]+$/) || [""])[0].toLowerCase(); const show = SHOW.includes(ext);
    const why = ok ? "" : "（" + (CPL[st] || ["コピー待ち"])[0] + "。コピーが終わると開けます）";
    return <td style={{ whiteSpace: "nowrap" }}>
      <button className="ghost oo" data-oo="file" disabled={!ok} title={"このPCのコピーを開く" + why} onClick={(e) => { e.stopPropagation(); opOpen(F.root, F.group, it.p, "file"); }}>開く</button>
      {show && <> <button className={cx("ghost oo", "show")} data-oo="show" disabled={!ok} title={"スライドショーで開く" + why} onClick={(e) => { e.stopPropagation(); opOpen(F.root, F.group, it.p, "show"); }}>スライドショー</button></>}
    </td>;
  },
};

/* 設定画面：「演者のスライドを開く」 */
let draft: OpenCfg | null = null;
export function OpenSettings({ c }: { c: Config }) {
  const [st, setSt] = useState<OpenCfg>(() => (draft = { ...OPEN.settings }));
  const set = (p: Partial<OpenCfg>) => { const n: OpenCfg = { ...st, ...p }; draft = n; setSt(n); };
  const ds = (c.op.dests || []).filter((d) => d.id && String(d.path || "").trim());
  return <div id="opOpenSet"><h3>演者のスライドを開く</h3>
    <p style={{ margin: 0 }}><label className="lbl"><input type="checkbox" id="ooOn" checked={st.enabled} onChange={(e) => set({ enabled: e.target.checked })} />演者をダブルクリック・演者画面の［スライドショー］［開く］で、発表ファイルを開けるようにする</label></p>
    <div className="grid2" style={{ marginTop: 10 }}>
      <span>開くコピー</span><span><select id="ooDest" value={st.dest} onChange={(e) => set({ dest: e.target.value })}><option value="">自動（このPCのフォルダのコピー先）</option>{ds.map((x) => <option key={x.id} value={x.id}>{x.label}（{x.path}）</option>)}</select></span>
      <span>ダブルクリックしたとき</span><span className="checks col">
        <label><input type="radio" name="ooDbl" value="file" checked={st.dbl === "file"} onChange={() => set({ dbl: "file" })} />発表ファイルを開く（PowerPoint など）</label>
        <label><input type="radio" name="ooDbl" value="show" checked={st.dbl === "show"} onChange={() => set({ dbl: "show" })} />発表ファイルをスライドショーで開く（PowerPoint のとき）</label>
        <label><input type="radio" name="ooDbl" value="folder" checked={st.dbl === "folder"} onChange={() => set({ dbl: "folder" })} />演者フォルダを開く（Explorer）</label></span>
      <span>発表ファイルが2つ以上あるとき</span><span className="checks col">
        <label><input type="radio" name="ooMulti" value="newest" checked={st.multi !== "folder"} onChange={() => set({ multi: "newest" })} />後から入ったほうを開く（差し替え版が後から届いたとき用。どちらか決められないときはフォルダ）</label>
        <label><input type="radio" name="ooMulti" value="folder" checked={st.multi === "folder"} onChange={() => set({ multi: "folder" })} />フォルダを開く（どれを使うか目で選ぶ）</label></span>
    </div>
    <p className="hint">開くのは、<b>このPCのコピー先にコピーが終わったファイル</b>です。NAS上のファイルは開きません（会場側の作業や、受付での差し替えに影響を出さないため）。コピー中・コピー待ちのときは開かずに知らせます。<br />コピー先を追加・変更したときは、［保存］してからもう一度開くと「開くコピー」に出ます。</p>
  </div>;
}
export async function openSettingsSave() {
  if (!draft) { setTimeout(() => openLoad(), 800); return; }   // コピー先を変えたときも「開くコピー」を読み直す
  const j: any = await api("/api/op/open/settings", draft); OPEN.settings = j.settings; OPEN.dest = j.dest; draft = null;
  setTimeout(() => openLoad(), 800);
}
