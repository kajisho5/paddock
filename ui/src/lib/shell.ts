/* Tauri 版の窓（PADDOCK GATE.exe）とのやりとり。ブラウザで開いているときは何もしない */
type Invoke = (cmd: string, args?: Record<string, unknown>) => Promise<unknown>;
const inv = (): Invoke | null => {
  const t = (window as any).__TAURI__;
  return t && t.core && typeof t.core.invoke === "function" ? t.core.invoke : null;
};
export const IN_SHELL = () => !!inv();

/* 開く前に：常に最前面を外し、開いたスライド・ファイルの窓が前に出られるようにする（GATE に戻ると最前面に戻る） */
export async function shellBeforeOpen() {
  const f = inv(); if (!f) return;
  // 窓が応えなくても、開くのは止めない（待つのは 300ms まで）
  try { await Promise.race([f("slide_opening"), new Promise((r) => setTimeout(r, 300))]); } catch (e) { console.warn("slide_opening", e); }
}
/* 開けなかったとき：すぐ最前面に戻す */
export async function shellOpenFailed() {
  const f = inv(); if (!f) return;
  try { await f("slide_open_failed"); } catch { /* */ }
}
export async function shellPinned(): Promise<boolean | null> {
  const f = inv(); if (!f) return null;
  try { return !!(await f("get_pinned")); } catch { return null; }
}
export async function shellSetPinned(on: boolean): Promise<boolean | null> {
  const f = inv(); if (!f) return null;
  try { return !!(await f("set_pinned", { on })); } catch { return null; }
}

/* 窓とつながったことを知らせる（設定前の画面でも） */
setTimeout(() => { const f = inv(); if (f) f("get_pinned").catch(() => {}); }, 0);
