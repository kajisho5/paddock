import { TOKEN } from "./boot";

/* サーバーとのやりとり。POST にはトークンを付ける（このPCの画面からの操作だけ受け付けるため） */
export async function api<T = any>(path: string, body?: unknown): Promise<T> {
  const o: RequestInit = body === undefined ? { cache: "no-store" }
    : { method: "POST", headers: { "Content-Type": "application/json", "X-SW-Token": TOKEN }, body: JSON.stringify(body) };
  const r = await fetch(path, o);
  let j: any = {};
  try { j = await r.json(); } catch { /* */ }
  if (r.status === 403 && j.error === "token") { location.reload(); throw new Error("reload"); }
  if (!r.ok) throw new Error(j.error || "HTTP " + r.status);
  return j as T;
}
export const enc = encodeURIComponent;
