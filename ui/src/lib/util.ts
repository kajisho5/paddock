/* 表示まわりの小さな道具（旧画面から移植。並び順・表記は旧画面と同じにする） */

export const nfc = (s: unknown): string => {
  try { return String(s == null ? "" : s).normalize("NFC"); } catch { return String(s); }
};

export const ls = {
  get<T>(k: string, d: T): T {
    try { const v = localStorage.getItem("swnw." + k); return v == null ? d : (JSON.parse(v) as T); } catch { return d; }
  },
  set(k: string, v: unknown) { try { localStorage.setItem("swnw." + k, JSON.stringify(v)); } catch { /* 保存できなくても動く */ } },
};

export function fmtSize(n?: number | null): string {
  if (n == null) return "";
  const u = ["B", "KB", "MB", "GB", "TB"]; let i = 0; let x = n;
  while (x >= 1024 && i < u.length - 1) { x /= 1024; i++; }
  return (i ? x.toFixed(x < 10 ? 1 : 0) : String(x)) + " " + u[i];
}
export const p2 = (n: number) => String(n).padStart(2, "0");
export function hms(t: number) { const d = new Date(t * 1000); return p2(d.getHours()) + ":" + p2(d.getMinutes()) + ":" + p2(d.getSeconds()); }
export function dtm(t: number) {
  const d = new Date(t * 1000), n = new Date();
  const day = d.toDateString() === n.toDateString() ? "" : (d.getMonth() + 1) + "/" + d.getDate() + " ";
  return day + p2(d.getHours()) + ":" + p2(d.getMinutes());
}
export function ago(t: number) {
  const s = Math.max(0, Date.now() / 1000 - t);
  if (s < 60) return Math.floor(s) + "秒前";
  if (s < 3600) return Math.floor(s / 60) + "分前";
  if (s < 86400) return Math.floor(s / 3600) + "時間前";
  return Math.floor(s / 86400) + "日前";
}
export function mss(sec: number) {
  sec = Math.max(0, Math.floor(sec));
  const h = Math.floor(sec / 3600), m = Math.floor((sec % 3600) / 60), s2 = sec % 60;
  return (h ? h + ":" + p2(m) : String(m)) + ":" + p2(s2);
}

/* 並べ替え用の読み替え：①〜⑳・全角数字などは NFKC で数字に、❶➀➊⓫⓵ など NFKC で変わらない丸数字も数字に直してから比べる */
const DINGNUM: Record<string, string> = (() => {
  const m: Record<string, string> = {};
  const put = (from: number, n0: number, cnt: number) => { for (let i = 0; i < cnt; i++) m[String.fromCharCode(from + i)] = String(n0 + i); };
  put(0x2776, 1, 10); put(0x2780, 1, 10); put(0x278a, 1, 10); put(0x24eb, 11, 10); put(0x24f5, 1, 10); put(0x24ff, 0, 1);
  return m;
})();
const SKC = new Map<string, string>();
export function nameKey(s0: unknown): string {
  const s = String(s0 == null ? "" : s0);
  let k = SKC.get(s);
  if (k !== undefined) return k;
  try { k = s.normalize("NFKC"); } catch { k = s; }
  k = k.replace(/[❶-➓⓫-⓿]/g, (c) => (DINGNUM[c] !== undefined ? DINGNUM[c] : c));
  if (SKC.size > 20000) SKC.clear();
  SKC.set(s, k);
  return k;
}
const COLL = new Intl.Collator("ja", { numeric: true, sensitivity: "base" });
export const cmpName = (a: string, b: string) => COLL.compare(nameKey(a), nameKey(b)) || (nfc(a) < nfc(b) ? -1 : nfc(a) > nfc(b) ? 1 : 0);
export function cmpPath(a: string, b: string) {
  const x = a.split("/"), y = b.split("/");
  for (let i = 0; i < Math.min(x.length, y.length); i++) { const c = cmpName(x[i], y[i]); if (c) return c; }
  return x.length - y.length;
}
export const whereText = (w: string) => nfc(w).split("/").join(" › ");

/* スライド番号の並び：1,2,3,5 → 「1〜3枚目、5枚目」 */
export function sl(arr: number[]) {
  const a = [...new Set(arr)].sort((x, y) => x - y); const out: string[] = [];
  for (let i = 0; i < a.length;) {
    let j = i; while (j + 1 < a.length && a[j + 1] === a[j] + 1) j++;
    out.push(i === j ? a[i] + "枚目" : a[i] + "〜" + a[j] + "枚目"); i = j + 1;
  }
  return out.join("、");
}

/* ファイルの並び（フォルダを先、名前は数字を数値として） */
export function sortKey(p: string, isDir: boolean) { const s = p.split("/"); return s.map((x, i) => ((i < s.length - 1 || isDir) ? "0" : "1") + x); }
export function cmpKeys(a: string[], b: string[]) {
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    if (a[i] !== b[i]) { if (a[i][0] !== b[i][0]) return a[i][0] < b[i][0] ? -1 : 1; return cmpName(a[i].slice(1), b[i].slice(1)); }
  }
  return a.length - b.length;
}

/* クリップボード（LANの他の端末から http で開いたときは navigator.clipboard が使えないので、昔の方法で） */
export function copyText(t: string): Promise<void> {
  if (navigator.clipboard && window.isSecureContext) return navigator.clipboard.writeText(t);
  return new Promise((ok, ng) => {
    const a = document.createElement("textarea"); a.value = t; a.style.position = "fixed"; a.style.opacity = "0";
    document.body.appendChild(a); a.select();
    let r = false; try { r = document.execCommand("copy"); } catch { /* */ }
    a.remove(); if (r) ok(); else ng(new Error("copy"));
  });
}

export const cx = (...a: (string | false | null | undefined | 0)[]) => a.filter(Boolean).join(" ");
