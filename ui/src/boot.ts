/* サーバーが埋め込む起動情報（トークン・どのアプリか）。開発時（vite）はダミー */
declare global { interface Window { SW_BOOT?: { token: string; kind: string; base: string } } }

const B = window.SW_BOOT || { token: "", kind: "watch", base: "" };
const real = (v: string, d: string) => (v && !v.startsWith("__") ? v : d);

export const TOKEN = real(B.token, "");
export type AppKind = "watch" | "reception" | "operator";
const k = real(B.kind, new URLSearchParams(location.search).get("kind") || "watch");
export const KIND: AppKind = k === "operator" || k === "reception" ? k : "watch";
export const BASE_VERSION = real(B.base, "");
export const IS_OP = KIND === "operator";
export const IS_RX = KIND === "reception";
export const APP_TITLE = IS_OP ? "SW NAS OPERATOR" : IS_RX ? "SW NAS RECEPTION" : "SW NAS WATCH";
export const APP_SUB = IS_OP ? "会場" : IS_RX ? "受付" : "READ ONLY";
