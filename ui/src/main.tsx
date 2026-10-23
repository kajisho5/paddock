import { createRoot } from "react-dom/client";
import { App } from "./App";
import { KIND } from "./boot";
import { startApp } from "./store";
import "./styles.css";

/* 見た目：受付・監視は明るいテーマ、会場の発表PC（OPERATOR）は暗いテーマ */
document.documentElement.dataset.theme = KIND === "operator" ? "dark" : "light";
document.documentElement.dataset.kind = KIND;

/* 画面の中身を簡単に覗けないように（右クリックメニュー・開発者ツールのショートカットを封じる。入力欄の右クリックは可） */
document.addEventListener("contextmenu", (e) => { if (!(e.target as HTMLElement).closest("input,textarea")) e.preventDefault(); }, true);
document.addEventListener("keydown", (e) => {
  const k = (e.key || "").toLowerCase();
  if (e.key === "F12" || (e.ctrlKey && e.shiftKey && ["i", "j", "c", "k"].includes(k)) || (e.ctrlKey && ["u", "s"].includes(k)) || (e.metaKey && e.altKey && ["i", "j", "c", "u"].includes(k))) { e.preventDefault(); e.stopPropagation(); }
}, true);

createRoot(document.getElementById("root")!).render(<App />);
startApp();
