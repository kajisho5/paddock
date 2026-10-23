import { useEffect } from "react";
import { IS_OP, IS_RX } from "./boot";
import { closeDrawer, OPON, store, useApp } from "./store";
import { Banner, Header, OpStrip } from "./components/Header";
import { ListPane } from "./components/ListView";
import { BoardPane } from "./components/Board";
import { CenterPane } from "./components/Folder";
import { LogPane } from "./components/LogPane";
import { openCfg, SettingsDialog } from "./components/Settings";
import { NetDialog } from "./op/Net";
import { AddDialog, UsbDialog } from "./rx/RxPanel";
import { cx } from "./lib/util";
import { GateApp } from "./gate/Gate";

let setupShown = false;
export function App() {
  const s = useApp();
  /* OPERATOR：はじめて起動したとき（まだ設定していないとき）は、設定を開く */
  useEffect(() => {
    if (IS_OP && !setupShown && s.S && s.S.local && !OPON() && !s.modal) { setupShown = true; openCfg(); }
  });
  useEffect(() => {
    const k = (e: KeyboardEvent) => {
      if (e.key !== "Escape" || store.modal) return;
      if (store.logOpen) { store.logOpen = false; store.emit(); return; }
      closeDrawer();
    };
    document.addEventListener("keydown", k); return () => document.removeEventListener("keydown", k);
  }, []);
  if (IS_OP && s.S && OPON()) return <>
    <GateApp />
    <SettingsDialog />
    <NetDialog />
    {s.quit && <div className="quitov"><div><b>終了しました</b>このウィンドウを閉じてください。もう一度使うときは、アプリ（exe）を起動してください。</div></div>}
    <div id="toast" className={cx("toast", s.toastMsg && "on")} key={s.toastSeq}>{s.toastMsg}</div>
  </>;
  return <div className={cx("app", "v-" + s.view, s.logOpen && "showlog", s.drawer && "drawer", IS_OP && "k-op", IS_RX && "k-rx")}>
    <Header />
    <OpStrip />
    <Banner />
    <main id="main" className="main">
      {s.view === "list" ? <ListPane /> : <BoardPane />}
      {(s.view === "list" || s.drawer) && <CenterPane />}
      <LogPane />
    </main>
    <SettingsDialog />
    {IS_OP && <NetDialog />}
    {IS_RX && <UsbDialog />}
    {IS_RX && <AddDialog />}
    {s.quit && <div className="quitov"><div><b>終了しました</b>このウィンドウを閉じてください。もう一度使うときは、アプリ（exe）を起動してください。</div></div>}
    <div id="toast" className={cx("toast", s.toastMsg && "on")} key={s.toastSeq}>{s.toastMsg}</div>
  </div>;
}
