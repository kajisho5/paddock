/* 変更ログ（右） */
import { cx, dtm, nfc, whereText } from "../lib/util";
import { inVenue, selectGroup, store, useApp, venueOf, vColor } from "../store";
import { KindPill } from "./Bits";
import { Icon } from "./Icons";

export function LogPane() {
  const s = useApp(); const S = s.S;
  const evs = S ? S.events.filter((e) => inVenue(e.root, e.group)).slice().reverse() : [];
  const multi = !!S && S.roots.length > 1;
  return <section id="logpane" className="pane log">
    <div className="ph lh"><h2>変更ログ</h2><button className="ghost" id="bLogClose" onClick={() => { s.logOpen = false; s.emit(); }}><Icon n="x" />閉じる</button></div>
    <div className="scroll" id="log">
      {!evs.length ? <div className="empty"><div className="ico"><Icon n="inbox" /></div><b>まだ変更はありません</b>NAS上のフォルダに変化があるとここに出ます。</div>
        : evs.map((e) => {
          const v = venueOf(e.root, e.group);
          return <div key={e.id} className={cx("ev", e.u && "u")} data-id={e.id} onClick={() => { if (e.group != null) { selectGroup(e.root, e.group); store.logOpen = false; store.emit(); } }}>
            <div className="top"><span className="t">{dtm(e.ts)}</span><KindPill k={e.kind} />{e.repl ? <span className="kind k-repl">差替{e.repl}</span> : null}<span className="ti">{nfc(e.title)}</span>{e.while_stopped && <span className="ws" title="アプリ停止中に起きた変更">停止中</span>}</div>
            {e.where && <div className="wh">{v && <span className="vdot" style={{ ["--vc" as any]: vColor(e.root, v) }} />}{whereText(e.where)}</div>}
            <div className="sm">{e.summary}</div>{e.detail && <div className="dt">{nfc(e.detail)}</div>}
            {(e.ana || []).map((a, i) => <div key={i} className={cx("an", a.warn && "w")}>▸ {nfc(a.file)}: {a.text || a.na || "解析待ち"}</div>)}
            {multi && <div className="rl">{nfc(e.root_label)}</div>}
          </div>;
        })}
    </div>
  </section>;
}
