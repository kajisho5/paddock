/* PADDOCK の共通部品（デザインシステム）。見た目はトークン（design/tokens.css）と Tailwind のクラスで決める */
import { useLayoutEffect, useRef, useState, type ReactNode } from "react";
import { Icon } from "../components/Icons";

const cx = (...a: (string | false | null | undefined)[]) => a.filter(Boolean).join(" ");

/** 切り替えボタン（タブ）。選んだ項目の下地がなめらかに移動する */
export function Segmented<T extends string>({ items, value, onChange, label, className }: {
  items: { v: T; label: ReactNode; id?: string; title?: string }[]; value: T; onChange: (v: T) => void; label: string; className?: string;
}) {
  const ref = useRef<HTMLDivElement>(null);
  const [ind, setInd] = useState<{ x: number; w: number } | null>(null);
  useLayoutEffect(() => {
    const el = ref.current?.querySelector<HTMLElement>("button[aria-selected=true]");
    if (el) setInd({ x: el.offsetLeft, w: el.offsetWidth });
  }, [value, items.length]);
  useLayoutEffect(() => {   // 文字の大きさ・幅が変わったときも合わせる
    const ro = new ResizeObserver(() => { const el = ref.current?.querySelector<HTMLElement>("button[aria-selected=true]"); if (el) setInd({ x: el.offsetLeft, w: el.offsetWidth }); });
    if (ref.current) ro.observe(ref.current);
    return () => ro.disconnect();
  }, []);
  return <div ref={ref} className={cx("seg", ind && "has-ind", className)} role="tablist" aria-label={label}>
    {ind && <span className="seg-ind" style={{ width: ind.w, transform: `translateX(${ind.x}px)` }} aria-hidden="true" />}
    {items.map((it) => <button key={it.v} type="button" role="tab" id={it.id} title={it.title} aria-selected={value === it.v} onClick={() => onChange(it.v)}>{it.label}</button>)}
  </div>;
}

/** 進捗バー。pct は 0〜100。幅ではなく拡大率で動かす（なめらか・軽い） */
export function Bar({ pct, className = "bar" }: { pct: number; className?: string }) {
  const p = Math.max(0, Math.min(100, pct || 0)) / 100;
  return <span className={className} role="progressbar" aria-valuemin={0} aria-valuemax={100} aria-valuenow={Math.round(p * 100)}>
    <i style={{ ["--p" as any]: p }} /></span>;
}

/** 何も無いときの表示（アイコン＋見出し＋説明） */
export function EmptyState({ icon = "shoe", title, children, style }: { icon?: string; title?: ReactNode; children?: ReactNode; style?: React.CSSProperties }) {
  return <div className="empty animate-fade-in" style={style}><div className="ico"><Icon n={icon} /></div>{title && <b>{title}</b>}{children}</div>;
}

/** 状態の点（on=正常・監視中 / busy=コピー中など / off=つながらない） */
export function StatusDot({ state, className }: { state?: "on" | "busy" | "off" | ""; className?: string }) {
  return <span className={cx("dot", state, className)} aria-hidden="true" />;
}

/** 小さな丸いラベル（チップ） */
export function Chip({ tone = "none", children, className }: { tone?: "ok" | "got" | "warn" | "bad" | "vio" | "info" | "none"; children: ReactNode; className?: string }) {
  const t: Record<string, string> = {
    ok: "bg-ok-bg text-ok-fg", got: "bg-got-bg text-got-fg", warn: "bg-warn-bg text-warn-fg", bad: "bg-bad-bg text-bad-fg",
    vio: "bg-vio-bg text-vio-fg", info: "bg-info-bg text-info-fg", none: "bg-card2 text-muted",
  };
  return <span className={cx("inline-flex items-center gap-1 rounded-full px-2 h-5 text-[11px] font-bold leading-none whitespace-nowrap", t[tone], className)}>{children}</span>;
}
