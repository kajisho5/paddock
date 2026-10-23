import { useEffect } from "react";
/* ダイアログの外枠（外側をクリック・Esc で閉じる） */
export function Modal({ onClose, children, wide, id }: { onClose: () => void; children: React.ReactNode; wide?: boolean; id?: string }) {
  useEffect(() => { const k = (e: KeyboardEvent) => { if (e.key === "Escape") onClose(); }; document.addEventListener("keydown", k); return () => document.removeEventListener("keydown", k); }, [onClose]);
  return <div className={"modal open" + (wide ? " wide" : "")} id={id || "modal"} onMouseDown={(e) => { if (e.target === e.currentTarget) onClose(); }}>{children}</div>;
}
