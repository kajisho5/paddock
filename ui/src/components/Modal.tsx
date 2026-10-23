/* ダイアログの外枠（外側をクリックで閉じる） */
export function Modal({ onClose, children, wide, id }: { onClose: () => void; children: React.ReactNode; wide?: boolean; id?: string }) {
  return <div className={"modal open" + (wide ? " wide" : "")} id={id || "modal"} onMouseDown={(e) => { if (e.target === e.currentTarget) onClose(); }}>{children}</div>;
}
