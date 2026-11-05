# PADDOCK ロゴ（C：パレードリング）最終形。周回路の上の切れ目に1頭（点）
O = "/tmp/claude-0/logo/k/"
W0, W1, H, T, DR = 12, 244, 136, 36, 18
ro = H / 2; ri = ro - T; L = W0 + ro; R = W1 - ro; c = T / 2
def ring_d(cy=128, a=82, b=174):
    top = cy - ro; t2 = top + T
    return (f"M{a} {top}H{L}A{ro} {ro} 0 0 0 {L} {cy+ro}H{R}A{ro} {ro} 0 0 0 {R} {top}H{b}"
            f"A{c} {c} 0 0 0 {b} {t2}H{R}A{ri} {ri} 0 0 1 {R} {cy+ri}H{L}A{ri} {ri} 0 0 1 {L} {t2}H{a}A{c} {c} 0 0 0 {a} {top}Z")
def body(fill="#000", dot_fill=None, cy=128):
    return f'<path fill="{fill}" d="{ring_d(cy)}"/><circle fill="{dot_fill or fill}" cx="128" cy="{cy - ro + c}" r="{DR}"/>'
def svg(b, vb="0 0 256 256"):
    return f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="{vb}"><title>PADDOCK</title>{b}</svg>'
if __name__ == "__main__":
    open(O + "symbol.svg", "w").write(svg(body()))
    print("ok")

def icon_layers(out_dir, scale=3.1):
    """アプリアイコン用（1024×1024）：輪と点を別のレイヤーに"""
    import os
    os.makedirs(out_dir, exist_ok=True)
    w = 1024; off = (w - 256 * scale) / 2
    g = f'transform="translate({off:.1f} {off:.1f}) scale({scale})"'
    top = 128 - ro + c
    open(os.path.join(out_dir, "ring.svg"), "w").write(
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1024 1024" width="1024" height="1024"><g {g}><path fill="#FFFFFF" d="{ring_d()}"/></g></svg>')
    open(os.path.join(out_dir, "dot.svg"), "w").write(
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1024 1024" width="1024" height="1024"><g {g}><circle fill="#FFFFFF" cx="128" cy="{top}" r="{DR}"/></g></svg>')
