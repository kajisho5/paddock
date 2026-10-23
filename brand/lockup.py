"""Lockup = app icon (squircle render) + outlined wordmark (Inter Display SemiBold)."""
import base64, sys
from fontTools.ttLib import TTFont
from fontTools.pens.svgPathPen import SVGPathPen
from fontTools.pens.transformPen import TransformPen
from fontTools.pens.boundsPen import BoundsPen
F='/usr/share/fonts/opentype/inter/InterDisplay-SemiBold.otf'
font=TTFont(F); gs=font.getGlyphSet(); cmap=font.getBestCmap(); upm=font['head'].unitsPerEm; hm=font['hmtx']
def outline(text, size, x0, base, track=-0.01):
    s=size/upm; pen=SVGPathPen(gs); b=BoundsPen(gs); x=0
    for ch in text:
        n=cmap[ord(ch)]
        t=(s,0,0,-s,x0+x*s,base)
        gs[n].draw(TransformPen(pen,t)); gs[n].draw(TransformPen(b,t))
        x+=hm[n][0]+track*upm
    return pen.getCommands(), b.bounds
def lockup(icon_png, name, out, fg, sub):
    I=200; gap=48
    p1,b1=outline('SW NAS', 52, I+gap, 96)
    p2,b2=outline(name, 104, I+gap, 196)
    w=int(max(b1[2],b2[2]))+8; h=I
    img=base64.b64encode(open(icon_png,'rb').read()).decode()
    svg=f'''<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" viewBox="0 0 {w} {h}" width="{w}" height="{h}">
<image width="{I}" height="{I}" xlink:href="data:image/png;base64,{img}"/>
<path fill="{sub}" d="{p1}"/><path fill="{fg}" d="{p2}"/></svg>'''
    open(out,'w').write(svg); return w,h
if __name__=='__main__':
    icon,name,out,mode=sys.argv[1:5]
    fg,sub=('#1D1D1F','#6E6E73') if mode=='light' else ('#F5F5F7','#A1A1A6')
    print(lockup(icon,name,out,fg,sub))
