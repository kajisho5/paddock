"""ui/（React）をビルドした1つのHTMLを、sw_nas_watch.py の UI_PACK に書き込む（画面の編集は ui/src で行う）

  python3 dev/embed_ui.py          # ui/dist/index.html を埋め込む
  python3 dev/embed_ui.py --build  # 先に npm run build してから埋め込む
"""
import base64
import os
import re
import subprocess
import sys
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
TOP = os.path.dirname(HERE)
UI = os.path.join(TOP, "ui")
if "--build" in sys.argv:
    subprocess.run(["npm", "run", "build"], cwd=UI, check=True)
html = open(os.path.join(UI, "dist", "index.html"), encoding="utf-8").read()
for ph in ("__TOKEN__", "__APPKIND__", "__VERSION__"):
    assert html.count(ph) == 1, ph
for bad in ("http://", "https://"):          # 外部から何も読み込まない（会場ではネットにつながらないことがある）
    for m in re.finditer(r'(?:src|href)\s*=\s*["\']' + bad, html):
        raise SystemExit("外部の読み込みがあります: " + html[m.start():m.start() + 80])
pack = base64.b64encode(zlib.compress(html.encode("utf-8"), 9)).decode("ascii")
lines = [pack[i:i + 100] for i in range(0, len(pack), 100)]
block = 'UI_PACK = (\n' + "".join('    "%s"\n' % x for x in lines) + ')\n'
p = os.path.join(TOP, "sw_nas_watch.py")
s = open(p, encoding="utf-8").read()
m = re.search(r"^UI_PACK = \(\n.*?^\)\n", s, flags=re.S | re.M)
assert m, "UI_PACK の場所が見つかりません"
s = s[:m.start()] + block + s[m.end():]
open(p, "w", encoding="utf-8").write(s)
print("embedded ui: %d bytes html, %d bytes packed" % (len(html), len(pack)))
