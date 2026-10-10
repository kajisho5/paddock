"""dev/share_setup.ps1 を sw_nas_operator.py の SHARE_PS に書き込む（編集はこの .ps1 で行う）"""
import os
import re
HERE = os.path.dirname(os.path.abspath(__file__))
ps = open(os.path.join(HERE, "share_setup.ps1"), encoding="utf-8").read()
assert "'''" not in ps and not ps.endswith("\\")
p = os.path.join(os.path.dirname(HERE), "sw_nas_operator.py")
s = open(p, encoding="utf-8").read()
m = re.search(r"^SHARE_PS = r'''.*?'''\n", s, flags=re.S | re.M)
assert m
s = s[:m.start()] + "SHARE_PS = r'''" + ps + "'''\n" + s[m.end():]
open(p, "w", encoding="utf-8").write(s)
print("embedded", len(ps))
