"""sw_nas_operator.py の PowerPoint を開く命令（PPT_PS）を ppt.ps1 に書き出す（CI の文法チェック用）"""
import re, sys
s = open("sw_nas_operator.py", encoding="utf-8").read()
m = re.search(r'PPT_PS = r"""(.*?)"""', s, re.S)
open(sys.argv[1] if len(sys.argv) > 1 else "ppt.ps1", "w", encoding="utf-8-sig").write(m.group(1))
