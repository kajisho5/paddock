"""配布用ビルド：ソースを含めない保護版の zip を作る（SEVENTHWELL 社内用スクリプト）

  python3 build_protected.py <embeddable-python.zip> <出力先フォルダ>

・起動は SW_NAS_WATCH.exe（exe/ のランチャーを zig でクロスコンパイル。pip install ziglang が必要）
・sw_nas_watch.py → 同梱Python(3.13)専用のバイトコード runtime/app/sw_nas_watch.pyc（説明文・assertを除去）
・画面（HTML/JS/CSS）は圧縮＋符号化して、テキストとしては読めない形で埋め込む
・同梱Pythonと同じバージョン（3.13.x）のPythonで実行すること（.pyc はバージョン固有）

配布ZIPの中身:
  SW_NAS_WATCH/SW_NAS_WATCH.exe, README.md, LICENSE.txt, runtime/app/sw_nas_watch.pyc, runtime/python/*
"""
import base64
import os
import py_compile
import re
import stat
import sys
import tempfile
import zipfile
import zlib

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "exe"))
import build_launcher  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "sw_nas_watch.py")


def transform(src):
    m = re.search(r"^HTML = r'''(.*?)'''\n", src, flags=re.S | re.M)
    if not m:
        raise SystemExit("HTML ブロックが見つかりません")
    blob = base64.b85encode(zlib.compress(m.group(1).encode("utf-8"), 9)).decode("ascii")
    repl = 'HTML = __import__("zlib").decompress(__import__("base64").b85decode(%r)).decode("utf-8")\n' % blob
    out = src[:m.start()] + repl + src[m.end():]
    out = re.sub(r'^r"""\n.*?\n"""\n', "", out, count=1, flags=re.S | re.M)   # 先頭の説明文
    return out


def main():
    if sys.version_info[:2] != (3, 13):
        raise SystemExit("同梱Pythonと同じ 3.13 で実行してください（現在 %d.%d）" % sys.version_info[:2])
    emb, outdir = sys.argv[1], sys.argv[2]
    version = re.search(r'^VERSION = "([^"]+)"', open(SRC, encoding="utf-8").read(), re.M).group(1)
    os.makedirs(outdir, exist_ok=True)
    src = transform(open(SRC, encoding="utf-8").read())
    with tempfile.TemporaryDirectory() as td:
        tmp = os.path.join(td, "sw_nas_watch.py")
        open(tmp, "w", encoding="utf-8").write(src)
        pyc = os.path.join(outdir, "sw_nas_watch.pyc")
        py_compile.compile(tmp, cfile=pyc, dfile="sw_nas_watch", optimize=2, doraise=True,
                           invalidation_mode=py_compile.PycInvalidationMode.UNCHECKED_HASH)
    exe = build_launcher.build(os.path.join(outdir, "SW_NAS_WATCH.exe"), version)
    out = os.path.join(outdir, "SW_NAS_WATCH_v%s_Windows.zip" % version)
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        def add(name, data, mode=0o644):
            zi = zipfile.ZipInfo("SW_NAS_WATCH/" + name, date_time=(2026, 10, 10, 12, 0, 0))
            zi.compress_type = zipfile.ZIP_DEFLATED
            zi.external_attr = (stat.S_IFREG | mode) << 16
            z.writestr(zi, data)
        add("SW_NAS_WATCH.exe", open(exe, "rb").read(), 0o755)
        add("runtime/app/sw_nas_watch.pyc", open(pyc, "rb").read())
        add("README.md", open(os.path.join(HERE, "README.md"), "rb").read())
        add("LICENSE.txt", open(os.path.join(HERE, "LICENSE.txt"), "rb").read())
        with zipfile.ZipFile(emb) as e:
            for it in e.infolist():
                add("runtime/python/" + it.filename, e.read(it.filename))
    print(out)


if __name__ == "__main__":
    main()
