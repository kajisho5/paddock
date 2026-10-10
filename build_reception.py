"""受付アプリ（SW NAS RECEPTION）の配布用ビルド：ソースを含めない保護版の zip を作る（SEVENTHWELL 社内用）

  python3 build_reception.py <embeddable-python.zip> <出力先フォルダ>

・起動は SW_NAS_RECEPTION.exe（SW NAS WATCH と同じランチャーを、名前だけ変えてビルド）
・sw_nas_reception.py → runtime/app/sw_nas_reception.pyc（画面に足す部分は圧縮＋符号化）
・sw_nas_watch.py     → runtime/app/sw_nas_watch.pyc（部品として読み込む。SW NAS WATCH の配布版と同じ作り方）
・同梱Pythonと同じバージョン（3.13.x）のPythonで実行すること（.pyc はバージョン固有）

配布ZIPの中身:
  SW_NAS_RECEPTION/SW_NAS_RECEPTION.exe, README.md, LICENSE.txt,
  runtime/app/sw_nas_reception.pyc, runtime/app/sw_nas_watch.pyc, runtime/python/*
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

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "exe"))
sys.path.insert(0, HERE)
import build_launcher  # noqa: E402
import build_protected  # noqa: E402

SRC_RX = os.path.join(HERE, "sw_nas_reception.py")
SRC_W = os.path.join(HERE, "sw_nas_watch.py")
VARIANT = {"title": "SW NAS RECEPTION", "exe": "SW_NAS_RECEPTION.exe", "pyc": "sw_nas_reception.pyc",
           "home_env": "SW_NAS_RECEPTION_HOME", "internal": "SW_NAS_RECEPTION", "ident": "SEVENTHWELL.SWNASRECEPTION"}


def transform_rx(src):
    for name in ("RX_CSS", "RX_JS"):
        m = re.search(r"^%s = r'''(.*?)'''\n" % name, src, flags=re.S | re.M)
        if not m:
            raise SystemExit("%s ブロックが見つかりません" % name)
        blob = base64.b85encode(zlib.compress(m.group(1).encode("utf-8"), 9)).decode("ascii")
        repl = '%s = __import__("zlib").decompress(__import__("base64").b85decode(%r)).decode("utf-8")\n' % (name, blob)
        src = src[:m.start()] + repl + src[m.end():]
    out, n = re.subn(r'^r"""\n.*?\n"""\n', "", src, count=1, flags=re.S | re.M)   # 先頭の説明文
    if n != 1:
        raise SystemExit("先頭の説明文が見つかりません")
    return out


def compile_to(src, name, outdir):
    with tempfile.TemporaryDirectory() as td:
        tmp = os.path.join(td, name + ".py")
        open(tmp, "w", encoding="utf-8").write(src)
        pyc = os.path.join(outdir, name + ".pyc")
        py_compile.compile(tmp, cfile=pyc, dfile=name, optimize=2, doraise=True,
                           invalidation_mode=py_compile.PycInvalidationMode.UNCHECKED_HASH)
    return pyc


def main():
    if sys.version_info[:2] != (3, 13):
        raise SystemExit("同梱Pythonと同じ 3.13 で実行してください（現在 %d.%d）" % sys.version_info[:2])
    emb, outdir = sys.argv[1], sys.argv[2]
    rx_src = open(SRC_RX, encoding="utf-8").read()
    version = re.search(r'^VERSION = "([^"]+)"', rx_src, re.M).group(1)
    os.makedirs(outdir, exist_ok=True)
    with tempfile.TemporaryDirectory() as work:
        pyc_w = compile_to(build_protected.transform(open(SRC_W, encoding="utf-8").read()), "sw_nas_watch", work)
        pyc_rx = compile_to(transform_rx(rx_src), "sw_nas_reception", work)
        exe = build_launcher.build(os.path.join(work, VARIANT["exe"]), version, VARIANT)
        lic = open(os.path.join(HERE, "LICENSE.txt"), encoding="utf-8").read()
        if "SW NAS WATCH 利用条件" not in lic:
            raise SystemExit("LICENSE.txt の見出しが想定と違います")
        lic = lic.replace("SW NAS WATCH 利用条件", "SW NAS RECEPTION 利用条件", 1)
        out = os.path.join(outdir, "SW_NAS_RECEPTION_v%s_Windows.zip" % version)
        with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
            def add(name, data, mode=0o644):
                zi = zipfile.ZipInfo("SW_NAS_RECEPTION/" + name, date_time=(2026, 10, 10, 12, 0, 0))
                zi.compress_type = zipfile.ZIP_DEFLATED
                zi.external_attr = (stat.S_IFREG | mode) << 16
                z.writestr(zi, data)
            add(VARIANT["exe"], open(exe, "rb").read(), 0o755)
            add("runtime/app/sw_nas_reception.pyc", open(pyc_rx, "rb").read())
            add("runtime/app/sw_nas_watch.pyc", open(pyc_w, "rb").read())
            add("README.md", open(os.path.join(HERE, "README_RECEPTION.md"), "rb").read())
            add("LICENSE.txt", lic.encode("utf-8"))
            with zipfile.ZipFile(emb) as e:
                for it in e.infolist():
                    add("runtime/python/" + it.filename, e.read(it.filename))
    print(out)


if __name__ == "__main__":
    main()
