"""PADDOCK SCOUT を部品にして動く別アプリ（受付・会場オペレーター）の配布用ビルド（SEVENTHWELL 社内用）

  python3 build_app.py reception <embeddable-python.zip> <出力先フォルダ>
  python3 build_app.py operator  <embeddable-python.zip> <出力先フォルダ>
  （build_reception.py / build_operator.py からも呼べる）

・ソースを含めない保護版の zip を作る。起動は各アプリの exe（PADDOCK SCOUT と同じランチャーを、名前だけ変えてビルド）
・<アプリ>.py      → runtime/app/<アプリ>.pyc（画面に足す部分は圧縮＋符号化）
・sw_nas_watch.py → runtime/app/sw_nas_watch.pyc（部品として読み込む。PADDOCK SCOUT の配布版と同じ作り方）
・同梱Pythonと同じバージョン（3.13.x）のPythonで実行すること（.pyc はバージョン固有）

配布ZIPの中身（例：受付）:
  PADDOCK_SADDLE/PADDOCK_SADDLE.exe, README.md, LICENSE.txt,
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

SRC_W = os.path.join(HERE, "sw_nas_watch.py")
APPS = {
    "reception": {
        "src": "sw_nas_reception.py", "mod": "sw_nas_reception", "blocks": ("RX_CSS", "RX_JS"),
        "readme": "README_RECEPTION.md",
        "variant": {"title": "PADDOCK SADDLE", "exe": "PADDOCK_SADDLE.exe", "pyc": "sw_nas_reception.pyc",
                    "home_env": "SW_NAS_RECEPTION_HOME", "internal": "PADDOCK_SADDLE",
                    "ident": "SEVENTHWELL.SWNASRECEPTION", "icon": "reception.ico"},
    },
    "operator": {
        "src": "sw_nas_operator.py", "mod": "sw_nas_operator", "blocks": ("OP_CSS", "OP_JS", "SHARE_PS"),
        "readme": "README_OPERATOR.md",
        "variant": {"title": "PADDOCK GATE", "exe": "PADDOCK_GATE.exe", "pyc": "sw_nas_operator.pyc",
                    "home_env": "SW_NAS_OPERATOR_HOME", "internal": "PADDOCK_GATE",
                    "ident": "SEVENTHWELL.SWNASOPERATOR", "icon": "operator.ico"},
    },
}


def transform_app(src, blocks):
    for name in blocks:
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


def transform_rx(src):   # 互換用
    return transform_app(src, APPS["reception"]["blocks"])


def compile_to(src, name, outdir):
    with tempfile.TemporaryDirectory() as td:
        tmp = os.path.join(td, name + ".py")
        open(tmp, "w", encoding="utf-8").write(src)
        pyc = os.path.join(outdir, name + ".pyc")
        py_compile.compile(tmp, cfile=pyc, dfile=name, optimize=2, doraise=True,
                           invalidation_mode=py_compile.PycInvalidationMode.UNCHECKED_HASH)
    return pyc


def build(kind, emb, outdir):
    if sys.version_info[:2] != (3, 13):
        raise SystemExit("同梱Pythonと同じ 3.13 で実行してください（現在 %d.%d）" % sys.version_info[:2])
    app = APPS[kind]
    v = app["variant"]
    top = v["internal"]
    src = open(os.path.join(HERE, app["src"]), encoding="utf-8").read()
    version = re.search(r'^VERSION = "([^"]+)"', src, re.M).group(1)
    os.makedirs(outdir, exist_ok=True)
    with tempfile.TemporaryDirectory() as work:
        pyc_w = compile_to(build_protected.transform(open(SRC_W, encoding="utf-8").read()), "sw_nas_watch", work)
        pyc_a = compile_to(transform_app(src, app["blocks"]), app["mod"], work)
        exe = build_launcher.build(os.path.join(work, v["exe"]), version, v)
        core = build_launcher.build_core(os.path.join(work, build_launcher.core_name(v)), version, v, emb)
        lic = open(os.path.join(HERE, "LICENSE.txt"), encoding="utf-8").read()
        if "PADDOCK SCOUT 利用条件" not in lic:
            raise SystemExit("LICENSE.txt の見出しが想定と違います")
        lic = lic.replace("PADDOCK SCOUT 利用条件", "%s 利用条件" % v["title"], 1)
        out = os.path.join(outdir, "%s_v%s_Windows.zip" % (top, version))
        with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
            def add(name, data, mode=0o644):
                zi = zipfile.ZipInfo(top + "/" + name, date_time=(2026, 10, 10, 12, 0, 0))
                zi.compress_type = zipfile.ZIP_DEFLATED
                zi.external_attr = (stat.S_IFREG | mode) << 16
                z.writestr(zi, data)
            add(v["exe"], open(exe, "rb").read(), 0o755)
            add("runtime/python/" + build_launcher.core_name(v), open(core, "rb").read(), 0o755)
            add("runtime/app/" + v["pyc"], open(pyc_a, "rb").read())
            add("runtime/app/sw_nas_watch.pyc", open(pyc_w, "rb").read())
            add("README.md", open(os.path.join(HERE, app["readme"]), "rb").read())
            add("LICENSE.txt", lic.encode("utf-8"))
            with zipfile.ZipFile(emb) as e:
                for it in e.infolist():
                    add("runtime/python/" + it.filename, e.read(it.filename))
    return out


if __name__ == "__main__":
    if len(sys.argv) != 4 or sys.argv[1] not in APPS:
        raise SystemExit("使い方: python3 build_app.py {%s} <embeddable-python.zip> <出力先フォルダ>" % "|".join(APPS))
    print(build(sys.argv[1], sys.argv[2], sys.argv[3]))
