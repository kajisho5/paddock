"""Mac 版に同梱する Python を用意する（macOS の GitHub Actions ランナーで実行）

  python3 mac/fetch_python.py <出力先フォルダ>

python-build-standalone（astral-sh）の CPython 3.13 を、Apple シリコン用と Intel 用の両方取ってきて、
1つの universal（どちらの Mac でも動く）にまとめる。使わない部分（tkinter・テストなど）は削る。
まとめた実行ファイルは仮の署名（ad-hoc）にしておく（本番の署名は build_mac.py で）。
"""
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request

MINOR = "3.13"
ARCHS = ("aarch64", "x86_64")
REMOVE = [
    "include", "share", "bin/idle3", "bin/idle" + MINOR, "bin/pip", "bin/pip3", "bin/pip" + MINOR,
    "bin/pydoc3", "bin/pydoc" + MINOR, "bin/python3-config", "bin/python" + MINOR + "-config",
    "lib/pkgconfig", "lib/itcl4.2.4", "lib/thread2.8.9", "lib/tcl9", "lib/tk9.0", "lib/tcl8", "lib/tcl8.6", "lib/tk8.6",
    "lib/python%s/test" % MINOR, "lib/python%s/idlelib" % MINOR, "lib/python%s/tkinter" % MINOR,
    "lib/python%s/turtledemo" % MINOR, "lib/python%s/ensurepip" % MINOR, "lib/python%s/lib2to3" % MINOR,
    "lib/python%s/site-packages" % MINOR, "lib/python%s/config-%s-darwin" % (MINOR, MINOR),
    "lib/python%s/__phello__" % MINOR,
]


# 決まった版を使う（毎回同じものを同梱する。更新するときはここを書き換える）
TAG = "20261021"
PYVER = "3.13.17"


def find_assets():
    got = {}
    for arch in ARCHS:
        name = "cpython-%s+%s-%s-apple-darwin-install_only_stripped.tar.gz" % (PYVER, TAG, arch)
        got[arch] = (name, "https://github.com/astral-sh/python-build-standalone/releases/download/%s/%s"
                     % (TAG, name.replace("+", "%2B")))
    return TAG, got


def is_macho(p):
    try:
        with open(p, "rb") as f:
            m = f.read(4)
    except OSError:
        return False
    return m in (b"\xcf\xfa\xed\xfe", b"\xce\xfa\xed\xfe", b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca")


def main():
    out = os.path.abspath(sys.argv[1])
    tag, assets = find_assets()
    print("python-build-standalone %s: %s" % (tag, ", ".join(n for n, _ in assets.values())))
    with tempfile.TemporaryDirectory() as td:
        roots = {}
        for arch in ARCHS:
            name, url = assets[arch]
            tgz = os.path.join(td, name)
            urllib.request.urlretrieve(url, tgz)
            d = os.path.join(td, arch)
            with tarfile.open(tgz) as t:
                t.extractall(d, filter="tar")
            roots[arch] = os.path.join(d, "python")
            for rel in REMOVE:
                p = os.path.join(roots[arch], rel)
                if os.path.islink(p) or os.path.isfile(p):
                    os.remove(p)
                elif os.path.isdir(p):
                    shutil.rmtree(p)
            ld = os.path.join(roots[arch], "lib", "python" + MINOR, "lib-dynload")
            for f in os.listdir(ld):
                if f.startswith("_tkinter") or f.startswith("_test") or f.startswith("xxlimited"):
                    os.remove(os.path.join(ld, f))
        a, b = roots["aarch64"], roots["x86_64"]
        if os.path.exists(out):
            shutil.rmtree(out)
        shutil.copytree(a, out, symlinks=True)
        merged = 0
        for dp, dns, fns in os.walk(out):
            for fn in fns:
                p = os.path.join(dp, fn)
                if os.path.islink(p) or not is_macho(p):
                    continue
                other = os.path.join(b, os.path.relpath(p, out))
                if not os.path.isfile(other):
                    raise SystemExit("Intel 用に無いファイル: %s" % os.path.relpath(p, out))
                tmp = p + ".universal"
                subprocess.run(["lipo", "-create", p, other, "-output", tmp], check=True)
                os.replace(tmp, p)
                subprocess.run(["codesign", "--force", "--sign", "-", p], check=True, capture_output=True)
                merged += 1
        print("universal にまとめた実行ファイル: %d" % merged)
        subprocess.run([os.path.join(out, "bin", "python" + MINOR), "-c",
                        "import sys, ssl, sqlite3, ctypes, zlib; print(sys.version); print(ssl.OPENSSL_VERSION)"], check=True)


if __name__ == "__main__":
    main()
