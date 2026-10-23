"""SW_NAS_WATCH.exe（起動用ランチャー）をビルドする（SEVENTHWELL 社内用）

  python3 exe/build_launcher.py <出力先.exe> <バージョン 例 1.5.0>

Linux/Mac/Windows どこでも可。コンパイラは zig（pip install ziglang）を使い、
Windows x64 用の exe をクロスコンパイルする。
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


# 別アプリ（受付アプリなど）のときに差し替える名前。既定（variant=None）は SW NAS WATCH のまま
WATCH = {"title": "SW NAS WATCH", "exe": "SW_NAS_WATCH.exe", "pyc": "sw_nas_watch.pyc",
         "home_env": "SW_NAS_WATCH_HOME", "internal": "SW_NAS_WATCH", "ident": "SEVENTHWELL.SWNASWATCH"}


def build(out, version, variant=None):
    m = re.fullmatch(r"(\d+)\.(\d+)\.(\d+)", version)
    if not m:
        raise SystemExit("バージョンは x.y.z 形式で指定してください: %r" % version)
    with tempfile.TemporaryDirectory() as td:
        for f in ("launcher.c", "app.ico", "app.manifest"):
            shutil.copy(os.path.join(HERE, f), td)
        rc = open(os.path.join(HERE, "launcher.rc"), encoding="ascii").read()
        rc = (rc.replace("@V1@", m.group(1)).replace("@V2@", m.group(2)).replace("@V3@", m.group(3))
                .replace("@VER@", version))
        v = variant or WATCH
        for k in v:
            if not re.fullmatch(r"[A-Za-z0-9 ._-]+", v[k]):
                raise SystemExit("名前に使えない文字があります: %r" % v[k])
        if variant:
            rc = (rc.replace('"SW_NAS_WATCH.exe"', '"%s"' % v["exe"]).replace('"SW_NAS_WATCH"', '"%s"' % v["internal"])
                    .replace('"SW NAS WATCH"', '"%s"' % v["title"]))
        man = open(os.path.join(td, "app.manifest"), encoding="utf-8").read()
        man, k = re.subn(r'(<assemblyIdentity\b[^>]*?\bversion=")[\d.]+(")', r"\g<1>%s.0\g<2>" % version, man, count=1)
        if variant:
            man = man.replace('name="SEVENTHWELL.SWNASWATCH"', 'name="%s"' % v["ident"]).replace(
                "<description>SW NAS WATCH</description>", "<description>%s</description>" % v["title"])
        if k != 1 or not man.startswith('<?xml version="1.0"'):
            raise SystemExit("manifest のバージョン置換に失敗しました")
        import xml.dom.minidom
        xml.dom.minidom.parseString(man.encode("utf-8"))   # 壊れた manifest だと Windows で起動できないため検査
        open(os.path.join(td, "app.manifest"), "w", encoding="utf-8").write(man)
        open(os.path.join(td, "launcher.rc"), "w", encoding="ascii").write(rc)
        tmp_out = os.path.join(td, "SW_NAS_WATCH.exe")
        defs = [] if not variant else [
            '-DAPP_TITLE=L"%s"' % v["title"], '-DAPP_PYC=L"%s"' % v["pyc"],
            '-DAPP_EXE=L"%s"' % v["exe"], '-DHOME_ENV=L"%s"' % v["home_env"]]
        cmd = [sys.executable, "-m", "ziglang", "cc", "-target", "x86_64-windows-gnu",
               "-O2", "-s", "-Wall", "-Wextra", "-Werror"] + defs + [
               "-municode", "-Wl,--subsystem,windows",
               "launcher.c", "launcher.rc", "-o", tmp_out, "-lkernel32", "-luser32"]
        subprocess.run(cmd, cwd=td, check=True)
        os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
        shutil.copy(tmp_out, out)
    return out


if __name__ == "__main__":
    print(build(sys.argv[1], sys.argv[2]))
