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


def build(out, version):
    m = re.fullmatch(r"(\d+)\.(\d+)\.(\d+)", version)
    if not m:
        raise SystemExit("バージョンは x.y.z 形式で指定してください: %r" % version)
    with tempfile.TemporaryDirectory() as td:
        for f in ("launcher.c", "app.ico", "app.manifest"):
            shutil.copy(os.path.join(HERE, f), td)
        rc = open(os.path.join(HERE, "launcher.rc"), encoding="ascii").read()
        rc = (rc.replace("@V1@", m.group(1)).replace("@V2@", m.group(2)).replace("@V3@", m.group(3))
                .replace("@VER@", version))
        man = open(os.path.join(td, "app.manifest"), encoding="utf-8").read()
        man, k = re.subn(r'(<assemblyIdentity\b[^>]*?\bversion=")[\d.]+(")', r"\g<1>%s.0\g<2>" % version, man, count=1)
        if k != 1 or not man.startswith('<?xml version="1.0"'):
            raise SystemExit("manifest のバージョン置換に失敗しました")
        import xml.dom.minidom
        xml.dom.minidom.parseString(man.encode("utf-8"))   # 壊れた manifest だと Windows で起動できないため検査
        open(os.path.join(td, "app.manifest"), "w", encoding="utf-8").write(man)
        open(os.path.join(td, "launcher.rc"), "w", encoding="ascii").write(rc)
        tmp_out = os.path.join(td, "SW_NAS_WATCH.exe")
        cmd = [sys.executable, "-m", "ziglang", "cc", "-target", "x86_64-windows-gnu",
               "-O2", "-s", "-Wall", "-Wextra", "-Werror",
               "-Wl,--subsystem,console",
               "launcher.c", "launcher.rc", "-o", tmp_out, "-lkernel32", "-luser32"]
        subprocess.run(cmd, cwd=td, check=True)
        os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
        shutil.copy(tmp_out, out)
    return out


if __name__ == "__main__":
    print(build(sys.argv[1], sys.argv[2]))
