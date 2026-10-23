"""PADDOCK_SCOUT.exe（起動用ランチャー）をビルドする（SEVENTHWELL 社内用）

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


# 別アプリ（受付アプリなど）のときに差し替える名前。既定（variant=None）は PADDOCK SCOUT のまま
WATCH = {"title": "PADDOCK SCOUT", "exe": "PADDOCK_SCOUT.exe", "pyc": "sw_nas_watch.pyc",
         "home_env": "SW_NAS_WATCH_HOME", "internal": "PADDOCK_SCOUT", "ident": "SEVENTHWELL.SWNASWATCH", "icon": "watch.ico"}


def core_name(v):
    """アプリ名のついた Python 本体の名前（runtime/python/ に置く）"""
    return v["internal"] + "_core.exe"


def build_core(out, version, variant, emb):
    """埋め込み用Python（zip）の DLL 名を見て、アプリ名のついた Python 本体をビルドする"""
    import zipfile
    with zipfile.ZipFile(emb) as z:
        dll = [n for n in z.namelist() if re.fullmatch(r"python3\d+\.dll", n)]
    if len(dll) != 1:
        raise SystemExit("埋め込み用Pythonの DLL が見つかりません: %r" % dll)
    return build(out, version, variant, core=dll[0])


def build(out, version, variant=None, core=None):
    """core=None：起動用ランチャー。core="python313.dll" など：アプリ名のついた Python 本体（host.c）"""
    m = re.fullmatch(r"(\d+)\.(\d+)\.(\d+)", version)
    if not m:
        raise SystemExit("バージョンは x.y.z 形式で指定してください: %r" % version)
    with tempfile.TemporaryDirectory() as td:
        for f in ("launcher.c", "host.c", "app.manifest"):
            shutil.copy(os.path.join(HERE, f), td)
        # アプリごとのアイコン（fresnel で作成。exe/icons/）
        ico = os.path.join(HERE, "icons", (variant or WATCH).get("icon", "watch.ico"))
        shutil.copy(ico, os.path.join(td, "app.ico"))
        rc = open(os.path.join(HERE, "launcher.rc"), encoding="ascii").read()
        rc = (rc.replace("@V1@", m.group(1)).replace("@V2@", m.group(2)).replace("@V3@", m.group(3))
                .replace("@VER@", version))
        v = variant or WATCH
        for k in v:
            if not re.fullmatch(r"[A-Za-z0-9 ._-]+", v[k]):
                raise SystemExit("名前に使えない文字があります: %r" % v[k])
        if variant:
            rc = (rc.replace('"PADDOCK_SCOUT.exe"', '"%s"' % v["exe"]).replace('"PADDOCK_SCOUT"', '"%s"' % v["internal"])
                    .replace('"PADDOCK SCOUT"', '"%s"' % v["title"]))
        if core:
            if not re.fullmatch(r"python3\d+\.dll", core):
                raise SystemExit("DLLの名前が想定と違います: %r" % core)
            rc = rc.replace('"%s"' % v["exe"], '"%s"' % core_name(v), 1)
        man = open(os.path.join(td, "app.manifest"), encoding="utf-8").read()
        man, k = re.subn(r'(<assemblyIdentity\b[^>]*?\bversion=")[\d.]+(")', r"\g<1>%s.0\g<2>" % version, man, count=1)
        if variant:
            man = man.replace('name="SEVENTHWELL.SWNASWATCH"', 'name="%s"' % v["ident"]).replace(
                "<description>PADDOCK SCOUT</description>", "<description>%s</description>" % v["title"])
        if k != 1 or not man.startswith('<?xml version="1.0"'):
            raise SystemExit("manifest のバージョン置換に失敗しました")
        import xml.dom.minidom
        xml.dom.minidom.parseString(man.encode("utf-8"))   # 壊れた manifest だと Windows で起動できないため検査
        open(os.path.join(td, "app.manifest"), "w", encoding="utf-8").write(man)
        open(os.path.join(td, "launcher.rc"), "w", encoding="ascii").write(rc)
        tmp_out = os.path.join(td, "PADDOCK_SCOUT.exe")
        defs = [] if not variant else [
            '-DAPP_TITLE=L"%s"' % v["title"], '-DAPP_PYC=L"%s"' % v["pyc"],
            '-DAPP_EXE=L"%s"' % v["exe"], '-DHOME_ENV=L"%s"' % v["home_env"]]
        defs.append('-DAPP_CORE=L"%s"' % core_name(v))
        if core:   # コンソール用（python.exe と同じ。ランチャーが窓を出さずに起動する）
            cmd = [sys.executable, "-m", "ziglang", "cc", "-target", "x86_64-windows-gnu",
                   "-O2", "-s", "-Wall", "-Wextra", "-Werror", '-DPYDLL=L"%s"' % core,
                   "-municode", "-Wl,--subsystem,console",
                   "host.c", "launcher.rc", "-o", tmp_out, "-lkernel32"]
        else:
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
