"""PADDOCK の Mac 版（.app）を作る（macOS で、同梱する Python 3.13 自身で実行する）

  <python>/bin/python3.13 mac/build_mac.py <watch|reception|operator> <python のフォルダ> <出力先フォルダ>

・mac/fetch_python.py で用意した universal の Python を .app/Contents/Resources/python に入れる
・アプリは Windows 版と同じく .pyc（画面の部分は圧縮・符号化）で入れる
・本体（Contents/MacOS/<アプリ>）は mac/host.c を universal でビルドする
・署名：環境変数 RW_IDENTITY（runway の mac-notarize が入れる Developer ID）があればそれで、無ければ仮の署名（ad-hoc）
  中の実行ファイル（.so・.dylib・python）はここで署名する。.app 全体は runway が最後に署名する（ad-hoc のときはここで）
"""
import os
import plistlib
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TOP = os.path.dirname(HERE)
sys.path.insert(0, TOP)
sys.path.insert(0, os.path.join(TOP, "exe"))
import build_app  # noqa: E402
import build_protected  # noqa: E402

APPS = {
    "watch": {"title": "PADDOCK SCOUT", "internal": "PADDOCK_SCOUT", "src": "sw_nas_watch.py", "pyc": "sw_nas_watch.pyc",
              "home_env": "SW_NAS_WATCH_HOME", "icon": "watch", "bundle": "com.seventhwell.paddock.scout"},
    "reception": {"title": "PADDOCK SADDLE", "internal": "PADDOCK_SADDLE", "src": "sw_nas_reception.py", "pyc": "sw_nas_reception.pyc",
                  "home_env": "SW_NAS_RECEPTION_HOME", "icon": "reception", "bundle": "com.seventhwell.paddock.saddle"},
    "operator": {"title": "PADDOCK GATE", "internal": "PADDOCK_GATE", "src": "sw_nas_operator.py", "pyc": "sw_nas_operator.pyc",
                 "home_env": "SW_NAS_OPERATOR_HOME", "icon": "operator", "bundle": "com.seventhwell.paddock.gate"},
}
MINOR = "3.13"


def is_macho(p):
    try:
        with open(p, "rb") as f:
            m = f.read(4)
    except OSError:
        return False
    return m in (b"\xcf\xfa\xed\xfe", b"\xce\xfa\xed\xfe", b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca")


def version_of(src):
    return re.search(r'^VERSION = "([^"]+)"', open(os.path.join(TOP, src), encoding="utf-8").read(), re.M).group(1)


def sign(path, ident, entitlements=None):
    cmd = ["codesign", "--force", "--sign", ident]
    if ident != "-":
        cmd += ["--timestamp", "--options", "runtime"]
    else:
        cmd += ["--options", "runtime"]
    if entitlements:
        cmd += ["--entitlements", entitlements]
    subprocess.run(cmd + [path], check=True, capture_output=True)


def build(kind, pyroot, outdir):
    if sys.version_info[:2] != (3, 13):
        raise SystemExit("同梱する Python 3.13 で実行してください（現在 %d.%d）" % sys.version_info[:2])
    a = APPS[kind]
    version = version_of(a["src"])
    app = os.path.join(outdir, a["title"] + ".app")
    if os.path.exists(app):
        shutil.rmtree(app)
    c = os.path.join(app, "Contents")
    res = os.path.join(c, "Resources")
    os.makedirs(os.path.join(c, "MacOS"))
    os.makedirs(os.path.join(res, "app"))
    # アプリ（.pyc）
    src_w = open(os.path.join(TOP, "sw_nas_watch.py"), encoding="utf-8").read()
    build_app.compile_to(build_protected.transform(src_w), "sw_nas_watch", os.path.join(res, "app"))
    if kind != "watch":
        conf = build_app.APPS[kind]
        src = open(os.path.join(TOP, conf["src"]), encoding="utf-8").read()
        build_app.compile_to(build_app.transform_app(src, conf["blocks"]), conf["mod"], os.path.join(res, "app"))
    # Python
    shutil.copytree(pyroot, os.path.join(res, "python"), symlinks=True)
    pylib = "libpython%s.dylib" % MINOR
    if not os.path.isfile(os.path.join(res, "python", "lib", pylib)):
        print("※ %s が無いため、python を直接動かす形になります" % pylib)
    # アイコン・メニューバーのアイコン・説明
    shutil.copy(os.path.join(TOP, "brand", "icons", a["icon"] + ".icns"), os.path.join(res, "AppIcon.icns"))
    shutil.copy(os.path.join(HERE, "menubar_%s.png" % a["icon"]), os.path.join(res, "menubar.png"))
    # 本体
    exe = os.path.join(c, "MacOS", a["internal"])
    subprocess.run(["clang", "-O2", "-Wall", "-Wextra", "-Werror", "-arch", "arm64", "-arch", "x86_64",
                    "-mmacosx-version-min=11.0",
                    '-DAPP_TITLE="%s"' % a["title"], '-DAPP_PYC="%s"' % a["pyc"], '-DHOME_ENV="%s"' % a["home_env"],
                    '-DPYLIB="%s"' % pylib, os.path.join(HERE, "host.c"), "-o", exe], check=True)
    info = {
        "CFBundleName": a["title"], "CFBundleDisplayName": a["title"], "CFBundleIdentifier": a["bundle"],
        "CFBundleExecutable": a["internal"], "CFBundleIconFile": "AppIcon", "CFBundlePackageType": "APPL",
        "CFBundleShortVersionString": version, "CFBundleVersion": version, "CFBundleInfoDictionaryVersion": "6.0",
        "CFBundleDevelopmentRegion": "ja", "LSMinimumSystemVersion": "11.0", "LSUIElement": True,
        "LSMultipleInstancesProhibited": True, "NSHighResolutionCapable": True,
        "NSHumanReadableCopyright": "Copyright (c) 2026 SEVENTHWELL. All rights reserved.",
        "NSAppleEventsUsageDescription": "スライドショーを始めるために PowerPoint・Keynote を操作します。",
        "NSLocalNetworkUsageDescription": "同じネットワークの NAS やバックアップのPCとやりとりします。",
    }
    with open(os.path.join(c, "Info.plist"), "wb") as f:
        plistlib.dump(info, f)
    with open(os.path.join(c, "PkgInfo"), "w") as f:
        f.write("APPL????")
    # 署名：中から外へ
    ident = os.environ.get("RW_IDENTITY") or "-"
    ent = os.path.join(HERE, "entitlements.plist")
    n = 0
    for dp, dns, fns in os.walk(os.path.join(res, "python"), topdown=False):
        for fn in fns:
            p = os.path.join(dp, fn)
            if not os.path.islink(p) and is_macho(p):
                sign(p, ident, ent if os.path.basename(dp) == "bin" else None)
                n += 1
    print("署名した中の実行ファイル: %d（%s）" % (n, "Developer ID" if ident != "-" else "仮の署名"))
    if ident == "-":   # 本番は runway が .app 全体を署名する
        sign(exe, ident, ent)
        sign(app, ident, ent)
        subprocess.run(["codesign", "--verify", "--strict", "--deep", "--verbose=2", app], check=True)
    print(app)
    return app, version


if __name__ == "__main__":
    if len(sys.argv) != 4 or sys.argv[1] not in APPS:
        raise SystemExit("使い方: python3.13 mac/build_mac.py {%s} <python のフォルダ> <出力先フォルダ>" % "|".join(APPS))
    build(sys.argv[1], sys.argv[2], sys.argv[3])
