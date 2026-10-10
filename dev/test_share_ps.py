"""共有のワンボタン設定スクリプト（sw_nas_operator.SHARE_PS）の動作確認
Linux の pwsh＋模擬環境（mock_harness.ps1）で動かす。Windows の実機での確認ではない。"""
import copy
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import sw_nas_operator  # noqa: E402  スクリプトの本体は sw_nas_operator.SHARE_PS（ここで書き出して使う）

PWSH = "/home/claude/tools/pwsh/pwsh"
SCRIPT = os.path.join(tempfile.mkdtemp(prefix="swshare_"), "share_setup.ps1")
open(SCRIPT, "w", encoding="utf-8-sig").write(sw_nas_operator.SHARE_PS)
HARNESS = os.path.join(HERE, "mock_harness.ps1")
SCHEME = "381b4222-f694-41f0-9685-ff5bb260df2e"

BASE = {
    "fw": {"Other-Rule": {"Group": "@FirewallAPI.dll,-28502", "Profile": "Private"}},
    "fwproducts": [], "fwgpo": [], "openfiles": [], "admins": ["Administrator", "架空オペレーター"], "autologon": "架空オペレーター",
    "svc": {"LanmanServer": {"StartMode": "Manual", "State": "Stopped"},
            "LanmanWorkstation": {"StartMode": "Auto", "State": "Running"},
            "FDResPub": {"StartMode": "Manual", "State": "Stopped"},
            "fdPHost": {"StartMode": "Manual", "State": "Running"}},
    "smb2": True, "users": {}, "users_group": ["架空オペレーター"], "shares": {}, "acl": [], "folders": [], "seq": 0,
    "scheme": SCHEME, "power": {SCHEME: {"STANDBYIDLE": 1800, "HIBERNATEIDLE": 3600}, "a1841308-3541-4fab-bc81-f71556f20b4a": {"STANDBYIDLE": 600, "HIBERNATEIDLE": 0}},
    "removable": [], "fail": [], "netcats": ["Public"], "untrusted": False, "explicit_ace": [],
}
FAILS = []


def check(name, cond, extra=""):
    print(("  OK  " if cond else "  NG  ") + name + (("  " + str(extra)) if extra and not cond else ""))
    if not cond:
        FAILS.append(name)


def recdir(td):
    return os.path.join(td, "PD", "SEVENTHWELL", "SW_NAS_OPERATOR")


def run(state, td, action, **kw):
    sp = os.path.join(td, "state.json")
    json.dump(state, open(sp, "w", encoding="utf-8"), ensure_ascii=False)
    params = {"job_id": "j1", "action": action, "folder": "D:\\発表データ", "share": "発表データ", "user": "share", "password": "share",
              "nosleep": True, "set_password": False, "wifi": False, "current_user": "架空オペレーター"}
    params.update(kw)
    pf = os.path.join(td, "params.json")
    json.dump(params, open(pf, "w", encoding="utf-8"), ensure_ascii=False)
    r = subprocess.run([PWSH, "-NoProfile", "-NonInteractive", "-File", HARNESS, "-Script", SCRIPT, "-State", sp, "-PF", pf,
                        "-PD", os.path.join(td, "PD")], capture_output=True, text=True, cwd=td, timeout=120)
    if r.returncode != 0:
        print(r.stdout[-2000:], r.stderr[-3000:])
        raise SystemExit("harness failed")
    res = json.load(open(os.path.join(recdir(td), "result.json"), encoding="utf-8"))
    st = json.load(open(sp, encoding="utf-8"))
    rp = os.path.join(recdir(td), "share_setup.json")
    rec = json.load(open(rp, encoding="utf-8")) if os.path.exists(rp) else None
    check("param file deleted / result id", not os.path.exists(pf) and res["id"] == "j1")
    return res, st, rec


def steps(res):
    return {s["key"]: s for s in res["steps"]}


def show(res):
    for s in res["steps"]:
        print("     %-12s %-3s %s" % (s["key"], {True: "ok", False: "NG", None: "-"}[s["ok"]], s["msg"][:110]))


def mine(st):
    return sorted(k for k in st["fw"] if k.startswith("SWNAS"))


def scenario_fresh():
    print("== 1. 何もないPCで設定 → もう一度 → 元に戻す")
    with tempfile.TemporaryDirectory() as td:
        res, st, rec = run(copy.deepcopy(BASE), td, "setup")
        show(res)
        check("setup ok", res["ok"] is True)
        check("6 own fw rules, other untouched", mine(st) == sorted(["SWNAS-SMB-TCP-445", "SWNAS-NB-TCP-139", "SWNAS-NB-UDP-137", "SWNAS-NB-UDP-138",
                                                                       "SWNAS-LLMNR-UDP-5355", "SWNAS-ICMPv4-Echo"]) and "Other-Rule" in st["fw"])
        check("rules: Profile Any, Wired only, LocalSubnet", all(v["Profile"] == "Any" and v["InterfaceType"] == "Wired" and v["RemoteAddress"] in ("LocalSubnet", ["LocalSubnet"])
                                                                for k, v in st["fw"].items() if k.startswith("SWNAS")))
        check("no network category cmdlets used", not any("NetConnectionProfile" in c for c in st["calls"]))
        check("services auto+running", all(st["svc"][n]["StartMode"] == "Auto" and st["svc"][n]["State"] == "Running" for n in st["svc"]))
        u = st["users"].get("share", {})
        check("user created with our description, in Users", u.get("Password") == "share" and u.get("Description") == "SW NAS OPERATOR file sharing" and "share" in st["users_group"])
        check("share created", st["shares"].get("発表データ", {}).get("Path") == "D:\\発表データ" and "MAIN-PC\\share" in st["shares"]["発表データ"]["Access"]
              and st["shares"]["発表データ"]["CachingMode"] == "None")
        sid = u.get("SID")
        check("acl granted by SID", st["acl"] == ["D:\\発表データ|*%s:(OI)(CI)M" % sid])
        check("power 0 on active scheme", st["power"][SCHEME] == {"STANDBYIDLE": 0, "HIBERNATEIDLE": 0})
        check("record dir protected", "protect-recdir" in st["calls"])
        check("record: services prev", sorted((s["name"], s["start"]) for s in rec["services"]) == [("FDResPub", "Manual"), ("LanmanServer", "Manual"), ("fdPHost", "Manual")])
        check("record: user sid/created, share/folder created, acl sid", rec["user"]["created"] is True and rec["user"]["sid"] == sid and rec["share"]["created"] is True
              and rec["folder"]["created"] is True and rec["acl"] == {"path": "D:\\発表データ", "sid": sid, "orig": None})
        check("record: power with scheme", rec["power"] == [{"scheme": SCHEME, "standby_ac": 1800, "hibernate_ac": 3600}])
        check("account expires in 30 days, share has our description", bool(u.get("Expires")) and st["shares"]["発表データ"]["Description"] == "SW NAS OPERATOR")
        rec1 = rec
        st["scheme"] = "a1841308-3541-4fab-bc81-f71556f20b4a"   # 電源プランを切り替えてから、もう一度
        res, st, rec = run(st, td, "setup", password="share2")
        check("2nd setup ok, record prev values kept", res["ok"] is True and rec["services"] == rec1["services"] and rec["power"][0] == rec1["power"][0]
              and rec["user"]["created"] is True)
        check("2nd: new power plan also recorded and set", len(rec["power"]) == 2 and st["power"]["a1841308-3541-4fab-bc81-f71556f20b4a"]["STANDBYIDLE"] == 0)
        check("2nd: own account password updated", st["users"]["share"]["Password"] == "share2")
        check("2nd: acl once, share access once", len(st["acl"]) == 1 and st["shares"]["発表データ"]["Access"].count("MAIN-PC\\share") == 1)
        # 開いているファイルがあると元に戻さない
        st["openfiles"] = ["D:\\発表データ\\第1会場\\S01\\001 架空演者A\\発表.pptx"]
        res, st, rec = run(st, td, "undo")
        check("undo refused while files open, nothing changed", res["ok"] is False and "open" in steps(res) and bool(st["shares"]) and bool(mine(st)) and rec is not None)
        st["openfiles"] = []
        res, st, rec = run(st, td, "undo")
        show(res)
        check("undo ok", res["ok"] is True)
        check("undo: own fw rules removed, other kept", list(st["fw"]) == ["Other-Rule"])
        check("undo: start modes restored, running not stopped", st["svc"]["LanmanServer"] == {"StartMode": "Manual", "State": "Running"})
        check("undo: user removed", "share" not in st["users"] and "share" not in st["users_group"])
        check("undo: share removed, acl removed", st["shares"] == {} and st["acl"] == [])
        check("undo: power restored (both plans)", st["power"][SCHEME] == {"STANDBYIDLE": 1800, "HIBERNATEIDLE": 3600}
              and st["power"]["a1841308-3541-4fab-bc81-f71556f20b4a"] == {"STANDBYIDLE": 600, "HIBERNATEIDLE": 0})
        check("undo: folder kept", "D:\\発表データ" in st["folders"])
        check("undo: record renamed", rec is None and any(f.startswith("share_setup.undone-") for f in os.listdir(recdir(td))))
        res, st, rec = run(st, td, "undo")
        check("undo again: no record → not ok", res["ok"] is False and steps(res)["undo"]["ok"] is False)


def scenario_accounts():
    print("== 2. 既存のアカウント（管理者・ログイン中・自動ログオン・ふつう）と共有名の衝突")
    for name, users, extra, expect in [
        ("admin", {"share": {"Enabled": True, "Password": "x", "Description": "", "SID": "S-1-5-21-9-9-9-500"}}, {"admins": ["share"]}, "管理者"),
        ("current", {"架空オペレーター": {"Enabled": True, "Password": "x", "Description": "", "SID": "S-1-5-21-9-9-9-1001"}}, {}, "ログイン"),
        ("autologon", {"会場PC": {"Enabled": True, "Password": "x", "Description": "", "SID": "S-1-5-21-9-9-9-1002"}}, {"autologon": "会場PC", "admins": []}, "ログイン"),
    ]:
        with tempfile.TemporaryDirectory() as td:
            base = copy.deepcopy(BASE)
            base["users"] = users
            base.update(extra)
            uname = list(users)[0]
            res, st, rec = run(base, td, "setup", user=uname, set_password=True)
            check("%s account refused before any change" % name, res["ok"] is False and any(expect in s["msg"] for s in res["steps"])
                  and not mine(st) and st["users"][uname]["Password"] == "x" and rec is None, [s["msg"] for s in res["steps"]])
    with tempfile.TemporaryDirectory() as td:
        base = copy.deepcopy(BASE)
        base["users"] = {"share": {"Enabled": False, "Password": "前からの", "Description": "", "SID": "S-1-5-21-9-9-9-1003"}}
        base["shares"] = {"発表データ": {"Path": "E:\\別のフォルダ", "Access": ["Everyone"], "CachingMode": "Manual"}}
        res, st, rec = run(base, td, "setup")
        check("share name conflict → nothing changed", res["ok"] is False and not mine(st) and rec is None)
        res, st, rec = run(st, td, "setup", share="発表データ2")
        check("existing normal account: password unchanged, enabled, added to Users", st["users"]["share"]["Password"] == "前からの"
              and st["users"]["share"]["Enabled"] is True and "share" in st["users_group"])
        res, st, rec = run(st, td, "undo")
        check("undo: account kept, disabled again, removed from Users", "share" in st["users"] and st["users"]["share"]["Enabled"] is False and "share" not in st["users_group"])
        check("undo: other share untouched", st["shares"] == {"発表データ": {"Path": "E:\\別のフォルダ", "Access": ["Everyone"], "CachingMode": "Manual"}})


def scenario_existing_share_same_folder():
    print("== 3. 同じフォルダがすでに同じ共有名で共有されている")
    with tempfile.TemporaryDirectory() as td:
        base = copy.deepcopy(BASE)
        base["shares"] = {"発表データ": {"Path": "D:\\発表データ", "Access": ["Everyone"], "CachingMode": "Manual"}}
        base["folders"] = ["D:\\発表データ"]
        res, st, rec = run(base, td, "setup", nosleep=False, wifi=True)
        check("granted to account", "MAIN-PC\\share" in st["shares"]["発表データ"]["Access"] and rec["share"]["granted"] == "MAIN-PC\\share" and rec["share"]["created"] is False)
        check("wifi option → InterfaceType Any", all(v["InterfaceType"] == "Any" for k, v in st["fw"].items() if k.startswith("SWNAS")))
        check("no power change when off", st["power"][SCHEME] == {"STANDBYIDLE": 1800, "HIBERNATEIDLE": 3600} and not rec.get("power"))
        res, st, rec = run(st, td, "undo")
        check("undo: share kept, access revoked", st["shares"]["発表データ"]["Access"] == ["Everyone"])


def scenario_failures():
    print("== 4. 失敗するとき")
    with tempfile.TemporaryDirectory() as td:
        base = copy.deepcopy(BASE)
        base["fail"] = ["newuser"]
        res, st, rec = run(base, td, "setup")
        S = steps(res)
        check("user fails → share skipped, other changes recorded", S["user"]["ok"] is False and S["share"]["ok"] is False and st["shares"] == {}
              and rec.get("firewall") is True)
        res, st, rec = run(st, td, "undo")
        check("undo after partial", res["ok"] is True and not mine(st))
    with tempfile.TemporaryDirectory() as td:
        base = copy.deepcopy(BASE)
        base["fail"] = ["newshare"]
        res, st, rec = run(base, td, "setup")
        show(res)
        check("non-terminating New-SmbShare error → reported as failure", steps(res)["share"]["ok"] is False and res["ok"] is False and st["shares"] == {})
        st["fail"] = []
        res, st, rec = run(st, td, "undo")
        check("undo after failed share ok", res["ok"] is True and "share" not in st["users"])
    with tempfile.TemporaryDirectory() as td:
        base = copy.deepcopy(BASE)
        res, st, rec = run(base, td, "setup")
        st["fail"] = ["fwremove"]
        res, st, rec = run(st, td, "undo")
        check("non-terminating fw removal error → undo not ok, record kept", res["ok"] is False and steps(res)["firewall"]["ok"] is False and rec is not None)
        st["fail"] = []
        res, st, rec = run(st, td, "undo")
        check("retry undo ok", res["ok"] is True and not mine(st) and rec is None)
    with tempfile.TemporaryDirectory() as td:
        base = copy.deepcopy(BASE)
        base["removable"] = ["E"]
        for folder, why in (("E:\\発表データ", "removable"), ("relative\\path", "relative"), ("C:\\Windows\\temp", "windows dir"),
                            ("C:\\Program Files\\x", "program files"), ("C:\\Users", "users root"), ("C:\\", "drive root")):
            res, st, rec = run(base, td, "setup", folder=folder)
            check("%s refused before any change" % why, res["ok"] is False and rec is None and not mine(st))
    with tempfile.TemporaryDirectory() as td:
        base = copy.deepcopy(BASE)
        base["fwgpo"] = ["Domain"]   # ドメインのプロファイルだけ方針で無効（いまはパブリックにつながっている）→ 問題にしない
        res, st, rec = run(base, td, "setup")
        check("GPO on inactive profile ignored", "firewall_gpo" not in steps(res) and res["ok"] is True)
    with tempfile.TemporaryDirectory() as td:
        base = copy.deepcopy(BASE)
        base["fwgpo"] = ["Public"]
        base["fwproducts"] = ["架空セキュリティ 2030"]
        res, st, rec = run(base, td, "setup")
        S = steps(res)
        check("GPO blocks local rules → warned", S["firewall_gpo"]["ok"] is False and res["ok"] is False)
        check("3rd party firewall hint", S["firewall3"]["ok"] is None and "架空セキュリティ" in S["firewall3"]["msg"])


def scenario_tampered_record():
    print("== 5. 書き換えられた記録で［元に戻す］")
    with tempfile.TemporaryDirectory() as td:
        base = copy.deepcopy(BASE)
        base["users"] = {"Administrator": {"Enabled": True, "Password": "x", "Description": "Built-in", "SID": "S-1-5-21-9-9-9-500"}}
        base["shares"] = {"C$": {"Path": "C:\\", "Access": [], "CachingMode": "None"}}
        os.makedirs(recdir(td))
        json.dump({"version": 2, "services": [{"name": "LanmanWorkstation", "start": "Disabled"}, {"name": "WinDefend", "start": "Disabled"},
                                              {"name": "LanmanServer", "start": "Bogus"}],
                   "user": {"name": "Administrator", "sid": "S-1-5-21-9-9-9-500", "created": True},
                   "share": {"name": "C$", "path": "D:\\x", "created": True},
                   "acl": {"path": "C:\\Windows", "sid": "S-1-5-32-545"}},
                  open(os.path.join(recdir(td), "share_setup.json"), "w", encoding="utf-8"))
        res, st, rec = run(base, td, "undo")
        show(res)
        check("services not touched (workstation/bogus/other)", st["svc"]["LanmanWorkstation"]["StartMode"] == "Auto" and st["svc"]["LanmanServer"]["StartMode"] == "Manual"
              and not any(c.startswith("Set-Service") for c in st["calls"]))
        check("other account not deleted", "Administrator" in st["users"])
        check("other share not removed", "C$" in st["shares"])
        check("acl outside folder not touched", not any(c.startswith("icacls C:\\Windows") for c in st["calls"]))


def scenario_more():
    print("== 6. 相手のPCのIPだけ許可・信用できない記録・元の権限・作った共有と違う・Serverが止まっている")
    with tempfile.TemporaryDirectory() as td:
        res, st, rec = run(copy.deepcopy(BASE), td, "setup", peer_ips=["192.0.2.12", "bad", "192.0.2.13"])
        check("rules scoped to peer IPs", all(v["RemoteAddress"] == ["192.0.2.12", "192.0.2.13"] for k, v in st["fw"].items() if k.startswith("SWNAS")),
              [v.get("RemoteAddress") for v in st["fw"].values()])
        st["untrusted"] = True
        res, st, rec = run(st, td, "undo")
        check("untrusted record moved aside, nothing undone", res["ok"] is False and bool(st["shares"])
              and any(f.startswith("share_setup.untrusted-") for f in os.listdir(recdir(td))))
    with tempfile.TemporaryDirectory() as td:
        base = copy.deepcopy(BASE)
        base["users"] = {"share": {"Enabled": True, "Password": "share", "Description": "", "SID": "S-1-5-21-9-9-9-1100"}}
        base["folders"] = ["D:\\発表データ"]
        base["explicit_ace"] = ["D:\\発表データ"]
        res, st, rec = run(base, td, "setup")
        check("pre-existing ACE → original access SDDL recorded", rec["acl"]["orig"] == "D:(A;OICI;0x1200a9;;;S-1-5-21-9)")
        st["shares"]["発表データ"]["Description"] = "誰かが作り直した"
        st["svc"]["LanmanServer"]["State"] = "Stopped"
        res, st, rec = run(st, td, "undo")
        show(res)
        check("undo: original folder access restored", any(c.startswith("restore-acl D:\\発表データ") for c in st["calls"]))
        check("undo: share with other description kept", "発表データ" in st["shares"])
        check("undo: LanmanServer started first", "Start-Service LanmanServer" in st["calls"])
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(recdir(td))
        json.dump({"version": 1, "firewall": True}, open(os.path.join(recdir(td), "share_setup.json"), "w"))
        base = copy.deepcopy(BASE)
        base["fw"]["SWNAS-SMB-TCP-445"] = {"Group": "SW NAS OPERATOR"}
        res, st, rec = run(base, td, "undo")
        check("old record version → refused, nothing changed", res["ok"] is False and "SWNAS-SMB-TCP-445" in st["fw"])
        res, st, rec = run(base, td, "setup")
        check("old record version → setup refused", res["ok"] is False and not any(c.startswith("New-") for c in st["calls"]))


scenario_fresh()
scenario_accounts()
scenario_existing_share_same_folder()
scenario_failures()
scenario_tampered_record()
scenario_more()
print("\nFAILED:", FAILS if FAILS else "none")
sys.exit(1 if FAILS else 0)
