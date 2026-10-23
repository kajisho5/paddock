#!/bin/bash
# Mac 版の起動確認（GitHub Actions の macOS ランナーで）：起動・メニューバー・画面・開き直し・終了
set -uo pipefail
cd "$(dirname "$0")/../dist"
mkdir -p ../smoke
fail=0
i=0
for app in "PADDOCK SCOUT" "PADDOCK SADDLE" "PADDOCK GATE"; do
  port=$((8941 + i)); i=$((i + 1))
  data="$HOME/Library/Application Support/${app}"
  echo "=== ${app}（ポート ${port}）"
  open -n "${app}.app" --args --no-browser --port "${port}"
  ok=""
  for t in $(seq 1 90); do curl -fs "http://127.0.0.1:${port}/api/ping" && { ok=1; break; }; sleep 1; done
  echo
  if [ -z "$ok" ]; then
    echo "::error::${app} が起動しない"; cat "${data}/last_run.log" 2>/dev/null; fail=1; continue
  fi
  sleep 4
  if grep -q "メニューバーにアイコンを出しました" "${data}/last_run.log"; then echo "OK メニューバーのアイコン"; else echo "::error::${app}: メニューバーのアイコンが出ていない"; fail=1; fi
  curl -fs "http://127.0.0.1:${port}/" -o /tmp/page.html || true
  if grep -qi "<html" /tmp/page.html; then echo "OK 画面"; else echo "::error::${app}: 画面が返らない"; fail=1; fi
  if ps -axo command | grep -F "${app}.app/Contents/MacOS/" | grep -v grep >/dev/null; then echo "OK アプリ名のプロセスで動いている"; else echo "::warning::${app}: プロセス名を確認できない"; fi
  screencapture -x "../smoke/${app}.png" 2>/dev/null || true
  open "${app}.app"   # Finder から開き直したとき：画面を開く
  sleep 6
  if ps -axo command | grep -F -- "--app=http://127.0.0.1:${port}/" | grep -v grep >/dev/null; then echo "OK 開き直しで画面が開いた"; else echo "::warning::${app}: 開き直しで画面が開いたか確認できない"; fi
  screencapture -x "../smoke/${app}-reopen.png" 2>/dev/null || true
  curl -fs -X POST -H "X-SW-Handover: 0.0.0" "http://127.0.0.1:${port}/api/handover"; echo
  for t in $(seq 1 20); do curl -fs "http://127.0.0.1:${port}/api/ping" >/dev/null 2>&1 || break; sleep 1; done
  sleep 3
  if ps -axo command | grep -F "${app}.app/Contents/MacOS/" | grep -v grep >/dev/null; then echo "::error::${app} が終了しない"; fail=1; else echo "OK 終了"; fi
  cp "${data}/last_run.log" "../smoke/${app}.log" 2>/dev/null || true
  pkill -f -- "--app=http://127.0.0.1:${port}/" 2>/dev/null || true
  sleep 1
done
# GATE の Mac での開き方（PowerPoint・Keynote が無いランナーでは、スライドショーは「見つからない」と知らせること）
cd ..
PY="$PWD/build/mac-python/bin/python3.13"
[ -x "$PY" ] || { echo "（Python が無いため、GATE の開き方の確認は省きます）"; exit $fail; }
"$PY" - <<'PY' || fail=1
import os, sys, tempfile
sys.path.insert(0, os.getcwd())
import sw_nas_operator as O
d = tempfile.mkdtemp()
p = os.path.join(d, "架空の発表.pptx")
open(p, "wb").write(b"x")
try:
    O.mac_open(p, "show")
    print("OK スライドショー（PowerPoint か Keynote がある）")
except ValueError as e:
    print("OK スライドショー：", e)
O.mac_open(d, "file")
print("OK フォルダを開く")
PY
exit $fail
