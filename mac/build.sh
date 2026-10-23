#!/bin/bash
# Mac 版の .app を作る（macOS で実行）。使い方: bash mac/build.sh watch reception operator
# 出力: dist/<アプリ名>.app
set -euo pipefail
cd "$(dirname "$0")/.."
PY="$PWD/build/mac-python"
if [ ! -x "$PY/bin/python3.13" ]; then
  python3 mac/fetch_python.py "$PY"
fi
mkdir -p dist
for k in "$@"; do
  "$PY/bin/python3.13" mac/build_mac.py "$k" "$PY" dist
done
