#!/bin/bash
cd "$(dirname "$0")" || exit 1
if command -v python3 >/dev/null 2>&1; then
  exec python3 sw_nas_watch.py "$@"
fi
echo "Python 3 が見つかりません。https://www.python.org/downloads/ からインストールしてください。"
read -r -p "Enterで閉じます"
