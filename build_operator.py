"""会場オペレーターアプリ（SW NAS OPERATOR）の配布用ビルド（SEVENTHWELL 社内用）

  python3 build_operator.py <embeddable-python.zip> <出力先フォルダ>

中身は build_app.py（受付・会場オペレーター共通）を参照。
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import build_app  # noqa: E402

if __name__ == "__main__":
    print(build_app.build("operator", sys.argv[1], sys.argv[2]))
