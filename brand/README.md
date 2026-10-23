# アイコンとロゴ（PADDOCK SCOUT / SADDLE / GATE）

fresnel（kajisho5/fresnel, fresnel-icon 0.2.2）で作成。Apple HIG の App icons に沿った作り。

- 1024×1024 の正方形、角丸なし（角丸はOS・書き出し時に付く）。背景グラデーション＋前景2グループ（蹄鉄／アプリごとの記号）
- 影・ハイライト・ぼかしは描かない（Liquid Glass がシステム側で付ける）。文字なし
- 3アプリ共通の「蹄鉄（PADDOCK＝馬）」の中に、役割の記号を置く：SCOUT（監視）＝目（見るだけ）、SADDLE（受付）＝受け取り（矢印とトレイ）、GATE（会場）＝再生（スライドショー）。ファイル名の watch / reception / operator はそれぞれ SCOUT / SADDLE / GATE
- Default / Dark / Mono（Tinted）を設定済み。`fresnel validate --strict` で問題なし

| フォルダ | 中身 |
|---|---|
| `src/` | レイヤーの SVG と spec.json（`npx fresnel-icon build src/watch.spec.json -o watch.icon`）。Mono は `fresnel set … --appearance tinted` で追加 |
| `icons/` | `.icon`（Icon Composer 形式）、`.icns`、1024px PNG（default / dark）、外観一覧 `*_sheet.png` |
| `logo/` | ロックアップ（アイコン＋ワードマーク。文字は Inter Display SemiBold をアウトライン化）。`_light` は明るい背景用、`_dark` は暗い背景用 |
| `../exe/icons/` | exe に埋め込む Windows 用 `.ico`（16〜256px） |

ロゴの使い方：アイコンの周りに余白を取り、24px 未満ではアイコンだけを使う。文字色は明るい背景で #1D1D1F、暗い背景で #F5F5F7。
