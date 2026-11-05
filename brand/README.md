# アイコンとロゴ（PADDOCK SCOUT / SADDLE / GATE）

fresnel（kajisho5/fresnel, fresnel-icon 0.2.2）で作成。Apple HIG の App icons に沿った作り。

- 1024×1024 の正方形、角丸なし（角丸はOS・書き出し時に付く）。背景グラデーション＋前景2グループ（蹄鉄／アプリごとの記号）
- 影・ハイライト・ぼかしは描かない（Liquid Glass がシステム側で付ける）。文字なし
- 記号は「パレードリング」：パドック（下見所）の周回路と、その切れ目から出ていく1頭（点）。3アプリ共通の形で、色で見分ける（SCOUT＝青、SADDLE＝緑、GATE＝濃紺に緑の点）。ファイル名の watch / reception / operator はそれぞれ SCOUT / SADDLE / GATE
- 記号の形は `src/make_mark.py` で作る（256 の枠。輪の太さ 36・点の半径 18・切れ目は上の辺の中央）。1色の記号とロゴは `logo/paddock_*`
- Default / Dark / Mono（Tinted）を設定済み。`fresnel validate --strict` で問題なし

| フォルダ | 中身 |
|---|---|
| `src/` | レイヤーの SVG と spec.json（`npx fresnel-icon build src/watch.spec.json -o watch.icon`）。Mono は `fresnel set … --appearance tinted` で追加 |
| `icons/` | `.icon`（Icon Composer 形式）、`.icns`、1024px PNG（default / dark）、外観一覧 `*_sheet.png` |
| `logo/` | ロックアップ（アイコン＋ワードマーク。文字は Inter Display SemiBold をアウトライン化）。`_light` は明るい背景用、`_dark` は暗い背景用 |
| `../exe/icons/` | exe に埋め込む Windows 用 `.ico`（16〜256px） |

ロゴの使い方：
- 周りの余白は、点の直径（記号の幅の約 1/7）以上。記号は 16px まで、記号＋文字は高さ 24px 以上で使う
- 色：明るい背景は #1D1D1F、暗い背景は #F5F5F7。点だけ緑（#22C463〜#5CF09A）にしてよい。輪と点の位置・太さは変えない、傾けない、影や縁取りを足さない
- `social-preview.png`（1280×640）は GitHub のリポジトリの Social preview 用
