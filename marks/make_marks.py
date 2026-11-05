"""目印画像（演者フォルダに入れる 00_受付済.jpg など）を作る。
PADDOCK SCOUT / SADDLE / GATE が名前で読み取る目印に合わせた一式。
使い方: python3 marks/make_marks.py [出力フォルダ]   （Pillow と Noto Sans CJK JP Bold が必要）"""
import os, sys
from PIL import Image, ImageDraw, ImageFont
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import sw_nas_watch as W

FONT = "/usr/share/fonts/opentype/noto/NotoSansCJK-Bold.ttc"
# (ファイル名, 画像の文字（改行で2行）)
MARKS = [
    ("00_受付済", "受付済"),
    ("01_会場確認済", "会場\n確認済"),
    ("02_事前預り", "事前預り"),
    ("03_会場直", "会場直"),
    ("04_会場取得", "会場取得"),
    ("05_発表終了", "発表終了"),
    ("06_演題取り下げ", "演題\n取り下げ"),
    ("07_演者変更", "演者変更"),
    ("08_データ修正", "データ\n修正"),
    ("09_データなし", "データ\nなし"),
    ("10_読んでください", "読んで\nください"),
    ("11_連絡", "連絡"),
    ("12_動画あり", "動画あり"),
    ("13_音声あり", "音声あり"),
    ("14_発表者ツール使用", "発表者\nツール使用"),
    ("15_PC持込_Win", "PC持込\nWindows"),
    ("16_PC持込_Mac", "PC持込\nMac"),
    ("17_Mac_Keynote", "Mac\nKeynote"),
    ("18_ビデオ持込", "ビデオ\n持込"),
    ("19_リモート登壇", "リモート\n登壇"),
    ("20_Zoom使用", "Zoom\n使用"),
    ("21_アダプター貸出", "アダプター\n貸出"),
    ("22_オペ操作", "オペ操作"),
    ("23_演台持上", "演台\n持ち上げ"),
    ("24_記念品お渡し", "記念品\nお渡し"),
    ("25_記念品お渡し済", "記念品\nお渡し済"),
    ("26_Win_365", "PowerPoint\nWin 365"),
    ("27_Win_2016", "PowerPoint\nWin 2016"),
    ("28_Win_2019", "PowerPoint\nWin 2019"),
    ("29_Mac_365", "PowerPoint\nMac 365"),
    ("30_COIあり", "COIあり"),
]
# 役割ごとの色（背景・文字）と、下に出す区分
ROLE = {
    "recv": ("#1E7BE0", "#FFFFFF", "受付"),
    "got": ("#0E9F8E", "#FFFFFF", "会場で取得"),
    "done": ("#3A4150", "#FFFFFF", "発表済み"),
    "drop": ("#8A8F98", "#FFFFFF", "取り下げ"),
    "direct": ("#7A4CD6", "#FFFFFF", "会場で受け取る"),
    "warn": ("#E0352B", "#FFFFFF", "注意"),
    "op": ("#F08A00", "#FFFFFF", "オペが対応"),
    "info": ("#E9ECF1", "#1D1D1F", "お知らせ"),
}
S = 600

def ring(draw, x, y, s, col):
    """PADDOCK の記号（周回路と1頭）を小さく描く。s は 256 の枠に対する倍率"""
    import re
    d = W.__dict__  # noqa
    ro, T, DR = 68, 36, 18
    def P(a, b): return (x + a * s, y + b * s)
    # 輪：太い線の角丸長円を、切れ目を空けて描く
    w = int(T * s)
    draw.arc([P(12, 60), P(148, 196)], 90, 270, fill=col, width=w)
    draw.arc([P(108, 60), P(244, 196)], 270, 90, fill=col, width=w)
    draw.line([P(80, 196 - T / 2), P(176, 196 - T / 2)], fill=col, width=w)
    for xa, xb in ((80, 82), (174, 176)):
        draw.line([P(xa, 60 + T / 2), P(xb, 60 + T / 2)], fill=col, width=w)
    r = T / 2 * s
    for cx in (82, 174):
        draw.ellipse([x + cx * s - r, y + (60 + T / 2) * s - r, x + cx * s + r, y + (60 + T / 2) * s + r], fill=col)
    r = DR * s
    draw.ellipse([x + 128 * s - r, y + (60 + T / 2) * s - r, x + 128 * s + r, y + (60 + T / 2) * s + r], fill=col)

def fit(draw, text, maxw, maxh):
    for size in range(200, 20, -4):
        f = ImageFont.truetype(FONT, size, index=0)
        b = draw.multiline_textbbox((0, 0), text, font=f, spacing=size * 0.12, align="center")
        if b[2] - b[0] <= maxw and b[3] - b[1] <= maxh:
            return f, b
    return f, b

def make(out):
    os.makedirs(out, exist_ok=True)
    marks = W.compile_marks({"marks": W.DEFAULT_MARKS})
    for fn, label in MARKS:
        m = W.mark_match(marks, fn + ".jpg")
        if not m:
            raise SystemExit("目印として読めない名前: " + fn)
        bg, fg, cat = ROLE[m[0]]
        im = Image.new("RGB", (S, S), bg); dr = ImageDraw.Draw(im)
        f, b = fit(dr, label, S - 90, S - 210)
        tw, th = b[2] - b[0], b[3] - b[1]
        dr.multiline_text(((S - tw) / 2 - b[0], (S - 70 - th) / 2 - b[1]), label, font=f, fill=fg, spacing=f.size * 0.12, align="center")
        cf = ImageFont.truetype(FONT, 34, index=0)
        dr.text((40, S - 78), cat, font=cf, fill=fg)
        ring(dr, S - 40 - 256 * 0.34, S - 40 - 196 * 0.34 + 4, 0.34, fg)
        im.save(os.path.join(out, fn + ".jpg"), quality=90)
    print("%d 枚を作りました: %s" % (len(MARKS), out))

if __name__ == "__main__":
    make(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "目印画像"))
