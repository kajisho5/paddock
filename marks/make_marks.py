"""目印画像（演者フォルダに入れる 00_受付済.jpg など）を作る。
PADDOCK SCOUT / SADDLE / GATE が名前で読み取る目印に合わせた一式。白地に、役割の色の丸と絵、下に文字。
「読んでください」はメモ（.txt に中身を書く）なので画像は作らない。
使い方: python3 marks/make_marks.py [出力フォルダ]   （Pillow と Noto Sans CJK JP Bold が必要）"""
import math, os, sys
from PIL import Image, ImageDraw, ImageFont
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import sw_nas_watch as W

FONT = "/usr/share/fonts/opentype/noto/NotoSansCJK-Bold.ttc"
FONT_R = "/usr/share/fonts/opentype/noto/NotoSansCJK-Medium.ttc"
S = 600          # 仕上がりの大きさ
K = 3            # なめらかに描くための拡大率
ROLE = {          # 役割ごとの色と、下に出す区分
    "recv": ("#1E7BE0", "受付"), "got": ("#0E9F8E", "会場で取得"), "done": ("#3A4150", "発表済み"),
    "drop": ("#8A8F98", "取り下げ"), "direct": ("#7A4CD6", "会場で受け取る"), "warn": ("#E0352B", "注意"),
    "op": ("#E57F00", "オペが対応"), "info": ("#6E7687", "お知らせ"),
}

# ---------------------------------------------------------------- 絵（100×100 の枠に白い線で描く）
class Pen:
    def __init__(self, d, ox, oy, sc, w=7.5):
        self.d, self.ox, self.oy, self.sc, self.w = d, ox, oy, sc, w
    def p(self, x, y): return (self.ox + x * self.sc, self.oy + y * self.sc)
    def dot(self, x, y, r, fill="#fff"):
        cx, cy = self.p(x, y); r *= self.sc; self.d.ellipse([cx - r, cy - r, cx + r, cy + r], fill=fill)
    def L(self, *pts, closed=False):
        q = [self.p(*a) for a in pts] + ([self.p(*pts[0])] if closed else [])
        self.d.line(q, fill="#fff", width=int(self.w * self.sc), joint="curve")
        for a in pts: self.dot(a[0], a[1], self.w / 2)
    def R(self, x0, y0, x1, y1, r=6, fill=False):
        a, b = self.p(x0, y0), self.p(x1, y1)
        if fill: self.d.rounded_rectangle([a, b], r * self.sc, fill="#fff")
        else: self.d.rounded_rectangle([a, b], r * self.sc, outline="#fff", width=int(self.w * self.sc))
    def C(self, x, y, r):
        a, b = self.p(x - r, y - r), self.p(x + r, y + r); self.d.ellipse([a, b], outline="#fff", width=int(self.w * self.sc))
    def A(self, x, y, r, a0, a1):
        a, b = self.p(x - r, y - r), self.p(x + r, y + r); self.d.arc([a, b], a0, a1, fill="#fff", width=int(self.w * self.sc))
    def F(self, *pts): self.d.polygon([self.p(*a) for a in pts], fill="#fff")

def i_check(P): P.L((26, 52), (43, 68), (75, 34))
def i_eye(P):
    r = 39; up = [(50 + r * math.sin(t), 65 - r * math.cos(t)) for t in [math.radians(a) for a in range(-67, 68, 6)]]
    lo = [(50 + r * math.sin(t), 35 + r * math.cos(t)) for t in [math.radians(a) for a in range(67, -68, -6)]]
    P.L(*(up + lo), closed=True); P.dot(50, 50, 10)
def i_inbox(P): P.L((50, 14), (50, 50)); P.L((37, 38), (50, 51), (63, 38)); P.L((18, 58), (18, 82), (82, 82), (82, 58))
def i_door(P): P.R(54, 16, 84, 84, 4); P.L((14, 50), (44, 50)); P.L((32, 37), (45, 50), (32, 63))
def i_download(P): P.L((50, 16), (50, 62)); P.L((32, 45), (50, 63), (68, 45)); P.L((22, 80), (78, 80))
def i_flag(P): P.L((30, 84), (30, 18)); P.F((30, 16), (78, 30), (30, 46))
def i_ban(P): P.C(50, 50, 32); P.L((28, 72), (72, 28))
def i_swap(P): P.L((18, 36), (78, 36)); P.L((64, 22), (78, 36), (64, 50)); P.L((82, 64), (22, 64)); P.L((36, 50), (22, 64), (36, 78))
def i_pencil(P): P.L((26, 74), (64, 36), (74, 46), (36, 84), (24, 86), closed=True); P.L((56, 44), (66, 54))
def i_nofile(P): P.L((28, 16), (58, 16), (74, 32), (74, 84), (28, 84), closed=True); P.L((42, 46), (60, 66)); P.L((60, 46), (42, 66))
def i_bubble(P): P.R(16, 22, 84, 66, 12); P.L((34, 66), (30, 82), (48, 66))
def i_video(P): P.R(14, 26, 86, 74, 10); P.F((42, 38), (42, 62), (63, 50))
def i_speaker(P):
    P.F((16, 40), (32, 40), (50, 24), (50, 76), (32, 60), (16, 60)); P.A(52, 50, 14, -55, 55); P.A(52, 50, 28, -55, 55)
def i_presenter(P): P.R(12, 18, 64, 56, 5); P.L((38, 56), (38, 68)); P.L((26, 70), (50, 70)); P.R(56, 46, 88, 76, 4, fill=True)
def i_laptop(P): P.R(24, 22, 76, 62, 5); P.L((12, 74), (88, 74))
def i_usb(P): P.R(36, 12, 64, 64, 6); P.R(42, 64, 58, 86, 2); P.dot(45, 26, 3.5); P.dot(55, 26, 3.5)
def i_remote(P): P.R(12, 18, 88, 70, 6); P.dot(50, 37, 9); P.A(50, 64, 16, 200, 340); P.L((50, 70), (50, 80)); P.L((34, 84), (66, 84))
def i_camera(P): P.R(12, 30, 64, 70, 9); P.F((68, 44), (88, 32), (88, 68), (68, 56))
def i_plug(P): P.R(30, 38, 70, 68, 8); P.L((42, 18), (42, 38)); P.L((58, 18), (58, 38)); P.L((50, 68), (50, 88))
def i_mouse(P): P.R(30, 14, 70, 86, 20); P.L((50, 16), (50, 38))
def i_podium(P): P.L((22, 46), (78, 46)); P.L((30, 46), (36, 86), (64, 86), (70, 46)); P.L((50, 8), (50, 32)); P.L((38, 20), (50, 8), (62, 20))
def i_gift(P): P.R(22, 44, 78, 84, 4); P.R(16, 32, 84, 46, 4); P.L((50, 32), (50, 84)); P.C(41, 23, 7); P.C(59, 23, 7)
def i_gift_ok(P): i_gift(P); P.dot(80, 80, 15, fill=P.bg); P.L((72, 80), (78, 86), (89, 73))
def i_slide(P): P.R(12, 16, 88, 66, 5); P.L((50, 66), (50, 78)); P.L((36, 88), (50, 78), (64, 88)); P.R(26, 44, 34, 56, 1, fill=True); P.R(42, 34, 50, 56, 1, fill=True); P.R(58, 26, 66, 56, 1, fill=True)
def i_doc(P): P.L((28, 16), (58, 16), (74, 32), (74, 84), (28, 84), closed=True); P.L((40, 48), (62, 48)); P.L((40, 62), (62, 62))

MARKS = [   # (ファイル名, 文字, 絵)
    ("00_受付済", "受付済", i_check),
    ("01_会場確認済", "会場確認済", i_eye),
    ("02_事前預り", "事前預り", i_inbox),
    ("03_会場直", "会場直", i_door),
    ("04_会場取得", "会場取得", i_download),
    ("05_発表終了", "発表終了", i_flag),
    ("06_演題取り下げ", "演題取り下げ", i_ban),
    ("07_演者変更", "演者変更", i_swap),
    ("08_データ修正", "データ修正", i_pencil),
    ("09_データなし", "データなし", i_nofile),
    ("11_連絡", "連絡", i_bubble),
    ("12_動画あり", "動画あり", i_video),
    ("13_音声あり", "音声あり", i_speaker),
    ("14_発表者ツール使用", "発表者ツール", i_presenter),
    ("15_PC持込_Win", "PC持込 Win", i_laptop),
    ("16_PC持込_Mac", "PC持込 Mac", i_laptop),
    ("17_Mac_Keynote", "Mac Keynote", i_laptop),
    ("18_ビデオ持込", "ビデオ持込", i_usb),
    ("19_リモート登壇", "リモート登壇", i_remote),
    ("20_Zoom使用", "Zoom使用", i_camera),
    ("21_アダプター貸出", "アダプター貸出", i_plug),
    ("22_オペ操作", "オペ操作", i_mouse),
    ("23_演台持上", "演台持ち上げ", i_podium),
    ("24_記念品お渡し", "記念品お渡し", i_gift),
    ("25_記念品お渡し済", "記念品お渡し済", i_gift_ok),
    ("26_Win_365", "PPT Win 365", i_slide),
    ("27_Win_2016", "PPT Win 2016", i_slide),
    ("28_Win_2019", "PPT Win 2019", i_slide),
    ("29_Mac_365", "PPT Mac 365", i_slide),
    ("30_COIあり", "COIあり", i_doc),
]

def fit(d, text, maxw, maxh, font=FONT):
    for size in range(110 * K, 20, -2 * K):
        f = ImageFont.truetype(font, size, index=0)
        b = d.textbbox((0, 0), text, font=f)
        if b[2] - b[0] <= maxw and b[3] - b[1] <= maxh:
            return f, b
    return f, b

def ring(d, x, y, s, col):
    """PADDOCK の記号（周回路と1頭）を小さく"""
    ro, T, DR = 68, 36, 18; w = int(T * s)
    P = lambda a, b: (x + a * s, y + b * s)
    d.arc([P(12, 60), P(148, 196)], 90, 270, fill=col, width=w); d.arc([P(108, 60), P(244, 196)], 270, 90, fill=col, width=w)
    d.line([P(80, 178), P(176, 178)], fill=col, width=w)
    for cx in (82, 174):
        d.line([P(80 if cx < 128 else cx, 78), P(cx if cx < 128 else 176, 78)], fill=col, width=w)
        r = T / 2 * s; d.ellipse([x + cx * s - r, y + 78 * s - r, x + cx * s + r, y + 78 * s + r], fill=col)
    r = DR * s; d.ellipse([x + 128 * s - r, y + 78 * s - r, x + 128 * s + r, y + 78 * s + r], fill=col)

def make(out):
    os.makedirs(out, exist_ok=True)
    marks = W.compile_marks({"marks": W.DEFAULT_MARKS})
    Z = S * K
    for fn, label, icon in MARKS:
        m = W.mark_match(marks, fn + ".jpg")
        if not m:
            raise SystemExit("目印として読めない名前: " + fn)
        col, cat = ROLE[m[0]]
        im = Image.new("RGB", (Z, Z), "#FFFFFF"); d = ImageDraw.Draw(im)
        cx, cy, R = Z / 2, 232 * K, 168 * K
        d.ellipse([cx - R, cy - R, cx + R, cy + R], fill=col)
        P = Pen(d, cx - 115 * K, cy - 115 * K, 2.3 * K); P.bg = col
        icon(P)
        f, b = fit(d, label, 540 * K, 96 * K)
        d.text(((Z - (b[2] - b[0])) / 2 - b[0], 470 * K - (b[3] - b[1]) / 2 - b[1]), label, font=f, fill="#1D1D1F")
        cf = ImageFont.truetype(FONT_R, 24 * K, index=0)
        d.text((32 * K, Z - 54 * K), cat, font=cf, fill=col)
        ring(d, Z - 32 * K - 256 * 0.26 * K, Z - 32 * K - 196 * 0.26 * K, 0.26 * K, "#C3C8D0")
        im.resize((S, S), Image.LANCZOS).save(os.path.join(out, fn + ".jpg"), quality=92)
    print("%d 枚を作りました: %s" % (len(MARKS), out))

if __name__ == "__main__":
    make(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "目印画像"))
