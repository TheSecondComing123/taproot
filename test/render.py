import glob
import sys

from PIL import Image, ImageDraw, ImageFont

S = 3
GLYPH = {1: "√", 2: "±", 3: "≈", 4: "·", 5: "↑", 6: "↓", 7: "θ", 8: "²", 17: "≠", 18: "≤", 19: "≥", 20: "∞", 21: "∪", 22: "→"}
font = ImageFont.truetype("/System/Library/Fonts/Menlo.ttc", 26)


def rgb(c):
    return ((c >> 10 & 31) << 3, (c >> 5 & 31) << 3, (c & 31) << 3)


for path in sorted(glob.glob(f"{sys.argv[1]}/*.ops")):
    pal = {}
    img = Image.new("RGB", (320 * S, 240 * S))
    d = ImageDraw.Draw(img)
    for line in open(path):
        k, *v = line.split()
        v = list(map(int, v))
        if k == "P":
            pal[v[0]] = rgb(v[1])
        elif k == "R":
            x, y, w, h, c = v
            d.rectangle([x * S, y * S, (x + w) * S - 1, (y + h) * S - 1], fill=pal.get(c, (255, 0, 255)))
        elif k == "C":
            x, y, w, fg, ch = v
            d.text((x * S + 4 * S, y * S + 4 * S), GLYPH.get(ch, chr(ch)), font=font, fill=pal.get(fg, (255, 0, 255)), anchor="mm")
    img.save(path[:-4] + ".png")
