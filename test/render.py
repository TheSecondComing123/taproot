import glob
import re
import sys

from PIL import Image, ImageDraw

S = 3
FONT = [[int(b, 16) for b in row.split(",")] for row in re.findall(r"\{ (0x[^}]*) \}", open("src/font.h").read())]


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
            for r, bits in enumerate(FONT[ch]):
                for b in range(w):
                    if bits & 0x80 >> b:
                        px, py = (x + b) * S, (y + r) * S
                        d.rectangle([px, py, px + S - 1, py + S - 1], fill=pal.get(fg, (255, 0, 255)))
    img.save(path[:-4] + ".png")
