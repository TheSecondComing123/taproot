import glob
import re
import sys

from PIL import Image, ImageDraw

S = 3
# graphx's default 8x8 font (ce toolchain, lgpl), chars 0-127, one byte per row, msb on the left
FONT = bytes.fromhex(
    "00000000000000007e81a581bdbd817e7effdbffc3c3ff7e6cfefefe7c38100010387cfe7c381000387c38fefe10107c"
    "00183c7eff7e187e0000183c3c180000ffffe7c3c3e7ffff003c664242663c00ffc399bdbd99c3ff0f070f7dcccccc78"
    "3c6666663c187e183f333f303070f0e07f637f636367e6c0995a3ce7e73c5a9980e0f8fef8e08000020e3efe3e0e0200"
    "183c7e18187e3c1866666666660066007fdbdb7b1b1b1b003f607c66663e06fc000000007e7e7e00183c7e187e3c18ff"
    "183c7e1818181800181818187e3c180000180cfe0c180000003060fe603000000000c0c0c0fe0000002466ff66240000"
    "00183c7effff000000ffff7e3c1800000000000000000000c0c0c0c0c000c000d8d8d800000000006c6cfe6cfe6c6c00"
    "187ec07c06fc180000c6cc183066c600386c3876dccc760030306000000000003060c0c0c0603000c06030303060c000"
    "00663cff3c660000003030fcfc30300000000000006060c0000000fc000000000000000000c0c000060c183060c08000"
    "7ccedef6e6c67c00307030303030fc007cc6067cc0c0fe00fc06063c0606fc000cccccccfe0c0c00fec0fc0606c67c00"
    "7cc0c0fcc6c67c00fe06060c183030007cc6c67cc6c67c007cc6c67e06067c0000c0c00000c0c00000606000006060c0"
    "183060c0603018000000fc00fc000000c06030183060c00078cc1830300030007cc6dededec07e00386cc6c6fec6c600"
    "fcc6c6fcc6c6fc007cc6c0c0c0c67c00f8ccc6c6c6ccf800fec0c0f8c0c0fe00fec0c0f8c0c0c0007cc6c0c0cec67c00"
    "c6c6c6fec6c6c6007e18181818187e000606060606c67c00c6ccd8f0d8ccc600c0c0c0c0c0c0fe00c6eefefed6c6c600"
    "c6e6f6decec6c6007cc6c6c6c6c67c00fcc6c6fcc0c0c0007cc6c6c6d6de7c06fcc6c6fcd8ccc6007cc6c07c06c67c00"
    "ff18181818181800c6c6c6c6c6c6fe00c6c6c6c6c67c3800c6c6c6c6d6fe6c00c6c66c386cc6c600c6c6c67c1830e000"
    "fe060c183060fe00f0c0c0c0c0c0f000c06030180c060200f03030303030f00010386cc60000000000000000000000ff"
    "c0c060000000000000007c067ec67e00c0c0c0fcc6c6fc0000007cc6c0c67c000606067ec6c67e0000007cc6fec07c00"
    "1c3630783030780000007ec6c67e06fcc0c0fcc6c6c6c6006000e0606060f000060006060606c67cc0c0ccd8f8ccc600"
    "e06060606060f0000000ccfefed6d6000000fcc6c6c6c60000007cc6c6c67c000000fcc6c6fcc0c000007ec6c67e0606"
    "0000fcc6c0c0c00000007ec07c06fc003030fc3030301c000000c6c6c6c67e000000c6c6c67c38000000c6c6d6fe6c00"
    "0000c66c386cc6000000c6c6c67e06fc0000fe0c3860fe001c3030e030301c00c0c0c000c0c0c000e030301c3030e000"
    "76dc0000000000000010386cc6c6fe00"
)


def glyphs():
    g = {c: FONT[c * 8:c * 8 + 8] for c in range(128)}
    src = open("src/main.c").read()
    table = src[src.index("glyphs[][9]"):src.index("};", src.index("glyphs[][9]"))]
    for row in re.findall(r"\{([^{}]*)\}", table):
        b = [int(x, 16) for x in row.split(",")]
        g[b[0]] = bytes(b[1:])
    return g


def rgb(c):
    return ((c >> 10 & 31) << 3, (c >> 5 & 31) << 3, (c & 31) << 3)


G = glyphs()
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
            for r, bits in enumerate(G.get(ch, G[0])):
                for b in range(8):
                    if bits & 0x80 >> b:
                        px, py = (x + b) * S, (y + r) * S
                        d.rectangle([px, py, px + S - 1, py + S - 1], fill=pal.get(fg, (255, 0, 255)))
    img.save(path[:-4] + ".png")
