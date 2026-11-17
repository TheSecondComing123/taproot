import glob
import sys

from PIL import Image

for path in sorted(glob.glob(f"{sys.argv[1]}/*.ppm")):
    Image.open(path).resize((960, 720), Image.NEAREST).save(path[:-4] + ".png")
