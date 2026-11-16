import random
import re
import subprocess
import sys

from sympy import Mul, Pow, Rational, diff, div, expand, factor_list, roots, symbols
from sympy.parsing.sympy_parser import implicit_multiplication_application, parse_expr, standard_transformations

x, y = symbols("x y")
TR = standard_transformations + (implicit_multiplication_application,)
GLYPHS = {"\x01": "√", "\x02": "±", "\x03": "≈", "\x04": "·"}


def ours(s):
    return s.replace("^", "**")


def to_input(p):
    return str(expand(p)).replace("**", "^")


def parse(s, evaluate=True):
    return parse_expr(ours(s), local_dict={"x": x, "y": y}, transformations=TR, evaluate=evaluate)


def run(cases):
    stdin = "".join(f"{c}\t{inp}\n" for c, inp, _ in cases)
    out = subprocess.run([sys.argv[1], "-r"], input=stdin.encode(), capture_output=True, check=True).stdout.decode()
    blocks = out.split("--\n")[:-1]
    for raw in blocks:
        lines = []
        for ln in raw.splitlines():
            k, t = ln.split("\t", 1)
            lines.append((int(k), "".join(GLYPHS.get(ch, ch) for ch in t)))
        yield lines


def rand_root():
    return Rational(random.randint(-9, 9), random.choice([1, 1, 1, 2, 3, 4]))


def gen_factor():
    k = random.randint(1, 3)
    p = random.choice([1, -1, 2, -3, Rational(1, 2)])
    for _ in range(k):
        r = rand_root()
        p *= x - r if r.q == 1 else r.q * x - r.p
    if random.random() < 0.5:
        while True:
            b, c = random.randint(-5, 5), random.randint(-9, 9)
            d = b * b - 4 * c
            if d < 0 or int(d**0.5) ** 2 != d:
                break
        p *= x**2 + b * x + c
    if random.random() < 0.3:
        p *= x ** random.randint(1, 2)
    return p


def numbers(text):
    """turn one of our root strings into a list of sympy numbers"""
    t = text.replace("i√", "i*√")
    t = re.sub(r"(\d)i", r"\1*I", t).replace("i", "I")
    t = re.sub(r"(\d)√", r"\1*√", t)
    t = re.sub(r"√(-?\d+)", r"sqrt(\1)", t)
    if "±" in t:
        return [parse_expr(t.replace("±", "+", 1)), parse_expr(t.replace("±", "-", 1))]
    return [parse_expr(t)]


def solutions(lines):
    found, prev = [], None
    for k, t in lines:
        if k == 3:
            return None, t
        if k == 1 and t != "no solution" and t != "every value works":
            body = t.split(" = ", 1)[1]
            m = re.search(r" \(multiplicity (\d+)\)", body)
            mult = int(m.group(1)) if m else 1
            body = re.sub(r" \(multiplicity \d+\)", "", body)
            found += numbers(body) * mult
        if k == 2 and not (prev and prev[0] == 1 and "√" in prev[1]):
            for part in t.split(" ≈ ", 1)[1].split(", "):
                found += numbers(part)
        if k != 0:
            prev = (k, t)
    return [complex(v.evalf()) for v in found], None


def same_roots(a, b):
    b = list(b)
    for r in a:
        best = min(range(len(b)), key=lambda i: abs(b[i] - r), default=None)
        if best is None or abs(b[best] - r) > 1e-5 * (1 + abs(r)):
            return False
        b.pop(best)
    return not b


def main():
    random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    cases = []
    for _ in range(n):
        p = gen_factor()
        cases.append(("f", to_input(p), p))
        cases.append(("s", to_input(p) + "=0", p))
        a = expand((x + random.randint(-4, 4)) ** random.randint(2, 6) * (random.randint(1, 3) * x - random.randint(-5, 5)))
        cases.append(("e", f"(x+{random.randint(0, 4)})^{random.randint(2, 7)}({random.randint(1, 3)}x-{random.randint(0, 5)})", None))
        cases.append(("d", to_input(a), a))
        num = expand(gen_factor() + random.randint(-9, 9))
        den = x - random.randint(-5, 5) if random.random() < 0.5 else random.randint(1, 3) * x**2 + random.randint(-3, 3) * x + 1
        if num.as_poly(x).degree() >= den.as_poly(x).degree():
            cases.append(("e", f"({to_input(num)})/({to_input(den)})", (num, den)))

    bad = 0
    for (cmd, inp, ref), lines in zip(cases, run(cases)):
        res = [t for k, t in lines if k == 1]
        errs = [t for k, t in lines if k == 3]
        ok, why = True, ""
        if errs:
            ok, why = False, errs[0]
        elif cmd == "f":
            got = parse(res[0][2:])
            ok = expand(got - ref) == 0
            if ok:
                for f in Mul.make_args(parse(res[0][2:].lstrip("-"), evaluate=False)):
                    base = f.base if isinstance(f, Pow) else f
                    fl = factor_list(base)[1]
                    if base.free_symbols and (len(fl) != 1 or fl[0][1] != 1):
                        ok, why = False, f"reducible factor {base}"
        elif cmd == "s":
            got, _ = solutions(lines)
            want = [complex(r.evalf()) for r, m in roots(ref, x).items() for _ in range(m)]
            ok = same_roots(got, want)
            why = f"got {got} want {want}"
        elif cmd == "e" and ref is None:
            ok = expand(parse(res[0][2:]) - expand(parse(inp))) == 0
        elif cmd == "e":
            num, den = ref
            q, r = div(num, den, x)
            if r == 0:
                ok = expand(parse(res[0][2:]) - q) == 0
            else:
                gq, gr = res[0][2:].split(", remainder ")
                ok = expand(parse(gq) - q) == 0 and expand(parse(gr) - r) == 0
        elif cmd == "d":
            ok = expand(parse(res[0][2:]) - diff(ref, x)) == 0
        if not ok:
            bad += 1
            print(f"FAIL {cmd} {inp}\n  {why}\n  " + "\n  ".join(t for _, t in lines))
    print(f"{len(cases) - bad}/{len(cases)} random cases passed")
    sys.exit(1 if bad else 0)


main()
