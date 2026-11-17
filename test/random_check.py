import random
import re
import subprocess
import sys

from sympy import Mul, Poly, Pow, Rational, diff, div, expand, factor_list, nan, simplify, solveset, sqf_list, symbols, zoo, S
from sympy.parsing.sympy_parser import implicit_multiplication_application, parse_expr, standard_transformations

x, y = symbols("x y")
TR = standard_transformations + (implicit_multiplication_application,)
GLYPHS = {"\x01": "√", "\x02": "±", "\x03": "≈", "\x04": "·", "\x11": "≠", "\x12": "≤", "\x13": "≥", "\x14": "∞", "\x15": "∪", "\x16": "→"}


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
    if len(blocks) != len(cases):
        sys.exit(f"runner gave {len(blocks)} results for {len(cases)} cases")
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
        if k == 2 and " ≈ " in t and not (prev and prev[0] == 1 and "√" in prev[1]):
            body = t.split(" ≈ ", 1)[1]
            m = re.search(r" \(multiplicity (\d+)\)", body)
            mult = int(m.group(1)) if m else 1
            body = re.sub(r" \(multiplicity \d+\)", "", body)
            for part in body.split(", "):
                found += numbers(part) * mult
        if k != 0:
            prev = (k, t)
    return [complex(v.evalf()) for v in found], None


def reference_roots(p):
    out = []
    for f, m in sqf_list(Poly(p, x))[1]:
        out += [complex(r) for r in f.nroots(n=30, maxsteps=500)] * m
    return out


def gen_numeric():
    """repeated irrational and complex factors, the cases the exact path can't take"""
    p = random.choice([1, 2, -1])
    deg = 0
    while deg < random.randint(3, 9):
        b, c = random.randint(-4, 4), random.randint(-6, 6)
        if b * b - 4 * c >= 0 and int((b * b - 4 * c) ** 0.5) ** 2 == b * b - 4 * c:
            continue
        m = random.choice([1, 1, 2, 3])
        p *= (x**2 + b * x + c) ** m
        deg += 2 * m
    if random.random() < 0.5:
        p *= x**3 + random.randint(-3, 3) * x + random.choice([-5, -3, 3, 5])
    return p


def endpoint(t):
    if t in ("∞", "-∞"):
        return float("inf") if t == "∞" else float("-inf")
    return float(numbers(t)[0].evalf())


def intervals(line):
    """our interval notation as (lo, hi, lo_closed, hi_closed) pieces"""
    if line in ("no solution",):
        return []
    out = []
    for piece in line.split(" ∪ "):
        if piece.startswith("{"):
            v = endpoint(piece[1:-1])
            out.append((v, v, True, True))
            continue
        lo, hi = piece[1:-1].split(",")
        out.append((endpoint(lo), endpoint(hi), piece[0] == "[", piece[-1] == "]"))
    return out


def inside(pieces, xv):
    for lo, hi, lc, hc in pieces:
        if (lo < xv or (lc and abs(lo - xv) < 1e-12)) and (xv < hi or (hc and abs(hi - xv) < 1e-12)):
            return True
    return False


def gen_inequality():
    p = 1
    for _ in range(random.randint(1, 4)):
        r = rand_root()
        p *= (x - r) ** random.choice([1, 1, 2])
    if random.random() < 0.3:
        p *= x**2 + random.randint(1, 5)
    num = expand(p * random.choice([1, -1, 2]))
    den = 1
    if random.random() < 0.4:
        den = x - rand_root()
    return num, den, random.choice(["<", ">", "<=", ">="])


def check_inequality(num, den, rel, lines):
    res = [t for k, t in lines if k == 1]
    if not res:
        return False, "no result"
    if res[0] == "all real numbers":
        pieces = [(float("-inf"), float("inf"), False, False)]
    else:
        pieces = intervals(res[0])
    f = num / den
    pts = set()
    for r in list(Poly(num, x).real_roots()) + (list(Poly(den, x).real_roots()) if den != 1 else []):
        pts.add(r)
    probes = []
    for r in pts:
        rv = float(r.evalf())
        probes += [(r, rv), (None, rv - 1e-5), (None, rv + 1e-5)]
    probes += [(None, -1e3), (None, 1e3), (None, 0.123)]
    for exact, xv in probes:
        val = f.subs(x, exact) if exact is not None else f.subs(x, Rational(xv))
        if val.has(zoo) or val is nan or (den != 1 and (den.subs(x, exact if exact is not None else Rational(xv)) == 0)):
            truth = False
        else:
            truth = {"<": val < 0, ">": val > 0, "<=": val <= 0, ">=": val >= 0}[rel]
        if bool(truth) != inside(pieces, xv):
            return False, f"at x={xv}: truth {truth}, ours {inside(pieces, xv)} from {res[0]}"
    return True, ""


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
        q = gen_numeric()
        cases.append(("s", to_input(q) + "=0", q))
        a = expand((x + random.randint(-4, 4)) ** random.randint(2, 6) * (random.randint(1, 3) * x - random.randint(-5, 5)))
        cases.append(("e", f"(x+{random.randint(0, 4)})^{random.randint(2, 7)}({random.randint(1, 3)}x-{random.randint(0, 5)})", None))
        cases.append(("d", to_input(a), a))
        num = expand(gen_factor() + random.randint(-9, 9))
        den = x - random.randint(-5, 5) if random.random() < 0.5 else random.randint(1, 3) * x**2 + random.randint(-3, 3) * x + 1
        if num.as_poly(x).degree() >= den.as_poly(x).degree():
            cases.append(("e", f"({to_input(num)})/({to_input(den)})", (num, den)))
        inum, iden, rel = gen_inequality()
        cases.append(("s", f"({to_input(inum)})/({to_input(iden)}){rel}0" if iden != 1 else f"{to_input(inum)}{rel}0", ("ineq", inum, iden, rel)))
        a1, a2 = rand_root(), rand_root()
        lhs_s = f"({to_input(x - a1)})/({to_input(x - a2)})+({random.randint(-3, 3)})"
        rhs_s = f"({random.randint(1, 3)})/({to_input(x - a2)})+({random.randint(-2, 2)})x"
        cases.append(("s", f"{lhs_s}={rhs_s}", ("rateq", parse(lhs_s), parse(rhs_s))))

    bad = sensitive = 0
    for (cmd, inp, ref), lines in zip(cases, run(cases)):
        res = [t for k, t in lines if k == 1]
        errs = [t for k, t in lines if k == 3]
        ok, why = True, ""
        if errs and errs[0] == "too sensitive to solve numerically":
            sensitive += 1
            continue
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
        elif cmd == "s" and isinstance(ref, tuple) and ref[0] == "ineq":
            ok, why = check_inequality(ref[1], ref[2], ref[3], lines)
        elif cmd == "s" and isinstance(ref, tuple) and ref[0] == "rateq":
            sol = solveset(ref[1] - ref[2], x, domain=S.Complexes)
            if not sol.is_FiniteSet:
                ok = any(t == "every value works" for k, t in lines if k == 1)
                why = f"identity, sympy says {sol}"
            else:
                want = [complex(v.evalf()) for v in sol]
                got, _ = solutions(lines)
                ok = got is not None and same_roots(sorted(set(got), key=lambda c: (c.real, c.imag)), want)
                why = f"got {got} want {want}"
        elif cmd == "s":
            got, _ = solutions(lines)
            want = reference_roots(ref)
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
                # after any cancelling, "= q+r/D" must still equal num/den
                mixed_line = next(t for t in res[1:] if t.startswith("= "))
                ok = simplify(parse(mixed_line[2:]) - num / den) == 0
                why = mixed_line
        elif cmd == "d":
            ok = expand(parse(res[0][2:]) - diff(ref, x)) == 0
        if not ok:
            bad += 1
            print(f"FAIL {cmd} {inp}\n  {why}\n  " + "\n  ".join(t for _, t in lines))
    print(f"{len(cases) - bad - sensitive}/{len(cases)} random cases passed, {sensitive} refused as too sensitive")
    sys.exit(1 if bad else 0)


main()
