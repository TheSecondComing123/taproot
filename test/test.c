#include "../src/cas.h"
#include <stdio.h>
#include <string.h>

enum { E = CMD_EXPAND, F = CMD_FACTOR, S = CMD_SOLVE, D = CMD_DERIV };

static int fails, total, verbose;

static const char *show(const char *s, int slot)
{
    static char buf[2][4096];
    char *o = buf[slot];
    for (; *s && o < buf[slot] + sizeof buf[0] - 4; s++) {
        const char *g = *s == 1 ? "√" : *s == 2 ? "±" : *s == 3 ? "≈" : *s == 4 ? "·" : 0;
        if (!g) *o++ = *s;
        else while (*g) *o++ = *g++;
    }
    *o = 0;
    return buf[slot];
}

static void dump(void)
{
    int i;
    for (i = 0; i < cas_nlines; i++) printf("    %c %s\n", "s=~!"[cas_kind[i]], show(cas_line[i], 0));
}

static void check(int cmd, const char *in, const char *want)
{
    char got[4096] = "";
    int i;
    total++;
    cas_run(cmd, in);
    for (i = 0; i < cas_nlines; i++) {
        if (cas_kind[i] == L_STEP) continue;
        if (*got) strcat(got, " | ");
        strcat(got, cas_line[i]);
    }
    if (strcmp(got, want)) {
        fails++;
        printf("FAIL [%d] %s\n  want %s\n  got  %s\n", cmd, in, show(want, 0), show(got, 1));
        dump();
    } else if (verbose) {
        printf("ok [%d] %s\n", cmd, in);
        dump();
    }
}

static void has_step(int cmd, const char *in, const char *want)
{
    int i;
    total++;
    cas_run(cmd, in);
    for (i = 0; i < cas_nlines; i++)
        if (cas_kind[i] == L_STEP && !strcmp(cas_line[i], want)) return;
    fails++;
    printf("FAIL [%d] %s: no step \"%s\"\n", cmd, in, show(want, 0));
    dump();
}

int main(int argc, char **argv)
{
    char deep[256];
    int i;
    verbose = argc > 1 && !strcmp(argv[1], "-v");

    check(E, "(2x-3)^5", "= 32x^5-240x^4+720x^3-1080x^2+810x-243");
    check(E, "(x+2y)^4", "= x^4+8x^3y+24x^2y^2+32xy^3+16y^4");
    check(E, "(x+1)(x-2)", "= x^2-x-2");
    check(E, "x(x+1)^2", "= x^3+2x^2+x");
    check(E, "2x^2+3x-x^2-3x", "= x^2");
    check(E, "x-x", "= 0");
    check(E, "0", "= 0");
    check(E, "2+3*4", "= 14");
    check(E, "-x^2", "= -x^2");
    check(E, "(-x)^2", "= x^2");
    check(E, "2^3^2", "= 512");
    check(E, "x^2/2-1/8", "= (1/2)x^2-1/8");
    check(E, "0.5x+1.25", "= (1/2)x+5/4");
    check(E, "(a+b+c)^2", "= a^2+2ab+2ac+b^2+2bc+c^2");
    check(E, "(x+1)^0", "= 1");
    check(E, "3(x+1)^2-(x-1)^2", "= 2x^2+8x+2");
    check(E, "X^2 + 2 X", "= x^2+2x");
    check(E, "x/2", "= (1/2)x");
    check(E, "(x+1)^2(x-1)", "= x^3+x^2-x-1");

    check(E, "(x^2-1)/(x-1)", "= x+1");
    check(E, "(x^3+2x-5)/(x-2)", "= x^2+2x+6, remainder 7 | = x^2+2x+6+7/(x-2)");
    check(E, "(2x^3-3x^2+4)/(x^2+1)", "= 2x-3, remainder -2x+7 | = 2x-3+(-2x+7)/(x^2+1)");
    check(E, "(x^2+1)/(2x+1)", "= (1/2)x-1/4, remainder 5/4 | = (1/2)x-1/4+(5/4)/(2x+1)");
    check(E, "(x+1)/(x-1)", "= 1, remainder 2 | = 1+2/(x-1)");
    check(E, "(x^3-1)/(x+1)", "= x^2-x+1, remainder -2 | = x^2-x+1-2/(x+1)");

    check(E, "x^3-2x+1, x=3", "= 22");
    check(E, "x^2y+y, x=2", "= 5y");
    check(E, "x^2y+y, x=2, y=-1", "= -5");
    check(E, "x^2, x=1/2", "= 1/4");
    check(E, "x^2, x=-1/2", "= 1/4");
    check(E, "5, x=2", "= 5");

    check(D, "3x^4-5x^2+7x-2", "= 12x^3-10x+7");
    check(D, "3x^4-5x^2+7x-2, x=1", "= 12x^3-10x+7 | at x=1: 9");
    check(D, "x^2y+y^3", "= 2xy");
    check(D, "y^3+2y", "= 3y^2+2");
    check(D, "5", "= 0");
    check(D, "(x+1)^3", "= 3x^2+6x+3");
    check(D, "x^2/2", "= x");

    check(E, "x^-1", "exponent must be a whole number (got -1)");
    check(E, "x^y", "exponent must be a whole number (got y)");
    check(E, "x^1.5", "exponent must be a whole number (got 3/2)");
    check(E, "x^61", "exponent too big (max 60)");
    check(E, "1/(x+1)", "fractions of polynomials aren't supported");
    check(E, "(x+1)/(x-1)+3", "fractions of polynomials aren't supported");
    check(E, "(x+y)/(x-1)", "fractions of polynomials aren't supported");
    check(E, "(x^3+1)/(x-2), x=1", "can't plug values into a division with a remainder");
    check(D, "(x^3+1)/(x-2)", "fractions of polynomials aren't supported");
    check(E, "(x+1", "missing )");
    check(E, "x+1)", "extra )");
    check(E, "x=1=2", "only one = allowed");
    check(E, "x=1", "use solve for equations");
    check(E, "a+b+c+d+e", "too many letters (max 4)");
    check(E, "(99x+99)^30", "numbers too big");
    check(E, "99999999999999999999", "numbers too big");
    check(E, "x/0", "division by zero");
    check(E, "x^2, x=y", "x= needs a number");
    check(E, "x^2, 3", "after a comma, write a value like x=3");
    check(E, "x^2, x=1, x=2", "x is given twice");
    check(E, "", "type an expression first");
    check(E, "   ", "type an expression first");
    check(E, "2*", "the expression ends too early");
    check(E, "2$", "unexpected $");
    check(E, ".", "a lone . isn't a number");
    check(E, "(x+y+1)^10", "too many terms (max 64)");
    check(S, "x^2=4, x=2", "solve finds the values itself, drop the , x=");

    strcpy(deep, "x");
    for (i = 0; i < 20; i++) {
        memmove(deep + 3, deep, strlen(deep) + 1);
        memcpy(deep, "1+(", 3);
        strcat(deep, ")");
    }
    check(E, deep, "expression too big for memory");

    has_step(E, "(2x-3)^5", "T3 C(5,2)(2x)^3(-3)^2 = 720x^3");
    has_step(E, "(x+2y)^4", "T1 C(4,0)x^4 = x^4");
    has_step(E, "(x^3+2x-5)/(x-2)", "synthetic division by x-2");
    has_step(E, "(x^3+2x-5)/(x-2)", "  1  2  6| 7");
    has_step(E, "(2x^3-3x^2+4)/(x^2+1)", "2x" G_DOT "(x^2+1), left -3x^2-2x+4");
    has_step(E, "x^3-2x+1, x=3", "remainder theorem: P(3) is the remainder of P/(x-3)");
    has_step(D, "3x^4-5x^2+7x-2", "d/dx -5x^2 = 2" G_DOT "(-5)x = -10x");
    has_step(D, "y^3+2y", "d/dy y^3 = 3y^2");

    printf("%d/%d passed\n", total - fails, total);
    return fails != 0;
}
