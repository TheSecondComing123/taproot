#include "cas.h"
#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <setjmp.h>
#include <string.h>

#define NV 4
#define MAXT 64
#define POOL 20
#define MAXD 40
#define MAXE 200
#define MAXPOW 60
#define TEXT 8192
#define STEP_LINES (CAS_MAXLINES - 48)
#define STEP_TEXT (TEXT - 2048)
#define MAXPTS (2 * MAXD + 8)

typedef struct { long long n, d; } Q;
typedef struct { Q c; uint8_t e[NV]; } Term;
typedef struct { uint8_t used; int n; Term t[MAXT]; } Poly;
typedef struct { Poly *n, *d; } Rat; /* d == 0 means 1 */
typedef struct { long double r, i; } Cx;
typedef struct { long long p, q; int mult; } Root;
/* a real point on the number line: a zero of the top ('n'), of the bottom ('d') or a hole ('h') */
typedef struct { long double v; long long p, q; int mult; char tag; const char *s; } Pt;

const char *cas_line[CAS_MAXLINES];
uint8_t cas_kind[CAS_MAXLINES];
int cas_nlines;
int (*cas_stop)(void);

static char text[TEXT];
static int textlen, hidden, quiet, clipped;
static char *w, *wend;
static char sink[1];

static Poly pool[POOL];
static char vars[NV];
static int nv, iv;
static uint8_t assigned[NV];
static Rat val[NV];
static jmp_buf fail_jmp, soft_jmp;
static int soft;
static const char *s, *send;
static int nest;
static Q da[MAXD + 1], db[MAXD + 1], dq[MAXD + 1], ga[MAXD + 1], gb[MAXD + 1], gc[MAXD + 1];
/* lcm of every one-variable polynomial divided by: its zeros are the domain restrictions */
static Poly *dom;
static int domv;

/* ---------- output ---------- */

static void wputc(char c)
{
    if (w < wend - 1) {
        *w++ = c;
        *w = 0;
    } else if (w != sink) {
        clipped = 1;
    }
}

static void wputs(const char *p)
{
    while (*p) wputc(*p++);
}

static void wll(long long v)
{
    char tmp[24];
    int n = 0;
    unsigned long long u = v < 0 ? -(unsigned long long)v : (unsigned long long)v;
    do tmp[n++] = '0' + u % 10; while (u /= 10);
    if (v < 0) wputc('-');
    while (n) wputc(tmp[--n]);
}

static void end(void)
{
    if (w == sink) return;
    textlen = w - text + 1;
    if (clipped && cas_kind[cas_nlines] != L_STEP) {
        cas_line[cas_nlines] = "answer too long to show";
        cas_kind[cas_nlines] = L_ERROR;
    }
    cas_nlines++;
}

static void begin(int kind)
{
    int ok = cas_nlines < CAS_MAXLINES && textlen < TEXT - 1;
    if (kind == L_STEP && quiet) {
        ok = 0;
    } else if (kind == L_STEP && (cas_nlines >= STEP_LINES || textlen >= STEP_TEXT)) {
        if (ok && !hidden) {
            hidden = 1;
            cas_line[cas_nlines] = "(more steps hidden)";
            cas_kind[cas_nlines++] = L_STEP;
        }
        ok = 0;
    }
    if (!ok) {
        w = sink;
        wend = sink + 1;
        *w = 0;
        return;
    }
    w = text + textlen;
    wend = text + TEXT;
    *w = 0;
    clipped = 0;
    cas_line[cas_nlines] = w;
    cas_kind[cas_nlines] = kind;
}

static void step(const char *msg)
{
    begin(L_STEP);
    wputs(msg);
    end();
}

__attribute__((noreturn)) static void die(void)
{
    end();
    longjmp(fail_jmp, 1);
}

__attribute__((noreturn)) static void fail(const char *msg)
{
    begin(L_ERROR);
    wputs(msg);
    die();
}

/* inside dgcd an overflow just means "give up on simplifying", not an error */
__attribute__((noreturn)) static void too_big(void)
{
    if (soft) longjmp(soft_jmp, 1);
    fail("numbers too big");
}

static void poll(void)
{
    if (cas_stop && cas_stop()) fail("stopped");
}

/* ---------- exact rationals ---------- */

static long long ckmul(long long a, long long b)
{
    /* any exact overflow test (even divide-back) compiles to ~2.9 kb of inline 64-bit code on the ez80.
       the long double product is within 2^-53 of the real one, so 9.2e18 < 2^63 is a safe cutoff */
    long double p;
    if ((unsigned long long)a + 0x7fffffff < 0xffffffffULL && (unsigned long long)b + 0x7fffffff < 0xffffffffULL) return a * b;
    p = (long double)a * b;
    if (p >= 9.2e18L || p <= -9.2e18L) too_big();
    return a * b;
}

static long long ckadd(long long a, long long b)
{
    long long r;
    if (__builtin_add_overflow(a, b, &r) || r == LLONG_MIN) too_big();
    return r;
}

static long long gcd(long long a, long long b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long lcm(long long a, long long b)
{
    return ckmul(a / gcd(a, b), b);
}

/* fractions go by pointer: a 16-byte struct copied by value costs ~3x the code on the ez80.
   r may be the same as a or b */
static void qset(Q *r, long long n)
{
    r->n = n;
    r->d = 1;
}

static void qnorm(Q *r, long long n, long long d)
{
    long long g;
    if (d == 0) fail("division by zero");
    if (d < 0) {
        n = -n;
        d = -d;
    }
    g = gcd(n, d);
    r->n = n / g;
    r->d = d / g;
}

static void qadd(Q *r, const Q *a, const Q *b)
{
    long long g = gcd(a->d, b->d);
    qnorm(r, ckadd(ckmul(a->n, b->d / g), ckmul(b->n, a->d / g)), ckmul(a->d / g, b->d));
}

static void qsub(Q *r, const Q *a, const Q *b)
{
    Q t = *b;
    t.n = -t.n;
    qadd(r, a, &t);
}

static void qmul(Q *r, const Q *a, const Q *b)
{
    long long g1 = gcd(a->n, b->d), g2 = gcd(b->n, a->d);
    qnorm(r, ckmul(a->n / g1, b->n / g2), ckmul(a->d / g2, b->d / g1));
}

static void qdiv(Q *r, const Q *a, const Q *b)
{
    Q t;
    if (!b->n) fail("division by zero");
    qnorm(&t, b->d, b->n);
    qmul(r, a, &t);
}

static void qpow(Q *r, const Q *a, int n)
{
    Q t = *a;
    qset(r, 1);
    while (n--) qmul(r, r, &t);
}

static int qone(const Q *a)
{
    return a->n == 1 && a->d == 1;
}

static void wq(const Q *a)
{
    wll(a->n);
    if (a->d != 1) {
        wputc('/');
        wll(a->d);
    }
}

/* n/d reduced */
static void wfrac(long long n, long long d)
{
    Q t;
    qnorm(&t, n, d);
    wq(&t);
}

/* a negative or fractional number in parentheses, for products like 2(-5) */
static void wqpar(const Q *a)
{
    int p = a->n < 0 || a->d != 1;
    if (p) wputc('(');
    wq(a);
    if (p) wputc(')');
}

static int qlen(const Q *a)
{
    char buf[48], *sw = w, *se = wend;
    int n;
    w = buf;
    wend = buf + sizeof buf;
    wq(a);
    n = w - buf;
    w = sw;
    wend = se;
    return n;
}

/* ---------- polynomials ---------- */

static int hasvars(const uint8_t *e)
{
    int v;
    for (v = 0; v < NV; v++)
        if (e[v]) return 1;
    return 0;
}

static void wvars(const uint8_t *e)
{
    int v;
    if (iv >= 0 && e[iv]) wputc('i');
    for (v = 0; v < NV; v++) {
        if (!e[v] || v == iv) continue;
        wputc(vars[v]);
        if (e[v] > 1) {
            wputc('^');
            wll(e[v]);
        }
    }
}

static void wmono(const Q *c0, const uint8_t *e, int first)
{
    int hv = hasvars(e);
    Q c = *c0;
    if (c.n < 0) {
        wputc('-');
        c.n = -c.n;
    } else if (!first) {
        wputc('+');
    }
    if (c.d != 1 && hv) {
        wputc('(');
        wq(&c);
        wputc(')');
    } else if (!qone(&c) || !hv) {
        wq(&c);
    }
    wvars(e);
}

/* a whole-number coefficient, for the many places that build terms from integers */
static void wmonoi(long long n, const uint8_t *e, int first)
{
    Q c;
    qset(&c, n);
    wmono(&c, e, first);
}

static void wpoly(const Poly *p)
{
    int i;
    if (!p->n) wputc('0');
    for (i = 0; i < p->n; i++) wmono(&p->t[i].c, p->t[i].e, !i);
}

/* degree ignores i, and real terms come before their imaginary twins, so 3+2i reads that way */
static int mcmp(const uint8_t *a, const uint8_t *b)
{
    int da_ = 0, db_ = 0, i;
    for (i = 0; i < NV; i++) {
        if (i == iv) continue;
        da_ += a[i];
        db_ += b[i];
    }
    if (da_ != db_) return da_ > db_ ? -1 : 1;
    for (i = 0; i < NV; i++)
        if (i != iv && a[i] != b[i]) return a[i] > b[i] ? -1 : 1;
    if (iv >= 0 && a[iv] != b[iv]) return a[iv] < b[iv] ? -1 : 1;
    return 0;
}

static void addterm(Poly *p, const Q *c0, const uint8_t *e0)
{
    uint8_t e[NV];
    Q c = *c0;
    int i, r;
    memcpy(e, e0, NV);
    if (iv >= 0 && e[iv] > 1) {
        if (e[iv] & 2) c.n = -c.n; /* i^2 = -1 */
        e[iv] &= 1;
    }
    if (!c.n) return;
    for (i = 0; i < p->n; i++) {
        r = mcmp(p->t[i].e, e);
        if (r == 0) {
            qadd(&p->t[i].c, &p->t[i].c, &c);
            if (!p->t[i].c.n) {
                memmove(&p->t[i], &p->t[i + 1], (p->n - i - 1) * sizeof(Term));
                p->n--;
            }
            return;
        }
        if (r > 0) break;
    }
    if (p->n == MAXT) fail("too many terms (max 64)");
    memmove(&p->t[i + 1], &p->t[i], (p->n - i) * sizeof(Term));
    p->t[i].c = c;
    memcpy(p->t[i].e, e, NV);
    p->n++;
}

static Poly *pnew(void)
{
    int i;
    for (i = 0; i < POOL; i++) {
        if (!pool[i].used) {
            pool[i].used = 1;
            pool[i].n = 0;
            return &pool[i];
        }
    }
    fail("expression too big for memory");
}

static void pfree(Poly *p)
{
    if (p) p->used = 0;
}

static void addtermi(Poly *p, long long n, const uint8_t *e)
{
    Q c;
    qset(&c, n);
    addterm(p, &c, e);
}

static Poly *pconst(const Q *c)
{
    Poly *p = pnew();
    uint8_t e[NV] = { 0 };
    addterm(p, c, e);
    return p;
}

static Poly *pconsti(long long n)
{
    Poly *p = pnew();
    uint8_t e[NV] = { 0 };
    addtermi(p, n, e);
    return p;
}

static Poly *pvar(int v)
{
    Poly *p = pnew();
    uint8_t e[NV] = { 0 };
    e[v] = 1;
    addtermi(p, 1, e);
    return p;
}

static Poly *pcopy(const Poly *a)
{
    Poly *p = pnew();
    p->n = a->n;
    memcpy(p->t, a->t, a->n * sizeof(Term));
    return p;
}

static int isconst(const Poly *p, Q *c)
{
    if (!p->n) {
        qset(c, 0);
        return 1;
    }
    if (p->n == 1 && !hasvars(p->t[0].e)) {
        *c = p->t[0].c;
        return 1;
    }
    return 0;
}

static int pequal(const Poly *a, const Poly *b)
{
    int i;
    if (a->n != b->n) return 0;
    for (i = 0; i < a->n; i++)
        if (a->t[i].c.n != b->t[i].c.n || a->t[i].c.d != b->t[i].c.d || memcmp(a->t[i].e, b->t[i].e, NV)) return 0;
    return 1;
}

static int hasi(const Poly *p)
{
    int i;
    for (i = 0; iv >= 0 && i < p->n; i++)
        if (p->t[i].e[iv]) return 1;
    return 0;
}

static Poly *padd(const Poly *a, const Poly *b, int neg)
{
    Poly *r = pcopy(a);
    int i;
    for (i = 0; i < b->n; i++) {
        Q c = b->t[i].c;
        if (neg) c.n = -c.n;
        addterm(r, &c, b->t[i].e);
    }
    return r;
}

static Poly *pmul(const Poly *a, const Poly *b)
{
    Poly *r = pnew();
    uint8_t e[NV];
    int i, j, v;
    for (i = 0; i < a->n; i++) {
        poll();
        for (j = 0; j < b->n; j++) {
            for (v = 0; v < NV; v++) {
                int x = a->t[i].e[v] + b->t[j].e[v];
                if (x > MAXE) fail("exponent too big (max 200)");
                e[v] = x;
            }
            Q c;
            qmul(&c, &a->t[i].c, &b->t[j].c);
            addterm(r, &c, e);
        }
    }
    return r;
}

static Poly *pscale(const Poly *a, const Q *c)
{
    Poly *r = pnew();
    Q t;
    int i;
    for (i = 0; i < a->n; i++) {
        qmul(&t, &a->t[i].c, c);
        addterm(r, &t, a->t[i].e);
    }
    return r;
}

static Poly *conj(const Poly *a)
{
    Poly *r = pcopy(a);
    int i;
    for (i = 0; i < r->n; i++)
        if (r->t[i].e[iv]) r->t[i].c.n = -r->t[i].c.n;
    return r;
}

/* one variable used: its index. none: -1. several: -2 */
static int univar(const Poly *p)
{
    int v, i, found = -1;
    for (v = 0; v < NV; v++) {
        for (i = 0; i < p->n; i++) {
            if (!p->t[i].e[v]) continue;
            if (found >= 0) return -2;
            found = v;
            break;
        }
    }
    return found;
}

static int pdeg(const Poly *p, int v)
{
    int i, d = -1;
    for (i = 0; i < p->n; i++)
        if (p->t[i].e[v] > d) d = p->t[i].e[v];
    return d;
}

static int todense(const Poly *p, int v, Q *c)
{
    int i, deg = -1;
    for (i = 0; i <= MAXD; i++) qset(&c[i], 0);
    for (i = 0; i < p->n; i++) {
        int e = v < 0 ? 0 : p->t[i].e[v];
        if (e > MAXD) fail("degree too high (max 40)");
        c[e] = p->t[i].c;
        if (e > deg) deg = e;
    }
    return deg;
}

static Poly *fromdense(const Q *c, int deg, int v)
{
    Poly *p = pnew();
    uint8_t e[NV];
    int i;
    for (i = deg; i >= 0; i--) {
        memset(e, 0, NV);
        if (v >= 0) e[v] = i;
        addterm(p, &c[i], e);
    }
    return p;
}

static Poly *pderiv(const Poly *p, int v)
{
    Poly *r = pnew();
    uint8_t e[NV];
    int i;
    for (i = 0; v >= 0 && i < p->n; i++) {
        if (!p->t[i].e[v]) continue;
        memcpy(e, p->t[i].e, NV);
        e[v]--;
        {
            Q k, c;
            qset(&k, p->t[i].e[v]);
            qmul(&c, &p->t[i].c, &k);
            addterm(r, &c, e);
        }
    }
    return r;
}

static void qeval(Q *r, const Poly *p, int v, const Q *x)
{
    Q t, xp = *x;
    int i;
    qset(r, 0);
    for (i = 0; i < p->n; i++) {
        qpow(&t, &xp, v < 0 ? 0 : p->t[i].e[v]);
        qmul(&t, &t, &p->t[i].c);
        qadd(r, r, &t);
    }
}

static long double ldeval(const Poly *p, int v, long double x)
{
    long double r = 0, t;
    int i, k;
    for (i = 0; i < p->n; i++) {
        t = (long double)p->t[i].c.n / p->t[i].c.d;
        for (k = v < 0 ? 0 : p->t[i].e[v]; k > 0; k--) t *= x;
        r += t;
    }
    return r;
}

/* ---------- dense one-variable division and gcd ---------- */

/* num / den: quotient into quo, remainder left in num; returns the remainder's degree */
static int ddiv(Q *num, int dn, const Q *den, int dd, Q *quo)
{
    int i, j;
    Q c, t;
    for (i = 0; i <= MAXD; i++) qset(&quo[i], 0);
    for (i = dn; i >= dd; i--) {
        if (!num[i].n) continue;
        qdiv(&c, &num[i], &den[dd]);
        quo[i - dd] = c;
        for (j = 0; j <= dd; j++) {
            qmul(&t, &c, &den[j]);
            qsub(&num[i - dd + j], &num[i - dd + j], &t);
        }
    }
    for (i = (dn < dd ? dn : dd - 1); i >= 0 && !num[i].n; i--);
    return i;
}

static void monic(Q *c, int deg)
{
    int i;
    Q lead = c[deg];
    for (i = 0; i <= deg; i++) qdiv(&c[i], &c[i], &lead);
}

/* gcd of ga (degree na) and gb (degree nb) into ga, monic. returns its degree, or -1 if the numbers overflowed */
static int dgcd(int na, int nb)
{
    static Q t[MAXD + 1];
    int nr, outer = soft;
    if (!outer) {
        if (setjmp(soft_jmp)) {
            soft = 0;
            return -1;
        }
        soft = 1;
    }
    while (nb >= 0) {
        nr = ddiv(ga, na, gb, nb, t);
        memcpy(t, ga, sizeof t);
        memcpy(ga, gb, sizeof t);
        memcpy(gb, t, sizeof t);
        na = nb;
        nb = nr;
        if (nb >= 0) monic(gb, nb);
    }
    if (na >= 0) monic(ga, na);
    soft = outer;
    return na;
}

static void wpar(const Poly *p)
{
    int paren = p->n > 1;
    if (paren) wputc('(');
    wpoly(p);
    if (paren) wputc(')');
}

/* ---------- step-by-step division ---------- */

static void wlinear(int v, const Q *a)
{
    uint8_t e[NV] = { 0 };
    Q t = *a;
    t.n = -t.n;
    wputc(vars[v]);
    if (t.n) wmono(&t, e, 0);
}

static void wcell(const Q *a, int width, char lead)
{
    int pad = width - qlen(a);
    wputc(lead);
    while (--pad > 0) wputc(' ');
    wq(a);
}

/* synthetic division of c (degree deg) by x-a. quotient into quo, returns remainder */
static void synthetic(Q *rem, const Q *c, int deg, const Q *a, Q *quo)
{
    static Q res[MAXD + 1], prod[MAXD + 1];
    int j, width = 0, l;
    res[0] = c[deg];
    qset(&prod[0], 0);
    for (j = 1; j <= deg; j++) {
        qmul(&prod[j], a, &res[j - 1]);
        qadd(&res[j], &c[deg - j], &prod[j]);
    }
    for (j = 0; j <= deg; j++) {
        if ((l = qlen(&c[deg - j])) > width) width = l;
        if ((l = qlen(&prod[j])) > width) width = l;
        if ((l = qlen(&res[j])) > width) width = l;
    }
    width++;
    begin(L_STEP);
    for (j = 0; j <= deg; j++) wcell(&c[deg - j], width, ' ');
    end();
    begin(L_STEP);
    for (j = 0; j < width; j++) wputc(' ');
    for (j = 1; j <= deg; j++) wcell(&prod[j], width, ' ');
    end();
    begin(L_STEP);
    for (j = 0; j <= deg; j++) wcell(&res[j], width, j == deg ? '|' : ' ');
    end();
    for (j = 0; j < deg; j++) quo[deg - 1 - j] = res[j];
    if (rem) *rem = res[deg];
}

static void longdiv(Q *num, int dn, const Q *den, int dd, int v, Q *quo)
{
    Poly *prod, *left;
    Q coef, t;
    int i, j;
    uint8_t e[NV] = { 0 };
    for (i = 0; i <= dn - dd; i++) qset(&quo[i], 0);
    for (i = dn; i >= dd; i--) {
        if (!num[i].n) continue;
        qdiv(&coef, &num[i], &den[dd]);
        quo[i - dd] = coef;
        for (j = 0; j <= dd; j++) {
            qmul(&t, &coef, &den[j]);
            qsub(&num[i - dd + j], &num[i - dd + j], &t);
        }
        prod = fromdense(den, dd, v);
        left = fromdense(num, i - 1, v);
        e[v] = i - dd;
        begin(L_STEP);
        wmono(&coef, e, 1);
        wputs(G_DOT "(");
        wpoly(prod);
        wputs("), left ");
        wpoly(left);
        end();
        pfree(prod);
        pfree(left);
    }
}

/* ---------- rational expressions ---------- */

static void wrat(Rat r)
{
    int top = r.d && r.n->n > 1, bot;
    if (top) wputc('(');
    wpoly(r.n);
    if (top) wputc(')');
    if (!r.d) return;
    bot = !(r.d->n == 1 && qone(&r.d->t[0].c) && univar(r.d) >= 0);
    wputc('/');
    if (bot) wputc('(');
    wpoly(r.d);
    if (bot) wputc(')');
}

static Rat rpoly(Poly *p)
{
    Rat r;
    r.n = p;
    r.d = 0;
    return r;
}

static void rfree(Rat a)
{
    pfree(a.n);
    pfree(a.d);
}

static Poly *dmul(const Poly *a, const Poly *b)
{
    if (!a) return b ? pcopy(b) : 0;
    if (!b) return pcopy(a);
    return pmul(a, b);
}

static int isnum(Rat a, Q *q)
{
    return !a.d && isconst(a.n, q);
}

static void replace(Poly **slot, Poly *p)
{
    pfree(*slot);
    *slot = p;
}

/* remember b's zeros as domain restrictions: dom = lcm(dom, b) for one-variable b */
static void track(const Poly *b)
{
    Q c;
    int v, nd, nb, k;
    if (isconst(b, &c) || domv == -2) return;
    v = univar(b);
    if (v < 0 || v == iv || (domv >= 0 && v != domv)) {
        domv = -2;
        return;
    }
    domv = v;
    if (!dom) {
        dom = pcopy(b);
        return;
    }
    nd = todense(dom, v, ga);
    nb = todense(b, v, gb);
    k = dgcd(nd, nb);
    if (k <= 0) {
        replace(&dom, pmul(dom, b));
        return;
    }
    memcpy(gc, ga, sizeof gc);
    todense(b, v, ga);
    ddiv(ga, nb, gc, k, gb);
    {
        Poly *part = fromdense(gb, nb - k, v);
        replace(&dom, pmul(dom, part));
        pfree(part);
    }
}

/* n/d when d divides n exactly (any number of variables), else 0 */
static Poly *pexact(const Poly *n, const Poly *d)
{
    Poly *r = pcopy(n), *q = pnew(), *t, *prod, *nr;
    const Term *ld = &d->t[0];
    uint8_t e[NV];
    int v, guard = 0;
    while (r->n) {
        for (v = 0; v < NV; v++) {
            if (r->t[0].e[v] < ld->e[v]) goto no;
            e[v] = r->t[0].e[v] - ld->e[v];
        }
        if (++guard > 300) goto no;
        t = pnew();
        {
            Q c;
            qdiv(&c, &r->t[0].c, &ld->c);
            addterm(t, &c, e);
            addterm(q, &t->t[0].c, e);
        }
        prod = pmul(t, d);
        nr = padd(r, prod, 1);
        pfree(prod);
        pfree(t);
        pfree(r);
        r = nr;
    }
    pfree(r);
    return q;
no:
    pfree(r);
    pfree(q);
    return 0;
}

/* bottom with integer coefficients, no common factor and a positive lead; the top scales with it, so a
   quotient and remainder stay relative to the divisor as typed */
static void normalize(Rat *r)
{
    long long l = 1, g = 0;
    int i;
    for (i = 0; i < r->d->n; i++) l = lcm(l, r->d->t[i].c.d);
    for (i = 0; i < r->d->n; i++) g = gcd(g, ckmul(r->d->t[i].c.n, l / r->d->t[i].c.d));
    {
        Q k;
        qnorm(&k, r->d->t[0].c.n < 0 ? -l : l, g);
        if (qone(&k)) return;
        replace(&r->n, pscale(r->n, &k));
        replace(&r->d, pscale(r->d, &k));
    }
}

/* cancel the lowest power of each variable shared by every term */
static void mindiv(Rat *r)
{
    uint8_t m[NV];
    int i, v, any = 0;
    for (v = 0; v < NV; v++) m[v] = MAXE;
    for (i = 0; i < r->n->n; i++)
        for (v = 0; v < NV; v++)
            if (r->n->t[i].e[v] < m[v]) m[v] = r->n->t[i].e[v];
    for (i = 0; i < r->d->n; i++)
        for (v = 0; v < NV; v++)
            if (r->d->t[i].e[v] < m[v]) m[v] = r->d->t[i].e[v];
    for (v = 0; v < NV; v++) any |= m[v];
    if (!any) return;
    for (i = 0; i < r->n->n; i++)
        for (v = 0; v < NV; v++) r->n->t[i].e[v] -= m[v];
    for (i = 0; i < r->d->n; i++)
        for (v = 0; v < NV; v++) r->d->t[i].e[v] -= m[v];
}

static int fold(Rat *r)
{
    Q c;
    if (!r->d) return 1;
    if (r->n->n && !isconst(r->d, &c)) return 0;
    if (r->n->n) {
        Q one;
        qset(&one, 1);
        qdiv(&c, &one, &c);
        replace(&r->n, pscale(r->n, &c));
    }
    replace(&r->d, 0);
    return 1;
}

static void rsimp(Rat *r)
{
    int v, vn, k, nn, nd;
    Poly *t;
    if (!r->d) return;
    if (r->n->n && hasi(r->d)) {
        Poly *cj = conj(r->d);
        begin(L_STEP);
        wputs("multiply top and bottom by the conjugate ");
        wpoly(cj);
        end();
        replace(&r->n, pmul(r->n, cj));
        replace(&r->d, pmul(r->d, cj));
        pfree(cj);
    }
    if (fold(r)) return;
    mindiv(r);
    if (fold(r)) return;
    v = univar(r->d);
    vn = univar(r->n);
    if (v >= 0 && v != iv && (vn == v || vn == -1)) {
        nn = todense(r->n, v, ga);
        nd = todense(r->d, v, gb);
        k = dgcd(nn, nd);
        if (k > 0) {
            memcpy(gc, ga, sizeof gc);
            t = fromdense(gc, k, v);
            begin(L_STEP);
            wputs("cancel the common factor ");
            wpar(t);
            end();
            pfree(t);
            nn = todense(r->n, v, ga);
            ddiv(ga, nn, gc, k, gb);
            replace(&r->n, fromdense(gb, nn - k, v));
            nd = todense(r->d, v, ga);
            ddiv(ga, nd, gc, k, gb);
            replace(&r->d, fromdense(gb, nd - k, v));
        }
    } else if (!hasi(r->n) && !hasi(r->d) && (t = pexact(r->n, r->d))) {
        begin(L_STEP);
        wpar(r->d);
        wputs(" divides evenly: ");
        wpoly(t);
        end();
        replace(&r->n, t);
        replace(&r->d, 0);
        return;
    }
    if (fold(r)) return;
    normalize(r);
}

static Rat radd(Rat a, Rat b, int neg)
{
    Rat r;
    Poly *x, *y;
    if (!a.d && !b.d) return rpoly(padd(a.n, b.n, neg));
    if (a.d && b.d && pequal(a.d, b.d)) {
        r.n = padd(a.n, b.n, neg);
        r.d = pcopy(a.d);
    } else {
        x = b.d ? pmul(a.n, b.d) : pcopy(a.n);
        y = a.d ? pmul(b.n, a.d) : pcopy(b.n);
        r.n = padd(x, y, neg);
        pfree(x);
        pfree(y);
        r.d = dmul(a.d, b.d);
        if (a.d && b.d) {
            begin(L_STEP);
            wputs("common denominator ");
            wpoly(r.d);
            end();
        }
    }
    rsimp(&r);
    return r;
}

static Rat rmul(Rat a, Rat b)
{
    Rat r;
    r.n = pmul(a.n, b.n);
    r.d = dmul(a.d, b.d);
    rsimp(&r);
    return r;
}

static Rat rdiv(Rat a, Rat b)
{
    Rat r;
    if (!b.n->n) fail("division by zero");
    track(b.n);
    r.n = b.d ? pmul(a.n, b.d) : pcopy(a.n);
    r.d = a.d ? pmul(a.d, b.n) : pcopy(b.n);
    rsimp(&r);
    return r;
}

static void binom_part(const Term *t, int k)
{
    int v, bare = qone(&t->c), nvars = 0;
    if (!k) return;
    for (v = 0; v < NV; v++) {
        if (t->e[v] > 1) bare = 0;
        if (t->e[v]) nvars++;
    }
    if (nvars != 1) bare = 0;
    if (!bare) wputc('(');
    wmono(&t->c, t->e, 1);
    if (!bare) wputc(')');
    if (k > 1) {
        wputc('^');
        wll(k);
    }
}

static Poly *binom(const Poly *a, int n)
{
    const Term *A = &a->t[0], *B = &a->t[1];
    Poly *r = pnew(), *term;
    long long c = 1;
    uint8_t e[NV];
    int k, v;
    begin(L_STEP);
    wputs("binomial theorem: (");
    wpoly(a);
    wputs(")^");
    wll(n);
    end();
    for (k = 0; k <= n; k++) {
        Q coef, t;
        poll();
        qset(&coef, c);
        qpow(&t, &A->c, n - k);
        qmul(&coef, &coef, &t);
        qpow(&t, &B->c, k);
        qmul(&coef, &coef, &t);
        for (v = 0; v < NV; v++) {
            int x = A->e[v] * (n - k) + B->e[v] * k;
            if (x > MAXE) fail("exponent too big (max 200)");
            e[v] = x;
        }
        term = pnew();
        addterm(term, &coef, e);
        if (term->n) addterm(r, &term->t[0].c, term->t[0].e);
        begin(L_STEP);
        wputc('T');
        wll(k + 1);
        wputs(" C(");
        wll(n);
        wputc(',');
        wll(k);
        wputc(')');
        binom_part(A, n - k);
        binom_part(B, k);
        wputs(" = ");
        wpoly(term);
        end();
        pfree(term);
        c = ckmul(c, n - k) / (k + 1);
    }
    return r;
}

static Poly *ppow(const Poly *a, int n)
{
    Poly *r, *t;
    if (a->n == 2 && n >= 2) return binom(a, n);
    if (a->n > 2 && n >= 2) {
        begin(L_STEP);
        wputs("multiply out (");
        wpoly(a);
        wputs(")^");
        wll(n);
        end();
    }
    r = pconsti(1);
    while (n--) {
        t = pmul(r, a);
        pfree(r);
        r = t;
    }
    return r;
}

static Rat rpow(Rat a, int k)
{
    Rat r;
    if (k < 0) {
        if (!a.n->n) fail("division by zero");
        track(a.n);
        r.n = a.d ? ppow(a.d, -k) : pconsti(1);
        r.d = ppow(a.n, -k);
    } else {
        r.n = ppow(a.n, k);
        r.d = a.d ? ppow(a.d, k) : 0;
    }
    rsimp(&r);
    return r;
}

/* ---------- parser ---------- */

__attribute__((noreturn)) static void unexpected(int ch)
{
    begin(L_ERROR);
    wputs("unexpected ");
    wputc(ch);
    die();
}

static int peek(void)
{
    while (s < send && *s == ' ') s++;
    return s < send ? (unsigned char)*s : 0;
}

static int varidx(int ch)
{
    int i;
    for (i = 0; i < nv; i++)
        if (vars[i] == ch) return i;
    return 0;
}

static Rat pexpr(void);
static Rat punary(void);

/* each ( or leading sign recurses ~5 frames; the calc stack is small */
static void deeper(void)
{
    if (++nest > 24) fail("too many nested ( or signs");
}

static Rat patom(void)
{
    int ch = peek();
    Rat r;
    if (isdigit(ch) || ch == '.') {
        long long n = 0, d = 1;
        int digits = 0;
        while (s < send && isdigit((unsigned char)*s)) {
            n = ckadd(ckmul(n, 10), *s++ - '0');
            digits++;
        }
        if (s < send && *s == '.') {
            s++;
            while (s < send && isdigit((unsigned char)*s)) {
                n = ckadd(ckmul(n, 10), *s++ - '0');
                d = ckmul(d, 10);
                digits++;
            }
        }
        if (!digits) fail("a lone . isn't a number");
        if (s < send && *s == '.') fail("a number has two decimal points");
        {
            Q q;
            qnorm(&q, n, d);
            return rpoly(pconst(&q));
        }
    }
    if (isalpha(ch)) {
        s++;
        return rpoly(pvar(varidx(tolower(ch))));
    }
    if (ch == '(') {
        s++;
        deeper();
        r = pexpr();
        if (peek() != ')') fail("missing )");
        s++;
        nest--;
        return r;
    }
    if (!ch) fail("the expression ends too early");
    if (ch == ')') fail("extra )");
    unexpected(ch);
}

static Rat ppower(void)
{
    Rat b = patom(), ex, r;
    Q q;
    if (peek() != '^') return b;
    s++;
    ex = punary();
    if (!isnum(ex, &q) || q.d != 1) {
        begin(L_ERROR);
        wputs("exponent must be a whole number (got ");
        wrat(ex);
        wputc(')');
        die();
    }
    if ((q.n > MAXPOW || q.n < -MAXPOW) && (b.d || b.n->n > 1 || q.n > MAXE || q.n < -MAXE)) fail("exponent too big (max 60)");
    r = rpow(b, (int)q.n);
    rfree(b);
    rfree(ex);
    return r;
}

static Rat punary(void)
{
    Rat r;
    int ch = peek();
    if (ch != '+' && ch != '-') return ppower();
    s++;
    deeper();
    r = punary();
    nest--;
    if (ch == '-') {
        Q m;
        qset(&m, -1);
        replace(&r.n, pscale(r.n, &m));
    }
    return r;
}

static Rat pterm(void)
{
    Rat a = punary(), b, r;
    for (;;) {
        int ch = peek();
        if (ch == '*' || ch == '/') {
            s++;
            b = punary();
            r = ch == '*' ? rmul(a, b) : rdiv(a, b);
        } else if (isalnum(ch) || ch == '(' || ch == '.') {
            b = ppower();
            r = rmul(a, b);
        } else {
            return a;
        }
        rfree(a);
        rfree(b);
        a = r;
    }
}

static Rat pexpr(void)
{
    Rat a = pterm(), b, r;
    for (;;) {
        int ch = peek();
        if (ch != '+' && ch != '-') return a;
        s++;
        b = pterm();
        r = radd(a, b, ch == '-');
        rfree(a);
        rfree(b);
        a = r;
    }
}

static Rat parse(const char *start, const char *stop)
{
    Rat r;
    s = start;
    send = stop;
    r = pexpr();
    if (peek()) {
        if (*s == ')') fail("extra )");
        unexpected(*s);
    }
    return r;
}

static void parse_value(const char *start, const char *stop)
{
    int v;
    s = start;
    send = stop;
    if (!isalpha(peek())) fail("after a comma, write a value like x=3");
    v = varidx(tolower((unsigned char)*s++));
    if (peek() != '=') fail("after a comma, write a value like x=3");
    s++;
    if (assigned[v]) {
        begin(L_ERROR);
        wputc(vars[v]);
        wputs(" is given twice");
        die();
    }
    val[v] = pexpr();
    if (peek()) unexpected(*s);
    assigned[v] = 1;
}

static void addvar(int ch)
{
    int i;
    for (i = 0; i < nv; i++)
        if (vars[i] == ch) return;
    if (nv == NV) fail("too many letters (max 4)");
    for (i = nv++; i > 0 && vars[i - 1] > ch; i--) vars[i] = vars[i - 1];
    vars[i] = ch;
}

/* ---------- values: x=3 evaluates, x=2x-3 composes ---------- */

static int nassigned(void)
{
    int v, n = 0;
    for (v = 0; v < NV; v++) n += assigned[v];
    return n;
}

static int exprvals(void)
{
    Q q;
    int v;
    for (v = 0; v < NV; v++)
        if (assigned[v] && !isnum(val[v], &q)) return 1;
    return 0;
}

static void wvalues(void)
{
    int v, first = 1;
    for (v = 0; v < nv; v++) {
        if (!assigned[v]) continue;
        if (!first) wputs(", ");
        first = 0;
        wputc(vars[v]);
        wputc('=');
        wrat(val[v]);
    }
}

static Rat psubst(const Poly *p)
{
    Rat acc = rpoly(pnew()), t, u, pw;
    int i, v;
    for (i = 0; i < p->n; i++) {
        Term tm = p->t[i];
        Q zq;
        int zero = 0;
        for (v = 0; v < NV; v++) zero |= assigned[v] && tm.e[v] && isnum(val[v], &zq) && !zq.n;
        if (zero) continue;
        for (v = 0; v < NV; v++)
            if (assigned[v]) tm.e[v] = 0;
        t = rpoly(pnew());
        addterm(t.n, &tm.c, tm.e);
        for (v = 0; v < NV; v++) {
            if (!assigned[v] || !p->t[i].e[v]) continue;
            pw = rpow(val[v], p->t[i].e[v]);
            u = rmul(t, pw);
            rfree(t);
            rfree(pw);
            t = u;
        }
        u = radd(acc, t, 0);
        rfree(acc);
        rfree(t);
        acc = u;
    }
    return acc;
}

static Rat rsubst(Rat r)
{
    Rat n = psubst(r.n), d, q;
    if (!r.d) return n;
    d = psubst(r.d);
    q = rdiv(n, d);
    rfree(n);
    rfree(d);
    return q;
}

/* ---------- roots of one-variable polynomials ---------- */

static Root roots[MAXD + 1];
static int nroots;
static long long ip[MAXD + 1];
static int ideg;
static long long dv0[256], dvn[256];
static long long bqa[2], bqb[2];
static int nbq, bqmult, nquads;
static struct { long long a, b, c; int mult; } quads[MAXD / 2 + 1];
static Cx z[MAXD];
static int zm[MAXD], nz;
static long double dkerr;
static Pt pts[MAXPTS];
static int npts, pstrlen;
static char pstr[1024];

static Poly *gcf(const Poly *p, Q *k, uint8_t *m)
{
    Poly *r;
    long long g = 0, l = 1;
    int i, v, show = 0;
    for (v = 0; v < NV; v++) m[v] = MAXE;
    for (i = 0; i < p->n; i++) {
        g = gcd(g, p->t[i].c.n);
        l = lcm(l, p->t[i].c.d);
        for (v = 0; v < NV; v++)
            if (p->t[i].e[v] < m[v]) m[v] = p->t[i].e[v];
    }
    qnorm(k, p->t[0].c.n < 0 ? -g : g, l);
    r = pnew();
    for (i = 0; i < p->n; i++) {
        uint8_t e[NV];
        Q c;
        for (v = 0; v < NV; v++) e[v] = p->t[i].e[v] - m[v];
        qdiv(&c, &p->t[i].c, k);
        addterm(r, &c, e);
    }
    for (v = 0; v < NV; v++) show |= m[v];
    if (r->n > 1 && (show || !qone(k))) {
        begin(L_STEP);
        wputs("GCF ");
        wmono(k, m, 1);
        wputs(": ");
        wpoly(r);
        end();
    }
    return r;
}

static int intdense(const Poly *p, int v)
{
    int i, deg = todense(p, v, da);
    for (i = 0; i <= deg; i++) ip[i] = da[i].n;
    return deg;
}

static void wip(int v)
{
    int i;
    Poly *p;
    for (i = 0; i <= ideg; i++) qset(&da[i], ip[i]);
    p = fromdense(da, ideg, v);
    wpoly(p);
    pfree(p);
}

static void wlinfactor(long long p, long long q, int v)
{
    uint8_t e[NV] = { 0 };
    e[v] = 1;
    wmonoi(q, e, 1);
    e[v] = 0;
    if (p) wmonoi(-p, e, 0);
}

static void sortll(long long *a, int n)
{
    int i, j;
    for (i = 1; i < n; i++) {
        long long t = a[i];
        for (j = i; j > 0 && a[j - 1] > t; j--) a[j] = a[j - 1];
        a[j] = t;
    }
}

/* builds divisors from the prime factorization, -1 if there are more than 256.
   ponytail: trial division, so a prime factor past ~10^10 still takes minutes on the calc (clear stops it) */
static int divisors(long long n, long long *out)
{
    long long p, m;
    int k = 1, i, base, e, tick = 0;
    if (n < 0) n = -n;
    out[0] = 1;
    for (p = 2; n > 1; p += 1 + (p > 2)) {
        if (!(++tick & 4095)) poll();
        if (p > n / p) p = n;
        if (n % p) continue;
        for (e = 0; n % p == 0; e++) n /= p;
        if (k * (e + 1) > 256) return -1;
        base = k;
        for (m = 1; e--;) {
            m *= p;
            for (i = 0; i < base; i++) out[k++] = out[i] * m;
        }
    }
    sortll(out, k);
    return k;
}

static void add_root(long long p, long long q, int mult)
{
    int i;
    for (i = 0; i < nroots; i++) {
        if (roots[i].p == p && roots[i].q == q) {
            roots[i].mult += mult;
            return;
        }
    }
    roots[nroots].p = p;
    roots[nroots].q = q;
    roots[nroots].mult = mult;
    nroots++;
}

/* P(1) or P(-1), or 0 when it doesn't fit */
static int psum(int sgn, long long *out)
{
    long long t = 0;
    int k;
    for (k = 0; k <= ideg; k++)
        if (__builtin_add_overflow(t, sgn < 0 && (k & 1) ? -ip[k] : ip[k], &t)) return 0;
    *out = t;
    return 1;
}

/* divides ip by (qx - p) when p/q is a root */
static int try_root(long long p, long long q)
{
    static long long b[MAXD + 1];
    long double r = (long double)p / q, sum = 0, scale = 0, pw = 1, t;
    int k, big = fabsl(r) > 1;
    if (big) r = 1 / r;
    for (k = 0; k <= ideg; k++) {
        t = ip[big ? ideg - k : k] * pw;
        sum += t;
        scale += fabsl(t);
        pw *= r;
    }
    if (fabsl(sum) > 1e-9L * scale) return 0;
    b[ideg] = 0;
    for (k = ideg; k >= 1; k--) {
        long long t2 = ckadd(ip[k], ckmul(p, b[k]));
        if (t2 % q) return 0;
        b[k - 1] = t2 / q;
    }
    if (ckadd(ip[0], ckmul(p, b[0]))) return 0;
    for (k = 0; k < ideg; k++) ip[k] = b[k];
    ideg--;
    return 1;
}

static void wcandidates(int n0, int nn)
{
    int i, j, count = 0;
    for (i = 0; i < nn && count <= 4; i++)
        for (j = 0; j < n0 && count <= 4; j++) count += gcd(dv0[j], dvn[i]) == 1;
    if (count > 4) {
        wputs("none of them work");
        return;
    }
    wputs("none of ");
    for (i = 0; i < nn; i++) {
        for (j = 0; j < n0; j++) {
            if (gcd(dv0[j], dvn[i]) != 1) continue;
            if (--count < 0) break;
            wputs(G_PM);
            wfrac(dv0[j], dvn[i]);
            if (count) wputs(", ");
        }
    }
    wputs(" work");
}

static void find_roots(int v)
{
    int i, j, sgn, n0 = 0, nn = 0, found, any = 0, h1, hm;
    long long p1, pm1;
    long double bound;
    if (ideg < 2) return;
    begin(L_STEP);
    wputs("rational roots " G_PM "p/q: p|");
    wll(ip[0] < 0 ? -ip[0] : ip[0]);
    wputs(", q|");
    wll(ip[ideg]);
    end();
    while (ideg >= 2) {
        found = 0;
        n0 = divisors(ip[0], dv0);
        nn = divisors(ip[ideg], dvn);
        if (n0 < 0 || nn < 0) {
            step("too many candidates, skipping the rest");
            return;
        }
        /* cheap filters: every root is within the cauchy bound, and p/q a root means (q-p) | P(1), (q+p) | P(-1) */
        for (bound = 1, i = 0; i < ideg; i++)
            if (1 + fabsl((long double)ip[i] / ip[ideg]) > bound) bound = 1 + fabsl((long double)ip[i] / ip[ideg]);
        h1 = psum(1, &p1);
        hm = psum(-1, &pm1);
        for (i = 0; i < nn && !found; i++) {
            for (j = 0; j < n0 && !found; j++) {
                if ((long double)dv0[j] / dvn[i] > bound || gcd(dv0[j], dvn[i]) != 1) continue;
                for (sgn = 1; sgn >= -1 && !found; sgn -= 2) {
                    long long p = sgn * dv0[j], q = dvn[i];
                    if (h1 && (q == p ? p1 != 0 : p1 % (q - p) != 0)) continue;
                    if (hm && (q == -p ? pm1 != 0 : pm1 % (q + p) != 0)) continue;
                    poll();
                    if (!try_root(p, q)) continue;
                    found = any = 1;
                    add_root(p, q, 1);
                    begin(L_STEP);
                    wputc(vars[v]);
                    wputc('=');
                    wfrac(p, q);
                    wputs(": P(");
                    wfrac(p, q);
                    wputs(")=0, so (");
                    wlinfactor(p, q, v);
                    wputs(") is a factor");
                    end();
                    begin(L_STEP);
                    wputs("divide by (");
                    wlinfactor(p, q, v);
                    wputs("): ");
                    wip(v);
                    end();
                }
            }
        }
        if (!found) break;
    }
    if (ideg == 1) {
        add_root(-ip[0], ip[1], 1);
        begin(L_STEP);
        wputs("last factor: ");
        wlinfactor(-ip[0], ip[1], v);
        end();
        ideg = 0;
        ip[0] = 1;
    } else if (!any) {
        begin(L_STEP);
        wcandidates(n0, nn);
        end();
    } else {
        begin(L_STEP);
        wputs("no more rational roots in ");
        wip(v);
        end();
    }
}

static long long isqrt(long long n)
{
    long long r = (long long)sqrtl((long double)n);
    while (r > 0 && r > n / r) r--;
    while (r + 1 <= n / (r + 1)) r++;
    return r;
}

/* ponytail: stops looking for square factors past 10^6, so huge discriminants may not fully simplify */
static long long sqpart(long long n, long long *rest)
{
    static long long last_n = -1, last_s, last_r;
    long long s_ = 1, j, n0 = n;
    if (n == last_n) {
        *rest = last_r;
        return last_s;
    }
    for (j = 2; j <= n / j && j <= 1000000; j++) {
        if (!(j & 4095)) poll();
        while (n % (j * j) == 0) {
            n /= j * j;
            s_ *= j;
        }
    }
    *rest = n;
    last_n = n0;
    last_s = s_;
    last_r = n;
    return s_;
}

static void wbq(int i, int v)
{
    uint8_t e[NV] = { 0 };
    e[v] = 2;
    wputc('(');
    wmonoi(bqb[i], e, 1);
    e[v] = 0;
    wmonoi(-bqa[i], e, 0);
    wputc(')');
    if (bqmult > 1) wputs("^2");
}

/* x^4 + ... with only even powers whose x^2-quadratic has rational roots */
static int biquad(int v)
{
    long long a = ip[4], b = ip[2], c = ip[0], d, sq;
    int i;
    Q u;
    if (ideg != 4 || ip[1] || ip[3]) return 0;
    d = ckadd(ckmul(b, b), -ckmul(4, ckmul(a, c)));
    if (d < 0) return 0;
    sq = isqrt(d);
    if (sq * sq != d) return 0;
    begin(L_STEP);
    wputs("only even powers, so treat it as a quadratic in ");
    wputc(vars[v]);
    wputs("^2");
    end();
    for (i = 0; i < 2; i++) {
        qnorm(&u, ckadd(-b, i ? -sq : sq), ckmul(2, a));
        bqa[i] = u.n;
        bqb[i] = u.d;
    }
    if (fabsl((long double)bqa[0] / bqb[0]) > fabsl((long double)bqa[1] / bqb[1])) {
        long long t = bqa[0];
        bqa[0] = bqa[1];
        bqa[1] = t;
        t = bqb[0];
        bqb[0] = bqb[1];
        bqb[1] = t;
    }
    nbq = sq ? 2 : 1;
    bqmult = sq ? 1 : 2;
    begin(L_STEP);
    wip(v);
    wputs(" = ");
    for (i = 0; i < nbq; i++) wbq(i, v);
    end();
    ideg = 0;
    ip[0] = 1;
    return 1;
}

static void wmult(int mult)
{
    if (mult < 2) return;
    wputs(" (multiplicity ");
    wll(mult);
    wputc(')');
}

static void wld(long double x)
{
    long long n;
    char frac[7];
    int i, neg = x < 0;
    if (neg) x = -x;
    if (!(x < 9e12L)) fail("root too big to print");
    n = (long long)(x * 1000000.0L + 0.5L);
    if (neg && n) wputc('-');
    wll(n / 1000000);
    n %= 1000000;
    if (!n) return;
    for (i = 5; i >= 0; i--) {
        frac[i] = '0' + n % 10;
        n /= 10;
    }
    frac[6] = 0;
    for (i = 5; frac[i] == '0'; i--) frac[i] = 0;
    wputc('.');
    wputs(frac);
}

/* (num ± k·√r·i^neg)/den, or with sgn != 0 just the + or - root */
static void wradical(long long num, long long k, long long r, int neg, long long den, int sgn)
{
    int paren = den != 1 && num;
    if (paren) wputc('(');
    if (num) wll(num);
    wputs(sgn > 0 ? (num ? "+" : "") : sgn < 0 ? "-" : G_PM);
    if (k != 1 || (!neg && r == 1)) wll(k);
    if (neg) wputc('i');
    if (r != 1) {
        wputs(G_SQRT);
        wll(r);
    }
    if (paren) wputc(')');
    if (den != 1) {
        wputc('/');
        wll(den);
    }
}

static void wparen(long long n)
{
    if (n < 0) wputc('(');
    wll(n);
    if (n < 0) wputc(')');
}

static long long disc(long long a, long long b, long long c)
{
    return ckadd(ckmul(b, b), -ckmul(4, ckmul(a, c)));
}

static void quad_steps(long long a, long long b, long long c, int v)
{
    long long d = disc(a, b, c), r, sq;
    int neg = d < 0;
    sq = sqpart(neg ? -d : d, &r);
    begin(L_STEP);
    wputs("quadratic formula: a=");
    wll(a);
    wputs(", b=");
    wll(b);
    wputs(", c=");
    wll(c);
    end();
    begin(L_STEP);
    wputs("disc = ");
    wparen(b);
    wputs("^2-4(");
    wll(a);
    wputs(")(");
    wll(c);
    wputs(") = ");
    wll(d);
    end();
    if (sq != 1 || neg) {
        begin(L_STEP);
        wputs(G_SQRT);
        wll(d);
        wputs(" = ");
        if (sq != 1 || r == 1) wll(sq);
        if (neg) wputc('i');
        if (r != 1) {
            wputs(G_SQRT);
            wll(r);
        }
        end();
    }
    if (gcd(gcd(b, sq), 2 * a) != 1) {
        begin(L_STEP);
        wputc(vars[v]);
        wputs(" = ");
        wradical(-b, sq, r, neg, ckmul(2, a), 0);
        end();
    }
}

/* the simplified pieces of (-b ± √disc)/(2a) */
static int quad_parts(long long a, long long b, long long c, long long *num, long long *k, long long *r, long long *den)
{
    long long d = disc(a, b, c), sq, g;
    int neg = d < 0;
    sq = sqpart(neg ? -d : d, r);
    g = gcd(gcd(b, sq), ckmul(2, a));
    *num = -b / g;
    *k = sq / g;
    *den = 2 * a / g;
    return neg;
}

static void quad_result(long long a, long long b, long long c, int v, int mult)
{
    long long num, k, r, den, d = disc(a, b, c);
    long double re, im;
    int neg = quad_parts(a, b, c, &num, &k, &r, &den);
    begin(L_RESULT);
    wputc(vars[v]);
    wputs(" = ");
    wradical(num, k, r, neg, den, 0);
    wmult(mult);
    end();
    if (r == 1) return;
    re = (long double)-b / (2 * a);
    im = sqrtl((long double)(neg ? -d : d)) / (2 * a);
    begin(L_APPROX);
    wputc(vars[v]);
    wputs(" " G_APPROX " ");
    if (neg) {
        if (b) wld(re);
        wputs(G_PM);
        wld(im);
        wputc('i');
    } else if (!b) {
        wputs(G_PM);
        wld(im);
    } else {
        wld(re + im);
        wputs(", ");
        wld(re - im);
    }
    wmult(mult);
    end();
}

/* long double math is a softfloat call per operation on the ez80; keeping it in a few out-of-line helpers saves kbs */
__attribute__((noinline)) static void cmul(Cx *a, const Cx *b)
{
    long double t = a->r * b->r - a->i * b->i;
    a->i = a->r * b->i + a->i * b->r;
    a->r = t;
}

__attribute__((noinline)) static void cdiv(Cx *a, const Cx *b)
{
    long double m = b->r * b->r + b->i * b->i, t;
    if (m == 0) m = 1e-30L;
    t = (a->r * b->r + a->i * b->i) / m;
    a->i = (a->i * b->r - a->r * b->i) / m;
    a->r = t;
}

__attribute__((noinline)) static long double cnorm(const Cx *a)
{
    return fabsl(a->r) + fabsl(a->i);
}

/* a -= b, returns |b| relative to the new a */
__attribute__((noinline)) static long double csubrel(Cx *a, const Cx *b)
{
    a->r -= b->r;
    a->i -= b->i;
    return cnorm(b) / (1 + cnorm(a));
}

/* value of the d-th derivative of monic c (degree n) at z */
__attribute__((noinline)) static void horner(const long double *c, int n, int d, const Cx *zz, Cx *v)
{
    long double f;
    int j, t;
    v->r = v->i = 0;
    for (j = n; j >= d; j--) {
        for (f = c[j], t = 0; t < d; t++) f *= j - t;
        cmul(v, zz);
        v->r += f;
    }
}

static void numeric(int fmult)
{
    static long double c[MAXD + 1];
    Cx w2, u = { 0.4L / 0.98488578L, 0.9L / 0.98488578L }, p, d, t, sum;
    long double m, maxd, rad = 2, r, tk, stp;
    int k, j, it, mult, n = ideg, base = nz;
    for (k = 0; k <= n; k++) c[k] = (long double)ip[k] / ip[n];
    /* fujiwara bound, 2 max |c[n-k]|^(1/k), rounded up to a power of 2 so no powl is needed */
    for (k = 1; k <= n; k++) {
        for (r = tk = stp = 1, j = 0; j < k; j++) stp *= 2;
        for (; tk < fabsl(c[n - k]); tk *= stp) r *= 2;
        if (2 * r > rad) rad = 2 * r;
    }
    w2.r = rad;
    w2.i = 0;
    for (k = base; k < base + n; k++) {
        z[k] = w2;
        z[k].r -= c[n - 1] / n;
        zm[k] = 1;
        cmul(&w2, &u);
    }
    for (it = 0; it < 1000; it++) {
        poll();
        maxd = 0;
        for (k = base; k < base + n; k++) {
            horner(c, n, 0, &z[k], &p);
            d.r = 1;
            d.i = 0;
            for (j = base; j < base + n; j++) {
                if (j == k) continue;
                t = z[k];
                csubrel(&t, &z[j]);
                cmul(&d, &t);
            }
            cdiv(&p, &d);
            m = csubrel(&z[k], &p);
            if (!(m <= maxd)) maxd = m;
        }
        if (!(maxd < 1e300L)) fail("the numeric solver broke down");
        if (maxd < 1e-14L) break;
    }
    /* repeated roots come back as a tight cluster: merge it, then polish on the derivative where it's a simple root.
       the last newton step estimates the error */
    nz = base;
    for (k = base; k < base + n; k++) {
        if (!zm[k]) continue;
        sum = z[k];
        mult = 1;
        for (j = k + 1; j < base + n; j++) {
            t = z[j];
            csubrel(&t, &z[k]);
            /* ponytail: 1e-3 catches triple roots in noisy high degrees, but merges distinct irrational roots closer than that */
            if (!zm[j] || cnorm(&t) > 1e-3L * (1 + cnorm(&z[k]))) continue;
            sum.r += z[j].r;
            sum.i += z[j].i;
            mult++;
            zm[j] = 0;
        }
        sum.r /= mult;
        sum.i /= mult;
        for (it = 0, m = 0; it < 8; it++) {
            horner(c, n, mult - 1, &sum, &p);
            horner(c, n, mult, &sum, &d);
            if (d.r == 0 && d.i == 0) break;
            cdiv(&p, &d);
            m = csubrel(&sum, &p);
        }
        if (!(m <= dkerr)) dkerr = m;
        if (fabsl(sum.i) < 1e-7L * (1 + fabsl(sum.r))) sum.i = 0;
        z[nz] = sum;
        zm[nz++] = mult * fmult;
    }
    for (k = 1; k < nz; k++) {
        t = z[k];
        mult = zm[k];
        for (j = k; j > 0 && ((z[j - 1].i != 0) > (t.i != 0) || ((z[j - 1].i != 0) == (t.i != 0) && z[j - 1].r > t.r)); j--) {
            z[j] = z[j - 1];
            zm[j] = zm[j - 1];
        }
        z[j] = t;
        zm[j] = mult;
    }
    if (!(dkerr < 1e-3L)) fail("too sensitive to solve numerically");
    begin(L_STEP);
    wputs("no exact formula used for degree ");
    wll(n);
    wputs(", solving numerically");
    end();
}

static void numeric_result(int v)
{
    int k;
    for (k = 0; k < nz; k++) {
        if (z[k].i < 0) continue;
        begin(L_APPROX);
        wputc(vars[v]);
        wputs(" " G_APPROX " ");
        wld(z[k].r);
        if (z[k].i > 0) {
            wputs(G_PM);
            wld(z[k].i);
            wputc('i');
        }
        wmult(zm[k]);
        end();
    }
    if (nz && dkerr > 1e-7L) {
        begin(L_APPROX);
        wputs("these are sensitive, last digits may be off");
        end();
    }
}

static void addquad(long long a, long long b, long long c, int mult)
{
    int i;
    for (i = 0; i < nquads; i++)
        if (quads[i].a == a && quads[i].b == b && quads[i].c == c) {
            quads[i].mult += mult;
            return;
        }
    quads[nquads].a = a;
    quads[nquads].b = b;
    quads[nquads].c = c;
    quads[nquads++].mult = mult;
}

/* an integer quartic ip with no rational roots as (p1x^2+q1x+r1)(p2x^2+q2x+r2), if it splits over the integers */
static int quartic_split(int v)
{
    long long a4 = ip[4], a3 = ip[3], a2 = ip[2], a1 = ip[1], a0 = ip[0];
    int i, j, sg, n4, n0;
    if (ideg != 4) return 0;
    n4 = divisors(a4, dv0);
    n0 = divisors(a0, dvn);
    if (n4 < 0 || n0 < 0) return 0;
    for (i = 0; i < n4; i++)
        for (j = 0; j < n0; j++)
            for (sg = 1; sg >= -1; sg -= 2) {
                long long p1 = dv0[i], p2 = a4 / p1, r1 = sg * dvn[j], r2 = a0 / r1, det, q1, q2;
                poll();
                /* p2 q1 + p1 q2 = a3, r2 q1 + r1 q2 = a1 */
                det = ckadd(ckmul(p2, r1), -ckmul(p1, r2));
                if (det) {
                    q1 = ckadd(ckmul(a3, r1), -ckmul(p1, a1));
                    q2 = ckadd(ckmul(p2, a1), -ckmul(a3, r2));
                    if (q1 % det || q2 % det) continue;
                    q1 /= det;
                    q2 /= det;
                } else {
                    /* the two linear conditions coincide: q1 = (a3 - p1 q2)/p2 into the x^2 one gives
                       p1 q2^2 - a3 q2 + p2 (a2 - p1 r2 - r1 p2) = 0 */
                    long long k2 = ckadd(a2, -ckadd(ckmul(p1, r2), ckmul(r1, p2))), dd2 = ckadd(ckmul(a3, a3), -ckmul(4, ckmul(p1, ckmul(p2, k2)))), sq2;
                    if (dd2 < 0) continue;
                    sq2 = isqrt(dd2);
                    if (sq2 * sq2 != dd2 || (a3 + sq2) % (2 * p1)) continue;
                    q2 = (a3 + sq2) / (2 * p1);
                    if (ckadd(a3, -ckmul(p1, q2)) % p2) continue;
                    q1 = ckadd(a3, -ckmul(p1, q2)) / p2;
                    if (ckadd(ckmul(r2, q1), ckmul(r1, q2)) != a1) continue;
                }
                if (ckadd(ckadd(ckmul(p1, r2), ckmul(q1, q2)), ckmul(r1, p2)) != a2) continue;
                addquad(p1, q1, r1, 1);
                addquad(p2, q2, r2, 1);
                begin(L_STEP);
                wip(v);
                wputs(" splits into two quadratics");
                end();
                ideg = 0;
                ip[0] = 1;
                return 1;
            }
    return 0;
}

/* make dense rational c (degree deg) the integer primitive ip with a positive lead */
static void toip(const Q *c, int deg)
{
    long long l = 1, g = 0;
    int i;
    for (i = 0; i <= deg; i++) l = lcm(l, c[i].d);
    for (i = 0; i <= deg; i++) g = gcd(g, ckmul(c[i].n, l / c[i].d));
    if (c[deg].n < 0) g = -g;
    for (i = 0; i <= deg; i++) ip[i] = ckmul(c[i].n, l / c[i].d) / g;
    ideg = deg;
}

static void dderiv(const Q *c, int deg, Q *out)
{
    int i;
    Q k;
    for (i = 0; i <= MAXD; i++) qset(&out[i], 0);
    for (i = 1; i <= deg; i++) {
        qset(&k, i);
        qmul(&out[i - 1], &c[i], &k);
    }
}

static void exact_or_numeric(int v, int mult)
{
    if (ideg == 1) {
        add_root(-ip[0], ip[1], mult);
    } else if (ideg == 2) {
        addquad(ip[2], ip[1], ip[0], mult);
        quad_steps(ip[2], ip[1], ip[0], v);
    } else if (ideg == 4 && quartic_split(v)) {
        int i;
        for (i = nquads - 2; i < nquads; i++) {
            quads[i].mult = mult;
            quad_steps(quads[i].a, quads[i].b, quads[i].c, v);
        }
    } else if (ideg >= 1) {
        numeric(mult);
    }
}

static Q fac[2 * MAXD + 2];
static int fdeg[MAXD], fmul[MAXD];

/* yun's algorithm on ip: square-free parts fac (monic, packed) where part i repeats fmul[i] times.
   returns how many parts, 0 if ip is square-free or the numbers overflow */
static int sqfree(void)
{
    /* da/db/dq are free while this runs; sharing them keeps bss under the calc's 60 kb */
    static Q yt[MAXD + 1];
    Q *yp = da, *yd = db, *yc = dq;
    int n = ideg, nc, nd, k, i, nf = 0, at = 0;
    for (i = 0; i <= MAXD; i++) qset(&yp[i], i <= n ? ip[i] : 0);
    if (setjmp(soft_jmp)) {
        soft = 0;
        return 0;
    }
    soft = 1;
    dderiv(yp, n, yd);
    memcpy(ga, yp, sizeof ga);
    memcpy(gb, yd, sizeof gb);
    k = dgcd(n, n - 1);
    if (k > 0) {
        /* c = P/g, d = P'/g - c' */
        memcpy(gc, ga, sizeof gc);
        memcpy(yt, yp, sizeof yt);
        ddiv(yt, n, gc, k, yc);
        nc = n - k;
        memcpy(yt, yd, sizeof yt);
        ddiv(yt, n - 1, gc, k, yd);
        dderiv(yc, nc, yt);
        for (i = 0; i <= MAXD; i++) qsub(&yd[i], &yd[i], &yt[i]);
        for (nd = MAXD; nd >= 0 && !yd[nd].n; nd--);
        for (i = 1; nc > 0; i++) {
            int na;
            memcpy(ga, yc, sizeof ga);
            memcpy(gb, yd, sizeof gb);
            na = nd >= 0 ? dgcd(nc, nd) : (monic(ga, nc), nc);
            if (na < 0) longjmp(soft_jmp, 1);
            memcpy(gc, ga, sizeof gc);
            memcpy(yt, yc, sizeof yt);
            ddiv(yt, nc, gc, na, yc);
            nc -= na;
            if (nd >= 0) {
                memcpy(yt, yd, sizeof yt);
                ddiv(yt, nd, gc, na, yd);
            }
            dderiv(yc, nc, yt);
            for (k = 0; k <= MAXD; k++) {
                if (nd < 0) qset(&yd[k], 0);
                qsub(&yd[k], &yd[k], &yt[k]);
            }
            for (nd = MAXD; nd >= 0 && !yd[nd].n; nd--);
            if (na > 0) {
                memcpy(fac + at, gc, (na + 1) * sizeof(Q));
                fdeg[nf] = na;
                fmul[nf++] = i;
                at += na + 1;
            }
        }
    }
    soft = 0;
    return nf;
}

/* a quadratic ip whose discriminant is a perfect square: its two rational roots */
static int rational_quadratic(int mult)
{
    long long d, sq;
    Q a, b;
    if (ideg != 2 || (d = disc(ip[2], ip[1], ip[0])) < 0) return 0;
    sq = isqrt(d);
    if (sq * sq != d) return 0;
    qnorm(&a, ckadd(-ip[1], sq), ckmul(2, ip[2]));
    qnorm(&b, ckadd(-ip[1], -sq), ckmul(2, ip[2]));
    add_root(a.n, a.d, mult);
    add_root(b.n, b.d, mult);
    step("the discriminant is a perfect square, so the roots are rational");
    ideg = 0;
    ip[0] = 1;
    return 1;
}

/* ip has no rational roots: split off repeated factors, then each part exactly if it's a quadratic or splits
   into two, numerically otherwise */
static void leftover(int v)
{
    int nf = sqfree(), i, at;
    if (nf < 1 || (nf == 1 && fmul[0] == 1)) {
        if (!rational_quadratic(1)) exact_or_numeric(v, 1);
        return;
    }
    step("some factors repeat, so solve each once");
    for (at = 0, i = 0; i < nf; at += fdeg[i++] + 1) {
        toip(fac + at, fdeg[i]);
        begin(L_STEP);
        wputc('(');
        wip(v);
        wputs(")^");
        wll(fmul[i]);
        end();
        if (!rational_quadratic(fmul[i])) exact_or_numeric(v, fmul[i]);
    }
}

/* every root of p (one variable v): rational ones exactly, a leftover quadratic or biquadratic exactly,
   anything else numerically. fills roots/quad/bq/z; steps unless quiet */
static void analyze(const Poly *p, int v)
{
    Poly *r;
    Q k;
    uint8_t m[NV];
    nroots = nbq = nz = nquads = 0;
    dkerr = 0;
    r = gcf(p, &k, m);
    if (m[v]) {
        add_root(0, 1, m[v]);
        begin(L_STEP);
        wputc(vars[v]);
        if (m[v] > 1) {
            wputc('^');
            wll(m[v]);
        }
        wputs(" factor gives ");
        wputc(vars[v]);
        wputs("=0");
        end();
    }
    ideg = intdense(r, v);
    pfree(r);
    if (ideg == 1) {
        add_root(-ip[0], ip[1], 1);
        begin(L_STEP);
        wip(v);
        wputs("=0 gives ");
        wputc(vars[v]);
        wputc('=');
        wfrac(-ip[0], ip[1]);
        end();
        ideg = 0;
    }
    find_roots(v);
    if (ideg >= 2 && !biquad(v)) leftover(v);
}

/* ---------- real points: zeros and excluded values on the number line ---------- */

static char *sv_w, *sv_wend;

static int sv_clipped;

static void pt_begin(void)
{
    sv_clipped = clipped;
    sv_w = w;
    sv_wend = wend;
    w = pstr + pstrlen;
    wend = pstr + sizeof pstr;
    *w = 0;
}

static const char *pt_end(void)
{
    const char *str = pstr + pstrlen;
    pstrlen = w - pstr + 1;
    w = sv_w;
    wend = sv_wend;
    clipped = sv_clipped;
    return str;
}

static int ptpri(char tag)
{
    return tag == 'd' ? 2 : tag == 'h';
}

static void addpt(long double x, long long p, long long q, int mult, char tag, const char *str)
{
    int i;
    if (tag == 'h') mult = 0;
    for (i = 0; i < npts; i++) {
        if (fabsl(pts[i].v - x) > 1e-9L * (1 + fabsl(x))) continue;
        pts[i].mult += mult;
        if (ptpri(tag) > ptpri(pts[i].tag)) pts[i].tag = tag;
        return;
    }
    if (npts == MAXPTS) return;
    pts[npts].v = x;
    pts[npts].p = p;
    pts[npts].q = q;
    pts[npts].mult = mult;
    pts[npts].tag = tag;
    pts[npts].s = str;
    npts++;
}

static void quadpts(long long a, long long b, long long c, int mult, char tag)
{
    long long num, k, r, den;
    long double sq;
    int sgn;
    if (quad_parts(a, b, c, &num, &k, &r, &den)) return;
    sq = sqrtl((long double)disc(a, b, c));
    for (sgn = -1; sgn <= 1; sgn += 2) {
        pt_begin();
        wradical(num, k, r, 0, den, a > 0 ? sgn : -sgn);
        addpt((-b + sgn * sq) / (2.0L * a), 0, 0, mult, tag, pt_end());
    }
}

/* real roots from the last analyze() into pts; returns their total multiplicity */
static int collect(char tag)
{
    int i, total = 0;
    for (i = 0; i < nroots; i++) {
        Q x;
        qnorm(&x, roots[i].p, roots[i].q);
        pt_begin();
        wq(&x);
        addpt((long double)x.n / x.d, x.n, x.d, roots[i].mult, tag, pt_end());
        total += roots[i].mult;
    }
    for (i = 0; i < nquads; i++) {
        if (disc(quads[i].a, quads[i].b, quads[i].c) < 0) continue;
        quadpts(quads[i].a, quads[i].b, quads[i].c, quads[i].mult, tag);
        total += 2 * quads[i].mult;
    }
    for (i = 0; i < nbq; i++) {
        if ((bqa[i] > 0) != (bqb[i] > 0) || !bqa[i]) continue;
        quadpts(bqb[i], 0, -bqa[i], bqmult, tag);
        total += 2 * bqmult;
    }
    for (i = 0; i < nz; i++) {
        if (z[i].i) continue;
        pt_begin();
        wld(z[i].r);
        addpt(z[i].r, 0, 0, zm[i], tag, pt_end());
        total += zm[i];
    }
    return total;
}

static void sortpts(void)
{
    int i, j;
    for (i = 1; i < npts; i++) {
        Pt t = pts[i];
        for (j = i; j > 0 && pts[j - 1].v > t.v; j--) pts[j] = pts[j - 1];
        pts[j] = t;
    }
}

static int approxpts(void)
{
    int i;
    for (i = 0; i < npts; i++)
        if (!pts[i].q && !strchr(pts[i].s, G_SQRT[0])) return 1;
    return 0;
}

/* the zeros of dom as excluded points; quiet */
static void domain_pts(int v)
{
    if (!dom || domv != v) return;
    quiet++;
    analyze(dom, v);
    collect('h');
    quiet--;
}

static void domain_line(void)
{
    int i;
    if (!dom || domv < 0) return;
    npts = pstrlen = 0;
    domain_pts(domv);
    if (!npts) return;
    sortpts();
    begin(L_RESULT);
    wputc(vars[domv]);
    wputs(" " G_NE " ");
    for (i = 0; i < npts; i++) {
        if (i) wputs(", ");
        wputs(pts[i].s);
    }
    end();
}

/* ---------- commands ---------- */

static void wres(const char *prefix, Rat r)
{
    begin(L_RESULT);
    wputs(prefix);
    wrat(r);
    end();
}

/* n/d with deg n >= deg d as quotient + remainder/d, with the division steps */
static void mixed(Rat r, int v)
{
    int dn = todense(r.n, v, da), dd = todense(r.d, v, db), rd;
    Poly *q, *rem;
    if (dn < dd) return;
    if (dd == 1 && qone(&db[1])) {
        Q root = db[0];
        root.n = -root.n;
        begin(L_STEP);
        wputs("synthetic division by ");
        wlinear(v, &root);
        end();
        synthetic(&da[0], da, dn, &root, dq);
        rd = da[0].n ? 0 : -1;
    } else {
        begin(L_STEP);
        wputs("long division by ");
        wpoly(r.d);
        end();
        longdiv(da, dn, db, dd, v, dq);
        for (rd = dd - 1; rd >= 0 && !da[rd].n; rd--);
    }
    q = fromdense(dq, dn - dd, v);
    rem = fromdense(da, rd, v);
    begin(L_RESULT);
    wputs("= ");
    wpoly(q);
    if (rem->n == 1 && rem->t[0].c.d == 1) {
        wmono(&rem->t[0].c, rem->t[0].e, 0);
    } else {
        wputs("+(");
        wpoly(rem);
        wputc(')');
    }
    wputs("/");
    wpar(r.d);
    end();
    begin(L_RESULT);
    wputs("quotient ");
    wpoly(q);
    wputs(", remainder ");
    wpoly(rem);
    end();
    pfree(q);
    pfree(rem);
}

static int ratvar(Rat r)
{
    int v = univar(r.n), vd = r.d ? univar(r.d) : -1;
    if (v == -2 || vd == -2 || (v >= 0 && vd >= 0 && v != vd)) return -2;
    return v >= 0 ? v : vd;
}

static Rat compose(Rat r)
{
    Rat t;
    if (!exprvals()) return r;
    begin(L_STEP);
    wputs("substitute ");
    wvalues();
    end();
    t = rsubst(r);
    memset(assigned, 0, sizeof assigned);
    return t;
}

static void check_domain(void)
{
    Q x, y;
    if (!dom || domv < 0 || !assigned[domv] || !isnum(val[domv], &x)) return;
    qeval(&y, dom, domv, &x);
    if (y.n) return;
    begin(L_ERROR);
    wputs("undefined: ");
    wputc(vars[domv]);
    wputc('=');
    wq(&x);
    wputs(" makes a denominator 0");
    die();
}

static void do_expand(Rat r)
{
    int v;
    r = compose(r);
    if (nassigned()) {
        check_domain();
        v = univar(r.n);
        begin(L_STEP);
        wputs("P = ");
        wrat(r);
        end();
        if (!r.d && v >= 0 && v != iv && assigned[v] && nassigned() == 1 && pdeg(r.n, v) >= 1 && pdeg(r.n, v) <= MAXD) {
            int deg = todense(r.n, v, da);
            Q x;
            isnum(val[v], &x);
            begin(L_STEP);
            wputs("remainder theorem: P(");
            wq(&x);
            wputs(") is the remainder of P/(");
            wlinear(v, &x);
            wputc(')');
            end();
            synthetic(0, da, deg, &x, dq);
        } else {
            begin(L_STEP);
            wputs("plug in ");
            wvalues();
            end();
        }
        wres("= ", rsubst(r));
        return;
    }
    wres("= ", r);
    v = ratvar(r);
    if (r.d && v >= 0 && v != iv) mixed(r, v);
    domain_line();
}

static long long lf[2 * MAXD + 2];
static int nlf, lfd[MAXD], lfm[MAXD];

static int lfat(int k)
{
    int i, at = 0;
    for (i = 0; i < k; i++) at += lfd[i] + 1;
    return at;
}

/* the factored form of p, with steps, into buf */
static void factor_into(const Poly *p, char *buf, int cap)
{
    Poly *r;
    Q k;
    uint8_t m[NV];
    int v, i, pieces, paren, hasmono;
    char *sw, *se;
    r = gcf(p, &k, m);
    v = hasi(r) ? -2 : univar(r);
    nroots = nbq = nquads = 0;
    ideg = 0;
    nlf = 0;
    if (v >= 0) {
        ideg = intdense(r, v);
        find_roots(v);
        if (!rational_quadratic(1) && !biquad(v) && !quartic_split(v) && ideg >= 3) {
            int nf = sqfree(), j, at;
            if (nf > 1 || (nf == 1 && fmul[0] > 1)) {
                step("some factors repeat");
                for (at = 0, j = 0; j < nf; at += fdeg[j++] + 1) {
                    toip(fac + at, fdeg[j]);
                    if (ideg == 4 && quartic_split(v)) {
                        quads[nquads - 1].mult = quads[nquads - 2].mult = fmul[j];
                    } else if (ideg == 2) {
                        addquad(ip[2], ip[1], ip[0], fmul[j]);
                    } else {
                        memcpy(lf + lfat(nlf), ip, (ideg + 1) * sizeof(long long));
                        lfd[nlf] = ideg;
                        lfm[nlf++] = fmul[j];
                    }
                }
                ideg = 0;
            }
        }
    }
    pieces = nroots + nbq + nquads + nlf + (ideg >= 1) + (v == -2);
    hasmono = hasvars(m) || !qone(&k);
    paren = pieces > 1 || hasmono;
    for (i = 0; i < nroots; i++) paren |= roots[i].mult > 1;
    sw = w;
    se = wend;
    w = buf;
    wend = buf + cap;
    *w = 0;
    if (!pieces || hasvars(m) || (k.d == 1 && k.n != 1 && k.n != -1)) {
        wmono(&k, m, 1);
    } else if (k.n == -1 && k.d == 1) {
        wputc('-');
    } else if (k.d != 1) {
        wputc('(');
        wq(&k);
        wputc(')');
    }
    for (i = 0; i < nroots; i++) {
        if (paren) wputc('(');
        wlinfactor(roots[i].p, roots[i].q, v);
        if (paren) wputc(')');
        if (roots[i].mult > 1) {
            wputc('^');
            wll(roots[i].mult);
        }
    }
    for (i = 0; i < nbq; i++) wbq(i, v);
    for (i = 0; i < nquads; i++) {
        uint8_t e[NV] = { 0 };
        wputc('(');
        e[v] = 2;
        wmonoi(quads[i].a, e, 1);
        e[v] = 1;
        if (quads[i].b) wmonoi(quads[i].b, e, 0);
        e[v] = 0;
        if (quads[i].c) wmonoi(quads[i].c, e, 0);
        wputc(')');
        if (quads[i].mult > 1) {
            wputc('^');
            wll(quads[i].mult);
        }
    }
    for (i = 0; i < nlf; i++) {
        memcpy(ip, lf + lfat(i), (lfd[i] + 1) * sizeof(long long));
        ideg = lfd[i];
        wputc('(');
        wip(v);
        wputc(')');
        if (lfm[i] > 1) {
            wputc('^');
            wll(lfm[i]);
        }
        ideg = 0;
    }
    if (ideg >= 1) {
        if (paren) wputc('(');
        wip(v);
        if (paren) wputc(')');
    }
    if (v == -2) {
        if (paren) wputc('(');
        wpoly(r);
        if (paren) wputc(')');
    }
    w = sw;
    wend = se;
    pfree(r);
}

/* a factored form as a fraction's top needs parentheses around a sum; as the bottom, around anything
   but one group like (x-1)^2 or a bare power like x^2 */
static void wfactored(const char *f, int bottom)
{
    int depth = 0, i, groups = 0, sum = 0, plain = 1, wrap;
    for (i = 0; f[i]; i++) {
        if (f[i] == '(') {
            if (!depth++) groups++;
            plain = 0;
        } else if (f[i] == ')') {
            depth--;
        } else if (!depth && i && (f[i] == '+' || f[i] == '-')) {
            sum = 1;
        } else if (!depth && isdigit((unsigned char)f[i]) && (!i || f[i - 1] != '^')) {
            plain = 0;
        }
    }
    wrap = sum || (bottom && !(groups == 1 && f[0] == '(') && !(groups == 0 && plain));
    if (wrap) wputc('(');
    wputs(f);
    if (wrap) wputc(')');
}

static void do_factor(Rat r)
{
    static char top[400], bot[400];
    Q q;
    int i, has = 0;
    for (i = 0; i < NV; i++) has |= assigned[i] && isnum(val[i], &q);
    r = compose(r);
    if (!r.n->n) {
        wres("= ", r);
        return;
    }
    if (r.d) step("top:");
    factor_into(r.n, top, sizeof top);
    if (r.d) {
        step("bottom:");
        factor_into(r.d, bot, sizeof bot);
    }
    begin(L_RESULT);
    wputs("= ");
    if (r.d) {
        wfactored(top, 0);
        wputc('/');
        wfactored(bot, 1);
    } else {
        wputs(top);
    }
    end();
    if (has) {
        check_domain();
        begin(L_RESULT);
        wputs("at ");
        wvalues();
        wputs(": ");
        wrat(rsubst(r));
        end();
    }
    domain_line();
}

static int rootcmp(const Root *a, const Root *b)
{
    long double x = (long double)a->p / a->q, y = (long double)b->p / b->q;
    return x < y ? -1 : x > y;
}

static void solve_results(int v)
{
    int i, j;
    for (i = 1; i < nroots; i++) {
        Root t = roots[i];
        for (j = i; j > 0 && rootcmp(&roots[j - 1], &t) > 0; j--) roots[j] = roots[j - 1];
        roots[j] = t;
    }
    for (i = 0; i < nroots; i++) {
        begin(L_RESULT);
        wputc(vars[v]);
        wputs(" = ");
        wfrac(roots[i].p, roots[i].q);
        wmult(roots[i].mult);
        end();
    }
    for (i = 0; i < nquads; i++) quad_result(quads[i].a, quads[i].b, quads[i].c, v, quads[i].mult);
    for (i = 0; i < nbq; i++) quad_result(bqb[i], 0, -bqa[i], v, bqmult);
    numeric_result(v);
}

static Poly *divide_out(const Poly *a, const Poly *g, int v)
{
    int na = todense(a, v, ga), ng = todense(g, v, gc);
    ddiv(ga, na, gc, ng, gb);
    return fromdense(gb, na - ng, v);
}

/* the part of n whose zeros also zero an original denominator: those are extraneous */
static Poly *extraneous(Poly **n, int v)
{
    Poly *g, *t;
    int k;
    if (!dom || domv != v || !(*n)->n) return 0;
    k = dgcd(todense(*n, v, ga), todense(dom, v, gb));
    if (k <= 0) return 0;
    g = fromdense(ga, k, v);
    for (;;) {
        t = divide_out(*n, g, v);
        replace(n, t);
        k = dgcd(todense(*n, v, ga), todense(g, v, gb));
        if (k <= 0) break;
    }
    return g;
}

static const char *relname(int rel)
{
    return rel == '<' ? "<" : rel == '>' ? ">" : rel == 'L' ? G_LE : rel == 'G' ? G_GE : "=";
}

static int lead_sign(const Poly *p)
{
    return p && p->n ? (p->t[0].c.n > 0 ? 1 : -1) : 1;
}

static void wbound(int i)
{
    wputs(i < 0 ? "-" G_INF : i >= npts ? G_INF : pts[i].s);
}

static void inequality(Rat r, int v, int rel)
{
    static signed char sign[MAXPTS + 1];
    static char inc[2 * MAXPTS + 1];
    int i, k, strict = rel == '<' || rel == '>', want = rel == '>' || rel == 'G' ? 1 : -1, any = 0, n;
    begin(L_STEP);
    wputs("move everything to one side: ");
    wrat(r);
    wputs(relname(rel));
    wputc('0');
    end();
    if (!r.n->n) {
        begin(L_RESULT);
        wputs(strict ? "no solution" : "all real numbers");
        end();
        return;
    }
    npts = pstrlen = 0;
    if (v >= 0 && pdeg(r.n, v) >= 1) {
        analyze(r.n, v);
        collect('n');
    }
    if (r.d) {
        quiet++;
        analyze(r.d, v);
        collect('d');
        quiet--;
    }
    domain_pts(v);
    sortpts();
    n = npts;
    if (n) {
        begin(L_STEP);
        wputs("critical points: ");
        for (i = 0; i < n; i++) {
            if (i) wputs(", ");
            wputs(pts[i].s);
        }
        end();
    }
    /* sign right of the last point from the leading coefficients, then flip across odd multiplicities */
    sign[n] = lead_sign(r.n) * lead_sign(r.d);
    for (i = n - 1; i >= 0; i--) sign[i] = pts[i].mult & 1 ? -sign[i + 1] : sign[i + 1];
    for (i = 0; i <= n; i++) {
        begin(L_STEP);
        wputc('(');
        wbound(i - 1);
        wputc(',');
        wbound(i);
        wputs("): ");
        wputc(sign[i] > 0 ? '+' : '-');
        end();
    }
    /* elements 0..2n alternate interval, point, interval... */
    for (k = 0; k <= 2 * n; k++) inc[k] = k & 1 ? !strict && pts[k / 2].tag == 'n' : sign[k / 2] == want;
    begin(L_RESULT);
    for (k = 0; k <= 2 * n;) {
        int a, b;
        if (!inc[k]) {
            k++;
            continue;
        }
        for (a = k; k <= 2 * n && inc[k]; k++);
        b = k - 1;
        if (any) wputs(" " G_CUP " ");
        any = 1;
        if (a == b && (a & 1)) {
            wputc('{');
            wputs(pts[a / 2].s);
            wputc('}');
            continue;
        }
        wputc(a & 1 ? '[' : '(');
        wbound(a & 1 ? a / 2 : a / 2 - 1);
        wputc(',');
        wbound(b / 2);
        wputc(b & 1 ? ']' : ')');
    }
    if (!any) wputs("no solution");
    end();
    if (any) {
        begin(L_RESULT);
        for (any = 0, k = 0; k <= 2 * n;) {
            int a, b, lo, hi;
            if (!inc[k]) {
                k++;
                continue;
            }
            for (a = k; k <= 2 * n && inc[k]; k++);
            b = k - 1;
            if (any) wputs(" or ");
            any = 1;
            lo = a == 0;
            hi = b == 2 * n;
            if (lo && hi) {
                wputs("all real numbers");
                continue;
            }
            if (a == b && (a & 1)) {
                wputc(vars[v]);
                wputs(" = ");
                wputs(pts[a / 2].s);
                continue;
            }
            if (hi) {
                wputc(vars[v]);
                wputs(a & 1 ? G_GE : ">");
                wputs(pts[(a - 1) / 2].s);
                continue;
            }
            if (!lo) {
                wputs(pts[(a - 1) / 2].s);
                wputs(a & 1 ? G_LE : "<");
            }
            wputc(vars[v]);
            if (!hi) {
                wputs(b & 1 ? G_LE : "<");
                wputs(pts[b / 2].s);
            }
        }
        end();
    }
    if (approxpts()) step("decimal endpoints are rounded");
}

static void do_solve(Rat r, int rel)
{
    Poly *n, *g;
    int v, i;
    if (hasi(r.n) || (r.d && hasi(r.d))) fail("solve needs real coefficients");
    v = ratvar(r);
    if (v == -2) fail("solve needs one variable");
    if (v < 0 && domv >= 0) v = domv;
    if (rel != '=') {
        inequality(r, v, rel);
        return;
    }
    n = r.n;
    if (r.d) {
        begin(L_STEP);
        wputs("multiply both sides by ");
        wpar(r.d);
        wputs(": ");
        wpoly(n);
        wputs("=0");
        end();
    }
    g = v >= 0 ? extraneous(&n, v) : 0;
    (void)g;
    npts = pstrlen = 0;
    if (v < 0 || pdeg(n, v) < 1) {
        begin(L_RESULT);
        wputs(n->n ? "no solution" : "every value works");
        end();
        if (!n->n) domain_line();
    } else {
        analyze(n, v);
        solve_results(v);
    }
    /* zeros of an original denominator that cancelled away: solving by hand would find them */
    npts = pstrlen = 0;
    if (v >= 0) {
        domain_pts(v);
        if (r.d) {
            quiet++;
            analyze(r.d, v);
            collect('d');
            quiet--;
        }
    }
    sortpts();
    for (i = 0; i < npts; i++) {
        if (pts[i].tag != 'h') continue;
        begin(L_APPROX);
        wputc(vars[v]);
        wputs(" = ");
        wputs(pts[i].s);
        wputs(" is extraneous: it makes a denominator 0");
        end();
    }
}

/* "= ..." for d/dx, "d/dy = ..." when the letter isn't x */
static void wderiv(int v, Rat q)
{
    begin(L_RESULT);
    if (vars[v] != 'x') {
        wputs("d/d");
        wputc(vars[v]);
        wputc(' ');
    }
    wputs("= ");
    wrat(q);
    end();
}

static void do_deriv(Rat r)
{
    Poly *dn, *dd;
    uint8_t e[NV];
    int i, v = -1, x = varidx('x');
    if (exprvals()) fail("d/dx values must be numbers");
    for (i = 0; i < r.n->n; i++)
        if (vars[x] == 'x' && x != iv && r.n->t[i].e[x]) v = x;
    for (i = 0; r.d && i < r.d->n; i++)
        if (vars[x] == 'x' && x != iv && r.d->t[i].e[x]) v = x;
    for (i = 0; v < 0 && i < r.n->n; i++) {
        int k;
        for (k = 0; k < NV; k++)
            if (k != iv && r.n->t[i].e[k]) {
                v = k;
                break;
            }
    }
    for (i = 0; v < 0 && r.d && i < r.d->n; i++) {
        int k;
        for (k = 0; k < NV; k++)
            if (k != iv && r.d->t[i].e[k]) {
                v = k;
                break;
            }
    }
    if (v < 0) {
        step("no variable, so the slope is 0");
        wres("= ", rpoly(pnew()));
        return;
    }
    if (r.d) {
        Rat q;
        dn = pderiv(r.n, v);
        dd = pderiv(r.d, v);
        begin(L_STEP);
        wputs("quotient rule: (top'" G_DOT "bottom-top" G_DOT "bottom')/bottom^2");
        end();
        begin(L_STEP);
        wputs("top' = ");
        wpoly(dn);
        wputs(", bottom' = ");
        wpoly(dd);
        end();
        {
            Poly *a = pmul(dn, r.d), *b = pmul(r.n, dd);
            q.n = padd(a, b, 1);
            q.d = pmul(r.d, r.d);
            pfree(a);
            pfree(b);
        }
        rsimp(&q);
        wderiv(v, q);
        if (nassigned()) {
            check_domain();
            begin(L_RESULT);
            wputs("at ");
            wvalues();
            wputs(": ");
            wrat(rsubst(q));
            end();
        }
        return;
    }
    step("power rule, term by term");
    for (i = 0; i < r.n->n; i++) {
        const Term *t = &r.n->t[i];
        int k = t->e[v];
        Q c;
        qset(&c, k);
        qmul(&c, &c, &t->c);
        memcpy(e, t->e, NV);
        if (k) e[v] = k - 1;
        begin(L_STEP);
        wputs("d/d");
        wputc(vars[v]);
        wputc(' ');
        wmono(&t->c, t->e, 1);
        wputs(" = ");
        if (k > 1 && !qone(&t->c)) {
            wll(k);
            wputs(G_DOT);
            wqpar(&t->c);
            wvars(e);
            wputs(" = ");
        }
        if (k) wmono(&c, e, 1);
        else wputc('0');
        end();
    }
    dn = pderiv(r.n, v);
    wderiv(v, rpoly(dn));
    if (nassigned()) {
        begin(L_RESULT);
        wputs("at ");
        wvalues();
        wputs(": ");
        wrat(rsubst(rpoly(dn)));
        end();
    }
}

static int need_quadratic(Rat r, Q *a, Q *b, Q *c)
{
    int v = ratvar(r);
    if (r.d || v < 0 || v == iv || pdeg(r.n, v) != 2) return -1;
    todense(r.n, v, da);
    *a = da[2];
    *b = da[1];
    *c = da[0];
    return v;
}

/* h = -b/(2a) and k = c - a h^2 for ax^2+bx+c */
static void vertex_of(const Q *a, const Q *b, const Q *c, Q *h, Q *k)
{
    Q t;
    qset(&t, 2);
    qmul(&t, &t, a);
    qdiv(h, b, &t);
    h->n = -h->n;
    qmul(&t, h, h);
    qmul(&t, &t, a);
    qsub(k, c, &t);
}

/* a(x-h)^2+k */
static void wvertex(const Q *a, const Q *h, const Q *k, int v)
{
    uint8_t e[NV] = { 0 };
    Q t = *h;
    t.n = -t.n;
    if (a->n == -1 && a->d == 1) wputc('-');
    else if (!qone(a)) wqpar(a);
    if (h->n) {
        wputc('(');
        wputc(vars[v]);
        wmono(&t, e, 0);
        wputc(')');
    } else {
        wputc(vars[v]);
    }
    wputs("^2");
    if (k && k->n) wmono(k, e, 0);
}

static void do_vertex(Rat r)
{
    static Q a, b, c, h, k, t, u;
    uint8_t e[NV] = { 0 };
    int v = need_quadratic(r, &a, &b, &c);
    if (v < 0) fail("vertex form needs a quadratic like 2x^2+8x+3");
    vertex_of(&a, &b, &c, &h, &k);
    qdiv(&t, &b, &a);
    if (!qone(&a)) {
        begin(L_STEP);
        wputs("factor ");
        wq(&a);
        wputs(" out of the ");
        wputc(vars[v]);
        wputs(" terms: ");
        wqpar(&a);
        wputc('(');
        wputc(vars[v]);
        wputs("^2");
        e[v] = 1;
        wmono(&t, e, 0);
        e[v] = 0;
        wputc(')');
        if (c.n) wmono(&c, e, 0);
        end();
    }
    /* half of b/a is -h */
    u = h;
    u.n = -u.n;
    begin(L_STEP);
    wputs("half of ");
    wq(&t);
    wputs(" is ");
    wq(&u);
    wputs(", add and subtract ");
    wqpar(&u);
    wputs("^2 = ");
    qmul(&t, &u, &u);
    wq(&t);
    end();
    begin(L_STEP);
    wputs("= ");
    wvertex(&a, &h, 0, v);
    if (c.n || u.n) {
        qmul(&t, &t, &a);
        t.n = -t.n;
        wmono(&t, e, 0);
        if (c.n) wmono(&c, e, 0);
    }
    end();
    begin(L_RESULT);
    wputs("= ");
    wvertex(&a, &h, &k, v);
    end();
    begin(L_RESULT);
    wputs("vertex (");
    wq(&h);
    wputs(", ");
    wq(&k);
    wputc(')');
    end();
    begin(L_RESULT);
    wputs("axis ");
    wputc(vars[v]);
    wputs(" = ");
    wq(&h);
    wputs(a.n > 0 ? ", opens up, min " : ", opens down, max ");
    wq(&k);
    end();
}

static void wto(int v, int left, int up)
{
    wputc(vars[v]);
    wputs(left ? G_TO "-" G_INF : G_TO G_INF);
    wputs(up ? ": y" G_TO G_INF : ": y" G_TO "-" G_INF);
}

static void do_zeros(Rat r)
{
    int v = ratvar(r), i, real, dn, dd;
    static Q y0, d0, lc, x;
    if (v < 0 || v == iv || hasi(r.n)) fail("zeros needs a function of one variable");
    npts = pstrlen = 0;
    dn = pdeg(r.n, v);
    dd = r.d ? pdeg(r.d, v) : 0;
    real = 0;
    if (dn >= 1) {
        analyze(r.n, v);
        real = collect('n');
        sortpts();
    }
    for (i = 0; i < npts; i++) {
        begin(L_RESULT);
        wputc(vars[v]);
        wputs(" = ");
        wputs(pts[i].s);
        wputs(pts[i].mult & 1 ? ", crosses" : ", touches");
        wmult(pts[i].mult);
        end();
    }
    if (dn >= 1 && !npts) {
        begin(L_RESULT);
        wputs("no real zeros");
        end();
    }
    if (dn - real > 0) {
        begin(L_APPROX);
        wputs("plus ");
        wll(dn - real);
        wputs(" complex zeros (solve lists them)");
        end();
    }
    npts = pstrlen = 0;
    if (r.d) {
        quiet++;
        analyze(r.d, v);
        collect('d');
        quiet--;
    }
    i = npts;
    domain_pts(v);
    sortpts();
    {
        int k, zero_out = 0;
        for (k = 0; k < npts; k++) zero_out |= fabsl(pts[k].v) < 1e-12L;
        if (!zero_out) {
            qset(&x, 0);
            qeval(&y0, r.n, v, &x);
            qset(&d0, 1);
            if (r.d) qeval(&d0, r.d, v, &x);
            qdiv(&y0, &y0, &d0);
            begin(L_RESULT);
            wputs("y-intercept (0, ");
            wq(&y0);
            wputc(')');
            end();
        }
        for (k = 0; k < npts; k++) {
            begin(L_RESULT);
            if (pts[k].tag == 'd') {
                wputs("vertical asymptote ");
                wputc(vars[v]);
                wputs(" = ");
                wputs(pts[k].s);
            } else {
                wputs("hole at ");
                wputc(vars[v]);
                wputs(" = ");
                wputs(pts[k].s);
                if (pts[k].q) {
                    qnorm(&x, pts[k].p, pts[k].q);
                    qeval(&y0, r.n, v, &x);
                    qset(&d0, 1);
                    if (r.d) qeval(&d0, r.d, v, &x);
                    qdiv(&y0, &y0, &d0);
                    wputs(", y = ");
                    wq(&y0);
                } else {
                    wputs(", y " G_APPROX " ");
                    wld(ldeval(r.n, v, pts[k].v) / (r.d ? ldeval(r.d, v, pts[k].v) : 1));
                }
            }
            end();
        }
    }
    (void)i;
    lc = r.n->t[0].c;
    begin(L_RESULT);
    if (!r.d) {
        wputs("degree ");
        wll(dn);
        wputs(", leading coefficient ");
        wq(&lc);
        end();
        begin(L_RESULT);
        wto(v, 1, (lc.n > 0) == !(dn & 1));
        wputs(", ");
        wto(v, 0, lc.n > 0);
    } else if (dn < dd) {
        wputs("horizontal asymptote y = 0");
    } else if (dn == dd) {
        wputs("horizontal asymptote y = ");
        qdiv(&lc, &lc, &r.d->t[0].c);
        wq(&lc);
    } else {
        int qd;
        Poly *q;
        todense(r.n, v, da);
        todense(r.d, v, db);
        ddiv(da, dn, db, dd, dq);
        q = fromdense(dq, dn - dd, v);
        qd = dn - dd;
        wputs(qd == 1 ? "slant asymptote y = " : "end behavior like y = ");
        wpoly(q);
        pfree(q);
    }
    end();
}

static void do_inverse(Rat r)
{
    static Q a, b, c, h, k, t;
    int v = ratvar(r), dn, dd;
    uint8_t e[NV] = { 0 };
    Rat f;
    if (v < 0 || v == iv) fail("inverse needs a function of one variable");
    dn = pdeg(r.n, v);
    dd = r.d ? pdeg(r.d, v) : 0;
    begin(L_STEP);
    wputs("y = ");
    wrat(r);
    wputs(", swap ");
    wputc(vars[v]);
    wputs(" and y, solve for y");
    end();
    if (dn == 2 && !dd) {
        need_quadratic(r, &a, &b, &c);
        vertex_of(&a, &b, &c, &h, &k);
        begin(L_STEP);
        wputs("vertex form: y = ");
        wvertex(&a, &h, &k, v);
        end();
        begin(L_RESULT);
        wputs("f^-1(");
        wputc(vars[v]);
        wputs(") = ");
        if (h.n) wq(&h);
        wputs(G_PM G_SQRT "(");
        f.n = pvar(v);
        e[v] = 0;
        t = k;
        t.n = -t.n;
        addterm(f.n, &t, e);
        f.d = 0;
        qset(&t, 1);
        qdiv(&t, &t, &a);
        replace(&f.n, pscale(f.n, &t));
        wrat(f);
        wputc(')');
        end();
        begin(L_APPROX);
        wputs("not one-to-one: + for ");
        wputc(vars[v]);
        wputs(G_GE);
        wq(&h);
        wputs(", - for ");
        wputc(vars[v]);
        wputs(G_LE);
        wq(&h);
        end();
        return;
    }
    if (dn > 1 || dd > 1 || (dn < 1 && dd < 1)) fail("inverse works for linear, quadratic and (ax+b)/(cx+d)");
    /* f = (a x + b)/(c x + d)  ->  f^-1 = (b - d x)/(c x - a) */
    {
        static Q A, B, C, D;
        todense(r.n, v, da);
        A = da[1];
        B = da[0];
        qset(&C, 0);
        qset(&D, 1);
        if (r.d) {
            todense(r.d, v, db);
            C = db[1];
            D = db[0];
        }
        qmul(&t, &A, &D);
        qmul(&h, &B, &C);
        qsub(&t, &t, &h);
        if (!t.n) fail("this function is constant, so it has no inverse");
        D.n = -D.n;
        A.n = -A.n;
        e[v] = 1;
        f.n = pnew();
        addterm(f.n, &D, e);
        e[v] = 0;
        addterm(f.n, &B, e);
        if (C.n) {
            f.d = pnew();
            e[v] = 1;
            addterm(f.d, &C, e);
            e[v] = 0;
            addterm(f.d, &A, e);
        } else {
            f.d = pconst(&A);
        }
        rsimp(&f);
        begin(L_RESULT);
        wputs("f^-1(");
        wputc(vars[v]);
        wputs(") = ");
        wrat(f);
        end();
    }
}

/* ---------- systems ---------- */

static Q mx[NV + 1][NV + 1];
static int mrows, mcols, mvar[NV];

static void wrow(int r)
{
    uint8_t e[NV];
    int j, first = 1;
    for (j = 0; j < mcols; j++) {
        if (!mx[r][j].n) continue;
        memset(e, 0, NV);
        e[mvar[j]] = 1;
        wmono(&mx[r][j], e, first);
        first = 0;
    }
    if (first) wputc('0');
    wputc('=');
    wq(&mx[r][mcols]);
}

static void rowop(int r, int p, const Q *f)
{
    Q t;
    int j;
    for (j = 0; j <= mcols; j++) {
        qmul(&t, f, &mx[p][j]);
        qsub(&mx[r][j], &mx[r][j], &t);
    }
}

static void linear_system(Poly **eq, int n)
{
    int i, j, row = 0, piv[NV + 1], col, free_ = 0;
    uint8_t e[NV];
    mrows = n;
    for (i = 0; i < n; i++)
        for (j = 0; j <= mcols; j++) qset(&mx[i][j], 0);
    for (i = 0; i < n; i++)
        for (j = 0; j < eq[i]->n; j++) {
            const Term *t = &eq[i]->t[j];
            int k, c = mcols;
            for (k = 0; k < mcols; k++)
                if (t->e[mvar[k]]) c = k;
            mx[i][c] = t->c;
            if (c == mcols) mx[i][c].n = -mx[i][c].n;
        }
    step("as rows:");
    for (i = 0; i < n; i++) {
        begin(L_STEP);
        wputc('R');
        wll(i + 1);
        wputs(": ");
        wrow(i);
        end();
    }
    for (col = 0; col < mcols && row < n; col++) {
        int p;
        for (p = row; p < n && !mx[p][col].n; p++);
        if (p == n) continue;
        if (p != row) {
            for (j = 0; j <= mcols; j++) {
                Q t = mx[p][j];
                mx[p][j] = mx[row][j];
                mx[row][j] = t;
            }
            begin(L_STEP);
            wputs("swap R");
            wll(row + 1);
            wputs(" and R");
            wll(p + 1);
            end();
        }
        if (!qone(&mx[row][col])) {
            static Q f;
            f = mx[row][col];
            for (j = 0; j <= mcols; j++) qdiv(&mx[row][j], &mx[row][j], &f);
            begin(L_STEP);
            wputc('R');
            wll(row + 1);
            wputs(" = R");
            wll(row + 1);
            wputc('/');
            wqpar(&f);
            wputs(": ");
            wrow(row);
            end();
        }
        for (i = 0; i < n; i++) {
            static Q f;
            f = mx[i][col];
            if (i == row || !f.n) continue;
            rowop(i, row, &f);
            begin(L_STEP);
            wputc('R');
            wll(i + 1);
            wputs(" = R");
            wll(i + 1);
            if (f.n < 0) wputc('+');
            else wputc('-');
            if (f.n < 0) f.n = -f.n;
            if (!qone(&f)) wqpar(&f);
            wputc('R');
            wll(row + 1);
            wputs(": ");
            wrow(i);
            end();
        }
        piv[row++] = col;
    }
    for (i = row; i < n; i++) {
        if (!mx[i][mcols].n) continue;
        begin(L_STEP);
        wputc('R');
        wll(i + 1);
        wputs(" says 0=");
        wq(&mx[i][mcols]);
        end();
        begin(L_RESULT);
        wputs("no solution");
        end();
        return;
    }
    for (i = 0; i < row; i++) {
        begin(L_RESULT);
        wputc(vars[mvar[piv[i]]]);
        wputs(" = ");
        {
            int first = 1;
            if (mx[i][mcols].n) {
                wq(&mx[i][mcols]);
                first = 0;
            }
            for (j = piv[i] + 1; j < mcols; j++) {
                Q t = mx[i][j];
                if (!t.n) continue;
                t.n = -t.n;
                memset(e, 0, NV);
                e[mvar[j]] = 1;
                wmono(&t, e, first);
                first = 0;
            }
            if (first) wputc('0');
        }
        end();
    }
    for (j = 0; j < mcols; j++) {
        for (i = 0; i < row && piv[i] != j; i++);
        if (i < row) continue;
        free_ = 1;
        begin(L_RESULT);
        wputc(vars[mvar[j]]);
        wputs(" can be any number");
        end();
    }
    if (free_) step("infinitely many solutions");
}

static int total_degree(const Poly *p)
{
    int i, v, d = 0;
    for (i = 0; i < p->n; i++) {
        int t = 0;
        for (v = 0; v < NV; v++) t += p->t[i].e[v];
        if (t > d) d = t;
    }
    return d;
}

static void wpair(int u, const Q *qu, long double lu, int v, const Q *qv, long double lv)
{
    int exact = qu != 0;
    begin(exact ? L_RESULT : L_APPROX);
    wputc('(');
    wputc(vars[u < v ? u : v]);
    wputs(", ");
    wputc(vars[u < v ? v : u]);
    wputs(exact ? ") = (" : ") " G_APPROX " (");
    if (exact) wq(u < v ? qu : qv);
    else wld(u < v ? lu : lv);
    wputs(", ");
    if (exact) wq(u < v ? qv : qu);
    else wld(u < v ? lv : lu);
    wputc(')');
    end();
}

/* one linear and one polynomial equation in two variables: substitute */
static void substitution(Poly *lin, Poly *other, int u, int v)
{
    Rat expr, sub;
    static Q cu, t, x;
    int i;
    uint8_t e[NV] = { 0 };
    qset(&cu, 0);
    for (i = 0; i < lin->n; i++)
        if (lin->t[i].e[u]) cu = lin->t[i].c;
    /* u = -(lin - cu·u)/cu */
    expr.n = pnew();
    for (i = 0; i < lin->n; i++) {
        if (lin->t[i].e[u]) continue;
        qdiv(&t, &lin->t[i].c, &cu);
        t.n = -t.n;
        addterm(expr.n, &t, lin->t[i].e);
    }
    expr.d = 0;
    begin(L_STEP);
    wputs("from the linear one: ");
    wputc(vars[u]);
    wputs(" = ");
    wrat(expr);
    end();
    memset(assigned, 0, sizeof assigned);
    assigned[u] = 1;
    val[u] = expr;
    sub = psubst(other);
    assigned[u] = 0;
    begin(L_STEP);
    wputs("substitute: ");
    wrat(sub);
    wputs("=0");
    end();
    if (sub.d || pdeg(sub.n, v) < 1) {
        begin(L_RESULT);
        wputs(sub.n->n ? "no solution" : "infinitely many solutions");
        end();
        return;
    }
    analyze(sub.n, v);
    for (i = 0; i < nroots; i++) {
        qnorm(&x, roots[i].p, roots[i].q);
        qeval(&t, expr.n, v, &x);
        wpair(u, &t, 0, v, &x, 0);
    }
    i = nroots;
    npts = pstrlen = 0;
    nroots = 0;
    collect('n');
    if (!i && !npts) {
        begin(L_RESULT);
        wputs("no real solutions");
        end();
    }
    for (i = 0; i < npts; i++) {
        if (pts[i].q) continue;
        wpair(u, 0, ldeval(expr.n, v, pts[i].v), v, 0, pts[i].v);
    }
    (void)e;
}

static void do_system(const char **part, const char **pend, int n)
{
    static Poly *eq[NV + 1];
    int i, v, used[NV] = { 0 }, nonlin = -1, lin = -1;
    if (n < 2) fail("a system needs at least two equations, split by commas");
    for (i = 0; i < n; i++) {
        const char *p, *rel = 0;
        Rat l, r, d;
        for (p = part[i]; p < pend[i]; p++)
            if (*p == '=') rel = p;
        l = parse(part[i], rel ? rel : pend[i]);
        if (rel) {
            r = parse(rel + 1, pend[i]);
            d = radd(l, r, 1);
            rfree(l);
            rfree(r);
        } else {
            d = l;
        }
        if (d.d) fail("systems need polynomial equations, no fractions with variables");
        eq[i] = d.n;
        if (hasi(eq[i])) fail("systems need real coefficients");
        for (v = 0; v < NV; v++)
            for (int j = 0; j < eq[i]->n; j++) used[v] |= eq[i]->t[j].e[v] != 0;
        if (total_degree(eq[i]) > 1) nonlin = i;
        else lin = i;
    }
    for (mcols = 0, v = 0; v < NV; v++)
        if (used[v]) mvar[mcols++] = v;
    if (!mcols) fail("no variables to solve for");
    if (nonlin < 0) {
        linear_system(eq, n);
        return;
    }
    if (n != 2 || mcols != 2 || lin < 0) fail("taproot solves linear systems and one linear + one other equation in two variables");
    {
        int u = -1;
        for (i = 0; i < eq[lin]->n; i++) {
            const Term *t = &eq[lin]->t[i];
            for (v = 0; v < NV; v++)
                if (t->e[v] && u < 0) u = v;
        }
        if (u < 0) fail("the linear equation has no variable");
        /* prefer solving for a variable with coefficient 1 */
        for (i = 0; i < eq[lin]->n; i++) {
            const Term *t = &eq[lin]->t[i];
            for (v = 0; v < NV; v++)
                if (t->e[v] && (t->c.n == 1 || t->c.n == -1) && t->c.d == 1) u = v;
        }
        substitution(eq[lin], eq[nonlin], u, mvar[0] == u ? mvar[1] : mvar[0]);
    }
}

/* ---------- entry ---------- */

/* the one relation in [a, b): returns its code ('=', '<', '>', 'L' for <=, 'G' for >=), sets *at and *len */
static int find_rel(const char *a, const char *b, const char **at, int *len)
{
    const char *p;
    int rel = 0, depth = 0;
    for (p = a; p < b; p++) {
        int r = *p == '=' ? '=' : *p == '<' ? '<' : *p == '>' ? '>' : *p == G_LE[0] ? 'L' : *p == G_GE[0] ? 'G' : 0;
        int l = 1;
        depth += (*p == '(') - (*p == ')');
        if (!r) continue;
        if (depth) fail("= and inequality signs can't go inside ( )");
        if ((r == '<' || r == '>') && p + 1 < b && p[1] == '=') {
            r = r == '<' ? 'L' : 'G';
            l = 2;
        }
        if (rel) fail("only one = or inequality sign allowed");
        rel = r;
        *at = p;
        *len = l;
        p += l - 1;
    }
    return rel;
}

/* "y=..." for the function commands: the left side must be one letter */
static const char *rhs_of(const char *a, const char *at, int len)
{
    while (a < at && *a == ' ') a++;
    if (at - a < 1 || !isalpha((unsigned char)*a)) fail("write it as y=... or just the expression");
    for (a++; a < at; a++)
        if (*a != ' ') fail("write it as y=... or just the expression");
    return at + len;
}

void cas_run(int cmd, const char *input)
{
    const char *part[NV + 1], *pend[NV + 1], *at = 0, *p;
    int cur = 0, depth = 0, i, rel = 0, rlen = 0;
    Rat r;

    cas_nlines = textlen = hidden = quiet = soft = 0;
    nv = nest = 0;
    iv = -1;
    nroots = nbq = nz = npts = pstrlen = nquads = 0;
    dom = 0;
    domv = -1;
    memset(assigned, 0, sizeof assigned);
    for (i = 0; i < POOL; i++) pool[i].used = 0;
    if (setjmp(fail_jmp)) return;

    for (p = input; *p; p++)
        if (isalpha((unsigned char)*p)) addvar(tolower((unsigned char)*p));
    for (i = 0; i < nv; i++)
        if (vars[i] == 'i') iv = i;
    part[0] = input;
    for (p = input; *p; p++) {
        if (*p == '(') depth++;
        else if (*p == ')') depth--;
        else if (*p == ',' && depth <= 0) {
            if (cur == NV) fail("too many parts after commas");
            pend[cur++] = p;
            part[cur] = p + 1;
        }
    }
    pend[cur] = p;
    for (p = part[0]; p < pend[0] && *p == ' '; p++);
    if (p == pend[0]) fail("type an expression first");

    if (cmd == CMD_SYSTEM) {
        do_system(part, pend, cur + 1);
        return;
    }
    rel = find_rel(part[0], pend[0], &at, &rlen);
    for (i = 1; i <= cur; i++) parse_value(part[i], pend[i]);
    if (cmd == CMD_SOLVE && cur) fail("solve finds the values itself, drop the , x=");
    if (rel && cmd != CMD_SOLVE) {
        if (rel != '=' || cmd == CMD_EXPAND || cmd == CMD_FACTOR || cmd == CMD_DERIV) fail("use solve for equations and inequalities");
        r = parse(rhs_of(part[0], at, rlen), pend[0]);
    } else if (rel) {
        Rat lhs = parse(part[0], at), rhs = parse(at + rlen, pend[0]);
        r = radd(lhs, rhs, 1);
        if (rel == '=' && (rhs.n->n || rhs.d)) {
            begin(L_STEP);
            wputs("move everything to one side: ");
            wrat(r);
            wputs("=0");
            end();
        }
        rfree(lhs);
        rfree(rhs);
    } else {
        r = parse(part[0], pend[0]);
    }
    switch (cmd) {
    case CMD_EXPAND: do_expand(r); break;
    case CMD_FACTOR: do_factor(r); break;
    case CMD_SOLVE: do_solve(r, rel ? rel : '='); break;
    case CMD_DERIV: do_deriv(r); break;
    case CMD_VERTEX: do_vertex(r); break;
    case CMD_ZEROS: do_zeros(r); break;
    case CMD_INVERSE: do_inverse(r); break;
    }
}
