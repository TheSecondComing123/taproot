#include "cas.h"
#include <ctype.h>
#include <limits.h>
#include <setjmp.h>
#include <stdarg.h>
#include <string.h>
#include <ti/error.h>
#include <ti/real.h>

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

typedef struct { int32_t n, d; } Q;
typedef struct { Q c; uint8_t e[NV]; } Term;
typedef struct { uint8_t used; int n; Term t[MAXT]; } Poly;
typedef struct { Poly *n, *d; } Rat; /* d == 0 means 1 */
/* floating point is the os's 14-digit bcd reals: the routines live in rom, so the program carries none */
typedef real_t R;
typedef struct { R r, i; } Cx;
typedef struct { int32_t p, q; int mult; } Root;
/* a real point on the number line: a zero of the top ('n'), of the bottom ('d') or a hole ('h') */
typedef struct { R v; int32_t p, q; int mult; char tag; const char *s; } Pt;

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
static int nest, typed_mixed;
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

static void wll(int32_t v)
{
    char tmp[24];
    int n = 0;
    uint32_t u = v < 0 ? -(uint32_t)v : (uint32_t)v;
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

static void wq(const Q *a);
static void wqpar(const Q *a);
static void wpoly(const Poly *p);
static void wrat(Rat r);
static void wreal(const R *x);

#define OPEN 8
#define MORE 16

static void wcoef(const Q *c0, int first, int hv);
static void wlin(const Q *m, int ch, const Q *b, int par);

/* one call per output line instead of a run of w* calls: begin a line of this kind (| MORE keeps
   writing the open one), write f with %s %c %d(int) %l(int32_t) %q %Q(Q *) %p(Poly *) %r(Rat)
   %R(R *) %M %T(Q *, a term's coefficient) %L %P(Q *m, letter, Q *b: m letter + b), then end it (| OPEN leaves it open) */
static void say(int kind, const char *f, ...)
{
    va_list ap;
    va_start(ap, f);
    if (!(kind & MORE)) begin(kind & 7);
    for (; *f; f++) {
        if (*f != '%') {
            wputc(*f);
            continue;
        }
        switch (*++f) {
        case 's': wputs(va_arg(ap, const char *)); break;
        case 'c': wputc(va_arg(ap, int)); break;
        case 'd': wll(va_arg(ap, int)); break;
        case 'l': wll(va_arg(ap, int32_t)); break;
        case 'q': wq(va_arg(ap, const Q *)); break;
        case 'Q': wqpar(va_arg(ap, const Q *)); break;
        case 'p': wpoly(va_arg(ap, const Poly *)); break;
        case 'r': wrat(va_arg(ap, Rat)); break;
        case 'R': wreal(va_arg(ap, const R *)); break;
        /* a term's coefficient, first or with its sign */
        case 'M':
        case 'T': wcoef(va_arg(ap, const Q *), *f == 'M', 1); break;
        /* m ch + b, P in parentheses */
        case 'L':
        case 'P': {
            const Q *m = va_arg(ap, const Q *);
            int ch = va_arg(ap, int);
            wlin(m, ch, va_arg(ap, const Q *), *f == 'P');
            break;
        }
        }
    }
    va_end(ap);
    if (!(kind & OPEN)) end();
}

static void step(const char *msg)
{
    say(L_STEP, msg);
}

__attribute__((noreturn)) static void die(void)
{
    end();
    longjmp(fail_jmp, 1);
}

__attribute__((noreturn)) static void fail(const char *msg)
{
    say(L_ERROR | OPEN, "%s", msg);
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

static int32_t ckmul(int32_t a, int32_t b)
{
    uint32_t ua, ub;
    if ((uint32_t)a + 46340 <= 92680 && (uint32_t)b + 46340 <= 92680) return a * b;
    ua = a < 0 ? -(uint32_t)a : (uint32_t)a;
    ub = b < 0 ? -(uint32_t)b : (uint32_t)b;
    if (ua && ub > INT32_MAX / ua) too_big();
    return a * b;
}

static int32_t ckadd(int32_t a, int32_t b)
{
    int32_t r;
    if (__builtin_add_overflow(a, b, &r) || r == INT32_MIN) too_big();
    return r;
}

static int32_t gcd(int32_t a, int32_t b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        int32_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int32_t lcm(int32_t a, int32_t b)
{
    return ckmul(a / gcd(a, b), b);
}

/* fractions go by pointer: a 16-byte struct copied by value costs ~3x the code on the ez80.
   r may be the same as a or b */
static void qset(Q *r, int32_t n)
{
    r->n = n;
    r->d = 1;
}

static void qnorm(Q *r, int32_t n, int32_t d)
{
    int32_t g;
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
    int32_t g = gcd(a->d, b->d);
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
    int32_t g1 = gcd(a->n, b->d), g2 = gcd(b->n, a->d);
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
        say(MORE | OPEN, "/%l", a->d);
    }
}

/* n/d reduced */
static void wfrac(int32_t n, int32_t d)
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

/* ---------- os reals ---------- */

/* the os calls return a 9-byte struct that every call site would otherwise copy out */
static void xadd(R *r, const R *a, const R *b) { *r = os_RealAdd(a, b); }
static void xsub(R *r, const R *a, const R *b) { *r = os_RealSub(a, b); }
static void xmul(R *r, const R *a, const R *b) { *r = os_RealMul(a, b); }
static void xdiv(R *r, const R *a, const R *b) { *r = os_RealDiv(a, b); }
static void xsqrt(R *r, const R *a) { *r = os_RealSqrt(a); }

/* v as a real, exact: 10 digits fit the 14-digit mantissa */
static void rset(R *r, int32_t v)
{
    uint32_t u = v < 0 ? -(uint32_t)v : (uint32_t)v;
    uint8_t d[10];
    int n = 0, i;
    memset(r, 0, sizeof *r);
    r->exp = (int8_t)0x80;
    if (!u) return;
    do d[n++] = u % 10; while (u /= 10);
    for (i = 0; i < n; i++) r->mant[i / 2] |= d[n - 1 - i] << (i & 1 ? 0 : 4);
    r->exp = (int8_t)(0x80 + n - 1);
    if (v < 0) r->sign = (int8_t)0x80;
}

static void rfrac(R *r, int32_t n, int32_t d)
{
    R b;
    rset(r, n);
    rset(&b, d);
    xdiv(r, r, &b);
}

static void rten(R *r, int e)
{
    memset(r, 0, sizeof *r);
    r->exp = (int8_t)(0x80 + e);
    r->mant[0] = 0x10;
}

static int rzero(const R *a)
{
    return !a->mant[0];
}

static void rabs(R *a)
{
    a->sign &= 0x7f;
}

static int rlt(const R *a, const R *b)
{
    return os_RealCompare(a, b) < 0;
}

/* tol * (1 + |x|) */
static void rtol(R *r, const R *x, int e)
{
    R one, t = *x;
    rabs(&t);
    rset(&one, 1);
    xadd(&t, &t, &one);
    rten(&one, e);
    xmul(r, &t, &one);
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
            say(MORE | OPEN, "^%d", e[v]);
        }
    }
}

/* the sign and coefficient of a term; hv says a letter follows, so 1 is dropped and fractions get parentheses */
static void wcoef(const Q *c0, int first, int hv)
{
    Q c = *c0;
    if (c.n < 0) {
        wputc('-');
        c.n = -c.n;
    } else if (!first) {
        wputc('+');
    }
    if (c.d != 1 && hv) {
        say(MORE | OPEN, "(%q)", &c);
    } else if (!qone(&c) || !hv) {
        wq(&c);
    }
}

static void wmono(const Q *c, const uint8_t *e, int first)
{
    wcoef(c, first, hasvars(e));
    wvars(e);
}

/* m ch + b, for the inverse steps where y is not one of the input's letters; par wraps two terms in () */
static void wlin(const Q *m, int ch, const Q *b, int par)
{
    static const uint8_t none[NV];
    par = par && m->n && b->n;
    if (par) wputc('(');
    if (m->n) {
        wcoef(m, 1, 1);
        wputc(ch);
    }
    if (b->n || !m->n) wmono(b, none, !m->n);
    if (par) wputc(')');
}

/* a whole-number coefficient, for the many places that build terms from integers */
static void wmonoi(int32_t n, const uint8_t *e, int first)
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

static void addtermi(Poly *p, int32_t n, const uint8_t *e)
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

static Poly *pconsti(int32_t n)
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

static void reval(R *r, const Poly *p, int v, const R *x)
{
    R t;
    int i, k;
    rset(r, 0);
    for (i = 0; i < p->n; i++) {
        rfrac(&t, p->t[i].c.n, p->t[i].c.d);
        for (k = v < 0 ? 0 : p->t[i].e[v]; k > 0; k--) xmul(&t, &t, x);
        xadd(r, r, &t);
    }
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

/* scale c to integer coefficients with no common factor: remainders grow far slower than when made monic */
static void prim(Q *c, int deg)
{
    int32_t l = 1, g = 0;
    Q k;
    int i;
    for (i = 0; i <= deg; i++) l = lcm(l, c[i].d);
    for (i = 0; i <= deg; i++) g = gcd(g, ckmul(c[i].n, l / c[i].d));
    qnorm(&k, l, g);
    for (i = 0; i <= deg; i++) qmul(&c[i], &c[i], &k);
}

/* gcd of ga (degree na) and gb (degree nb) into ga, monic. returns its degree, or -1 if the numbers overflowed.
   integer pseudo-remainders with the common factor divided out each round: euclid over fractions blows
   past 64 bits on a degree-12 input */
static int dgcd(int na, int nb)
{
    static Q t[MAXD + 1];
    int i, outer = soft;
    if (!outer) {
        if (setjmp(soft_jmp)) {
            soft = 0;
            return -1;
        }
        soft = 1;
    }
    if (na >= 0) prim(ga, na);
    if (nb >= 0) prim(gb, nb);
    while (nb >= 0) {
        while (na >= nb) {
            int32_t lb = gb[nb].n, la = ga[na].n;
            int sh = na - nb;
            for (i = 0; i <= na; i++) ga[i].n = ckmul(ga[i].n, lb);
            for (i = 0; i <= nb; i++) ga[i + sh].n = ckadd(ga[i + sh].n, -ckmul(la, gb[i].n));
            for (na--; na >= 0 && !ga[na].n; na--);
        }
        if (na >= 0) prim(ga, na);
        memcpy(t, ga, sizeof t);
        memcpy(ga, gb, sizeof t);
        memcpy(gb, t, sizeof t);
        i = na;
        na = nb;
        nb = i;
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
        say(MORE, "%s%p), left %p", G_DOT "(", prod, left);
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
    int32_t l = 1, g = 0;
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
    Poly *t, *cut = 0;
    if (!r->d) return;
    if (r->n->n && hasi(r->d)) {
        Poly *cj = conj(r->d);
        Poly *n = pmul(r->n, cj), *d = pmul(r->d, cj);
        say(L_STEP, "multiply top and bottom by the conjugate %p", cj);
        say(L_STEP, "top: (%p)(%p) = %p", r->n, cj, n);
        say(L_STEP, "bottom: (%p)(%p) = %p", r->d, cj, d);
        replace(&r->n, n);
        replace(&r->d, d);
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
            cut = t;
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
        say(MORE, " divides evenly: %p", t);
        replace(&r->n, t);
        replace(&r->d, 0);
        return;
    }
    if (!fold(r)) normalize(r);
    if (cut) {
        say(L_STEP | OPEN, "cancel the common factor ");
        wpar(cut);
        say(MORE, ": %r", *r);
        pfree(cut);
    }
}

static void wcross(const Poly *n, const Poly *d)
{
    say(MORE | OPEN, "(%p)", n);
    if (d) {
        say(MORE | OPEN, "(%p)", d);
    }
}

/* shown is for sums the user typed; the ones taproot makes itself show their result in their own step */
static Rat radd(Rat a, Rat b, int neg, int shown)
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
        if (shown) {
            say(L_STEP | OPEN, "common denominator %p, top ", r.d);
            wcross(a.n, b.d);
            wputc(neg ? '-' : '+');
            wcross(b.n, a.d);
            say(MORE, " = %p", r.n);
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
        say(MORE | OPEN, "^%d", k);
    }
}

static Poly *binom(const Poly *a, int n)
{
    const Term *A = &a->t[0], *B = &a->t[1];
    Poly *r = pnew(), *term;
    int32_t c = 1;
    uint8_t e[NV];
    int k, v;
    say(L_STEP, "binomial theorem: (%p)^%d", a, n);
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
        say(L_STEP | OPEN, "T%d C(%d,%d)", k + 1, n, k);
        binom_part(A, n - k);
        binom_part(B, k);
        say(MORE, " = %p", term);
        pfree(term);
        c = ckmul(c, n - k) / (k + 1);
    }
    return r;
}

static Poly *ppow(const Poly *a, int n)
{
    Poly *r, *t;
    int k;
    if (a->n == 2 && n >= 2) return binom(a, n);
    r = pconsti(1);
    for (k = 1; k <= n; k++) {
        t = pmul(r, a);
        if (a->n > 2 && k > 1) say(L_STEP, "(%p)^%d = %p", a, k, t);
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
    say(L_ERROR | OPEN, "unexpected %c", ch);
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
static int ratvar(Rat r);
static Rat punary(void);

/* each ( or leading sign recurses ~5 frames; the calc stack is small */
static void deeper(void)
{
    if (++nest > 24) fail("too many nested ( or signs");
}

/* *a = *r, freeing the old *a and *b */
static void rnext(Rat *a, Rat *b, const Rat *r)
{
    rfree(*a);
    rfree(*b);
    *a = *r;
}

static Rat patom(void)
{
    int ch = peek();
    Rat r;
    if (isdigit(ch) || ch == '.') {
        int32_t n = 0, d = 1;
        int digits = 0, dot = 0;
        for (; s < send; s++) {
            if (isdigit((unsigned char)*s)) {
                n = ckadd(ckmul(n, 10), *s - '0');
                if (dot) d = ckmul(d, 10);
                digits++;
            } else if (*s == '.' && !dot) {
                dot = 1;
            } else {
                break;
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
    if (ex.d || !isconst(ex.n, &q) || q.d != 1) {
        say(L_ERROR | OPEN, "exponent must be a whole number (got %r)", ex);
        die();
    }
    if ((q.n > MAXPOW || q.n < -MAXPOW) && (b.d || b.n->n > 1 || q.n > MAXE || q.n < -MAXE)) fail("exponent too big (max 60)");
    r = rpow(b, (int)q.n);
    rnext(&b, &ex, &r);
    return b;
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

/* a product of two polynomials, one with several terms, gets its own step */
static Rat rmul_shown(const Rat *a, const Rat *b)
{
    Rat r = rmul(*a, *b);
    Q c;
    if (!a->d && !b->d && !isconst(a->n, &c) && !isconst(b->n, &c) && (a->n->n > 1 || b->n->n > 1)) {
        say(L_STEP, a->n->n > 1 ? "(%p)(%p) = %p" : "%p(%p) = %p", a->n, b->n, r.n);
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
        } else if (isalnum(ch) || ch == '(' || ch == '.') {
            b = ppower();
        } else {
            return a;
        }
        r = ch == '/' ? rdiv(a, b) : rmul_shown(&a, &b);
        rnext(&a, &b, &r);
    }
}

static int proper(const Rat *t)
{
    int v = ratvar(*t);
    return !t->d || (v >= 0 && pdeg(t->n, v) < pdeg(t->d, v));
}

static Rat pexpr(void)
{
    Rat a = pterm(), b, r;
    int top = !nest, terms = 1, fracs = !!a.d, mixed_ok = proper(&a);
    for (;;) {
        int ch = peek();
        if (ch != '+' && ch != '-') break;
        s++;
        b = pterm();
        terms++;
        fracs += !!b.d;
        mixed_ok &= proper(&b);
        r = radd(a, b, ch == '-', 1);
        rnext(&a, &b, &r);
    }
    /* x+1/x is already quotient plus remainder; dividing it back out would just repeat it */
    if (top) typed_mixed = terms > 1 && fracs == 1 && mixed_ok;
    return a;
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
        say(L_ERROR | OPEN, "%c is given twice", vars[v]);
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
        if (assigned[v] && (val[v].d || !isconst(val[v].n, &q))) return 1;
    return 0;
}

static void wvalues(void)
{
    int v, first = 1;
    for (v = 0; v < nv; v++) {
        if (!assigned[v]) continue;
        if (!first) wputs(", ");
        first = 0;
        say(MORE | OPEN, "%c=%r", vars[v], val[v]);
    }
}

static Rat psubst(const Poly *p)
{
    Rat acc = rpoly(pnew()), t, u, pw;
    int i, v;
    for (i = 0; i < p->n; i++) {
        const Term *pt = &p->t[i];
        Term tm = *pt;
        Q zq;
        for (v = 0; v < NV; v++) {
            if (!assigned[v]) continue;
            if (tm.e[v] && !val[v].d && isconst(val[v].n, &zq) && !zq.n) break;
            tm.e[v] = 0;
        }
        if (v < NV) continue;
        t = rpoly(pnew());
        addterm(t.n, &tm.c, tm.e);
        for (v = 0; v < NV; v++) {
            if (!assigned[v] || !pt->e[v]) continue;
            pw = rpow(val[v], pt->e[v]);
            u = rmul(t, pw);
            rnext(&t, &pw, &u);
        }
        u = radd(acc, t, 0, 0);
        rnext(&acc, &t, &u);
    }
    return acc;
}

static Rat rsubst(Rat r)
{
    Rat n = psubst(r.n), d, q;
    if (!r.d) return n;
    d = psubst(r.d);
    q = rdiv(n, d);
    rnext(&n, &d, &q);
    return n;
}

/* ---------- roots of one-variable polynomials ---------- */

static Root roots[MAXD + 1];
static int nroots;
static int32_t ip[MAXD + 1];
static int ideg;
static int32_t dv0[256], dvn[256];
static int32_t bqa[2], bqb[2];
static int nbq, bqmult, nquads;
/* num, k, r, den, mult of x^2 = (num+-k sqrt r)/den when the x^2-quadratic has no rational roots (mult 0 is none),
   then whether the + and the - one are positive */
static int32_t nest4[7];
static struct { int32_t a, b, c; int mult; } quads[MAXD / 2 + 1];
static Cx z[MAXD];
static int zm[MAXD], nz;
static R dkerr;
static Pt pts[MAXPTS];
static int npts, pstrlen;
static char pstr[1024];

static Poly *gcf(const Poly *p, Q *k, uint8_t *m)
{
    Poly *r;
    int32_t g = 0, l = 1;
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
        say(L_STEP | OPEN, "GCF ");
        wmono(k, m, 1);
        say(MORE, ": %p", r);
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

static void wlinfactor(int32_t p, int32_t q, int v)
{
    uint8_t e[NV] = { 0 };
    e[v] = 1;
    wmonoi(q, e, 1);
    e[v] = 0;
    if (p) wmonoi(-p, e, 0);
}

static void sortll(int32_t *a, int n)
{
    int i, j;
    for (i = 1; i < n; i++) {
        int32_t t = a[i];
        for (j = i; j > 0 && a[j - 1] > t; j--) a[j] = a[j - 1];
        a[j] = t;
    }
}

/* builds divisors from the prime factorization, -1 if there are more than 256.
   ponytail: trial division, so a prime factor past ~10^10 still takes minutes on the calc (clear stops it) */
static int divisors(int32_t n, int32_t *out)
{
    int32_t p, m;
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

static void add_root(int32_t p, int32_t q, int mult)
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

/* P(1) or P(-1), or 0 when it doesn't fit, which filters nothing */
static int32_t psum(int sgn)
{
    int32_t t = 0;
    int k;
    for (k = 0; k <= ideg; k++)
        if (__builtin_add_overflow(t, sgn < 0 && (k & 1) ? -ip[k] : ip[k], &t)) return 0;
    return t;
}

/* divides ip by (qx - p) when p/q is a root */
static int try_root(int32_t p, int32_t q)
{
    static int32_t b[MAXD + 1];
    int k;
    if (setjmp(soft_jmp)) {
        soft = 0;
        return 0;
    }
    soft = 1;
    b[ideg] = 0;
    for (k = ideg; k >= 1; k--) {
        int32_t t = ckadd(ip[k], ckmul(p, b[k]));
        if (t % q) break;
        b[k - 1] = t / q;
    }
    if (k || ckadd(ip[0], ckmul(p, b[0]))) {
        soft = 0;
        return 0;
    }
    soft = 0;
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
    for (i = 0; i < nn; i++)
        for (j = 0; j < n0; j++)
            if (gcd(dv0[j], dvn[i]) == 1) {
                Q c = { dv0[j], dvn[i] };
                say(MORE | OPEN, --count ? G_PM "%q, " : G_PM "%q", &c);
            }
    wputs(" work");
}

static void find_roots(int v)
{
    int i, j, sgn, n0 = 0, nn = 0, any = 0, ch = vars[v];
    int32_t p1, pm1, bound;
    if (ideg < 2) return;
    say(L_STEP, "rational roots " G_PM "p/q: p|%l, q|%l", ip[0] < 0 ? -ip[0] : ip[0], ip[ideg]);
    while (ideg >= 2) {
        n0 = divisors(ip[0], dv0);
        nn = divisors(ip[ideg], dvn);
        if (n0 < 0 || nn < 0) {
            step("too many candidates, skipping the rest");
            return;
        }
        /* cheap filters: every root is within the cauchy bound, and p/q a root means (q-p) | P(1), (q+p) | P(-1) */
        for (bound = 1, i = 0; i < ideg; i++) {
            int32_t a = ip[i] < 0 ? -ip[i] : ip[i], c = (a + ip[ideg] - 1) / ip[ideg] + 1;
            if (c > bound) bound = c;
        }
        p1 = psum(1);
        pm1 = psum(-1);
        for (i = 0; i < nn; i++) {
            for (j = 0; j < n0; j++) {
                if (dv0[j] / dvn[i] > bound || gcd(dv0[j], dvn[i]) != 1) continue;
                for (sgn = 0; sgn < 2; sgn++) {
                    int32_t p = sgn ? -dv0[j] : dv0[j], q = dvn[i];
                    Q r = { p, q }, m = { q, 1 }, b = { -p, 1 };
                    if ((q == p ? p1 : p1 % (q - p)) || (q == -p ? pm1 : pm1 % (q + p))) continue;
                    poll();
                    if (!try_root(p, q)) continue;
                    any = 1;
                    add_root(p, q, 1);
                    say(L_STEP, "%c=%q: P(%q)=0, so (%L) is a factor", ch, &r, &r, &m, ch, &b);
                    say(L_STEP | OPEN, "divide by (%L): ", &m, ch, &b);
                    wip(v);
                    end();
                    goto next;
                }
            }
        }
        break;
    next:;
    }
    if (ideg == 1) {
        Q m = { ip[1], 1 }, b = { ip[0], 1 };
        add_root(-ip[0], ip[1], 1);
        say(L_STEP, "last factor: %L", &m, ch, &b);
        ideg = 0;
        ip[0] = 1;
    } else if (!any) {
        begin(L_STEP);
        wcandidates(n0, nn);
        end();
    } else {
        say(L_STEP | OPEN, "no more rational roots in ");
        wip(v);
        end();
    }
}

static int32_t isqrt(int32_t n)
{
    int32_t x = n, y = n / 2 + 1;
    if (n < 2) return n;
    while (y < x) {
        x = y;
        y = (x + n / x) / 2;
    }
    return x;
}

static int32_t sqpart(int32_t n, int32_t *rest)
{
    static int32_t last_n = -1, last_s, last_r;
    int32_t s_ = 1, j, n0 = n;
    if (n == last_n) {
        *rest = last_r;
        return last_s;
    }
    for (j = 2; j <= n / j; j++) {
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

static void swap2(int32_t *a)
{
    int32_t t = a[0];
    a[0] = a[1];
    a[1] = t;
}

/* x^4 + ... with only even powers whose x^2-quadratic has rational roots */
static int biquad(int v)
{
    int32_t a = ip[4], b = ip[2], c = ip[0], d, sq;
    int i;
    Q u;
    if (ideg != 4 || ip[1] || ip[3]) return 0;
    d = ckadd(ckmul(b, b), -ckmul(4, ckmul(a, c)));
    if (d < 0) return 0;
    sq = isqrt(d);
    if (sq * sq != d) return 0;
    say(L_STEP, "only even powers, so treat it as a quadratic in %c^2", vars[v]);
    for (i = 0; i < 2; i++) {
        qnorm(&u, ckadd(-b, i ? -sq : sq), ckmul(2, a));
        bqa[i] = u.n;
        bqb[i] = u.d;
    }
    if (ckmul(bqa[0] < 0 ? -bqa[0] : bqa[0], bqb[1]) > ckmul(bqa[1] < 0 ? -bqa[1] : bqa[1], bqb[0])) {
        swap2(bqa);
        swap2(bqb);
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
    say(MORE | OPEN, " (multiplicity %d)", mult);
}

/* x rounded to 6 decimals, trailing zeros dropped */
static void wreal(const R *x)
{
    R t = os_RealRound(x, 6);
    int e = (uint8_t)t.exp - 0x80, p, last = 0, k;
    uint8_t dig[16];
    for (k = 0; k < 14; k++) dig[k] = (t.mant[k / 2] >> (k & 1 ? 0 : 4)) & 15;
    if (rzero(&t)) {
        wputc('0');
        return;
    }
    if (e > 12) fail("root too big to print");
    if (t.sign & 0x80) wputc('-');
    for (p = e < 0 ? 0 : e; p >= 0; p--) wputc('0' + (e - p >= 0 && e - p < 14 ? dig[e - p] : 0));
    for (p = -1; p >= -6; p--)
        if (e - p >= 0 && e - p < 14 && dig[e - p]) last = p;
    if (!last) return;
    wputc('.');
    for (p = -1; p >= last; p--) wputc('0' + (e - p >= 0 && e - p < 14 ? dig[e - p] : 0));
}

/* (num ± k·√r·i^neg)/den, or with sgn != 0 just the + or - root */
static void wradical(int32_t num, int32_t k, int32_t r, int neg, int32_t den, int sgn)
{
    int paren = den != 1 && num;
    if (paren) wputc('(');
    if (num) wll(num);
    wputs(sgn > 0 ? (num ? "+" : "") : sgn < 0 ? "-" : G_PM);
    if (k != 1 || (!neg && r == 1)) wll(k);
    if (neg) wputc('i');
    if (r != 1) {
        say(MORE | OPEN, G_SQRT "%l", r);
    }
    if (paren) wputc(')');
    if (den != 1) {
        say(MORE | OPEN, "/%l", den);
    }
}

static void wparen(int32_t n)
{
    if (n < 0) wputc('(');
    wll(n);
    if (n < 0) wputc(')');
}

static int32_t disc(int32_t a, int32_t b, int32_t c)
{
    return ckadd(ckmul(b, b), -ckmul(4, ckmul(a, c)));
}

/* pw 2 solves for v^2 */
static void quad_steps(int32_t a, int32_t b, int32_t c, int v, int pw)
{
    int32_t d = disc(a, b, c), r, sq;
    int neg = d < 0;
    sq = sqpart(neg ? -d : d, &r);
    say(L_STEP, "quadratic formula: a=%l, b=%l, c=%l", a, b, c);
    say(L_STEP | OPEN, "disc = ");
    wparen(b);
    say(MORE, "^2-4(%l)(%l) = %l", a, c, d);
    if (sq != 1 || neg) {
        say(L_STEP | OPEN, G_SQRT "%l = ", d);
        if (sq != 1 || r == 1) wll(sq);
        if (neg) wputc('i');
        if (r != 1) {
            say(MORE | OPEN, G_SQRT "%l", r);
        }
        end();
    }
    if (gcd(gcd(b, sq), 2 * a) != 1) {
        say(L_STEP | OPEN, pw > 1 ? "%c^2 = " : "%c = ", vars[v]);
        wradical(-b, sq, r, neg, ckmul(2, a), 0);
        end();
    }
}

/* the simplified pieces of (-b ± √disc)/(2a) */
static int quad_parts(int32_t a, int32_t b, int32_t c, int32_t *num, int32_t *k, int32_t *r, int32_t *den)
{
    int32_t d = disc(a, b, c), sq, g;
    int neg = d < 0;
    sq = sqpart(neg ? -d : d, r);
    g = gcd(gcd(b, sq), ckmul(2, a));
    *num = -b / g;
    *k = sq / g;
    *den = 2 * a / g;
    return neg;
}

static void quad_result(int32_t a, int32_t b, int32_t c, int v, int mult)
{
    int32_t num, k, r, den, d = disc(a, b, c);
    R re, im, t;
    int neg = quad_parts(a, b, c, &num, &k, &r, &den);
    say(L_RESULT | OPEN, "%c = ", vars[v]);
    wradical(num, k, r, neg, den, 0);
    wmult(mult);
    end();
    if (r == 1) return;
    rfrac(&re, -b, 2 * a);
    rset(&im, neg ? -d : d);
    xsqrt(&im, &im);
    rset(&t, 2 * a);
    xdiv(&im, &im, &t);
    say(L_APPROX | OPEN, "%c", vars[v]);
    wputs(" " G_APPROX " ");
    if (neg) {
        if (b) wreal(&re);
        say(MORE | OPEN, G_PM "%Ri", &im);
    } else if (!b) {
        say(MORE | OPEN, G_PM "%R", &im);
    } else {
        xadd(&t, &re, &im);
        say(MORE | OPEN, "%R, ", &t);
        xsub(&t, &re, &im);
        wreal(&t);
    }
    wmult(mult);
    end();
}

__attribute__((noinline)) static void cmul(Cx *a, const Cx *b)
{
    R t1, t2, t3, t4;
    xmul(&t1, &a->r, &b->r);
    xmul(&t2, &a->i, &b->i);
    xmul(&t3, &a->r, &b->i);
    xmul(&t4, &a->i, &b->r);
    xsub(&a->r, &t1, &t2);
    xadd(&a->i, &t3, &t4);
}

__attribute__((noinline)) static void cdiv(Cx *a, const Cx *b)
{
    R m, t1, t2;
    xmul(&m, &b->r, &b->r);
    xmul(&t1, &b->i, &b->i);
    xadd(&m, &m, &t1);
    if (rzero(&m)) rten(&m, -30);
    xmul(&t1, &a->r, &b->r);
    xmul(&t2, &a->i, &b->i);
    xadd(&t1, &t1, &t2);
    xmul(&t2, &a->i, &b->r);
    xmul(&a->i, &a->r, &b->i);
    xsub(&a->i, &t2, &a->i);
    xdiv(&a->i, &a->i, &m);
    xdiv(&a->r, &t1, &m);
}

__attribute__((noinline)) static void cnorm(R *r, const Cx *a)
{
    R t = a->i;
    *r = a->r;
    rabs(r);
    rabs(&t);
    xadd(r, r, &t);
}

/* a -= b, r = |b| relative to the new a */
__attribute__((noinline)) static void csubrel(R *r, Cx *a, const Cx *b)
{
    R t, one;
    xsub(&a->r, &a->r, &b->r);
    xsub(&a->i, &a->i, &b->i);
    cnorm(&t, a);
    rset(&one, 1);
    xadd(&t, &t, &one);
    cnorm(r, b);
    xdiv(r, r, &t);
}

/* value of the d-th derivative of monic c (degree n) at z */
__attribute__((noinline)) static void horner(const R *c, int n, int d, const Cx *zz, Cx *v)
{
    R f;
    int32_t k;
    int j, t;
    rset(&v->r, 0);
    rset(&v->i, 0);
    for (j = n; j >= d; j--) {
        for (k = 1, t = 0; t < d; t++) k *= j - t;
        rset(&f, k);
        xmul(&f, &f, &c[j]);
        cmul(v, zz);
        xadd(&v->r, &v->r, &f);
    }
}

/* sum of |d-th derivative coefficient| |x|^k: the scale rounding errors in the d-th derivative work against */
__attribute__((noinline)) static void hornabs(const R *c, int n, int d, const R *x, R *v)
{
    R f;
    int32_t k;
    int j, t;
    rset(v, 0);
    for (j = n; j >= d; j--) {
        for (k = 1, t = 0; t < d; t++) k *= j - t;
        rset(&f, k);
        xmul(&f, &f, &c[j]);
        rabs(&f);
        xmul(v, v, x);
        xadd(v, v, &f);
    }
}

static void numeric(int fmult)
{
    static R c[MAXD + 1];
    static Cx w2, u, p, d, t, sum;
    static R m, maxd, rad, r, tk, stp, two, eps, tol;
    int k, j, it, mult, n = ideg, base = nz;
    for (k = 0; k <= n; k++) rfrac(&c[k], ip[k], ip[n]);
    /* fujiwara bound, 2 max |c[n-k]|^(1/k), rounded up to a power of 2 */
    rset(&rad, 1);
    rset(&two, 2);
    for (k = 1; k <= n; k++) {
        R a = c[n - k];
        rabs(&a);
        for (rset(&r, 1), rset(&tk, 1), rset(&stp, 1), j = 0; j < k; j++) xmul(&stp, &stp, &two);
        for (; rlt(&tk, &a); xmul(&tk, &tk, &stp)) xmul(&r, &r, &two);
        if (rlt(&rad, &r)) rad = r;
    }
    /* work in y = x/rad so every root sits near the unit circle and nothing overflows the os reals */
    for (rset(&r, 1), k = n - 1; k >= 0; k--) {
        xmul(&r, &r, &rad);
        xdiv(&c[k], &c[k], &r);
    }
    rset(&w2.r, 2);
    rset(&w2.i, 0);
    rset(&u.r, 97);
    xsqrt(&u.r, &u.r);
    rset(&u.i, 9);
    xdiv(&u.i, &u.i, &u.r);
    rset(&m, 4);
    xdiv(&u.r, &m, &u.r);
    rset(&m, n);
    xdiv(&m, &c[n - 1], &m);
    for (k = base; k < base + n; k++) {
        z[k] = w2;
        xsub(&z[k].r, &z[k].r, &m);
        zm[k] = 1;
        cmul(&w2, &u);
    }
    rten(&eps, -12);
    for (it = 0; it < 1000; it++) {
        poll();
        rset(&maxd, 0);
        for (k = base; k < base + n; k++) {
            horner(c, n, 0, &z[k], &p);
            rset(&d.r, 1);
            rset(&d.i, 0);
            for (j = base; j < base + n; j++) {
                if (j == k) continue;
                t = z[k];
                csubrel(&m, &t, &z[j]);
                cmul(&d, &t);
            }
            cdiv(&p, &d);
            csubrel(&m, &z[k], &p);
            if (rlt(&maxd, &m)) maxd = m;
        }
        if (rlt(&maxd, &eps)) break;
    }

    /* repeated roots come back as a tight cluster: merge it, then polish on the derivative where it's a simple root.
       the last newton step estimates the error */
    nz = base;
    for (k = base; k < base + n; k++) {
        if (!zm[k]) continue;
        sum = z[k];
        mult = 1;
        for (j = k + 1; j < base + n; j++) {
            /* compared in x units, not the scaled y ones */
            t = z[j];
            csubrel(&m, &t, &z[k]);
            cnorm(&m, &t);
            xmul(&m, &m, &rad);
            cnorm(&tol, &z[k]);
            xmul(&tol, &tol, &rad);
            rtol(&tol, &tol, -3);
            /* ponytail: 1e-3 catches triple roots in noisy high degrees, but merges distinct irrational roots closer than that */
            if (!zm[j] || rlt(&tol, &m)) continue;
            xadd(&sum.r, &sum.r, &z[j].r);
            xadd(&sum.i, &sum.i, &z[j].i);
            mult++;
            zm[j] = 0;
        }
        rset(&m, mult);
        xdiv(&sum.r, &sum.r, &m);
        xdiv(&sum.i, &sum.i, &m);
        for (rset(&m, 0), it = 0; it < 8; it++) {
            horner(c, n, mult - 1, &sum, &p);
            horner(c, n, mult, &sum, &d);
            if (rzero(&d.r) && rzero(&d.i)) break;
            cdiv(&p, &d);
            csubrel(&m, &sum, &p);
        }
        /* forward error ~ the last newton step plus the condition number times the reals' 1e-14 rounding:
           an ill-conditioned expansion like (x+2)^40-1 converges nicely to roots of the rounded polynomial */
        {
            R ay, num;
            cnorm(&ay, &sum);
            hornabs(c, n, mult - 1, &ay, &num);
            horner(c, n, mult, &sum, &d);
            cnorm(&tol, &d);
            rset(&eps, 1);
            xadd(&ay, &ay, &eps);
            xmul(&tol, &tol, &ay);
            rten(&eps, -14);
            xmul(&num, &num, &eps);
            if (rzero(&tol)) rten(&tol, -99);
            xdiv(&num, &num, &tol);
            xadd(&m, &m, &num);
        }
        if (rlt(&dkerr, &m)) dkerr = m;
        xmul(&sum.r, &sum.r, &rad);
        xmul(&sum.i, &sum.i, &rad);
        /* a merged cluster only knows its root to about eps^(1/mult), so it gets a looser real-or-not test */
        rtol(&tol, &sum.r, mult > 1 ? -4 : -7);
        t.r = sum.i;
        rabs(&t.r);
        if (rlt(&t.r, &tol)) rset(&sum.i, 0);
        z[nz] = sum;
        zm[nz++] = mult * fmult;
    }
    /* complex roots of a real polynomial come in conjugate pairs, so a loner is a real root whose cluster
       spread too wide for 14 digits: make it real and fold it into the nearest real cluster */
    for (k = base; k < nz; k++) {
        if (rzero(&z[k].i)) continue;
        for (j = base; j < nz; j++) {
            if (j == k || zm[j] != zm[k]) continue;
            t = z[j];
            xadd(&t.i, &t.i, &z[k].i);
            xsub(&t.r, &t.r, &z[k].r);
            cnorm(&m, &t);
            rtol(&tol, &z[k].r, -3);
            if (rlt(&m, &tol)) break;
        }
        if (j == nz) {
            rset(&z[k].i, 0);
            zm[k] = -zm[k]; /* marks a loner for the next pass */
        }
    }
    for (k = base; k < nz; k++) {
        if (zm[k] >= 0) continue;
        zm[k] = -zm[k];
        for (j = base; j < nz; j++) {
            if (j == k || !rzero(&z[j].i) || zm[j] < 2) continue;
            xsub(&m, &z[j].r, &z[k].r);
            rabs(&m);
            rtol(&tol, &z[k].r, -2);
            if (rlt(&tol, &m)) continue;
            /* the cluster's polished value is the better one; it just gains the loner's multiplicity */
            zm[j] += zm[k];
            z[k] = z[--nz];
            zm[k--] = zm[nz];
            break;
        }
    }
    for (k = 1; k < nz; k++) {
        t = z[k];
        mult = zm[k];
        for (j = k; j > 0 && (!rzero(&z[j - 1].i) > !rzero(&t.i) || (!rzero(&z[j - 1].i) == !rzero(&t.i) && rlt(&t.r, &z[j - 1].r))); j--) {
            z[j] = z[j - 1];
            zm[j] = zm[j - 1];
        }
        z[j] = t;
        zm[j] = mult;
    }
    rten(&m, -3);
    if (!rlt(&dkerr, &m)) fail("too sensitive to solve numerically");
}

static void numeric_result(int v)
{
    R lim;
    int k;
    for (k = 0; k < nz; k++) {
        if (z[k].i.sign & 0x80) continue;
        say(L_APPROX | OPEN, "%c", vars[v]);
        wputs(" " G_APPROX " ");
        wreal(&z[k].r);
        if (!rzero(&z[k].i)) {
            say(MORE | OPEN, G_PM "%Ri", &z[k].i);
        }
        wmult(zm[k]);
        end();
    }
    rten(&lim, -7);
    if (nz && rlt(&lim, &dkerr)) {
        say(L_APPROX, "these are sensitive, last digits may be off");
    }
}

static void addquad(int32_t a, int32_t b, int32_t c, int mult)
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

static void wquad(int32_t a, int32_t b, int32_t c, int v)
{
    uint8_t e[NV] = { 0 };
    wputc('(');
    e[v] = 2;
    wmonoi(a, e, 1);
    e[v] = 1;
    if (b) wmonoi(b, e, 0);
    e[v] = 0;
    if (c) wmonoi(c, e, 0);
    wputc(')');
}

/* an integer quartic ip with no rational roots as (p1x^2+q1x+r1)(p2x^2+q2x+r2), if it splits over the integers */
static int quartic_split(int v)
{
    int32_t a4 = ip[4], a3 = ip[3], a2 = ip[2], a1 = ip[1], a0 = ip[0];
    int i, j, sg, n4, n0;
    if (ideg != 4) return 0;
    n4 = divisors(a4, dv0);
    n0 = divisors(a0, dvn);
    if (n4 < 0 || n0 < 0) return 0;
    for (i = 0; i < n4; i++)
        for (j = 0; j < n0; j++)
            for (sg = 1; sg >= -1; sg -= 2) {
                int32_t p1 = dv0[i], p2 = a4 / p1, r1 = sg * dvn[j], r2 = a0 / r1, det, q1, q2;
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
                    int32_t k2 = ckadd(a2, -ckadd(ckmul(p1, r2), ckmul(r1, p2))), dd2 = ckadd(ckmul(a3, a3), -ckmul(4, ckmul(p1, ckmul(p2, k2)))), sq2;
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
                wputs(" = ");
                wquad(p1, q1, r1, v);
                wquad(p2, q2, r2, v);
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
    int32_t l = 1, g = 0;
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

/* ax^4+bx^2+c whose x^2-quadratic has irrational roots: x^2 = (num +- k sqrt r)/den, and x is +-sqrt of each */
static int nested(int v, int mult)
{
    int32_t d, sq;
    if (ideg != 4 || ip[1] || ip[3] || (d = disc(ip[4], ip[2], ip[0])) <= 0) return 0;
    sq = isqrt(d);
    if (sq * sq == d) return 0;
    say(L_STEP, "only even powers, so treat it as a quadratic in %c^2", vars[v]);
    quad_steps(ip[4], ip[2], ip[0], v, 2);
    quad_parts(ip[4], ip[2], ip[0], &nest4[0], &nest4[1], &nest4[2], &nest4[3]);
    nest4[4] = mult;
    /* the two x^2 multiply to c/a and add to -b/a, and a > 0 */
    nest4[5] = ip[0] < 0 || ip[2] < 0;
    nest4[6] = ip[0] > 0 && ip[2] < 0;
    say(L_STEP | OPEN, "%c^2 = ", vars[v]);
    wradical(nest4[0], nest4[1], nest4[2], 0, nest4[3], 0);
    end();
    return 1;
}

static void exact_or_numeric(int v, int mult)
{
    if (ideg == 1) {
        add_root(-ip[0], ip[1], mult);
    } else if (ideg == 2) {
        addquad(ip[2], ip[1], ip[0], mult);
        quad_steps(ip[2], ip[1], ip[0], v, 1);
    } else if (ideg == 4 && quartic_split(v)) {
        int i;
        for (i = nquads - 2; i < nquads; i++) {
            quads[i].mult = mult;
            quad_steps(quads[i].a, quads[i].b, quads[i].c, v, 1);
        }
    } else if (ideg >= 1 && !nested(v, mult)) {
        int n = ideg;
        numeric(mult);
        say(L_STEP, "no exact formula used for degree %d, solving numerically", n);
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
    int32_t d, sq;
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
        say(L_STEP | OPEN, "(");
        wip(v);
        say(MORE, ")^%d", fmul[i]);
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
    nest4[4] = 0;
    rset(&dkerr, 0);
    r = gcf(p, &k, m);
    if (m[v]) {
        add_root(0, 1, m[v]);
        say(L_STEP | OPEN, "%c", vars[v]);
        if (m[v] > 1) {
            say(MORE | OPEN, "^%d", m[v]);
        }
        say(MORE, " factor gives %c=0", vars[v]);
    }
    ideg = intdense(r, v);
    pfree(r);
    if (ideg == 1) {
        add_root(-ip[0], ip[1], 1);
        begin(L_STEP);
        wip(v);
        say(MORE | OPEN, "=0 gives %c=", vars[v]);
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

static void addpt(const R *x, int32_t p, int32_t q, int mult, char tag, const char *str)
{
    R d, tol;
    int i;
    if (tag == 'h') mult = 0;
    rtol(&tol, x, -9);
    for (i = 0; i < npts; i++) {
        xsub(&d, &pts[i].v, x);
        rabs(&d);
        if (rlt(&tol, &d)) continue;
        pts[i].mult += mult;
        if (ptpri(tag) > ptpri(pts[i].tag)) pts[i].tag = tag;
        return;
    }
    if (npts == MAXPTS) return;
    pts[npts].v = *x;
    pts[npts].p = p;
    pts[npts].q = q;
    pts[npts].mult = mult;
    pts[npts].tag = tag;
    pts[npts].s = str;
    npts++;
}

/* sqrt of |num + sg k sqrt r|/den */
static void nest_val(int sg, R *x)
{
    R t;
    rset(x, nest4[2]);
    xsqrt(x, x);
    rset(&t, nest4[1] * sg);
    xmul(x, x, &t);
    rset(&t, nest4[0]);
    xadd(x, x, &t);
    rset(&t, nest4[3]);
    xdiv(x, x, &t);
    rabs(x);
    xsqrt(x, x);
}

/* sqrt((num + sg k sqrt r)/den), or i sqrt of minus it, after pre; the root goes first, so sqrt2-1 */
static void wnest(int sg, const char *pre)
{
    int32_t num = nest4[0], den = nest4[3];
    int pos = nest4[sg > 0 ? 5 : 6];
    if (!pos) {
        num = -num;
        sg = -sg;
    }
    say(MORE | OPEN, pos ? "%s" G_SQRT "(" : "%si" G_SQRT "(", pre);
    if (den != 1) wputc('(');
    if (num < 0 && sg > 0) {
        wradical(0, nest4[1], nest4[2], 0, 1, 1);
        wll(num);
    } else {
        wradical(num, nest4[1], nest4[2], 0, 1, sg);
    }
    if (den != 1) {
        say(MORE | OPEN, ")/%l", den);
    }
    wputc(')');
}

static void quadpts(int32_t a, int32_t b, int32_t c, int mult, char tag)
{
    int32_t num, k, r, den;
    R sq, x, t;
    int sgn;
    if (quad_parts(a, b, c, &num, &k, &r, &den)) return;
    rset(&sq, disc(a, b, c));
    xsqrt(&sq, &sq);
    for (sgn = -1; sgn <= 1; sgn += 2) {
        rset(&x, -b);
        (sgn < 0 ? xsub : xadd)(&x, &x, &sq);
        rset(&t, 2 * a);
        xdiv(&x, &x, &t);
        pt_begin();
        wradical(num, k, r, 0, den, a > 0 ? sgn : -sgn);
        addpt(&x, 0, 0, mult, tag, pt_end());
    }
}

/* real roots from the last analyze() into pts; returns their total multiplicity */
static int collect(char tag)
{
    int i, total = 0;
    for (i = 0; i < nroots; i++) {
        Q x;
        R rx;
        qnorm(&x, roots[i].p, roots[i].q);
        rfrac(&rx, x.n, x.d);
        pt_begin();
        wq(&x);
        addpt(&rx, x.n, x.d, roots[i].mult, tag, pt_end());
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
    for (i = 0; i < 4 && nest4[4]; i++) {
        R x;
        if (!nest4[i < 2 ? 5 : 6]) continue;
        nest_val(i < 2 ? 1 : -1, &x);
        if (i & 1) x.sign ^= 0x80;
        pt_begin();
        wnest(i < 2 ? 1 : -1, i & 1 ? "-" : "");
        addpt(&x, 0, 0, nest4[4], tag, pt_end());
        total += nest4[4];
    }
    for (i = 0; i < nz; i++) {
        if (!rzero(&z[i].i)) continue;
        pt_begin();
        wreal(&z[i].r);
        addpt(&z[i].r, 0, 0, zm[i], tag, pt_end());
        total += zm[i];
    }
    return total;
}

static void sortpts(void)
{
    int i, j;
    for (i = 1; i < npts; i++) {
        Pt t = pts[i];
        for (j = i; j > 0 && rlt(&t.v, &pts[j - 1].v); j--) pts[j] = pts[j - 1];
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
    say(L_RESULT | OPEN, "%c", vars[domv]);
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
    say(L_RESULT, "%s%r", prefix, r);
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
        say(L_STEP | OPEN, "synthetic division by ");
        wlinear(v, &root);
        end();
        synthetic(&da[0], da, dn, &root, dq);
        rd = da[0].n ? 0 : -1;
    } else {
        say(L_STEP, "long division by %p", r.d);
        longdiv(da, dn, db, dd, v, dq);
        for (rd = dd - 1; rd >= 0 && !da[rd].n; rd--);
    }
    q = fromdense(dq, dn - dd, v);
    rem = fromdense(da, rd, v);
    say(L_RESULT | OPEN, "= %p", q);
    if (rem->n == 1 && rem->t[0].c.d == 1) {
        wmono(&rem->t[0].c, rem->t[0].e, 0);
    } else {
        say(MORE | OPEN, "+(%p)", rem);
    }
    wputs("/");
    wpar(r.d);
    end();
    say(L_RESULT, "quotient %p, remainder %p", q, rem);
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
    say(L_STEP | OPEN, "substitute ");
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
    say(L_ERROR | OPEN, "undefined: %c=%q makes a denominator 0", vars[domv], &x);
    die();
}

static void do_expand(Rat r)
{
    int v;
    r = compose(r);
    if (nassigned()) {
        check_domain();
        v = univar(r.n);
        say(L_STEP, "P = %r", r);
        if (!r.d && v >= 0 && v != iv && assigned[v] && nassigned() == 1 && pdeg(r.n, v) >= 1 && pdeg(r.n, v) <= MAXD) {
            int deg = todense(r.n, v, da);
            Q x;
            isnum(val[v], &x);
            say(L_STEP | OPEN, "remainder theorem: P(%q) is the remainder of P/(", &x);
            wlinear(v, &x);
            say(MORE, ")");
            synthetic(0, da, deg, &x, dq);
        } else {
            say(L_STEP | OPEN, "plug in ");
            wvalues();
            end();
        }
        wres("= ", rsubst(r));
        return;
    }
    wres("= ", r);
    v = ratvar(r);
    if (r.d && v >= 0 && v != iv && !typed_mixed) mixed(r, v);
    domain_line();
}

static int32_t lf[2 * MAXD + 2];
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
                        memcpy(lf + lfat(nlf), ip, (ideg + 1) * sizeof(int32_t));
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
        say(MORE | OPEN, "(%q)", &k);
    }
    for (i = 0; i < nroots; i++) {
        if (paren) wputc('(');
        wlinfactor(roots[i].p, roots[i].q, v);
        if (paren) wputc(')');
        if (roots[i].mult > 1) {
            say(MORE | OPEN, "^%d", roots[i].mult);
        }
    }
    for (i = 0; i < nbq; i++) wbq(i, v);
    for (i = 0; i < nquads; i++) {
        wquad(quads[i].a, quads[i].b, quads[i].c, v);
        if (quads[i].mult > 1) {
            say(MORE | OPEN, "^%d", quads[i].mult);
        }
    }
    for (i = 0; i < nlf; i++) {
        memcpy(ip, lf + lfat(i), (lfd[i] + 1) * sizeof(int32_t));
        ideg = lfd[i];
        wputc('(');
        wip(v);
        wputc(')');
        if (lfm[i] > 1) {
            say(MORE | OPEN, "^%d", lfm[i]);
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
    say(L_RESULT | OPEN, "= ");
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
        say(L_RESULT | OPEN, "at ");
        wvalues();
        say(MORE, ": %r", rsubst(r));
    }
    domain_line();
}

static int rootcmp(const Root *a, const Root *b)
{
    int32_t x = ckmul(a->p, b->q), y = ckmul(b->p, a->q);
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
        say(L_RESULT | OPEN, "%c = ", vars[v]);
        wfrac(roots[i].p, roots[i].q);
        wmult(roots[i].mult);
        end();
    }
    for (i = 0; i < nquads; i++) quad_result(quads[i].a, quads[i].b, quads[i].c, v, quads[i].mult);
    for (i = 0; i < nbq; i++) quad_result(bqb[i], 0, -bqa[i], v, bqmult);
    for (i = 1; nest4[4] && i >= -1; i -= 2) {
        R x;
        say(L_RESULT | OPEN, "%c = ", vars[v]);
        wnest(i, G_PM);
        wmult(nest4[4]);
        end();
        nest_val(i, &x);
        say(L_APPROX | OPEN, nest4[i > 0 ? 5 : 6] ? "%c " G_APPROX " " G_PM "%R" : "%c " G_APPROX " " G_PM "%Ri", vars[v], &x);
        wmult(nest4[4]);
        end();
    }
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
    say(L_STEP, "move everything to one side: %r%s0", r, relname(rel));
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
        say(L_STEP | OPEN, "critical points: ");
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
        say(L_STEP | OPEN, "(");
        wbound(i - 1);
        wputc(',');
        wbound(i);
        say(MORE, "): %c", sign[i] > 0 ? '+' : '-');
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
            say(MORE | OPEN, "{%s}", pts[a / 2].s);
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
                say(MORE | OPEN, "%c = %s", vars[v], pts[a / 2].s);
                continue;
            }
            if (hi) {
                say(MORE | OPEN, "%c%s%s", vars[v], a & 1 ? G_GE : ">", pts[(a - 1) / 2].s);
                continue;
            }
            if (!lo) {
                say(MORE | OPEN, "%s%s", pts[(a - 1) / 2].s, a & 1 ? G_LE : "<");
            }
            wputc(vars[v]);
            if (!hi) {
                say(MORE | OPEN, "%s%s", b & 1 ? G_LE : "<", pts[b / 2].s);
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
        say(L_STEP | OPEN, "multiply both sides by ");
        wpar(r.d);
        say(MORE, ": %p=0", n);
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
        say(L_APPROX, "%c = %s is extraneous: it makes a denominator 0", vars[v], pts[i].s);
    }
}

/* "= ..." for d/dx, "d/dy = ..." when the letter isn't x */
/* sq set prints top/(sq)^2 instead of q */
static void wderiv(int v, Rat q, const Poly *top, const Poly *sq)
{
    begin(L_RESULT);
    if (vars[v] != 'x') {
        say(MORE | OPEN, "d/d%c ", vars[v]);
    }
    if (sq) say(MORE, top->n > 1 ? "= (%p)/(%p)^2" : "= %p/(%p)^2", top, sq);
    else say(MORE, "= %r", q);
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
        Poly *top;
        int sq;
        dn = pderiv(r.n, v);
        dd = pderiv(r.d, v);
        begin(L_STEP);
        wputs("quotient rule: (top'" G_DOT "bottom-top" G_DOT "bottom')/bottom^2");
        end();
        say(L_STEP, "top' = %p, bottom' = %p", dn, dd);
        say(L_STEP, "= ((%p)(%p)-(%p)(%p))/(%p)^2", dn, r.d, r.n, dd, r.d);
        {
            Poly *a = pmul(dn, r.d), *b = pmul(r.n, dd);
            top = padd(a, b, 1);
            q.n = pcopy(top);
            q.d = pmul(r.d, r.d);
            pfree(a);
            pfree(b);
        }
        rsimp(&q);
        /* nothing cancelled keeps the bottom squared the way it's written by hand */
        sq = r.d->n > 1 && q.d && pdeg(q.d, v) == 2 * pdeg(r.d, v);
        if (!sq) {
            say(L_STEP, top->n > 1 ? "= (%p)/(%p)^2, then cancel" : "= %p/(%p)^2, then cancel", top, r.d);
        }
        wderiv(v, q, top, sq ? r.d : 0);
        if (nassigned()) {
            check_domain();
            say(L_RESULT | OPEN, "at ");
            wvalues();
            say(MORE, ": %r", rsubst(q));
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
        say(L_STEP | OPEN, "d/d%c ", vars[v]);
        wmono(&t->c, t->e, 1);
        wputs(" = ");
        if (k > 1 && !qone(&t->c)) {
            say(MORE | OPEN, "%d" G_DOT "%Q", k, &t->c);
            wvars(e);
            wputs(" = ");
        }
        if (k) wmono(&c, e, 1);
        else wputc('0');
        end();
    }
    dn = pderiv(r.n, v);
    wderiv(v, rpoly(dn), 0, 0);
    if (nassigned()) {
        say(L_RESULT | OPEN, "at ");
        wvalues();
        say(MORE, ": %r", rsubst(rpoly(dn)));
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
static void wvertex(const Q *a, const Q *h, const Q *k, int ch)
{
    uint8_t e[NV] = { 0 };
    Q t = *h;
    t.n = -t.n;
    if (a->n == -1 && a->d == 1) wputc('-');
    else if (!qone(a)) wqpar(a);
    if (h->n) {
        say(MORE | OPEN, "(%c", ch);
        wmono(&t, e, 0);
        wputc(')');
    } else {
        wputc(ch);
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
        say(L_STEP | OPEN, "factor %q out of the %c terms: %Q(%c^2", &a, vars[v], &a, vars[v]);
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
    say(L_STEP | OPEN, "half of %q is %q, add and subtract %Q^2 = ", &t, &u, &u);
    qmul(&t, &u, &u);
    say(MORE, "%q", &t);
    say(L_STEP | OPEN, "= ");
    wvertex(&a, &h, 0, vars[v]);
    if (c.n || u.n) {
        qmul(&t, &t, &a);
        t.n = -t.n;
        wmono(&t, e, 0);
        if (c.n) wmono(&c, e, 0);
    }
    end();
    say(L_RESULT | OPEN, "= ");
    wvertex(&a, &h, &k, vars[v]);
    end();
    say(L_RESULT, "vertex (%q, %q)", &h, &k);
    say(L_RESULT | OPEN, "axis %c = %q", vars[v], &h);
    wputs(a.n > 0 ? ", opens up, min " : ", opens down, max ");
    say(MORE, "%q", &k);
}

static void wto(int v, int left, int up)
{
    say(MORE | OPEN, "%c%s", vars[v], left ? G_TO "-" G_INF : G_TO G_INF);
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
        say(L_RESULT | OPEN, "%c = %s", vars[v], pts[i].s);
        wputs(pts[i].mult & 1 ? ", crosses" : ", touches");
        wmult(pts[i].mult);
        end();
    }
    if (dn >= 1 && !npts) {
        say(L_RESULT, "no real zeros");
    }
    if (dn - real > 0) {
        say(L_APPROX, "plus %d complex zeros (solve lists them)", dn - real);
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
        for (k = 0; k < npts; k++) zero_out |= rzero(&pts[k].v);
        if (!zero_out) {
            qset(&x, 0);
            qeval(&y0, r.n, v, &x);
            qset(&d0, 1);
            if (r.d) qeval(&d0, r.d, v, &x);
            qdiv(&y0, &y0, &d0);
            say(L_RESULT, "y-intercept (0, %q)", &y0);
        }
        for (k = 0; k < npts; k++) {
            begin(L_RESULT);
            if (pts[k].tag == 'd') {
                say(MORE | OPEN, "vertical asymptote %c = %s", vars[v], pts[k].s);
            } else {
                say(MORE | OPEN, "hole at %c = %s", vars[v], pts[k].s);
                if (pts[k].q) {
                    qnorm(&x, pts[k].p, pts[k].q);
                    qeval(&y0, r.n, v, &x);
                    qset(&d0, 1);
                    if (r.d) qeval(&d0, r.d, v, &x);
                    qdiv(&y0, &y0, &d0);
                    say(MORE | OPEN, ", y = %q", &y0);
                } else {
                    R yn, yd;
                    reval(&yn, r.n, v, &pts[k].v);
                    rset(&yd, 1);
                    if (r.d) reval(&yd, r.d, v, &pts[k].v);
                    xdiv(&yn, &yn, &yd);
                    wputs(", y " G_APPROX " ");
                    wreal(&yn);
                }
            }
            end();
        }
    }
    (void)i;
    lc = r.n->t[0].c;
    begin(L_RESULT);
    if (!r.d) {
        say(MORE, "degree %d, leading coefficient %q", dn, &lc);
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
    static Q a, b, c, h, k, t, one;
    int v = ratvar(r), dn, dd, x;
    uint8_t e[NV] = { 0 };
    Rat f;
    if (v < 0 || v == iv) fail("inverse needs a function of one variable");
    x = vars[v];
    dn = pdeg(r.n, v);
    dd = r.d ? pdeg(r.d, v) : 0;
    qset(&one, 1);
    say(L_STEP, "y = %r, swap %c and y, solve for y", r, x);
    if (dn == 2 && !dd) {
        need_quadratic(r, &a, &b, &c);
        vertex_of(&a, &b, &c, &h, &k);
        if (b.n) {
            say(L_STEP | OPEN, "vertex form: y = ");
            wvertex(&a, &h, &k, x);
            end();
        }
        /* (y-h)^2 = (x-k)/a */
        f.n = pvar(v);
        t = k;
        t.n = -t.n;
        addterm(f.n, &t, e);
        f.d = 0;
        qdiv(&t, &one, &a);
        replace(&f.n, pscale(f.n, &t));
        say(L_STEP | OPEN, "%c = ", x);
        wvertex(&a, &h, &k, 'y');
        end();
        begin(L_STEP);
        wvertex(&one, &h, 0, 'y');
        say(MORE, " = %r", f);
        say(L_RESULT | OPEN, "f^-1(%c) = ", x);
        if (h.n) wq(&h);
        say(MORE, G_PM G_SQRT "(%r)", f);
        say(L_APPROX, "not one-to-one: + for %c" G_GE "%q, - for %c" G_LE "%q", x, &h, x, &h);
        return;
    }
    if (dn > 1 || dd > 1 || (dn < 1 && dd < 1)) fail("inverse works for linear, quadratic and (ax+b)/(cx+d)");
    /* x = (A y + B)/(C y + D)  ->  y (C x - A) = B - D x */
    {
        static Q A, B, C, D, nA, nD, zero;
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
        nA = A;
        nA.n = -A.n;
        nD = D;
        nD.n = -D.n;
        qset(&zero, 0);
        if (C.n) {
            say(L_STEP, "%c = %P/%P", x, &A, 'y', &B, &C, 'y', &D);
            if (D.n) {
                say(L_STEP, "%c(%L) = %L", x, &C, 'y', &D, &A, 'y', &B);
                say(L_STEP, "%M%cy%T%c = %L", &C, x, &D, x, &A, 'y', &B);
            } else {
                say(L_STEP, "%M%cy = %L", &C, x, &A, 'y', &B);
            }
            if (A.n) {
                say(L_STEP, "%M%cy%Ty = %L", &C, x, &nA, &nD, x, &B);
                say(L_STEP, "y(%L) = %L", &C, x, &nA, &nD, x, &B);
            } else {
                say(L_STEP, "%M%cy = %L", &C, x, &nD, x, &B);
            }
        } else {
            if (qone(&D)) {
                say(L_STEP, "%c = %L", x, &A, 'y', &B);
            } else {
                say(L_STEP, "%c = %P/%q", x, &A, 'y', &B, &D);
                say(L_STEP, "%L = %L", &D, x, &zero, &A, 'y', &B);
            }
            t = B;
            t.n = -t.n;
            say(L_STEP, "%L = %L", &A, 'y', &zero, &D, x, &t);
        }
        e[v] = 1;
        f.n = pnew();
        addterm(f.n, &nD, e);
        e[v] = 0;
        addterm(f.n, &B, e);
        if (C.n) {
            f.d = pnew();
            e[v] = 1;
            addterm(f.d, &C, e);
            e[v] = 0;
            addterm(f.d, &nA, e);
        } else {
            f.d = pconst(&nA);
        }
        rsimp(&f);
        say(L_RESULT, "f^-1(%c) = %r", x, f);
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
    say(MORE | OPEN, "=%q", &mx[r][mcols]);
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
        say(L_STEP | OPEN, "R%d: ", i + 1);
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
            say(L_STEP, "swap R%d and R%d", row + 1, p + 1);
        }
        if (!qone(&mx[row][col])) {
            static Q f;
            f = mx[row][col];
            for (j = 0; j <= mcols; j++) qdiv(&mx[row][j], &mx[row][j], &f);
            say(L_STEP | OPEN, "R%d = R%d/%Q: ", row + 1, row + 1, &f);
            wrow(row);
            end();
        }
        for (i = 0; i < n; i++) {
            static Q f;
            f = mx[i][col];
            if (i == row || !f.n) continue;
            rowop(i, row, &f);
            say(L_STEP | OPEN, "R%d = R%d%c", i + 1, i + 1, f.n < 0 ? '+' : '-');
            if (f.n < 0) f.n = -f.n;
            if (!qone(&f)) wqpar(&f);
            say(MORE | OPEN, "R%d: ", row + 1);
            wrow(i);
            end();
        }
        piv[row++] = col;
    }
    for (i = row; i < n; i++) {
        if (!mx[i][mcols].n) continue;
        say(L_STEP, "R%d says 0=%q", i + 1, &mx[i][mcols]);
        say(L_RESULT, "no solution");
        return;
    }
    for (i = 0; i < row; i++) {
        say(L_RESULT | OPEN, "%c = ", vars[mvar[piv[i]]]);
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
        say(L_RESULT, "%c can be any number", vars[mvar[j]]);
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

static void wpair(int u, const Q *qu, const R *lu, int v, const Q *qv, const R *lv)
{
    int exact = qu != 0;
    say((exact ? L_RESULT : L_APPROX) | OPEN, "(%c, %c", vars[u < v ? u : v], vars[u < v ? v : u]);
    wputs(exact ? ") = (" : ") " G_APPROX " (");
    if (exact) wq(u < v ? qu : qv);
    else wreal(u < v ? lu : lv);
    wputs(", ");
    if (exact) wq(u < v ? qv : qu);
    else wreal(u < v ? lv : lu);
    say(MORE, ")");
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
    say(L_STEP, "from the linear one: %c = %r", vars[u], expr);
    memset(assigned, 0, sizeof assigned);
    assigned[u] = 1;
    val[u] = expr;
    sub = psubst(other);
    assigned[u] = 0;
    say(L_STEP, "substitute: %r=0", sub);
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
        say(L_RESULT, "no real solutions");
    }
    for (i = 0; i < npts; i++) {
        if (pts[i].q) continue;
        {
            R yv;
            reval(&yv, expr.n, v, &pts[i].v);
            wpair(u, 0, &yv, v, 0, &pts[i].v);
        }
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
            d = radd(l, r, 1, 0);
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
    nest4[4] = 0;
    dom = 0;
    domv = -1;
    memset(assigned, 0, sizeof assigned);
    for (i = 0; i < POOL; i++) pool[i].used = 0;
    /* an os math error (a real past 1e99) lands here with the handler already gone. the handler goes
       on before setjmp so a fail() longjmp comes back with the stack os_PopErrorHandler expects */
    if (os_PushErrorHandler()) {
        say(L_ERROR, "a number got too big for the calculator");
        return;
    }
    if (setjmp(fail_jmp)) {
        os_PopErrorHandler();
        return;
    }

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
        os_PopErrorHandler();
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
        r = radd(lhs, rhs, 1, 0);
        if (rel == '=' && (rhs.n->n || rhs.d)) {
            say(L_STEP, "move everything to one side: %r=0", r);
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
    os_PopErrorHandler();
}
