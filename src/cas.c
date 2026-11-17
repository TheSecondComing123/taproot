#include "cas.h"
#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <setjmp.h>
#include <string.h>

#define NV 4
#define MAXT 64
#define POOL 16
#define MAXD 40
#define MAXE 200
#define MAXPOW 60
#define TEXT 8192
#define STEP_LINES (CAS_MAXLINES - 48)
#define STEP_TEXT (TEXT - 2048)
#define FRAC "fractions of polynomials aren't supported"

typedef struct { long long n, d; } Q;
typedef struct { Q c; uint8_t e[NV]; } Term;
typedef struct { uint8_t used; int n; Term t[MAXT]; } Poly;

const char *cas_line[CAS_MAXLINES];
uint8_t cas_kind[CAS_MAXLINES];
int cas_nlines;

static char text[TEXT];
static int textlen, hidden;
static char *w, *wend;
static char sink[1];

static Poly pool[POOL];
static char vars[NV];
static int nv;
static uint8_t assigned[NV];
static Q val[NV];
static jmp_buf fail_jmp;
static const char *s, *send;
static int nest;
static Poly *inexact_q, *inexact_r, *inexact_d;
static Q da[MAXD + 1], db[MAXD + 1], dq[MAXD + 1];

static void wputc(char c)
{
    if (w < wend - 1) {
        *w++ = c;
        *w = 0;
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
    cas_nlines++;
}

static void begin(int kind)
{
    int ok = cas_nlines < CAS_MAXLINES && textlen < TEXT - 1;
    if (kind == L_STEP && (cas_nlines >= STEP_LINES || textlen >= STEP_TEXT)) {
        if (ok && !hidden) {
            hidden = 1;
            begin(L_APPROX);
            wputs("(more steps hidden)");
            end();
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
    cas_line[cas_nlines] = w;
    cas_kind[cas_nlines] = kind;
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

int (*cas_stop)(void);

static void poll(void)
{
    if (cas_stop && cas_stop()) fail("stopped");
}

static long long ckmul(long long a, long long b)
{
    /* any exact overflow test (even divide-back) compiles to ~2.9 kb of inline 64-bit code on the ez80.
       the long double product is within 2^-53 of the real one, so 9.2e18 < 2^63 is a safe cutoff */
    long double p;
    if ((unsigned long long)a + 0x7fffffff < 0xffffffffULL && (unsigned long long)b + 0x7fffffff < 0xffffffffULL) return a * b;
    p = (long double)a * b;
    if (p >= 9.2e18L || p <= -9.2e18L) fail("numbers too big");
    return a * b;
}

static long long ckadd(long long a, long long b)
{
    long long r;
    if (__builtin_add_overflow(a, b, &r) || r == LLONG_MIN) fail("numbers too big");
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

static Q qint(long long n)
{
    Q q = { n, 1 };
    return q;
}

static Q qmake(long long n, long long d)
{
    long long g;
    if (d == 0) fail("division by zero");
    if (d < 0) {
        n = -n;
        d = -d;
    }
    g = gcd(n, d);
    return (Q){ n / g, d / g };
}

static Q qadd(Q a, Q b)
{
    long long g = gcd(a.d, b.d);
    return qmake(ckadd(ckmul(a.n, b.d / g), ckmul(b.n, a.d / g)), ckmul(a.d / g, b.d));
}

static Q qmul(Q a, Q b)
{
    long long g1 = gcd(a.n, b.d), g2 = gcd(b.n, a.d);
    return qmake(ckmul(a.n / g1, b.n / g2), ckmul(a.d / g2, b.d / g1));
}

static Q qneg(Q a)
{
    a.n = -a.n;
    return a;
}

static Q qdiv(Q a, Q b)
{
    if (!b.n) fail("division by zero");
    return qmul(a, qmake(b.d, b.n));
}

static Q qpow(Q a, int n)
{
    Q r = qint(1);
    while (n--) r = qmul(r, a);
    return r;
}

static void wq(Q a)
{
    wll(a.n);
    if (a.d != 1) {
        wputc('/');
        wll(a.d);
    }
}

static int qlen(Q a)
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
    for (v = 0; v < NV; v++) {
        if (!e[v]) continue;
        wputc(vars[v]);
        if (e[v] > 1) {
            wputc('^');
            wll(e[v]);
        }
    }
}

static void wmono(Q c, const uint8_t *e, int first)
{
    int hv = hasvars(e);
    if (c.n < 0) {
        wputc('-');
        c.n = -c.n;
    } else if (!first) {
        wputc('+');
    }
    if (c.d != 1 && hv) {
        wputc('(');
        wq(c);
        wputc(')');
    } else if (c.n != 1 || c.d != 1 || !hv) {
        wq(c);
    }
    wvars(e);
}

static void wpoly(const Poly *p)
{
    int i;
    if (!p->n) wputc('0');
    for (i = 0; i < p->n; i++) wmono(p->t[i].c, p->t[i].e, !i);
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
        wq(val[v]);
    }
}

static int mcmp(const uint8_t *a, const uint8_t *b)
{
    int da_ = 0, db_ = 0, i;
    for (i = 0; i < NV; i++) {
        da_ += a[i];
        db_ += b[i];
    }
    if (da_ != db_) return da_ > db_ ? -1 : 1;
    for (i = 0; i < NV; i++)
        if (a[i] != b[i]) return a[i] > b[i] ? -1 : 1;
    return 0;
}

static void addterm(Poly *p, Q c, const uint8_t *e)
{
    int i, r;
    if (!c.n) return;
    for (i = 0; i < p->n; i++) {
        r = mcmp(p->t[i].e, e);
        if (r == 0) {
            p->t[i].c = qadd(p->t[i].c, c);
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
    p->used = 0;
}

static Poly *pconst(Q c)
{
    Poly *p = pnew();
    uint8_t e[NV] = { 0 };
    addterm(p, c, e);
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
        *c = qint(0);
        return 1;
    }
    if (p->n == 1 && !hasvars(p->t[0].e)) {
        *c = p->t[0].c;
        return 1;
    }
    return 0;
}

static void operand(const Poly *p)
{
    if (p == inexact_q) fail(FRAC);
}

static Poly *padd(Poly *a, Poly *b, int neg)
{
    Poly *r;
    int i;
    operand(a);
    operand(b);
    r = pcopy(a);
    for (i = 0; i < b->n; i++) addterm(r, neg ? qneg(b->t[i].c) : b->t[i].c, b->t[i].e);
    return r;
}

static Poly *pmul(Poly *a, Poly *b)
{
    Poly *r;
    uint8_t e[NV];
    int i, j, v;
    operand(a);
    operand(b);
    r = pnew();
    for (i = 0; i < a->n; i++) {
        poll();
        for (j = 0; j < b->n; j++) {
            for (v = 0; v < NV; v++) {
                int x = a->t[i].e[v] + b->t[j].e[v];
                if (x > MAXE) fail("exponent too big (max 200)");
                e[v] = x;
            }
            addterm(r, qmul(a->t[i].c, b->t[j].c), e);
        }
    }
    return r;
}

static Poly *pscale(Poly *a, Q c)
{
    Poly *r;
    int i;
    operand(a);
    r = pnew();
    for (i = 0; i < a->n; i++) addterm(r, qmul(a->t[i].c, c), a->t[i].e);
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

static int todense(const Poly *p, int v, Q *c)
{
    int i, deg = -1;
    for (i = 0; i <= MAXD; i++) c[i] = qint(0);
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
        addterm(p, c[i], e);
    }
    return p;
}

static void wlinear(int v, Q a)
{
    uint8_t e[NV] = { 0 };
    wputc(vars[v]);
    if (a.n) wmono(qneg(a), e, 0);
}

static void wcell(Q a, int width, char lead)
{
    int pad = width - qlen(a);
    wputc(lead);
    while (--pad > 0) wputc(' ');
    wq(a);
}

/* synthetic division of c (degree deg) by x-a. quotient into quo, returns remainder */
static Q synthetic(const Q *c, int deg, Q a, Q *quo)
{
    static Q res[MAXD + 1], prod[MAXD + 1];
    int j, width = 0;
    res[0] = c[deg];
    prod[0] = qint(0);
    for (j = 1; j <= deg; j++) {
        prod[j] = qmul(a, res[j - 1]);
        res[j] = qadd(c[deg - j], prod[j]);
    }
    for (j = 0; j <= deg; j++) {
        if (qlen(c[deg - j]) > width) width = qlen(c[deg - j]);
        if (qlen(prod[j]) > width) width = qlen(prod[j]);
        if (qlen(res[j]) > width) width = qlen(res[j]);
    }
    width++;
    begin(L_STEP);
    for (j = 0; j <= deg; j++) wcell(c[deg - j], width, ' ');
    end();
    begin(L_STEP);
    for (j = 0; j < width; j++) wputc(' ');
    for (j = 1; j <= deg; j++) wcell(prod[j], width, ' ');
    end();
    begin(L_STEP);
    for (j = 0; j <= deg; j++) wcell(res[j], width, j == deg ? '|' : ' ');
    end();
    for (j = 0; j < deg; j++) quo[deg - 1 - j] = res[j];
    return res[deg];
}

static void longdiv(Q *num, int dn, const Q *den, int dd, int v, Q *quo)
{
    Poly *t, *prod, *left;
    Q coef;
    int i, j;
    for (i = 0; i <= dn - dd; i++) quo[i] = qint(0);
    for (i = dn; i >= dd; i--) {
        if (!num[i].n) continue;
        coef = qdiv(num[i], den[dd]);
        quo[i - dd] = coef;
        for (j = 0; j <= dd; j++) num[i - dd + j] = qadd(num[i - dd + j], qneg(qmul(coef, den[j])));
        t = pnew();
        {
            uint8_t e[NV] = { 0 };
            e[v] = i - dd;
            addterm(t, coef, e);
        }
        prod = fromdense(den, dd, v);
        left = fromdense(num, i - 1, v);
        begin(L_STEP);
        wpoly(t);
        wputs(G_DOT "(");
        wpoly(prod);
        wputs("), left ");
        wpoly(left);
        end();
        pfree(t);
        pfree(prod);
        pfree(left);
    }
}

static Poly *pdiv(Poly *a, Poly *b)
{
    Poly *q, *r;
    Q c;
    int va, vb, dn, dd;
    operand(a);
    operand(b);
    if (isconst(b, &c)) {
        if (!c.n) fail("division by zero");
        return pscale(a, qdiv(qint(1), c));
    }
    if (!a->n) return pnew();
    va = univar(a);
    vb = univar(b);
    if (va == -2 || vb == -2 || (va >= 0 && va != vb)) fail(FRAC);
    dn = todense(a, vb, da);
    dd = todense(b, vb, db);
    if (dn < dd) fail(FRAC);
    if (dd == 1 && db[1].n == 1 && db[1].d == 1) {
        Q root = qneg(db[0]);
        begin(L_STEP);
        wputs("synthetic division by ");
        wlinear(vb, root);
        end();
        da[0] = synthetic(da, dn, root, dq);
        da[1] = qint(0);
    } else {
        begin(L_STEP);
        wputs("long division by ");
        wpoly(b);
        end();
        longdiv(da, dn, db, dd, vb, dq);
    }
    q = fromdense(dq, dn - dd, vb);
    r = fromdense(da, dd - 1, vb);
    if (!r->n) {
        pfree(r);
        return q;
    }
    if (inexact_q) fail(FRAC);
    inexact_q = q;
    inexact_r = r;
    inexact_d = pcopy(b);
    return q;
}

static void binom_part(const Term *t, int k)
{
    int v, bare = t->c.n == 1 && t->c.d == 1;
    int nvars = 0;
    if (!k) return;
    for (v = 0; v < NV; v++) {
        if (t->e[v] > 1) bare = 0;
        if (t->e[v]) nvars++;
    }
    if (nvars != 1) bare = 0;
    if (!bare) wputc('(');
    wmono(t->c, t->e, 1);
    if (!bare) wputc(')');
    if (k > 1) {
        wputc('^');
        wll(k);
    }
}

static Poly *binom(const Poly *a, int n)
{
    const Term *A = &a->t[0], *B = &a->t[1];
    Poly *r = pnew();
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
        Q coef;
        poll();
        coef = qmul(qmul(qint(c), qpow(A->c, n - k)), qpow(B->c, k));
        for (v = 0; v < NV; v++) {
            int x = A->e[v] * (n - k) + B->e[v] * k;
            if (x > MAXE) fail("exponent too big (max 200)");
            e[v] = x;
        }
        addterm(r, coef, e);
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
        wmono(coef, e, 1);
        end();
        c = ckmul(c, n - k) / (k + 1);
    }
    return r;
}

static Poly *ppow(Poly *a, int n)
{
    Poly *r, *t;
    operand(a);
    if (a->n == 2 && n >= 2) return binom(a, n);
    if (a->n > 2 && n >= 2) {
        begin(L_STEP);
        wputs("multiply out (");
        wpoly(a);
        wputs(")^");
        wll(n);
        end();
    }
    r = pconst(qint(1));
    while (n--) {
        t = pmul(r, a);
        pfree(r);
        r = t;
    }
    return r;
}

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

static Poly *pexpr(void);
static Poly *punary(void);

/* each ( or leading sign recurses ~5 frames; the calc stack is small */
static void deeper(void)
{
    if (++nest > 24) fail("too many nested ( or signs");
}

static Poly *patom(void)
{
    int ch = peek();
    Poly *p;
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
        return pconst(qmake(n, d));
    }
    if (isalpha(ch)) {
        uint8_t e[NV] = { 0 };
        e[varidx(tolower(ch))] = 1;
        s++;
        p = pnew();
        addterm(p, qint(1), e);
        return p;
    }
    if (ch == '(') {
        s++;
        deeper();
        p = pexpr();
        if (peek() != ')') fail("missing )");
        s++;
        nest--;
        return p;
    }
    if (!ch) fail("the expression ends too early");
    if (ch == ')') fail("extra )");
    unexpected(ch);
}

static Poly *ppower(void)
{
    Poly *b = patom(), *ex, *r;
    Q q;
    if (peek() != '^') return b;
    s++;
    ex = punary();
    if (!isconst(ex, &q) || q.d != 1 || q.n < 0) {
        begin(L_ERROR);
        wputs("exponent must be a whole number (got ");
        wpoly(ex);
        wputc(')');
        die();
    }
    if (q.n > MAXPOW) fail("exponent too big (max 60)");
    r = ppow(b, (int)q.n);
    pfree(b);
    pfree(ex);
    return r;
}

static Poly *punary(void)
{
    Poly *p, *r;
    int ch = peek();
    if (ch == '+') {
        s++;
        deeper();
        p = punary();
        nest--;
        return p;
    }
    if (ch != '-') return ppower();
    s++;
    deeper();
    p = punary();
    nest--;
    r = pscale(p, qint(-1));
    pfree(p);
    return r;
}

static Poly *pterm(void)
{
    Poly *a = punary(), *b, *r;
    for (;;) {
        int ch = peek();
        if (ch == '*' || ch == '/') {
            s++;
            b = punary();
            r = ch == '*' ? pmul(a, b) : pdiv(a, b);
        } else if (isalnum(ch) || ch == '(' || ch == '.') {
            b = ppower();
            r = pmul(a, b);
        } else {
            return a;
        }
        pfree(a);
        pfree(b);
        a = r;
    }
}

static Poly *pexpr(void)
{
    Poly *a = pterm(), *b, *r;
    for (;;) {
        int ch = peek();
        if (ch != '+' && ch != '-') return a;
        s++;
        b = pterm();
        r = padd(a, b, ch == '-');
        pfree(a);
        pfree(b);
        a = r;
    }
}

static Poly *parse(const char *start, const char *stop)
{
    Poly *p;
    s = start;
    send = stop;
    p = pexpr();
    if (peek()) {
        if (*s == ')') fail("extra )");
        unexpected(*s);
    }
    return p;
}

static void parse_value(const char *start, const char *stop)
{
    Poly *p;
    Q q;
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
    p = pexpr();
    if (peek()) unexpected(*s);
    if (inexact_q || !isconst(p, &q)) {
        begin(L_ERROR);
        wputc(vars[v]);
        wputs("= needs a number");
        die();
    }
    assigned[v] = 1;
    val[v] = q;
    pfree(p);
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

static Poly *subst(const Poly *p)
{
    Poly *r = pnew();
    uint8_t e[NV];
    int i, v;
    for (i = 0; i < p->n; i++) {
        Q c = p->t[i].c;
        memcpy(e, p->t[i].e, NV);
        for (v = 0; v < NV; v++) {
            if (!assigned[v]) continue;
            c = qmul(c, qpow(val[v], e[v]));
            e[v] = 0;
        }
        addterm(r, c, e);
    }
    return r;
}

static int nassigned(void)
{
    int v, n = 0;
    for (v = 0; v < NV; v++) n += assigned[v];
    return n;
}

static void result(const char *prefix, const Poly *p)
{
    begin(L_RESULT);
    wputs(prefix);
    wpoly(p);
    end();
}

static void do_expand(Poly *p)
{
    int v = univar(p);
    if (inexact_q) {
        const Poly *r = inexact_r;
        if (nassigned()) fail("can't plug values into a division with a remainder");
        begin(L_RESULT);
        wputs("= ");
        wpoly(p);
        wputs(", remainder ");
        wpoly(r);
        end();
        begin(L_RESULT);
        wputs("= ");
        wpoly(p);
        if (r->n == 1 && r->t[0].c.d == 1) {
            wmono(r->t[0].c, r->t[0].e, 0);
        } else {
            wputs("+(");
            wpoly(r);
            wputc(')');
        }
        wputs("/(");
        wpoly(inexact_d);
        wputc(')');
        end();
        return;
    }
    if (!nassigned()) {
        result("= ", p);
        return;
    }
    begin(L_STEP);
    wputs("P = ");
    wpoly(p);
    end();
    if (v >= 0 && assigned[v] && nassigned() == 1 && p->n && hasvars(p->t[0].e) && p->t[0].e[v] <= MAXD) {
        int deg = todense(p, v, da);
        begin(L_STEP);
        wputs("remainder theorem: P(");
        wq(val[v]);
        wputs(") is the remainder of P/(");
        wlinear(v, val[v]);
        wputc(')');
        end();
        synthetic(da, deg, val[v], dq);
    } else {
        begin(L_STEP);
        wputs("plug in ");
        wvalues();
        end();
    }
    result("= ", subst(p));
}

static void do_deriv(Poly *p)
{
    Poly *r;
    uint8_t e[NV];
    int i, v = -1, x = varidx('x');
    if (inexact_q) fail(FRAC);
    for (i = 0; i < p->n; i++)
        if (vars[x] == 'x' && p->t[i].e[x]) v = x;
    if (v < 0) {
        for (i = 0; i < p->n && v < 0; i++) {
            int k;
            for (k = 0; k < NV; k++)
                if (p->t[i].e[k]) {
                    v = k;
                    break;
                }
        }
    }
    r = pnew();
    if (v < 0) {
        begin(L_STEP);
        wputs("no variable, so the slope is 0");
        end();
    } else {
        begin(L_STEP);
        wputs("power rule, term by term");
        end();
    }
    for (i = 0; v >= 0 && i < p->n; i++) {
        const Term *t = &p->t[i];
        int k = t->e[v];
        Q c = qmul(t->c, qint(k));
        memcpy(e, t->e, NV);
        if (k) e[v] = k - 1;
        if (k) addterm(r, c, e);
        begin(L_STEP);
        wputs("d/d");
        wputc(vars[v]);
        wputc(' ');
        wmono(t->c, t->e, 1);
        wputs(" = ");
        if (k > 1 && !(t->c.n == 1 && t->c.d == 1)) {
            wll(k);
            wputs(G_DOT);
            if (t->c.n < 0 || t->c.d != 1) {
                wputc('(');
                wq(t->c);
                wputc(')');
            } else {
                wq(t->c);
            }
            wvars(e);
            wputs(" = ");
        }
        if (k) wmono(c, e, 1);
        else wputc('0');
        end();
    }
    result("= ", r);
    if (nassigned()) {
        begin(L_RESULT);
        wputs("at ");
        wvalues();
        wputs(": ");
        wpoly(subst(r));
        end();
    }
}

typedef struct { long long p, q; int mult; } Root;

static Root roots[MAXD + 1];
static int nroots;
static long long ip[MAXD + 1];
static int ideg;
static long long dv0[256], dvn[256];
static long long bqa[2], bqb[2];
static int nbq, bqmult;
typedef struct { long double r, i; } Cx;

static Cx z[MAXD];
static int zm[MAXD], nz;
static long double dkerr;

static Poly *gcf(const Poly *p, Q *k, uint8_t *m)
{
    Poly *r;
    long long g = 0, l = 1;
    int i, v, show = 0;
    for (v = 0; v < NV; v++) m[v] = MAXE;
    for (i = 0; i < p->n; i++) {
        g = gcd(g, p->t[i].c.n);
        l = ckmul(l / gcd(l, p->t[i].c.d), p->t[i].c.d);
        for (v = 0; v < NV; v++)
            if (p->t[i].e[v] < m[v]) m[v] = p->t[i].e[v];
    }
    *k = qmake(p->t[0].c.n < 0 ? -g : g, l);
    r = pnew();
    for (i = 0; i < p->n; i++) {
        uint8_t e[NV];
        for (v = 0; v < NV; v++) e[v] = p->t[i].e[v] - m[v];
        addterm(r, qdiv(p->t[i].c, *k), e);
    }
    for (v = 0; v < NV; v++) show |= m[v];
    if (r->n > 1 && (show || k->n != 1 || k->d != 1)) {
        begin(L_STEP);
        wputs("GCF ");
        wmono(*k, m, 1);
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
    for (i = 0; i <= ideg; i++) da[i] = qint(ip[i]);
    p = fromdense(da, ideg, v);
    wpoly(p);
    pfree(p);
}

static void wlinfactor(long long p, long long q, int v)
{
    uint8_t e[NV] = { 0 };
    e[v] = 1;
    wmono(qint(q), e, 1);
    e[v] = 0;
    if (p) wmono(qint(-p), e, 0);
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
    int k = 1, i, base, e;
    if (n < 0) n = -n;
    out[0] = 1;
    for (p = 2; n > 1; p += 1 + (p > 2)) {
        if (!(p & 4095)) poll();
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
        long long t = ckadd(ip[k], ckmul(p, b[k]));
        if (t % q) return 0;
        b[k - 1] = t / q;
    }
    if (ckadd(ip[0], ckmul(p, b[0]))) return 0;
    for (k = 0; k < ideg; k++) ip[k] = b[k];
    ideg--;
    return 1;
}

static void wcandidates(int n0, int nn)
{
    int i, j, count = 0;
    for (i = 0; i < nn; i++)
        for (j = 0; j < n0; j++) count += gcd(dv0[j], dvn[i]) == 1;
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
            wq(qmake(dv0[j], dvn[i]));
            if (count) wputs(", ");
        }
    }
    wputs(" work");
}

static void find_roots(int v)
{
    int i, j, sgn, n0, nn, found, any = 0;
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
            begin(L_STEP);
            wputs("too many candidates, skipping the rest");
            end();
            return;
        }
        for (i = 0; i < nn && !found; i++) {
            for (j = 0; j < n0 && !found; j++) {
                if (gcd(dv0[j], dvn[i]) != 1) continue;
                for (sgn = 1; sgn >= -1 && !found; sgn -= 2) {
                    long long p = sgn * dv0[j], q = dvn[i];
                    poll();
                    if (!try_root(p, q)) continue;
                    found = any = 1;
                    add_root(p, q, 1);
                    begin(L_STEP);
                    wputc(vars[v]);
                    wputc('=');
                    wq(qmake(p, q));
                    wputs(": P(");
                    wq(qmake(p, q));
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
    long long s = 1, j;
    for (j = 2; j <= n / j && j <= 1000000; j++) {
        if (!(j & 4095)) poll();
        while (n % (j * j) == 0) {
            n /= j * j;
            s *= j;
        }
    }
    *rest = n;
    return s;
}

/* x^4 + ... with only even powers whose x^2-quadratic has rational roots */
static int biquad(int v)
{
    long long a = ip[4], b = ip[2], c = ip[0], d, s;
    int i;
    Q u;
    if (ideg != 4 || ip[1] || ip[3]) return 0;
    d = ckadd(ckmul(b, b), -ckmul(4, ckmul(a, c)));
    if (d < 0) return 0;
    s = isqrt(d);
    if (s * s != d) return 0;
    begin(L_STEP);
    wputs("only even powers, so treat it as a quadratic in ");
    wputc(vars[v]);
    wputs("^2");
    end();
    for (i = 0; i < 2; i++) {
        u = qmake(ckadd(-b, i ? -s : s), ckmul(2, a));
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
    nbq = s ? 2 : 1;
    bqmult = s ? 1 : 2;
    begin(L_STEP);
    wip(v);
    wputs(" = ");
    for (i = 0; i < nbq; i++) {
        uint8_t e[NV] = { 0 };
        e[v] = 2;
        wputc('(');
        wmono(qint(bqb[i]), e, 1);
        e[v] = 0;
        wmono(qint(-bqa[i]), e, 0);
        wputc(')');
    }
    if (bqmult > 1) wputs("^2");
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

static void wradical(long long num, long long k, long long r, int neg, long long den)
{
    int paren = den != 1 && num;
    if (paren) wputc('(');
    if (num) wll(num);
    wputs(G_PM);
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

static void quad_steps(long long a, long long b, long long c, int v)
{
    long long d = ckadd(ckmul(b, b), -ckmul(4, ckmul(a, c))), r, s;
    int neg = d < 0;
    s = sqpart(neg ? -d : d, &r);
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
    if (s != 1 || neg) {
        begin(L_STEP);
        wputs(G_SQRT);
        wll(d);
        wputs(" = ");
        if (s != 1 || r == 1) wll(s);
        if (neg) wputc('i');
        if (r != 1) {
            wputs(G_SQRT);
            wll(r);
        }
        end();
    }
    if (gcd(gcd(b, s), 2 * a) != 1) {
        begin(L_STEP);
        wputc(vars[v]);
        wputs(" = ");
        wradical(-b, s, r, neg, ckmul(2, a));
        end();
    }
}

static void quad_result(long long a, long long b, long long c, int v, int mult)
{
    long long d = ckadd(ckmul(b, b), -ckmul(4, ckmul(a, c))), r, s, g;
    long double re, im;
    int neg = d < 0;
    s = sqpart(neg ? -d : d, &r);
    g = gcd(gcd(b, s), ckmul(2, a));
    begin(L_RESULT);
    wputc(vars[v]);
    wputs(" = ");
    wradical(-b / g, s / g, r, neg, 2 * a / g);
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
__attribute__((noinline)) static void horner(const long double *c, int n, int d, const Cx *z, Cx *v)
{
    long double f;
    int j, t;
    v->r = v->i = 0;
    for (j = n; j >= d; j--) {
        for (f = c[j], t = 0; t < d; t++) f *= j - t;
        cmul(v, z);
        v->r += f;
    }
}

static void numeric(void)
{
    static long double c[MAXD + 1];
    Cx w, u = { 0.4L / 0.98488578L, 0.9L / 0.98488578L }, p, d, t, sum;
    long double m, maxd, rad = 2, r, tk, step;
    int k, j, it, mult, n = ideg;
    for (k = 0; k <= n; k++) c[k] = (long double)ip[k] / ip[n];
    /* fujiwara bound, 2 max |c[n-k]|^(1/k), rounded up to a power of 2 so no powl is needed */
    for (k = 1; k <= n; k++) {
        for (r = tk = step = 1, j = 0; j < k; j++) step *= 2;
        for (; tk < fabsl(c[n - k]); tk *= step) r *= 2;
        if (2 * r > rad) rad = 2 * r;
    }
    w.r = rad;
    w.i = 0;
    for (k = 0; k < n; k++) {
        z[k] = w;
        z[k].r -= c[n - 1] / n;
        zm[k] = 1;
        cmul(&w, &u);
    }
    for (it = 0; it < 1000; it++) {
        poll();
        maxd = 0;
        for (k = 0; k < n; k++) {
            horner(c, n, 0, &z[k], &p);
            d.r = 1;
            d.i = 0;
            for (j = 0; j < n; j++) {
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
    nz = 0;
    dkerr = 0;
    for (k = 0; k < n; k++) {
        if (!zm[k]) continue;
        sum = z[k];
        mult = 1;
        for (j = k + 1; j < n; j++) {
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
        zm[nz++] = mult;
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

static void do_factor(Poly *p)
{
    Poly *r;
    Q k;
    uint8_t m[NV];
    int v, i, pieces, paren, hasmono;
    if (inexact_q) fail(FRAC);
    if (!p->n) {
        result("= ", p);
        return;
    }
    r = gcf(p, &k, m);
    v = univar(r);
    ideg = 0;
    if (v >= 0) {
        ideg = intdense(r, v);
        find_roots(v);
        biquad(v);
    }
    pieces = nroots + nbq + (ideg >= 1) + (v == -2);
    hasmono = hasvars(m) || k.n != 1 || k.d != 1;
    paren = pieces > 1 || hasmono;
    for (i = 0; i < nroots; i++) paren |= roots[i].mult > 1;
    begin(L_RESULT);
    wputs("= ");
    if (!pieces || hasvars(m) || (k.d == 1 && k.n != 1 && k.n != -1)) {
        wmono(k, m, 1);
    } else if (k.n == -1 && k.d == 1) {
        wputc('-');
    } else if (k.d != 1) {
        wputc('(');
        wq(k);
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
    for (i = 0; i < nbq; i++) {
        uint8_t e[NV] = { 0 };
        e[v] = 2;
        wputc('(');
        wmono(qint(bqb[i]), e, 1);
        e[v] = 0;
        wmono(qint(-bqa[i]), e, 0);
        wputc(')');
        if (bqmult > 1) wputs("^2");
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
    end();
    if (nassigned()) {
        begin(L_RESULT);
        wputs("at ");
        wvalues();
        wputs(": ");
        wpoly(subst(p));
        end();
    }
}

static int rootcmp(const Root *a, const Root *b)
{
    long double x = (long double)a->p / a->q, y = (long double)b->p / b->q;
    return x < y ? -1 : x > y;
}

static void do_solve(Poly *p)
{
    Poly *r;
    Q k;
    uint8_t m[NV];
    int v, i, j, quad = 0;
    if (inexact_q) fail(FRAC);
    v = univar(p);
    if (v == -2) fail("solve needs one variable");
    if (v == -1) {
        begin(L_RESULT);
        wputs(p->n ? "no solution" : "every value works");
        end();
        return;
    }
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
    if (ideg == 1) {
        add_root(-ip[0], ip[1], 1);
        begin(L_STEP);
        wip(v);
        wputs("=0 gives ");
        wputc(vars[v]);
        wputc('=');
        wq(qmake(-ip[0], ip[1]));
        end();
        ideg = 0;
    }
    find_roots(v);
    if (ideg == 2) {
        quad = 1;
        quad_steps(ip[2], ip[1], ip[0], v);
    } else if (ideg >= 3 && !biquad(v)) {
        numeric();
    }

    for (i = 1; i < nroots; i++) {
        Root t = roots[i];
        for (j = i; j > 0 && rootcmp(&roots[j - 1], &t) > 0; j--) roots[j] = roots[j - 1];
        roots[j] = t;
    }
    for (i = 0; i < nroots; i++) {
        begin(L_RESULT);
        wputc(vars[v]);
        wputs(" = ");
        wq(qmake(roots[i].p, roots[i].q));
        if (roots[i].mult > 1) {
            wputs(" (multiplicity ");
            wll(roots[i].mult);
            wputc(')');
        }
        end();
    }
    if (quad) quad_result(ip[2], ip[1], ip[0], v, 1);
    for (i = 0; i < nbq; i++) quad_result(bqb[i], 0, -bqa[i], v, bqmult);
    numeric_result(v);
}

void cas_run(int cmd, const char *input)
{
    const char *part[NV + 1], *pend[NV + 1], *eq = 0, *p;
    int cur = 0, depth = 0, i;
    Poly *poly;

    cas_nlines = 0;
    textlen = 0;
    hidden = 0;
    nv = 0;
    nroots = nbq = nz = nest = 0;
    inexact_q = inexact_r = inexact_d = 0;
    memset(assigned, 0, sizeof assigned);
    for (i = 0; i < POOL; i++) pool[i].used = 0;
    if (setjmp(fail_jmp)) return;

    for (p = input; *p; p++)
        if (isalpha((unsigned char)*p)) addvar(tolower((unsigned char)*p));
    part[0] = input;
    for (p = input; *p; p++) {
        if (*p == '(') depth++;
        else if (*p == ')') depth--;
        else if (*p == ',' && depth <= 0) {
            if (cur == NV) fail("too many values after commas");
            pend[cur++] = p;
            part[cur] = p + 1;
        } else if (*p == '=' && cur == 0) {
            if (eq) fail("only one = allowed");
            eq = p;
        }
    }
    pend[cur] = p;

    for (p = part[0]; p < pend[0] && *p == ' '; p++);
    if (p == pend[0]) fail("type an expression first");
    for (i = 1; i <= cur; i++) parse_value(part[i], pend[i]);
    if (cmd == CMD_SOLVE && cur) fail("solve finds the values itself, drop the , x=");
    if (eq && cmd != CMD_SOLVE) fail("use solve for equations");

    poly = parse(part[0], eq ? eq : pend[0]);
    if (eq) {
        Poly *lhs = poly, *rhs = parse(eq + 1, pend[0]);
        poly = padd(lhs, rhs, 1);
        if (rhs->n) {
            begin(L_STEP);
            wputs("move everything to one side: ");
            wpoly(poly);
            wputs("=0");
            end();
        }
        pfree(lhs);
        pfree(rhs);
    }
    if (cmd == CMD_EXPAND) do_expand(poly);
    else if (cmd == CMD_FACTOR) do_factor(poly);
    else if (cmd == CMD_SOLVE) do_solve(poly);
    else do_deriv(poly);
}
