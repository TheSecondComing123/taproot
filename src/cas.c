#include "cas.h"
#include <ctype.h>
#include <limits.h>
#include <setjmp.h>
#include <string.h>

#define NV 4
#define MAXT 64
#define POOL 16
#define MAXD 40
#define MAXE 200
#define MAXPOW 60
#define TEXT 8192
#define STEP_LINES (CAS_MAXLINES - 16)
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

static long long ckmul(long long a, long long b)
{
    long long r;
    if (__builtin_mul_overflow(a, b, &r) || r == LLONG_MIN) fail("numbers too big");
    return r;
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
        Q coef = qmul(qmul(qint(c), qpow(A->c, n - k)), qpow(B->c, k));
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
        p = pexpr();
        if (peek() != ')') fail("missing )");
        s++;
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
        return punary();
    }
    if (ch != '-') return ppower();
    s++;
    p = punary();
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
    if (!isconst(p, &q)) {
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
    if (v >= 0 && assigned[v] && nassigned() == 1 && p->n && hasvars(p->t[0].e)) {
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

void cas_run(int cmd, const char *input)
{
    const char *part[NV + 1], *pend[NV + 1], *eq = 0, *p;
    int cur = 0, depth = 0, i;
    Poly *poly;

    cas_nlines = 0;
    textlen = 0;
    hidden = 0;
    nv = 0;
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
    if (cmd == CMD_FACTOR) fail("factor isn't built yet");
    if (cmd == CMD_SOLVE) fail("solve isn't built yet");

    poly = parse(part[0], pend[0]);
    if (cmd == CMD_EXPAND) do_expand(poly);
    else do_deriv(poly);
}
