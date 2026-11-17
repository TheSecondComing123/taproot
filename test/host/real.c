#include <math.h>
#include <string.h>
#include <ti/error.h>
#include <ti/real.h>

jmp_buf sim_os_err;

static long double get(const real_t *r)
{
    long double m = 0;
    int i, e = (uint8_t)r->exp - 0x80;
    for (i = 0; i < 14; i++) m = m * 10 + ((r->mant[i / 2] >> (i & 1 ? 0 : 4)) & 15);
    m = m * powl(10, e - 13);
    return r->sign & 0x80 ? -m : m;
}

static real_t put(long double x)
{
    real_t r;
    long double a = fabsl(x);
    long long digits;
    int e, i;
    memset(&r, 0, sizeof r);
    r.exp = (int8_t)0x80;
    if (x != x) longjmp(sim_os_err, 1);
    if (a < 1e-99L) return r;
    if (a >= 1e100L) longjmp(sim_os_err, 1);
    e = (int)floorl(log10l(a));
    digits = llroundl(a / powl(10, e - 13));
    if (digits >= 100000000000000LL) {
        digits /= 10;
        e++;
    } else if (digits < 10000000000000LL) {
        digits *= 10;
        e--;
    }
    for (i = 13; i >= 0; i--) {
        r.mant[i / 2] |= (uint8_t)((digits % 10) << (i & 1 ? 0 : 4));
        digits /= 10;
    }
    r.exp = (int8_t)(0x80 + e);
    if (x < 0) r.sign = (int8_t)0x80;
    return r;
}

real_t os_RealAdd(const real_t *a, const real_t *b) { return put(get(a) + get(b)); }
real_t os_RealSub(const real_t *a, const real_t *b) { return put(get(a) - get(b)); }
real_t os_RealMul(const real_t *a, const real_t *b) { return put(get(a) * get(b)); }

real_t os_RealDiv(const real_t *a, const real_t *b)
{
    if (get(b) == 0) longjmp(sim_os_err, 1);
    return put(get(a) / get(b));
}

real_t os_RealSqrt(const real_t *a)
{
    if (get(a) < 0) longjmp(sim_os_err, 1);
    return put(sqrtl(get(a)));
}

real_t os_RealRound(const real_t *a, char digits)
{
    long double s = powl(10, digits);
    return put(roundl(get(a) * s) / s);
}

int os_RealCompare(const real_t *a, const real_t *b)
{
    long double x = get(a), y = get(b);
    return (x > y) - (x < y);
}
