#include <graphx.h>
#include <ti/getcsc.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static uint8_t pool[16 * 1284];
static char text[8192];

/* volatile so lto can't fold the math and skip linking the runtime routines */
static volatile long long ll_a = 123456789012LL, ll_b = -987654321LL;
static volatile long double ld_x = 2.0L;

static int row;
static void line(const char *s)
{
    gfx_PrintStringXY(s, 4, 4 + row * 10);
    row++;
}

static void lltos(long long v, char *out)
{
    char tmp[24];
    int n = 0;
    unsigned long long u = v < 0 ? -(unsigned long long)v : (unsigned long long)v;
    do tmp[n++] = '0' + u % 10; while (u /= 10);
    if (v < 0) *out++ = '-';
    while (n) *out++ = tmp[--n];
    *out = 0;
}

int main(void)
{
    char buf[64], num[24];
    long long r;

    memset(pool, 1, sizeof pool);
    memset(text, 'a', sizeof text);

    gfx_Begin();
    gfx_SetMonospaceFont(8);

    lltos(ll_a * ll_b, num);
    snprintf(buf, sizeof buf, "mul: %s", num);
    line(buf);

    lltos(ll_a / ll_b, num);
    snprintf(buf, sizeof buf, "div: %s", num);
    line(buf);

    line(__builtin_mul_overflow(ll_a, ll_a, &r) ? "overflow check: caught" : "overflow check: MISSED");
    line(__builtin_add_overflow(ll_a, ll_b, &r) ? "add check: WRONG" : "add check: ok");

    long double s = 1.0L;
    for (int i = 0; i < 8; i++) s = (s + ld_x / s) / 2.0L;
    lltos((long long)(s * 1e12L), num);
    snprintf(buf, sizeof buf, "sqrt2 e12: %s", num);
    line(buf);

    snprintf(buf, sizeof buf, "sizes: ld=%d ll=%d", (int)sizeof(long double), (int)sizeof(long long));
    line(buf);
    snprintf(buf, sizeof buf, "pool[100]=%d text[100]=%c", pool[100], text[100]);
    line(buf);
    line("press any key");

    while (!os_GetCSC());
    gfx_End();
    return 0;
}
