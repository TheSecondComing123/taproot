#include <graphx.h>
#include <ti/getcsc.h>
#include <string.h>
#include "cas.h"
#include "font.h"

#define X0 6
#define CW 7
#define RH 15
#define COLS ((320 - 2 * X0) / CW)
#define PER (COLS - 1)
#define MAXIN 110
#define BAR 222
#define SUPY 1

enum { C_BASE, C_MANTLE, C_CRUST, C_SURF, C_OVER, C_DIM, C_TEXT, C_SUB, C_BLUE, C_PEACH, C_GREEN, C_MAUVE, C_TEAL, C_RED, C_YELLOW, C_PINK, C_SKY, C_MAROON };
enum { M_NONE, M_2ND, M_ALPHA, M_LOCK };
enum { BOLD = 1, PRETTY = 2 };

static const uint16_t palette[] = {
    gfx_RGBTo1555(0x1e, 0x1e, 0x2e), gfx_RGBTo1555(0x18, 0x18, 0x25), gfx_RGBTo1555(0x11, 0x11, 0x1b),
    gfx_RGBTo1555(0x31, 0x32, 0x44), gfx_RGBTo1555(0x6c, 0x70, 0x86), gfx_RGBTo1555(0x93, 0x99, 0xb2),
    gfx_RGBTo1555(0xcd, 0xd6, 0xf4), gfx_RGBTo1555(0xa6, 0xad, 0xc8), gfx_RGBTo1555(0x89, 0xb4, 0xfa),
    gfx_RGBTo1555(0xfa, 0xb3, 0x87), gfx_RGBTo1555(0xa6, 0xe3, 0xa1), gfx_RGBTo1555(0xcb, 0xa6, 0xf7),
    gfx_RGBTo1555(0x94, 0xe2, 0xd5), gfx_RGBTo1555(0xf3, 0x8b, 0xa8), gfx_RGBTo1555(0xf9, 0xe2, 0xaf),
    gfx_RGBTo1555(0xf5, 0xc2, 0xe7), gfx_RGBTo1555(0x89, 0xdc, 0xeb), gfx_RGBTo1555(0xeb, 0xa0, 0xac),
};

/* the four keys under the screen, then the same keys after 2nd, then graph's key help */
static const char *const label[] = { "expand", "factor", "solve", "d/dx", "vertex", "zeros", "system", "inverse", "help" };
static const uint8_t accent[] = { C_BLUE, C_PEACH, C_GREEN, C_MAUVE, C_YELLOW, C_SKY, C_PINK, C_MAROON, C_TEAL };
#define KEYS 8


/* the key is everything before the first double space */
static const char *help[] = {
    "commands",
    "y=         expand  (2nd: vertex)",
    "window     factor  (2nd: zeros)",
    "zoom       solve   (2nd: system)",
    "trace      d/dx    (2nd: inverse)",
    "enter      solve if there's =, else again",
    "an empty line runs on the last answer",
    "typing",
    "x,t,\x07,n    x",
    "alpha      a letter, 2nd alpha for many",
    "sto\x16       =",
    "2nd math   =, then again for < > \x12 \x13",
    "2nd .      i, as in (2+i)/(1-i)",
    "x\x08         ^2",
    ",          x=3 plugs in, x=2x-1 composes",
    "moving",
    "\x17 \x16        cursor, 2nd jumps to the ends",
    "\x05 \x06        scroll, 2nd for a page",
    "2nd enter  earlier inputs",
    "del        backspace",
    "clear      the line, then the answer",
    "2nd mode   quit",
};
static const uint8_t help_kind[] = { L_RESULT, 0, 0, 0, 0, 0, 0, L_RESULT, 0, 0, 0, 0, 0, 0, 0, L_RESULT, 0, 0, 0, 0, 0, 0 };

static const char normal[] = {
    [sk_0] = '0', [sk_1] = '1', [sk_2] = '2', [sk_3] = '3', [sk_4] = '4', [sk_5] = '5', [sk_6] = '6', [sk_7] = '7',
    [sk_8] = '8', [sk_9] = '9', [sk_DecPnt] = '.', [sk_Add] = '+', [sk_Sub] = '-', [sk_Mul] = '*', [sk_Div] = '/',
    [sk_Power] = '^', [sk_LParen] = '(', [sk_RParen] = ')', [sk_Chs] = '-', [sk_GraphVar] = 'x', [sk_Comma] = ',',
    [sk_Store] = '=',
};

static const char alpha[] = {
    [sk_Math] = 'a', [sk_Apps] = 'b', [sk_Prgm] = 'c', [sk_Recip] = 'd', [sk_Sin] = 'e', [sk_Cos] = 'f', [sk_Tan] = 'g',
    [sk_Power] = 'h', [sk_Square] = 'i', [sk_Comma] = 'j', [sk_LParen] = 'k', [sk_RParen] = 'l', [sk_Div] = 'm',
    [sk_Log] = 'n', [sk_7] = 'o', [sk_8] = 'p', [sk_9] = 'q', [sk_Mul] = 'r', [sk_Ln] = 's', [sk_4] = 't', [sk_5] = 'u',
    [sk_6] = 'v', [sk_Sub] = 'w', [sk_Store] = 'x', [sk_1] = 'y', [sk_2] = 'z',
};

static char in[MAXIN + 1], ans[MAXIN + 1], hist[4][MAXIN + 1];
static int cur, last, shown = -1, scroll, nhist, hpos, ans_long;
static uint8_t pending, mode;
static const char **lines;
static const uint8_t *kinds;
static int nout, vis;
static const char *msg;

/* one byte per pixel row, bit 0 on the left: testing bit 0 compiles to one instruction, bit 7 to a signed compare */
static void glyph(const uint8_t *g, int h, uint8_t *p, uint8_t color)
{
    for (; h--; p += 320) {
        uint8_t b = *g++, *q = p;
        for (; b; b >>= 1, q++)
            if (b & 1) *q = color;
    }
}

static int digit(char c)
{
    return c >= '0' && c <= '9';
}

/* PRETTY draws ^2 and ^-1 as small raised digits and carries the radical's bar over the number under it */
static void text(const char *s, int n, int x, int y, uint8_t color, int style)
{
    int up = 0, bar = 0;
    uint8_t *p = &gfx_vbuffer[y][x];
    for (; n-- > 0 && *s; s++) {
        uint8_t c = *s;
        if (style & PRETTY && c == '^' && (digit(s[1]) || (s[1] == '-' && digit(s[2])))) {
            up = 1;
            continue;
        }
        if (up && (digit(c) || s[-1] == '^')) {
            glyph(sup[c == '-' ? 10 : c - '0'], 6, p + SUPY * 320, color);
            p += 5;
            continue;
        }
        up = 0;
        bar = style & PRETTY && (c == G_SQRT[0] || (bar && (digit(c) || (c == '-' && s[-1] == G_SQRT[0]))));
        if (bar && c != G_SQRT[0]) memset(p, color, CW);
        if (c != ' ') glyph(font[style & BOLD][c > ' ' ? c - 0x12 : c > 8 ? c - 9 : c - 1], 14, p, color);
        p += CW;
    }
}

static int cut(const char *s, int w)
{
    int i, n = strlen(s);
    if (n <= w) return n;
    for (i = w; i > w * 55 / 100; i--)
        if ((s[i] == '+' || s[i] == '-' || s[i] == ' ') && s[i - 1] != '^') return s[i] == ' ' ? i + 1 : i;
    return w;
}

static int input_rows(void)
{
    int r = strlen(in) / PER + 1;
    return r > 3 ? 3 : r;
}

/* walks every wrapped output row, answers first, then a divider and the steps; draws the ones in
   [scroll, scroll + vis), returns the total */
static int layout(int top, int vis)
{
    int i, pass, row = 0, keys = shown == KEYS, divided = 0;
    for (pass = 0; pass < 2; pass++)
        for (i = 0; i < nout; i++) {
            const char *s = lines[i], *key;
            int k = kinds[i], style, ind;
            uint8_t color;
            if ((keys || k != L_STEP) == pass) continue;
            if (pass && !divided) {
                divided = 1;
                if ((unsigned)(row - scroll) < (unsigned)vis) {
                    int y = top + (row - scroll) * RH;
                    text("steps", 5, X0, y, C_DIM, 0);
                    gfx_SetColor(C_SURF);
                    gfx_HorizLine(X0 + 6 * CW, y + 8, 320 - 2 * X0 - 6 * CW);
                }
                row++;
            }
            style = (k == L_RESULT || k == L_ERROR ? BOLD : 0) | (keys ? 0 : PRETTY);
            color = k == L_RESULT ? accent[shown] : k == L_APPROX ? C_DIM : k == L_ERROR ? C_RED : C_TEXT;
            key = keys && k == L_STEP ? strstr(s, "  ") : 0;
            for (ind = 0;; row++, ind = 2, key = 0) {
                int m = cut(s, COLS - ind), lab = key ? key - s : 0;
                if ((unsigned)(row - scroll) < (unsigned)vis) {
                    int y = top + (row - scroll) * RH;
                    text(s, lab, X0, y, C_SUB, 0);
                    text(s + lab, m - lab, X0 + (ind + lab) * CW, y, color, style);
                }
                s += m;
                if (!*s) break;
            }
            row++;
        }
    return row;
}

/* the start screen, a row each: rows 2-4 are examples for the first three keys */
static void hint(int y)
{
    static const char *const tip[] = {
        "type a problem, then press a key below", "", "(2x-3)^5", "x^3-8", "x^2-5x+6=0", "",
        "2nd: vertex, zeros, system, inverse", "graph: what every key does",
    };
    int i;
    for (i = 0; i < 8; i++, y += RH) {
        int ex = (unsigned)(i - 2) < 3;
        text(tip[i], 99, X0, y, ex ? C_TEXT : C_DIM, 0);
        if (ex) text(label[i - 2], 99, X0 + 14 * CW, y, accent[i - 2], BOLD);
    }
}

static void draw(void)
{
    int r, rows = input_rows(), top = rows * RH + 13, total, i;

    vis = (BAR - 4 - top) / RH;

    gfx_FillScreen(C_BASE);
    gfx_SetColor(C_MANTLE);
    gfx_FillRectangle(0, 0, 320, rows * RH + 8);
    for (r = 0; r < rows; r++) text(in + r * PER, PER, X0, 4 + r * RH, C_TEXT, 0);
    {
        int x = X0 + cur % PER * CW, y = 4 + cur / PER * RH;
        static const uint8_t color[] = { C_YELLOW, C_BLUE, C_GREEN, C_GREEN };
        char g = mode ? (" \x05" "aA")[mode] : in[cur];
        gfx_SetColor(color[mode]);
        gfx_FillRectangle(x, y, CW, 14);
        if (g) text(&g, 1, x, y, C_CRUST, 0);
    }

    if (shown < 0) {
        hint(top);
    } else {
        total = layout(top, 0);
        if (scroll > total - vis) scroll = total - vis;
        if (scroll < 0) scroll = 0;
        layout(top, vis);
        if (total > vis) {
            int track = vis * RH, h = track * vis / total;
            gfx_SetColor(C_SURF);
            gfx_FillRectangle(316, top, 2, track);
            gfx_SetColor(C_OVER);
            gfx_FillRectangle(316, top + (track - h) * scroll / (total - vis), 2, h);
        }
    }

    if (msg) {
        gfx_SetColor(C_SURF);
        gfx_FillRectangle(0, BAR - RH - 6, 320, RH + 4);
        text(msg, COLS, X0, BAR - RH - 4, C_YELLOW, 0);
    }

    gfx_SetColor(C_CRUST);
    gfx_FillRectangle(0, BAR - 2, 320, 240 - BAR + 2);
    for (i = 0; i < 5; i++) {
        int k = i == 4 ? KEYS : mode == M_2ND ? i + 4 : i, n = strlen(label[k]), on = k == shown;
        gfx_SetColor(on ? accent[k] : C_SURF);
        gfx_FillRectangle(i * 64 + 1, BAR, 62, 240 - BAR);
        text(label[k], n, i * 64 + 32 - n * CW / 2, BAR + 2, on ? C_CRUST : accent[k], on);
    }
    gfx_SwapDraw();
}

static void show(int cmd)
{
    shown = cmd;
    scroll = 0;
}

/* = or an inequality before the first top-level comma; the ones after it are values like x=3 */
static int equation(void)
{
    int i, depth = 0;
    for (i = 0; in[i]; i++) {
        if (in[i] == '(') depth++;
        else if (in[i] == ')') depth--;
        else if (in[i] == ',' && depth <= 0) return 0;
        else if (strchr("=<>" G_LE G_GE, in[i])) return 1;
    }
    return 0;
}

/* polled while math runs: clear stops it, any other key waits for the main loop */
static int stop(void)
{
    uint8_t k = os_GetCSC();
    if (k == sk_Clear) return 1;
    if (k) pending = k;
    return 0;
}

static void run(int cmd)
{
    int i;
    if (!*in) {
        strcpy(in, ans);
        cur = strlen(in);
    }
    if (!*in) {
        msg = ans_long ? "answer too long to reuse" : "type something first";
        return;
    }
    if (strcmp(in, hist[0])) {
        memmove(hist[1], hist[0], 3 * sizeof *hist);
        strcpy(hist[0], in);
        if (nhist < 4) nhist++;
    }
    hpos = 0;
    last = cmd;
    msg = "working, clear stops";
    draw();
    msg = 0;
    cas_run(cmd, in);
    lines = cas_line;
    kinds = cas_kind;
    nout = cas_nlines;
    show(cmd);
    *ans = 0;
    ans_long = 0;
    for (i = 0; i < nout && cmd != CMD_SOLVE && cmd != CMD_SYSTEM; i++) {
        const char *s = lines[i];
        if (kinds[i] != L_RESULT) continue;
        if (s[0] == '=' && !strchr(s, ',')) {
            if (strlen(s + 2) <= MAXIN) strcpy(ans, s + 2);
            else ans_long = 1;
        }
        break;
    }
}

static void insert(const char *t)
{
    int n = strlen(t), len = strlen(in);
    if (len + n > MAXIN) {
        msg = "line is full";
        return;
    }
    memmove(in + cur + n, in + cur, len - cur + 1);
    memcpy(in + cur, t, n);
    cur += n;
}

/* 2nd math types =, and again right after cycles it through < > <= >= */
static void relation(void)
{
    static const char cycle[] = { '=', '<', '>', G_LE[0], G_GE[0], '=', 0 };
    const char *p;
    if (cur && (p = strchr(cycle, in[cur - 1]))) {
        in[cur - 1] = p[1];
        return;
    }
    insert("=");
}

int main(void)
{
    char ch[2] = { 0, 0 };
    uint8_t k, m, f;

    gfx_Begin();
    gfx_SetDrawBuffer();
    memcpy(gfx_palette, palette, sizeof palette);
    cas_stop = stop;

    for (;;) {
        draw();
        k = pending;
        pending = 0;
        while (!k) k = os_GetCSC();
        msg = 0;

        if (k == sk_2nd) {
            mode = mode == M_2ND ? M_NONE : M_2ND;
            continue;
        }
        if (k == sk_Alpha) {
            mode = mode == M_2ND ? M_LOCK : mode ? M_NONE : M_ALPHA;
            continue;
        }
        m = mode;
        if (m != M_LOCK) mode = M_NONE;
        if (m >= M_ALPHA && k < sizeof alpha && alpha[k]) {
            ch[0] = alpha[k];
            insert(ch);
            continue;
        }
        /* y= window zoom trace are scan codes counting down */
        f = sk_Yequ - k;
        if (f < 4) {
            run(m == M_2ND ? f + CMD_VERTEX : f);
            continue;
        }
        if (m == M_2ND) {
            if (k == sk_Mode) break;
            if (k == sk_Math) {
                relation();
                continue;
            }
            if (k == sk_DecPnt) {
                insert("i");
                continue;
            }
            if (k == sk_Enter) {
                if (nhist) {
                    strcpy(in, hist[hpos]);
                    cur = strlen(in);
                    hpos = (hpos + 1) % nhist;
                }
                continue;
            }
            if (k == sk_Left) cur = 0;
            else if (k == sk_Right) cur = strlen(in);
            else if (k == sk_Up) scroll -= vis;
            else if (k == sk_Down) scroll += vis;
            else if (k != sk_Graph) msg = "2nd + key not used";
            if (k != sk_Graph) continue;
        }
        switch (k) {
        case sk_Graph:
            lines = help;
            kinds = help_kind;
            nout = sizeof help / sizeof *help;
            show(KEYS);
            break;
        case sk_Enter: run(equation() && last < CMD_VERTEX ? CMD_SOLVE : last); break;
        case sk_Del:
            if (cur) {
                memmove(in + cur - 1, in + cur, strlen(in) - cur + 1);
                cur--;
            }
            break;
        case sk_Clear:
            if (*in) in[cur = 0] = 0;
            else shown = -1;
            break;
        case sk_Left: if (cur) cur--; break;
        case sk_Right: if (in[cur]) cur++; break;
        case sk_Up: scroll--; break;
        case sk_Down: scroll++; break;
        case sk_Square: insert("^2"); break;
        default:
            if (k < sizeof normal && normal[k]) {
                ch[0] = normal[k];
                insert(ch);
            } else {
                msg = "key not used here";
            }
        }
    }
    gfx_End();
    return 0;
}
