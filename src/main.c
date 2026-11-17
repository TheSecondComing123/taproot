#include <graphx.h>
#include <ti/getcsc.h>
#include <string.h>
#include "cas.h"
#include "font.h"

#define X0 4
#define RH 10
#define CW 6
#define COLS ((320 - 2 * X0) / CW - 1)
#define PER (COLS - 1)
#define MAXIN 110
#define BAR 226

enum { C_BASE, C_MANTLE, C_CRUST, C_SURF, C_OVER, C_TEXT, C_SUB, C_BLUE, C_PEACH, C_GREEN, C_MAUVE, C_TEAL, C_RED, C_YELLOW, C_LAV, C_PINK, C_SKY, C_MAROON, C_NONE = 255 };
enum { M_NONE, M_2ND, M_ALPHA, M_LOCK };

static const uint8_t rgb[][3] = {
    { 0x1e, 0x1e, 0x2e }, { 0x18, 0x18, 0x25 }, { 0x11, 0x11, 0x1b }, { 0x31, 0x32, 0x44 }, { 0x6c, 0x70, 0x86 },
    { 0xcd, 0xd6, 0xf4 }, { 0xa6, 0xad, 0xc8 }, { 0x89, 0xb4, 0xfa }, { 0xfa, 0xb3, 0x87 }, { 0xa6, 0xe3, 0xa1 },
    { 0xcb, 0xa6, 0xf7 }, { 0x94, 0xe2, 0xd5 }, { 0xf3, 0x8b, 0xa8 }, { 0xf9, 0xe2, 0xaf }, { 0xb4, 0xbe, 0xfe },
    { 0xf5, 0xc2, 0xe7 }, { 0x89, 0xdc, 0xeb }, { 0xeb, 0xa0, 0xac },
};

/* the four keys under the screen, then the same keys after 2nd, then graph's key help */
static const char *const label[] = { "expand", "factor", "solve", "d/dx", "vertex", "zeros", "system", "inverse", "keys" };
static const uint8_t accent[] = { C_BLUE, C_PEACH, C_GREEN, C_MAUVE, C_YELLOW, C_SKY, C_PINK, C_MAROON, C_TEAL };
#define KEYS 8

static const char *help[] = {
    "y=        expand (2x-3)^5",
    "window    factor x^3-1",
    "zoom      solve  x^2-x-6<0",
    "trace     d/dx   3x^4-5x, x=1",
    "2nd y=    vertex 2x^2+8x+3",
    "2nd wind  zeros  (x^2-1)/(x-2)",
    "2nd zoom  system x+y=3, x-y=1",
    "2nd trace inverse (2x+1)/(x-3)",
    "on an empty line they use the answer",
    "2nd enter earlier inputs",
    "2nd math  = again for < > \x12 \x13",
    "2nd .     i, so (2+i)/(1-i) works",
    ",         x=3 plugs in, x=2x-1 composes",
    "X,T,\x07,n   types x",
    "alpha     next key types a letter",
    "2nd alpha letters until alpha",
    "x\x08        types ^2",
    "sto       types =",
    "enter     solve if =, else last",
    "del       backspace",
    "clear     line, output, or a run",
    "\x05 \x06       scroll, 2nd = page",
    "2nd mode  quit",
};
static const uint8_t help_kind[sizeof help / sizeof *help];

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
static int cur, mode, last, shown = -1, scroll, nhist, hpos, ans_long;
static uint8_t pending;
static char head[MAXIN + 16];
static const char **lines;
static const uint8_t *kinds;
static int nout;
static const char *msg;

static void text(const char *s, int n, int x, int y, uint8_t color)
{
    gfx_SetTextFGColor(color);
    gfx_SetTextXY(x, y);
    while (n-- > 0 && *s) gfx_PrintChar(*s++);
}

static int cut(const char *s, int w)
{
    int i, n = strlen(s);
    if (n <= w) return n;
    for (i = w; i > w * 55 / 100; i--)
        if (s[i] == '+' || s[i] == '-' || s[i] == ' ') return s[i] == ' ' ? i + 1 : i;
    return w;
}

static int input_rows(void)
{
    int r = strlen(in) / PER + 1;
    return r > 3 ? 3 : r;
}

/* walks every wrapped output row, answers before steps; draws the visible ones, returns the total */
static int layout(int top, int vis, int draw)
{
    int i, pass, row = 0, steps = 0;
    for (i = 0; i < nout; i++) steps |= kinds[i] == L_STEP;
    for (pass = 0; pass < 4; pass++)
    for (i = pass == 1 || pass == 3 ? 0 : -1; i < (pass == 1 || pass == 3 ? nout : 0); i++) {
        const char *s = pass == 0 ? head : pass == 2 ? "steps" : lines[i];
        int k = pass == 0 ? -1 : pass == 2 ? L_APPROX : kinds[i];
        uint8_t color = k < 0 ? C_SUB : k == L_RESULT ? accent[shown] : k == L_APPROX ? C_OVER : k == L_ERROR ? C_RED : C_TEXT;
        int first = 1;
        if (pass == 2 && (!steps || shown == KEYS)) continue;
        if (pass == 1 && k == L_STEP) continue;
        if (pass == 3 && k != L_STEP) continue;
        do {
            int ind = first ? 0 : 2, n = cut(s, COLS - ind);
            if (draw && row >= scroll && row < scroll + vis) {
                int x = X0 + ind * CW, y = top + (row - scroll) * RH;
                int lab = k < 0 && first ? (int)strlen(label[shown]) : 0;
                text(s, lab, x, y, accent[shown]);
                text(s + lab, n - lab, x + lab * CW, y, color);
            }
            s += n;
            row++;
            first = 0;
        } while (*s);
    }
    return row;
}

static void draw(void)
{
    int r, rows = input_rows(), top = 15 + rows * RH + 6, vis = (BAR - 2 - top) / RH, total, i;

    gfx_FillScreen(C_BASE);
    gfx_SetColor(C_MANTLE);
    gfx_FillRectangle(0, 0, 320, 12);
    text("taproot", 7, X0, 2, C_LAV);
    if (msg) text(msg, 28, X0 + 9 * CW, 2, C_YELLOW);
    if (mode) {
        const char *tag = mode == M_2ND ? "2nd" : mode == M_ALPHA ? "a" : "A-lock";
        int w = strlen(tag) * CW + 6;
        gfx_SetColor(mode == M_2ND ? C_BLUE : C_GREEN);
        gfx_FillRectangle(320 - w - 3, 1, w, 10);
        text(tag, 6, 320 - w, 2, C_CRUST);
    }

    text(">", 1, X0, 16, C_OVER);
    for (r = 0; r < rows; r++) text(in + r * PER, PER, X0 + CW, 16 + r * RH, C_TEXT);
    {
        int x = X0 + CW + cur % PER * CW, y = 15 + cur / PER * RH;
        char g = mode == M_2ND ? '\x05' : mode == M_ALPHA ? 'a' : mode == M_LOCK ? 'A' : in[cur];
        gfx_SetColor(mode == M_2ND ? C_BLUE : mode ? C_GREEN : C_YELLOW);
        gfx_FillRectangle(x, y, CW, RH);
        if (g) text(&g, 1, x, y + 1, C_CRUST);
    }
    gfx_SetColor(C_SURF);
    gfx_HorizLine(X0, top - 4, 320 - 2 * X0);

    if (shown < 0) {
        text("type a polynomial, then press a", 99, X0, top, C_OVER);
        text("command key below the screen", 99, X0, top + RH, C_OVER);
    } else {
        total = layout(top, vis, 0);
        if (scroll > total - vis) scroll = total - vis;
        if (scroll < 0) scroll = 0;
        layout(top, vis, 1);
        if (total > vis) {
            int track = BAR - 4 - top, h = track * vis / total;
            gfx_SetColor(C_SURF);
            gfx_FillRectangle(317, top, 2, track);
            gfx_SetColor(C_OVER);
            gfx_FillRectangle(317, top + (track - h) * scroll / (total - vis), 2, h);
        }
    }

    gfx_SetColor(C_CRUST);
    gfx_FillRectangle(0, BAR, 320, 240 - BAR);
    for (i = 0; i < 5; i++) {
        int k = i == 4 ? KEYS : mode == M_2ND ? i + 4 : i, n = strlen(label[k]);
        if (i) {
            gfx_SetColor(C_SURF);
            gfx_VertLine(i * 64, BAR + 3, 9);
        }
        if (k == shown) {
            gfx_SetColor(accent[k]);
            gfx_FillRectangle(i * 64 + 8, BAR, 48, 2);
        }
        text(label[k], n, i * 64 + 32 - n * CW / 2, BAR + 4, accent[k]);
    }
    gfx_SwapDraw();
}

static void show(int cmd)
{
    shown = cmd;
    scroll = 0;
    strcpy(head, label[cmd]);
    strcat(head, "  ");
    strcat(head, cmd == KEYS ? "" : in);
}

static int isrel(char c)
{
    return c == '=' || c == '<' || c == '>' || c == G_LE[0] || c == G_GE[0];
}

/* = or an inequality before the first top-level comma; the ones after it are values like x=3 */
static int equation(void)
{
    int i, depth = 0;
    for (i = 0; in[i]; i++) {
        if (in[i] == '(') depth++;
        else if (in[i] == ')') depth--;
        else if (in[i] == ',' && depth <= 0) return 0;
        else if (isrel(in[i])) return 1;
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
        for (i = 3; i > 0; i--) strcpy(hist[i], hist[i - 1]);
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
    if (cur && (p = strchr(cycle, in[cur - 1])) && *p) {
        in[cur - 1] = p[1];
        return;
    }
    insert("=");
}

int main(void)
{
    char ch[2] = { 0, 0 };
    int i, page;
    uint8_t k;

    gfx_Begin();
    gfx_SetDrawBuffer();
    for (i = 0; i < (int)(sizeof rgb / sizeof *rgb); i++) gfx_palette[i] = gfx_RGBTo1555(rgb[i][0], rgb[i][1], rgb[i][2]);
    gfx_SetFontData(font[0]);
    gfx_SetMonospaceFont(CW);
    gfx_SetTextTransparentColor(C_NONE);
    gfx_SetTextBGColor(C_NONE);
    cas_stop = stop;

    for (;;) {
        draw();
        k = pending;
        pending = 0;
        while (!k) k = os_GetCSC();
        msg = 0;
        page = (BAR - 2 - (15 + input_rows() * RH + 6)) / RH;

        if (k == sk_2nd) {
            mode = mode == M_2ND ? M_NONE : M_2ND;
            continue;
        }
        if (k == sk_Alpha) {
            mode = mode == M_2ND ? M_LOCK : mode ? M_NONE : M_ALPHA;
            continue;
        }
        if (mode == M_ALPHA || mode == M_LOCK) {
            if (mode == M_ALPHA) mode = M_NONE;
            if (k < sizeof alpha && alpha[k]) {
                ch[0] = alpha[k];
                insert(ch);
                continue;
            }
        }
        if (mode == M_2ND) {
            mode = M_NONE;
            if (k == sk_Mode) break;
            if (k == sk_Math) {
                relation();
                continue;
            }
            if (k == sk_DecPnt) {
                insert("i");
                continue;
            }
            if (k == sk_Yequ || k == sk_Window || k == sk_Zoom || k == sk_Trace) {
                run(k == sk_Yequ ? CMD_VERTEX : k == sk_Window ? CMD_ZEROS : k == sk_Zoom ? CMD_SYSTEM : CMD_INVERSE);
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
            else if (k == sk_Up) scroll -= page;
            else if (k == sk_Down) scroll += page;
            else if (k != sk_Graph) msg = "2nd + key not used";
            if (k != sk_Graph) continue;
        }
        switch (k) {
        case sk_Yequ: run(CMD_EXPAND); break;
        case sk_Window: run(CMD_FACTOR); break;
        case sk_Zoom: run(CMD_SOLVE); break;
        case sk_Trace: run(CMD_DERIV); break;
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
