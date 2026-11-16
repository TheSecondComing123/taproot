#include <graphx.h>
#include <ti/getcsc.h>
#include <string.h>
#include "cas.h"

#define X0 4
#define RH 10
#define COLS 38
#define PER (COLS - 1)
#define MAXIN 110
#define BAR 226

enum { C_BASE, C_MANTLE, C_CRUST, C_SURF, C_OVER, C_TEXT, C_SUB, C_BLUE, C_PEACH, C_GREEN, C_MAUVE, C_TEAL, C_RED, C_YELLOW, C_LAV, C_NONE = 255 };
enum { M_NONE, M_2ND, M_ALPHA, M_LOCK };

static const uint8_t rgb[][3] = {
    { 0x1e, 0x1e, 0x2e }, { 0x18, 0x18, 0x25 }, { 0x11, 0x11, 0x1b }, { 0x31, 0x32, 0x44 }, { 0x6c, 0x70, 0x86 },
    { 0xcd, 0xd6, 0xf4 }, { 0xa6, 0xad, 0xc8 }, { 0x89, 0xb4, 0xfa }, { 0xfa, 0xb3, 0x87 }, { 0xa6, 0xe3, 0xa1 },
    { 0xcb, 0xa6, 0xf7 }, { 0x94, 0xe2, 0xd5 }, { 0xf3, 0x8b, 0xa8 }, { 0xf9, 0xe2, 0xaf }, { 0xb4, 0xbe, 0xfe },
};

static const uint8_t glyphs[][8] = {
    { 0x07, 0x04, 0x04, 0x08, 0x48, 0x28, 0x10, 0x00 },
    { 0x10, 0x10, 0x7c, 0x10, 0x10, 0x00, 0x7c, 0x00 },
    { 0x00, 0x32, 0x4c, 0x00, 0x32, 0x4c, 0x00, 0x00 },
    { 0x00, 0x00, 0x00, 0x18, 0x18, 0x00, 0x00, 0x00 },
    { 0x10, 0x38, 0x54, 0x10, 0x10, 0x10, 0x00, 0x00 },
    { 0x10, 0x10, 0x10, 0x54, 0x38, 0x10, 0x00, 0x00 },
    { 0x38, 0x44, 0x44, 0x7c, 0x44, 0x44, 0x38, 0x00 },
    { 0x30, 0x48, 0x10, 0x20, 0x78, 0x00, 0x00, 0x00 },
};

static const char *const label[] = { "expand", "factor", "solve", "d/dx", "keys" };
static const uint8_t accent[] = { C_BLUE, C_PEACH, C_GREEN, C_MAUVE, C_TEAL };
#define KEYS 4

static const char *help[] = {
    "X,T,\x07,n   types x",
    "alpha     next key types a letter",
    "2nd alpha letters until alpha",
    "x\x08        types ^2",
    "sto       types =",
    ",         values: x^2+1, x=3",
    "enter     solve if =, else last",
    "del       backspace",
    "clear     line, then output",
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

static char in[MAXIN + 1];
static int cur, mode, last, shown = -1, scroll;
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

/* walks every wrapped output row; draws the visible ones, returns the total */
static int layout(int top, int vis, int draw)
{
    int i, row = 0;
    for (i = -1; i < nout; i++) {
        const char *s = i < 0 ? head : lines[i];
        int k = i < 0 ? -1 : kinds[i];
        uint8_t color = k < 0 ? C_SUB : k == L_RESULT ? accent[shown] : k == L_APPROX ? C_SUB : k == L_ERROR ? C_RED : C_TEXT;
        int first = 1;
        do {
            int ind = first ? 0 : 2, n = cut(s, COLS - ind);
            if (draw && row >= scroll && row < scroll + vis) {
                int x = X0 + ind * 8, y = top + (row - scroll) * RH;
                int lab = k < 0 && first ? (int)strlen(label[shown]) : 0;
                text(s, lab, x, y, accent[shown]);
                text(s + lab, n - lab, x + lab * 8, y, color);
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
    if (msg) text(msg, 28, X0 + 9 * 8, 2, C_YELLOW);
    if (mode) {
        const char *tag = mode == M_2ND ? "2nd" : mode == M_ALPHA ? "a" : "A-lock";
        int w = strlen(tag) * 8 + 6;
        gfx_SetColor(mode == M_2ND ? C_BLUE : C_GREEN);
        gfx_FillRectangle(320 - w - 3, 1, w, 10);
        text(tag, 6, 320 - w, 2, C_CRUST);
    }

    text(">", 1, X0, 16, C_OVER);
    for (r = 0; r < rows; r++) text(in + r * PER, PER, X0 + 8, 16 + r * RH, C_TEXT);
    {
        int x = X0 + 8 + cur % PER * 8, y = 15 + cur / PER * RH;
        char g = mode == M_2ND ? '\x05' : mode == M_ALPHA ? 'a' : mode == M_LOCK ? 'A' : in[cur];
        gfx_SetColor(mode == M_2ND ? C_BLUE : mode ? C_GREEN : C_YELLOW);
        gfx_FillRectangle(x, y, 8, RH);
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
        int n = strlen(label[i]);
        if (i) {
            gfx_SetColor(C_SURF);
            gfx_VertLine(i * 64, BAR + 3, 9);
        }
        if (i == shown) {
            gfx_SetColor(accent[i]);
            gfx_FillRectangle(i * 64 + 8, BAR, 48, 2);
        }
        text(label[i], n, i * 64 + 32 - n * 4, BAR + 4, accent[i]);
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

static void run(int cmd)
{
    if (!*in) {
        msg = "type something first";
        return;
    }
    last = cmd;
    msg = "working...";
    draw();
    msg = 0;
    cas_run(cmd, in);
    lines = cas_line;
    kinds = cas_kind;
    nout = cas_nlines;
    show(cmd);
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

int main(void)
{
    char ch[2] = { 0, 0 };
    int i, page;
    uint8_t k;

    gfx_Begin();
    gfx_SetDrawBuffer();
    for (i = 0; i < (int)(sizeof rgb / sizeof *rgb); i++) gfx_palette[i] = gfx_RGBTo1555(rgb[i][0], rgb[i][1], rgb[i][2]);
    for (i = 0; i < (int)(sizeof glyphs / sizeof *glyphs); i++) gfx_SetCharData(i + 1, glyphs[i]);
    gfx_SetMonospaceFont(8);
    gfx_SetTextTransparentColor(C_NONE);
    gfx_SetTextBGColor(C_NONE);

    for (;;) {
        draw();
        while (!(k = os_GetCSC()));
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
                insert("=");
                continue;
            }
            if (k == sk_Left) cur = 0;
            else if (k == sk_Right) cur = strlen(in);
            else if (k == sk_Up) scroll -= page;
            else if (k == sk_Down) scroll += page;
            if (k == sk_Left || k == sk_Right || k == sk_Up || k == sk_Down) continue;
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
        case sk_Enter: run(strchr(in, '=') ? CMD_SOLVE : last); break;
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
                msg = "that key isn't used here";
            }
        }
    }
    gfx_End();
    return 0;
}
