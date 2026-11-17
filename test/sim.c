/* runs src/main.c on the mac: fake graphx records draw calls, fake keypad replays a script */
#include <graphx.h>
#include <ti/getcsc.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef CW
#define CW 8
#endif

uint16_t sim_palette[256];

#define MAXOPS 20000
static struct { char kind; int x, y, w, h, c; } ops[MAXOPS], shown[MAXOPS];
static int nops, nshown, fg, color, tx, ty, frame;
static char **keys;
static int nkeys, at;
static const char *outdir;

static void op(char kind, int x, int y, int w, int h, int c)
{
    if (nops == MAXOPS) {
        fprintf(stderr, "too many draw ops\n");
        exit(2);
    }
    ops[nops].kind = kind;
    ops[nops].x = x;
    ops[nops].y = y;
    ops[nops].w = w;
    ops[nops].h = h;
    ops[nops].c = c;
    nops++;
}

void gfx_Begin(void) {}
void gfx_End(void) {}
uint8_t *gfx_SetCharData(uint8_t index, const uint8_t *data) { (void)index; (void)data; return 0; }
static int mono = 8;
void gfx_SetMonospaceFont(uint8_t spacing) { mono = spacing; }
uint8_t gfx_SetTextTransparentColor(uint8_t c) { return c; }
uint8_t gfx_SetTextBGColor(uint8_t c) { return c; }
uint8_t gfx_SetTextFGColor(uint8_t c) { fg = c; return c; }
void gfx_SetTextXY(int x, int y) { tx = x; ty = y; }
uint8_t gfx_SetColor(uint8_t c) { color = c; return c; }
void gfx_FillScreen(uint8_t c) { nops = 0; op('R', 0, 0, 320, 240, c); }
void gfx_FillRectangle(int x, int y, int w, int h) { op('R', x, y, w, h, color); }
void gfx_HorizLine(int x, int y, int len) { op('R', x, y, len, 1, color); }
void gfx_VertLine(int x, int y, int len) { op('R', x, y, 1, len, color); }

void gfx_PrintChar(const char ch)
{
    if (tx < 0 || tx + mono > 320 || ty < 0 || ty + 8 > 240) fprintf(stderr, "char '%c' off screen at %d,%d\n", ch, tx, ty);
    op('C', tx, ty, mono, 8, (unsigned char)ch);
    ops[nops - 1].h = fg;
    tx += mono;
}

void gfx_SwapDraw(void)
{
    memcpy(shown, ops, nops * sizeof *ops);
    nshown = nops;
}

/* text dump: one line per text row, chars placed by x */
static void dump(FILE *f)
{
    int ys[64], ny = 0, i, j;
    for (i = 0; i < nshown; i++) {
        if (shown[i].kind != 'C') continue;
        for (j = 0; j < ny && ys[j] != shown[i].y; j++);
        if (j == ny && ny < 64) ys[ny++] = shown[i].y;
    }
    for (i = 1; i < ny; i++)
        for (j = i; j > 0 && ys[j - 1] > ys[j]; j--) {
            int t = ys[j];
            ys[j] = ys[j - 1];
            ys[j - 1] = t;
        }
    static const char *glyph[] = { "?", "√", "±", "≈", "·", "↑", "↓", "θ", "²", "?", "?", "?", "?", "?", "?", "?", "?", "≠", "≤", "≥", "∞", "∪", "→" };
    for (j = 0; j < ny; j++) {
        int row[40], last = -1;
        for (i = 0; i < 40; i++) row[i] = ' ';
        for (i = 0; i < nshown; i++) {
            int c = shown[i].x / 8;
            if (shown[i].kind != 'C' || shown[i].y != ys[j] || c < 0 || c > 39) continue;
            row[c] = shown[i].c;
            if (c > last) last = c;
        }
        fprintf(f, "%3d|", ys[j]);
        for (i = 0; i <= last; i++) {
            if (row[i] > 0 && row[i] < 23) fputs(glyph[row[i]], f);
            else fputc(row[i], f);
        }
        fputc('\n', f);
    }
}

static void snap(void)
{
    char path[512];
    FILE *f;
    int i;
    snprintf(path, sizeof path, "%s/frame%02d.ops", outdir, frame);
    f = fopen(path, "w");
    for (i = 0; i < 32; i++) fprintf(f, "P %d %d\n", i, sim_palette[i]);
    for (i = 0; i < nshown; i++)
        fprintf(f, "%c %d %d %d %d %d\n", shown[i].kind, shown[i].x, shown[i].y, shown[i].w, shown[i].h, shown[i].c);
    fclose(f);
    printf("--- frame %02d (after key %d)\n", frame++, at);
    dump(stdout);
}

static const struct { const char *name; uint8_t code; } names[] = {
    { "0", sk_0 }, { "1", sk_1 }, { "2", sk_2 }, { "3", sk_3 }, { "4", sk_4 }, { "5", sk_5 }, { "6", sk_6 },
    { "7", sk_7 }, { "8", sk_8 }, { "9", sk_9 }, { "dot", sk_DecPnt }, { "add", sk_Add }, { "sub", sk_Sub },
    { "mul", sk_Mul }, { "div", sk_Div }, { "pow", sk_Power }, { "lp", sk_LParen }, { "rp", sk_RParen },
    { "neg", sk_Chs }, { "xt", sk_GraphVar }, { "sq", sk_Square }, { "sto", sk_Store }, { "comma", sk_Comma },
    { "enter", sk_Enter }, { "del", sk_Del }, { "clear", sk_Clear }, { "left", sk_Left }, { "right", sk_Right },
    { "up", sk_Up }, { "down", sk_Down }, { "2nd", sk_2nd }, { "alpha", sk_Alpha }, { "mode", sk_Mode },
    { "math", sk_Math }, { "apps", sk_Apps }, { "prgm", sk_Prgm }, { "inv", sk_Recip }, { "sin", sk_Sin },
    { "cos", sk_Cos }, { "tan", sk_Tan }, { "log", sk_Log }, { "ln", sk_Ln }, { "vars", sk_Vars }, { "stat", sk_Stat },
    { "f1", sk_Yequ }, { "f2", sk_Window }, { "f3", sk_Zoom }, { "f4", sk_Trace }, { "f5", sk_Graph },
};

static const char *letter_key = "math apps prgm inv sin cos tan pow sq comma lp rp div log 7 8 9 mul ln 4 5 6 sub sto 1 2";

static uint8_t code(const char *name)
{
    unsigned i;
    for (i = 0; i < sizeof names / sizeof *names; i++)
        if (!strcmp(names[i].name, name)) return names[i].code;
    fprintf(stderr, "unknown key %s\n", name);
    exit(2);
}

static uint8_t queue[512];
static int qn, qi;

static void push(const char *name)
{
    queue[qn++] = code(name);
}

static void type(const char *s)
{
    for (; *s; s++) {
        const char *sym = 0;
        char one[2] = { *s, 0 };
        switch (*s) {
        case '.': sym = "dot"; break;
        case '+': sym = "add"; break;
        case '-': sym = "sub"; break;
        case '*': sym = "mul"; break;
        case '/': sym = "div"; break;
        case '^': sym = "pow"; break;
        case '(': sym = "lp"; break;
        case ')': sym = "rp"; break;
        case ',': sym = "comma"; break;
        case '=': sym = "sto"; break;
        case '<': push("2nd"); push("math"); push("2nd"); sym = "math"; break;
        case '>': push("2nd"); push("math"); push("2nd"); push("math"); push("2nd"); sym = "math"; break;
        case '{': push("2nd"); push("math"); push("2nd"); push("math"); push("2nd"); push("math"); push("2nd"); sym = "math"; break;
        case '}': push("2nd"); push("math"); push("2nd"); push("math"); push("2nd"); push("math"); push("2nd"); push("math"); push("2nd"); sym = "math"; break;
        case 'i': push("2nd"); sym = "dot"; break;
        case 'x': sym = "xt"; break;
        }
        if (*s >= '0' && *s <= '9') sym = one;
        if (!sym && *s >= 'a' && *s <= 'z') {
            char buf[16];
            const char *p = letter_key;
            int n = *s - 'a';
            while (n--) p = strchr(p, ' ') + 1;
            sscanf(p, "%15s", buf);
            push("alpha");
            push(buf);
            continue;
        }
        if (sym) push(sym);
    }
}

/* main.c polls for clear while math runs; the frame shown then says "working" */
static int busy(void)
{
    int i;
    for (i = 0; i < nshown; i++)
        if (shown[i].kind == 'C' && shown[i].y == 2 && shown[i].x == 4 + 9 * CW) return shown[i].c == 'w';
    return 0;
}

uint8_t os_GetCSC(void)
{
    if (busy()) {
        if (at < nkeys && !strcmp(keys[at], "stop")) {
            at++;
            return sk_Clear;
        }
        return 0;
    }
    if (qi < qn) return queue[qi++];
    qi = qn = 0;
    while (at < nkeys) {
        char *k = keys[at++];
        if (!strcmp(k, "snap")) {
            snap();
            continue;
        }
        if (!strncmp(k, "type:", 5)) type(k + 5);
        else push(k);
        return queue[qi++];
    }
    snap();
    exit(0);
}

int sim_main(void);

int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "usage: sim outdir key...\n");
        return 2;
    }
    outdir = argv[1];
    keys = argv + 2;
    nkeys = argc - 2;
    return sim_main();
}
