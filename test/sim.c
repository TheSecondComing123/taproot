/* runs src/main.c on the mac: fake graphx draws into a framebuffer, fake keypad replays a script */
#include <graphx.h>
#include <ti/getcsc.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../src/cas.h"

uint16_t sim_palette[256];
uint8_t sim_vbuf[240][320];
static uint8_t shown[240][320], color;
static int frame, busy;
static char **keys;
static int nkeys, at;
static const char *outdir;

void gfx_Begin(void) {}
void gfx_End(void) {}
uint8_t gfx_SetColor(uint8_t c) { uint8_t old = color; color = c; return old; }
void gfx_FillScreen(uint8_t c) { memset(sim_vbuf, c, sizeof sim_vbuf); }
void gfx_SwapDraw(void) { memcpy(shown, sim_vbuf, sizeof shown); }

void gfx_FillRectangle(int x, int y, int w, int h)
{
    int i, j;
    if (x < 0 || y < 0 || x + w > 320 || y + h > 240) fprintf(stderr, "rectangle off screen at %d,%d\n", x, y);
    for (j = y; j < y + h; j++)
        for (i = x; i < x + w; i++)
            if (i >= 0 && i < 320 && j >= 0 && j < 240) sim_vbuf[j][i] = color;
}

void gfx_HorizLine(int x, int y, int len) { gfx_FillRectangle(x, y, len, 1); }

/* cas.c is built with cas_run renamed, so the keypad knows when math is running */
void sim_cas_run(int cmd, const char *input);
void cas_run(int cmd, const char *input)
{
    busy = 1;
    sim_cas_run(cmd, input);
    busy = 0;
}

static void snap(void)
{
    char path[512];
    FILE *f;
    int x, y;
    snprintf(path, sizeof path, "%s/frame%02d.ppm", outdir, frame);
    f = fopen(path, "wb");
    fprintf(f, "P6\n320 240\n255\n");
    for (y = 0; y < 240; y++)
        for (x = 0; x < 320; x++) {
            uint16_t c = sim_palette[shown[y][x]];
            fputc((c >> 10 & 31) << 3, f);
            fputc((c >> 5 & 31) << 3, f);
            fputc((c & 31) << 3, f);
        }
    fclose(f);
    printf("--- frame %02d (after key %d)\n", frame++, at);
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

uint8_t os_GetCSC(void)
{
    if (busy) {
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
