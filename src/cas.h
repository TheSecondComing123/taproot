#ifndef CAS_H
#define CAS_H

#include <stdint.h>

enum { CMD_EXPAND, CMD_FACTOR, CMD_SOLVE, CMD_DERIV, CMD_VERTEX, CMD_ZEROS, CMD_SYSTEM, CMD_INVERSE };
enum { L_STEP, L_RESULT, L_APPROX, L_ERROR };

/* glyph codes, drawn with gfx_SetCharData on the calc. 9-16 are skipped: tab, newline and
   the bytes python's splitlines treats as line breaks */
#define G_SQRT "\x01"
#define G_PM "\x02"
#define G_APPROX "\x03"
#define G_DOT "\x04"
#define G_NE "\x11"
#define G_LE "\x12"
#define G_GE "\x13"
#define G_INF "\x14"
#define G_CUP "\x15"
#define G_TO "\x16"

#define CAS_MAXLINES 120

extern const char *cas_line[CAS_MAXLINES];
extern uint8_t cas_kind[CAS_MAXLINES];
extern int cas_nlines;

/* polled during long loops; returning nonzero stops the run with an error */
extern int (*cas_stop)(void);

void cas_run(int cmd, const char *input);

#endif
