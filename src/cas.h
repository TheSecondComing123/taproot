#ifndef CAS_H
#define CAS_H

#include <stdint.h>

enum { CMD_EXPAND, CMD_FACTOR, CMD_SOLVE, CMD_DERIV };
enum { L_STEP, L_RESULT, L_APPROX, L_ERROR };

/* glyph codes, drawn with gfx_SetCharData on the calc */
#define G_SQRT "\x01"
#define G_PM "\x02"
#define G_APPROX "\x03"
#define G_DOT "\x04"

#define CAS_MAXLINES 80

extern const char *cas_line[CAS_MAXLINES];
extern uint8_t cas_kind[CAS_MAXLINES];
extern int cas_nlines;

void cas_run(int cmd, const char *input);

#endif
