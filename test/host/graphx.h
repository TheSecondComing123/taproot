#ifndef GRAPHX_H
#define GRAPHX_H

#include <stdint.h>

extern uint16_t sim_palette[256];
extern uint8_t sim_vbuf[240][320];
#define gfx_palette sim_palette
#define gfx_vbuffer sim_vbuf
#define gfx_RGBTo1555(r, g, b) ((uint16_t)(((r) >> 3) << 10 | ((g) >> 3) << 5 | ((b) >> 3)))
#define gfx_SetDrawBuffer()

void gfx_Begin(void);
void gfx_End(void);
void gfx_SwapDraw(void);
void gfx_FillScreen(uint8_t index);
uint8_t gfx_SetColor(uint8_t index);
void gfx_FillRectangle(int x, int y, int w, int h);
void gfx_HorizLine(int x, int y, int len);

#endif
