#ifndef GRAPHX_H
#define GRAPHX_H

#include <stdint.h>

extern uint16_t sim_palette[256];
#define gfx_palette sim_palette
#define gfx_RGBTo1555(r, g, b) ((uint16_t)(((r) >> 3) << 10 | ((g) >> 3) << 5 | ((b) >> 3)))
#define gfx_SetDrawBuffer()

void gfx_Begin(void);
void gfx_End(void);
void gfx_SwapDraw(void);
uint8_t *gfx_SetCharData(uint8_t index, const uint8_t *data);
void gfx_SetMonospaceFont(uint8_t spacing);
uint8_t gfx_SetTextTransparentColor(uint8_t color);
uint8_t gfx_SetTextBGColor(uint8_t color);
uint8_t gfx_SetTextFGColor(uint8_t color);
void gfx_SetTextXY(int x, int y);
void gfx_PrintChar(const char c);
void gfx_FillScreen(uint8_t index);
uint8_t gfx_SetColor(uint8_t index);
void gfx_FillRectangle(int x, int y, int w, int h);
void gfx_HorizLine(int x, int y, int len);
void gfx_VertLine(int x, int y, int len);

#endif
