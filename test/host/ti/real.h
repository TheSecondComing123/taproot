/* the os real-number routines taproot uses, emulated on the mac: same 14-digit bcd layout, and an
   "os error" (overflow past 1e99, divide by 0, sqrt of a negative) longjmps like the calc's handler */
#ifndef TI_REAL_H
#define TI_REAL_H

#include <stdint.h>

typedef struct real_t { int8_t sign, exp; uint8_t mant[7]; } real_t;

real_t os_RealAdd(const real_t *a, const real_t *b);
real_t os_RealSub(const real_t *a, const real_t *b);
real_t os_RealMul(const real_t *a, const real_t *b);
real_t os_RealDiv(const real_t *a, const real_t *b);
real_t os_RealSqrt(const real_t *a);
real_t os_RealRound(const real_t *a, char digits);
int os_RealCompare(const real_t *a, const real_t *b);

#endif
