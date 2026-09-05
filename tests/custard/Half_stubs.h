/* The target side of Half.fst.  nvcc's <cuda_fp16.h> and <cuda_bf16.h>
   declare __half, __nv_bfloat16 and these functions for real; this file
   declares them in a way a plain C compiler accepts, so that the test can
   run here.  Nothing in Half.fst depends on which of the two it is.

   Everything is static inline so that the test needs no second translation
   unit: the point is the F* side. */

#ifndef __HALF_STUBS_H
#define __HALF_STUBS_H

#include <stdbool.h>
#include <stdint.h>

/* A stand-in with the storage of the real thing (16 bits) and the arithmetic
   of a float.  Rounding to binary16 is what a real __half does and what this
   deliberately does not: the test is about the F* side reaching the C names,
   not about the numerics of a stub. */
typedef struct { uint16_t bits; } __half;
typedef struct { uint16_t bits; } __nv_bfloat16;

static inline __half __float2half(float x) {
  /* Only exact small values are used here, so a scaled integer is enough. */
  __half h; h.bits = (uint16_t)(int)(x * 256.0f); return h;
}
static inline float __half2float(__half h) { return (float)h.bits / 256.0f; }
static inline __half __hadd(__half a, __half b) {
  __half h; h.bits = (uint16_t)(a.bits + b.bits); return h;
}
static inline __half __hmul(__half a, __half b) {
  __half h; h.bits = (uint16_t)((uint32_t)a.bits * b.bits / 256u); return h;
}
static inline bool __hlt(__half a, __half b) { return a.bits < b.bits; }

static inline __nv_bfloat16 __float2bfloat16(float x) {
  __nv_bfloat16 h; h.bits = (uint16_t)(int)(x * 256.0f); return h;
}
static inline float __bfloat162float(__nv_bfloat16 h) {
  return (float)h.bits / 256.0f;
}
static inline __nv_bfloat16 __hadd_bf(__nv_bfloat16 a, __nv_bfloat16 b) {
  __nv_bfloat16 h; h.bits = (uint16_t)(a.bits + b.bits); return h;
}

#endif
