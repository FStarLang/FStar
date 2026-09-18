#ifndef NARROW_OVERRIDE_STUBS_H
#define NARROW_OVERRIDE_STUBS_H 1

/* Section 66.  A consumer's override of the narrow-float support block.

   This is the arrangement the override exists for: the replacement type and
   operations live in a header named by [@@custard_c_header] on an F*
   declaration, so the only way they can reach the generated header is if the
   [custard_c_header] includes are emitted *above* the block.  Emitted below
   it, this file redefines custard_f16 and the translation unit does not
   compile -- which is what makes this a test and not just an example.

   The stand-in for CUDA's __half is a struct with a different member name,
   so nothing here can accidentally agree with the block it replaces.  The
   test is compiled as both C and C++, so the two literal spellings are
   switched on __cplusplus exactly as the block does. */

#include <stdint.h>
#include <string.h>
#ifndef __cplusplus
#include <stdbool.h>
#endif

#define CUSTARD_FLOAT16_DEFINED

typedef struct { uint16_t ovr; } custard_f16;
typedef struct { uint16_t ovr; } custard_bf16;

#ifdef __cplusplus
#define CUSTARD_F16_LIT(b)  (custard_f16{ (uint16_t)(b) })
#define CUSTARD_BF16_LIT(b) (custard_bf16{ (uint16_t)(b) })
#else
#define CUSTARD_F16_LIT(b)  ((custard_f16){ (uint16_t)(b) })
#define CUSTARD_BF16_LIT(b) ((custard_bf16){ (uint16_t)(b) })
#endif
#define CUSTARD_F16_INIT(b)  { (uint16_t)(b) }
#define CUSTARD_BF16_INIT(b) { (uint16_t)(b) }

/* Only what this test uses.  A real override supplies the whole vocabulary;
   the point here is which header wins, not the arithmetic. */
static inline float custard_f16_to_f32(custard_f16 h) {
  uint32_t s = (uint32_t)(h.ovr >> 15) & 1u;
  uint32_t e = (uint32_t)(h.ovr >> 10) & 0x1Fu;
  uint32_t m = (uint32_t)h.ovr & 0x3FFu;
  uint32_t out; float f;
  if (e == 0u) { out = s << 31; if (m != 0u) { out = 0u; } }
  else { out = (s << 31) | ((e + 112u) << 23) | (m << 13); }
  memcpy(&f, &out, sizeof f);
  return f;
}

static inline custard_f16 custard_f16_of_f32(float f) {
  uint32_t u; custard_f16 r;
  memcpy(&u, &f, sizeof u);
  r.ovr = (uint16_t)(((u >> 16) & 0x8000u) |
                     ((((u >> 23) & 0xFFu) - 112u) << 10) |
                     ((u >> 13) & 0x3FFu));
  return r;
}

static inline custard_f16 custard_f16_of_i64(int64_t x) {
  return custard_f16_of_f32((float)x);
}

static inline custard_f16 custard_f16_add(custard_f16 a, custard_f16 b) {
  return custard_f16_of_f32(custard_f16_to_f32(a) + custard_f16_to_f32(b));
}

static inline bool custard_f16_eq(custard_f16 a, custard_f16 b) {
  return custard_f16_to_f32(a) == custard_f16_to_f32(b);
}

/* The declaration that carries the [@@custard_c_header] naming this file.
   It reads the override's own member, so the test would not link if some
   other custard_f16 were the one in scope. */
static inline uint16_t narrow_override_bits(custard_f16 v) { return v.ovr; }

#endif
