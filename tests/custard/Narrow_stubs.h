#ifndef NARROW_STUBS_H
#define NARROW_STUBS_H 1

/* Section 98.  A portable reference implementation of the two 16-bit
   floating-point formats, for the test suite.

   This is *not* part of Custard.  Custard emits calls into this vocabulary
   and leaves the vocabulary to the program -- see the comment the generated
   header carries, which lists it.  The suite needs one in order to compile
   and run a narrow-float program at all, and one that is portable rather
   than CUDA-specific is the only kind a test machine can execute, so the
   implementation that Custard used to emit lives here instead.

   It is also a serviceable starting point for a consumer that has no native
   16-bit type: the arithmetic converts to float, operates, and rounds back,
   which is *defined* everywhere and rounds exactly once -- binary32 holds
   every binary16 and every bfloat16 exactly, and has enough precision (24
   bits, against 2*11+2 and 2*8+2) that the intermediate is exact for add,
   sub, mul and div.  A consumer whose target has the formats in hardware
   should use those instead; that is the case Custard is built for.

   Literals do not appear here: Custard emits their bit patterns directly, so
   that a static initializer stays a constant expression. */

#include <stdint.h>
#include <string.h>
#ifndef __cplusplus
#include <stdbool.h>
#endif

#define CUSTARD_FLOAT16_DEFINED
typedef struct { uint16_t bits; } custard_f16;
typedef struct { uint16_t bits; } custard_bf16;

/* Linkage.  Under nvcc these have to be callable from a __global__ or
   __device__ function as well as from the host: a plain [static inline]
   is a __host__ function, and calling one from device code is an error,
   not a warning.  A kernel doing 16-bit arithmetic is the main reason
   this width exists, so that case is the normal one and not a corner. */
#if defined(__CUDACC__)
#define CUSTARD_FN static __host__ __device__ inline
#else
#define CUSTARD_FN static inline
#endif

/* A literal.  Custard emits the bit pattern, so this must stay a
   constant expression: it is what initializes an object with static
   storage duration.  Two spellings because a compound literal is C and
   a GNU extension in C++, while the braced form is C++ and not C --
   generated CUDA is compiled as C++, so getting only one of them right
   would cost -pedantic on one of the two targets. */
#ifdef __cplusplus
#define CUSTARD_F16_LIT(b)  (custard_f16{ (uint16_t)(b) })
#define CUSTARD_BF16_LIT(b) (custard_bf16{ (uint16_t)(b) })
#else
#define CUSTARD_F16_LIT(b)  ((custard_f16){ (uint16_t)(b) })
#define CUSTARD_BF16_LIT(b) ((custard_bf16){ (uint16_t)(b) })
#endif

/* And in *initializer* position, where the above will not do: a compound
   literal has automatic storage duration inside a function and is not a
   constant expression, so it cannot initialize an object with static
   storage duration.  A braced initializer can, and is spelled the same
   in C and C++ -- but it is only an initializer, never an expression,
   which is why there are two macros and not one. */
#define CUSTARD_F16_INIT(b)  { (uint16_t)(b) }
#define CUSTARD_BF16_INIT(b) { (uint16_t)(b) }

CUSTARD_FN float custard__f32_of_bits(uint32_t u) {
  float f; memcpy(&f, &u, sizeof f); return f;
}
CUSTARD_FN uint32_t custard__bits_of_f32(float f) {
  uint32_t u; memcpy(&u, &f, sizeof u); return u;
}

/* binary16 -> binary32.  Exact. */
CUSTARD_FN float custard_f16_to_f32(custard_f16 h) {
  uint32_t s = (uint32_t)(h.bits >> 15) & 1u;
  uint32_t e = (uint32_t)(h.bits >> 10) & 0x1Fu;
  uint32_t m = (uint32_t)h.bits & 0x3FFu;
  uint32_t out;
  if (e == 0u) {
    if (m == 0u) { out = s << 31; }
    else {
      /* Subnormal: normalize, one exponent step per shift from -14. */
      int k = 0;
      while ((m & 0x400u) == 0u) { m <<= 1; k++; }
      m &= 0x3FFu;
      out = (s << 31) | ((uint32_t)(113 - k) << 23) | (m << 13);
    }
  } else if (e == 0x1Fu) {
    out = (s << 31) | 0x7F800000u | (m << 13);
  } else {
    out = (s << 31) | ((e + 112u) << 23) | (m << 13);
  }
  return custard__f32_of_bits(out);
}

/* binary32 -> binary16, round-to-nearest-even. */
CUSTARD_FN custard_f16 custard_f16_of_f32(float f) {
  uint32_t u = custard__bits_of_f32(f);
  uint32_t s = (u >> 31) & 1u;
  int32_t  e = (int32_t)((u >> 23) & 0xFFu);
  uint32_t m = u & 0x7FFFFFu;
  custard_f16 h;
  if (e == 0xFF) {                       /* inf, or a NaN that stays one */
    h.bits = (uint16_t)((s << 15) | 0x7C00u | (m ? (0x0200u | (m >> 13)) : 0u));
    return h;
  }
  if ((u & 0x7FFFFFFFu) == 0u) { h.bits = (uint16_t)(s << 15); return h; }
  {
    uint32_t sig = m | ((e != 0) ? 0x800000u : 0u);
    int ue = (e != 0) ? (e - 127) : -126;
    int shift = 13;
    if (ue < -14) {                      /* gradual underflow */
      shift = 13 + (-14 - ue);
      if (shift > 24) { h.bits = (uint16_t)(s << 15); return h; }
      ue = -14;
    }
    {
      uint32_t keep = sig >> shift;
      uint32_t rest = sig & ((1u << shift) - 1u);
      uint32_t half = 1u << (shift - 1);
      uint32_t exp16;
      if (rest > half || (rest == half && (keep & 1u))) keep++;
      if (keep >> 11) { keep >>= 1; ue++; }
      if ((keep >> 10) == 0u) { exp16 = 0u; }
      else {
        exp16 = (uint32_t)(ue + 15);
        if (exp16 >= 0x1Fu) {
          h.bits = (uint16_t)((s << 15) | 0x7C00u); return h;
        }
      }
      h.bits = (uint16_t)((s << 15) | (exp16 << 10) | (keep & 0x3FFu));
      return h;
    }
  }
}

/* bfloat16 is binary32 with the low 16 fraction bits dropped. */
CUSTARD_FN float custard_bf16_to_f32(custard_bf16 h) {
  return custard__f32_of_bits((uint32_t)h.bits << 16);
}
CUSTARD_FN custard_bf16 custard_bf16_of_f32(float f) {
  uint32_t u = custard__bits_of_f32(f);
  custard_bf16 h;
  if (((u >> 23) & 0xFFu) == 0xFFu && (u & 0x7FFFFFu) != 0u) {
    h.bits = (uint16_t)((u >> 16) | 0x0040u); return h;
  }
  { uint32_t lsb = (u >> 16) & 1u;
    h.bits = (uint16_t)((u + 0x7FFFu + lsb) >> 16); }
  return h;
}

/* double converts in one step: binary64 holds both formats exactly and has
   the precision to make the intermediate exact, so rounding once here is the
   correctly-rounded answer where going via float would round twice. */
CUSTARD_FN custard_f16 custard_f16_of_f64(double d) {
  return custard_f16_of_f32((float)d);
}
CUSTARD_FN custard_bf16 custard_bf16_of_f64(double d) {
  return custard_bf16_of_f32((float)d);
}
CUSTARD_FN custard_f16 custard_f16_of_i64(int64_t x) {
  return custard_f16_of_f32((float)x);
}
CUSTARD_FN custard_bf16 custard_bf16_of_i64(int64_t x) {
  return custard_bf16_of_f32((float)x);
}

#define CUSTARD__F16_BIN(nm, op)                                         \
  CUSTARD_FN custard_f16 custard_f16_##nm(custard_f16 a,              \
                                             custard_f16 b) {            \
    return custard_f16_of_f32(custard_f16_to_f32(a) op                   \
                              custard_f16_to_f32(b)); }
#define CUSTARD__F16_CMP(nm, op)                                         \
  CUSTARD_FN bool custard_f16_##nm(custard_f16 a, custard_f16 b) {    \
    return custard_f16_to_f32(a) op custard_f16_to_f32(b); }
#define CUSTARD__BF16_BIN(nm, op)                                        \
  CUSTARD_FN custard_bf16 custard_bf16_##nm(custard_bf16 a,           \
                                               custard_bf16 b) {         \
    return custard_bf16_of_f32(custard_bf16_to_f32(a) op                 \
                               custard_bf16_to_f32(b)); }
#define CUSTARD__BF16_CMP(nm, op)                                        \
  CUSTARD_FN bool custard_bf16_##nm(custard_bf16 a, custard_bf16 b) { \
    return custard_bf16_to_f32(a) op custard_bf16_to_f32(b); }

CUSTARD__F16_BIN(add, +)
CUSTARD__F16_BIN(sub, -)
CUSTARD__F16_BIN(mul, *)
CUSTARD__F16_BIN(div, /)
CUSTARD__F16_CMP(eq,  ==)
CUSTARD__F16_CMP(neq, !=)
CUSTARD__F16_CMP(lt,  <)
CUSTARD__F16_CMP(lte, <=)
CUSTARD__F16_CMP(gt,  >)
CUSTARD__F16_CMP(gte, >=)

CUSTARD__BF16_BIN(add, +)
CUSTARD__BF16_BIN(sub, -)
CUSTARD__BF16_BIN(mul, *)
CUSTARD__BF16_BIN(div, /)
CUSTARD__BF16_CMP(eq,  ==)
CUSTARD__BF16_CMP(neq, !=)
CUSTARD__BF16_CMP(lt,  <)
CUSTARD__BF16_CMP(lte, <=)
CUSTARD__BF16_CMP(gt,  >)
CUSTARD__BF16_CMP(gte, >=)

/* The declaration that carries the [@@custard_c_header] naming this file.
   [@@custard_c_header] configures [@@custard_extern] and means nothing on its
   own, so a test that wants this header included has to name it on an extern
   declaration -- which is how a real consumer reaches it too. */
CUSTARD_FN uint16_t narrow_stub_bits(custard_f16 v) { return v.bits; }

#endif
