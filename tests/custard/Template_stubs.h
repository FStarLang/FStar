/* The target side of Template.fst (section 69).  Real CUDA spells the type
   `nvcuda::wmma::fragment<nvcuda::wmma::matrix_a, 16, 16, 16, __half,
   nvcuda::wmma::row_major>' and real C++ spells the other one
   `std::bitset<64>'; both are template-ids, and neither is expressible in
   C11.  What this file does is give the *same shape* -- a name applied to
   type and value arguments -- a C11 meaning, using function-like macros,
   so that the generated file can be compiled and run by the ordinary test
   harness rather than only by nvcc.

   The property under test is what Custard emits: that the arguments reach
   the target at all, in the right order, with a value argument spelled as a
   value.  A C++ compiler reading `tpl_fragment(a, 16, 16, 16, t, l)' as
   `fragment<a, 16, 16, 16, t, l>' is a one-line change to this file. */

#ifndef __TEMPLATE_STUBS_H
#define __TEMPLATE_STUBS_H

#include <stdint.h>

/* One C11 type per instantiation, which is what a template-id denotes.  The
   name is pasted from the tag and the leading size, so the macro is a stand-in
   for instantiation and not a way of ignoring the arguments. */
typedef struct { uint32_t v; } tpl_matrix_a_16;
typedef struct { uint32_t v; } tpl_matrix_b_16;
typedef struct { uint64_t bits; } tpl_bits64;

#define tpl_fragment(U, M, N, K, T, L) U##_##M
#define tpl_bitset(N) tpl_bits##N

static inline tpl_matrix_a_16 tpl_fill_a(void) {
  tpl_matrix_a_16 f = { 2 }; return f;
}
static inline tpl_matrix_b_16 tpl_fill_b(void) {
  tpl_matrix_b_16 f = { 3 }; return f;
}

static inline uint32_t tpl_mma(tpl_matrix_a_16 a, tpl_matrix_b_16 b) {
  return a.v * b.v;
}

static inline tpl_bits64 tpl_mask(void) { tpl_bits64 b = { ~(uint64_t)0 }; return b; }

static inline uint32_t tpl_count(tpl_bits64 b) {
  uint32_t n = 0;
  for (uint32_t i = 0; i < 64; i++) { n += (uint32_t)((b.bits >> i) & 1); }
  return n;
}

#endif
