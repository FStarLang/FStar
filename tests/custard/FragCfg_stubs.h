/* The target side of FragCfg.fst: the C11 shape of a TensorCore fragment
   API.  Real CUDA spells the type `auto&' and the calls `wmma::...'; both
   are exercised by TensorC.fst (section 45.1).  What this file is for is
   the *indexing*: one C type and three C constructors, selected in F* by a
   typeclass whose indices are all erased. */

#ifndef __FRAGCFG_STUBS_H
#define __FRAGCFG_STUBS_H

#include <stdint.h>

typedef struct { uint32_t v; } fc_frag_t;

static inline fc_frag_t fc_frag_a_16(void)   { fc_frag_t f = { 2 }; return f; }
static inline fc_frag_t fc_frag_b_16(void)   { fc_frag_t f = { 3 }; return f; }
static inline fc_frag_t fc_frag_acc_16(void) { fc_frag_t f = { 0 }; return f; }

static inline uint32_t fc_mma(fc_frag_t c, fc_frag_t a, fc_frag_t b) {
  return c.v + a.v * b.v;
}

#endif
