/* The target side of TensorC.fst.

   Kuiper's real header is <mma.h> under nvcc, where the fragment types are
   C++ templates and the entry points are namespace-qualified.  Neither of
   those is available to a plain C compiler, so this stands in for them with
   the same *shapes*: a qualified name in value position, and a type whose
   spelling is not an identifier.

   The point of the test is that Custard emits these names verbatim.  What is
   on the other side of them is the target's business. */

#ifndef __TENSORC_STUBS_H
#define __TENSORC_STUBS_H

#include <stdint.h>

/* A type whose C spelling is not an identifier.  In Kuiper this is [auto&],
   inferred from a macro that expands to wmma::fragment<...>. */
typedef struct { uint32_t x[8]; } tc_frag_t;
#define tc_auto_ref tc_frag_t

/* A namespace-qualified name.  C has no namespaces, so [::] is spelled with a
   macro here; under nvcc these are wmma::fill_fragment and wmma::mma_sync. */
static inline tc_frag_t tc_mk_a(void) {
  tc_frag_t f; for (int i = 0; i < 8; i++) f.x[i] = 2; return f;
}
static inline tc_frag_t tc_mk_acc(void) {
  tc_frag_t f; for (int i = 0; i < 8; i++) f.x[i] = 0; return f;
}
static inline void tc_fill(tc_frag_t *d, uint32_t v) {
  for (int i = 0; i < 8; i++) d->x[i] = v;
}
static inline uint32_t tc_sum(tc_frag_t a, tc_frag_t b) {
  uint32_t s = 0; for (int i = 0; i < 8; i++) s += a.x[i] * b.x[i]; return s;
}

#define TC_NS(f) tc_##f

#endif
