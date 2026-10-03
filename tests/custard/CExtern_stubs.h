/* The target side of CExtern.fst.  Everything is static inline so that the
   test needs no second translation unit: the point is the F* side. */

#ifndef __CEXTERN_STUBS_H
#define __CEXTERN_STUBS_H

#include <stdint.h>

typedef struct {
  uint32_t v;
} cextern_handle_t;

typedef uint32_t cextern_tag_t;

static inline cextern_handle_t cextern_make(uint32_t n) {
  cextern_handle_t h;
  h.v = n;
  return h;
}

static inline uint32_t cextern_get(cextern_handle_t h) { return h.v; }

static inline cextern_tag_t cextern_mk_tag(void) { return (uint32_t)7; }

static inline uint32_t cextern_tag_val(cextern_tag_t t) { return t; }

static uint32_t cextern_total_v = 0;

static inline void cextern_bump(uint32_t n) { cextern_total_v += n; }

static inline uint32_t cextern_total(void) { return cextern_total_v; }

#endif
