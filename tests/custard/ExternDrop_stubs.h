/* The target side of ExternDrop.fst.  Static inline, so the test needs no
   second translation unit: the point is the F* side, and specifically that
   the call Custard emits has the arity these prototypes declare. */

#ifndef __EXTERNDROP_STUBS_H
#define __EXTERNDROP_STUBS_H

#include <stdint.h>

static inline uint32_t ed_major(uint32_t n) { return n + 1U; }

static inline uint32_t ed_scale(uint32_t n) { return n * 2U; }

#endif
