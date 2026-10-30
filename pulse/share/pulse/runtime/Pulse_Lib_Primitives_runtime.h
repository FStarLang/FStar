/* C runtime for Pulse.Lib.Primitives: the atomic operations on a
   `ref U32.t`.  The F* implementation (Pulse.Lib.Primitives-model.fst) is
   only a model -- a read followed by a write -- and is never extracted.

   The functions are static inline, so this header must be included before
   the extracted code's own declarations of them: with Karamel, use
   `-add-include '"Pulse_Lib_Primitives_runtime.h"'`; with Custard's C
   backend, compile with `-include Pulse_Lib_Primitives_runtime.h`. */
#ifndef PULSE_LIB_PRIMITIVES_RUNTIME_H
#define PULSE_LIB_PRIMITIVES_RUNTIME_H

#include <stdbool.h>
#include <stdint.h>

static inline uint32_t Pulse_Lib_Primitives_read_atomic(uint32_t *r) {
  return __atomic_load_n(r, __ATOMIC_SEQ_CST);
}

static inline void Pulse_Lib_Primitives_write_atomic(uint32_t *r, uint32_t v) {
  __atomic_store_n(r, v, __ATOMIC_SEQ_CST);
}

static inline bool Pulse_Lib_Primitives_cas(uint32_t *r, uint32_t old_v,
                                            uint32_t new_v) {
  return __atomic_compare_exchange_n(r, &old_v, new_v, false,
                                     __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
}

#endif
