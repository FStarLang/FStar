#include "Pulse_Lib_Primitives_runtime.h"

uint32_t Pulse_Lib_Primitives_read_atomic(uint32_t *r) {
  return __atomic_load_n(r, __ATOMIC_SEQ_CST);
}

void Pulse_Lib_Primitives_write_atomic(uint32_t *r, uint32_t v) {
  __atomic_store_n(r, v, __ATOMIC_SEQ_CST);
}

bool Pulse_Lib_Primitives_cas(uint32_t *r, uint32_t old_v, uint32_t new_v) {
  return __atomic_compare_exchange_n(r, &old_v, new_v, false,
                                     __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
}
