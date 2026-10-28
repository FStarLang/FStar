/* C runtime for Pulse.Lib.Primitives: the atomic operations on a
   `ref U32.t`.  The F* implementation (Pulse.Lib.Primitives-model.fst) is
   only a model -- a read followed by a write -- and is never extracted. */
#ifndef PULSE_LIB_PRIMITIVES_RUNTIME_H
#define PULSE_LIB_PRIMITIVES_RUNTIME_H

#include <stdbool.h>
#include <stdint.h>

uint32_t Pulse_Lib_Primitives_read_atomic(uint32_t *r);

void Pulse_Lib_Primitives_write_atomic(uint32_t *r, uint32_t v);

bool Pulse_Lib_Primitives_cas(uint32_t *r, uint32_t old_v, uint32_t new_v);

#endif
