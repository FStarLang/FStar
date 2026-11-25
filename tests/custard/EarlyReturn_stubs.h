#ifndef EARLY_RETURN_STUBS_H
#define EARLY_RETURN_STUBS_H
#include <stdint.h>

static uint32_t er_state;
static inline uint32_t er_tick(uint32_t n) {
  er_state = er_state * 10 + n;
  return n;
}
static inline void er_note(uint32_t n) { er_state = er_state * 10 + n; }
static inline uint32_t er_trace(void) { return er_state; }
static inline void er_reset(void) { er_state = 0; }
#endif
