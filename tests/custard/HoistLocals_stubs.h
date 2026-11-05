#ifndef HOIST_LOCALS_STUBS_H
#define HOIST_LOCALS_STUBS_H
#include <stdint.h>

static uint32_t hl_state;
static inline uint32_t hl_tick(uint32_t n) {
  hl_state = hl_state * 10 + n;
  return n;
}
static inline uint32_t hl_trace(void) { return hl_state; }
static inline void hl_reset(void) { hl_state = 0; }

#ifdef HOIST_LEFT
typedef struct { uint32_t value; } hl_left_t;
static inline hl_left_t hl_make_left(void) {
  hl_left_t x = { 4 }; return x;
}
static inline uint32_t hl_get_left(hl_left_t x) { return x.value; }
#else
typedef struct { uint32_t value; } hl_right_t;
static inline hl_right_t hl_make_right(void) {
  hl_right_t x = { 4 }; return x;
}
static inline uint32_t hl_get_right(hl_right_t x) { return x.value; }
#endif
#endif
