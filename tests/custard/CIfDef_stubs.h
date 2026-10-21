#ifndef CUSTARD_CIFDEF_STUBS_H
#define CUSTARD_CIFDEF_STUBS_H

#include <stdbool.h>
#include <stdint.h>

#ifdef CUSTARD_IFDEF_A
#define CIFDEF_A_PRESENT 1
typedef struct { uint32_t value; } cifdef_payload;
static inline cifdef_payload cifdef_make(void) {
  cifdef_payload p = { 7 };
  return p;
}
static inline uint32_t cifdef_read(cifdef_payload p) { return p.value; }
static inline uint32_t cifdef_yes(void) { return 7; }
#else
#define CIFDEF_A_PRESENT 0
static inline uint32_t cifdef_no(void) { return 11; }
#endif

#ifdef CIfDef_second
#define CIFDEF_B_PRESENT 1
#else
#define CIFDEF_B_PRESENT 0
#endif

static uint32_t cifdef_ticks;
static uint32_t cifdef_values;

static inline bool cifdef_tick(bool b) { ++cifdef_ticks; return b; }
static inline uint32_t cifdef_value(void) { ++cifdef_values; return 9; }
static inline uint32_t cifdef_bool(bool b) { return b ? 13 : 0; }
static inline void cifdef_reset(void) { cifdef_ticks = cifdef_values = 0; }
static inline bool cifdef_counts_ok(void) {
  return cifdef_ticks == 10 && cifdef_values == 2;
}
static inline uint32_t cifdef_expected(bool runtime, uint32_t x) {
  uint32_t a = CIFDEF_A_PRESENT;
  uint32_t b = CIFDEF_B_PRESENT;
  return (a ? 7 : 11) + (a != b) + (a ? (b ? 3 : 5) : 7)
    + (a && runtime ? 7 : 0) + (a && !runtime ? 7 : 0)
    + (a && !b ? 7 : 0) + 5 * (a && runtime ? 7 : 0)
    + 2 * (!a && !runtime ? 11 : 0)
    + (a ? x + 9 : 0) + (a ? 7 : 0) + (a ? 13 : 0);
}

#endif
