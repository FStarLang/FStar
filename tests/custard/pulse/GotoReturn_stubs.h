#ifndef GOTO_RETURN_STUBS_H
#define GOTO_RETURN_STUBS_H
#include <stdbool.h>
#include <stdint.h>

static inline int32_t gr_opaque_int32(int32_t x) { return x; }
static inline bool gr_opaque_bool(bool x) { return x; }
static inline uint32_t gr_opaque_uint32(uint32_t x) { return x; }
static inline uint64_t gr_opaque_uint64(uint64_t x) { return x; }
static inline int64_t gr_opaque_int64(int64_t x) { return x; }

static int32_t gr_effects;
static inline void gr_side_effect(int32_t x) { gr_effects = gr_effects * 10 + x; }
static inline int32_t gr_side_effects(void) { return gr_effects; }
#endif
