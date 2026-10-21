#ifndef FOREIGN_BINDINGS_H
#define FOREIGN_BINDINGS_H
#include <stdint.h>
static inline uint32_t fb_hook(uint32_t x) { return x + 3U; }
#define FB_VALUE UINT32_C(5)
#define fb_identity(x) (x)
#endif
