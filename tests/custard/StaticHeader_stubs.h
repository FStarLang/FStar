#ifndef STATIC_HEADER_STUBS_H
#define STATIC_HEADER_STUBS_H
#include <stdint.h>
static inline uint32_t static_header_hook(uint32_t x) { return x + 2; }
#endif
