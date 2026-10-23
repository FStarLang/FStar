#ifndef CEXTERNSTMT_STUBS_H
#define CEXTERNSTMT_STUBS_H

#include <stdint.h>

static uint32_t cs_value;
static uint32_t cs_calls;
#define CS_STORE(x) if (1) cs_value = (x)
#define CS_BLOCK(x) if (1) { cs_value = (x); }
#define CS_PAIR(x) cs_value = (x); cs_calls++
static inline void cs_reset(void) { cs_value = 0; cs_calls = 0; }
static inline uint32_t cs_get(void) { return cs_value; }
static inline uint32_t cs_count(void) { return cs_calls; }

#endif
