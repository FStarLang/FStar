#ifndef CEXTERNGROUPING_STUBS_H
#define CEXTERNGROUPING_STUBS_H

#include <stdint.h>

#define CG_NUMBER 1U + 2U
#define CG_PLUS(x) (x) + 2U
#define CG_WIDE 255U + 1U
#define CG_FALSE 0
#define CG_FLAG 0 || 1
#define CG_BOX 1 ? ((CExternGrouping_box){ 11, 0 }) : ((CExternGrouping_box){ 22, 0 })
#define CG_BOX_FN() CG_BOX
#define CG_VARIANT 1 ? ((CExternGrouping_variant){ CEXTERNGROUPING_FULL, {7} }) : \
                      ((CExternGrouping_variant){ CEXTERNGROUPING_EMPTY, {0} })
#define CG_COMMA (void)0, 2U

static inline uint32_t cg_identity(uint32_t x) { return x; }
static uint32_t cg_ticks;
static inline uint32_t cg_tick(void) { return ++cg_ticks; }
static inline uint32_t cg_count(void) { return cg_ticks; }

#endif
