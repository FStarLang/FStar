#include <stdint.h>

/* The external whose target name is exactly the one the generated equality
   helper for [ExtEq.pair] would otherwise take (section 117.2). */
int32_t ExtEq_pair__eq(int32_t n) { return (int32_t)(n + 1); }
