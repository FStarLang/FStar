/* Section 68, sharpened by EverParse's section 65.1.

   The three uses a [#define] has and an [extern] object does not.  Written as
   a separate translation unit that includes only the generated header,
   because that is what a consumer is: it sees the header and nothing else.

   The [#if] probe is the one worth being careful about.  EverParse first
   wrote it against a *zero*-valued constant --

     #if MACRO_MAJOR_TYPE_UINT64 == 0

   -- which does not discriminate: the preprocessor cannot see an object at
   all, so with the macro absent the line reads [0 == 0] and is true.  The
   correct answer came out for the wrong reason and nothing was reported.
   Only a non-zero expected value catches it. */

#include "Macro.h"

#if MACRO_MAX_SIMPLE_VALUE != 23
#error "MACRO_MAX_SIMPLE_VALUE is not visible to the preprocessor"
#endif

/* A case label. */
int macro_probe_case(uint8_t x) {
  switch (x) {
    case MACRO_MAJOR_TYPE_UINT64: return 1;
    case MACRO_MAJOR_TYPE_TEXT_STRING: return 2;
    default: return 0;
  }
}

/* An initializer for an object with static storage duration. */
static uint8_t macro_probe_static = MACRO_MAX_SIMPLE_VALUE;

int macro_probe(void) {
  return macro_probe_case(0) == 1 && macro_probe_case(3) == 2 &&
         macro_probe_static == 23;
}
