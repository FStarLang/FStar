/* The target side of NoPrefixX.fst.  Both names are written here exactly as
   the F* source expects them to come out: [ticket] because
   --custard_c_no_prefix says so, [noprefixx_fixed] because the attribute
   does.  A separate translation unit, so the link is the assertion. */

#include "NoPrefixX.h"

uint32_t ticket(uint32_t n) { return n + (uint32_t)1; }

uint32_t noprefixx_fixed(uint32_t n) { return n * (uint32_t)3; }
