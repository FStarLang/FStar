/* Section 36.2.  The runtime entry point CustardRulePlugin's rule synthesizes
   a call to.

   Nothing in CustardRuleTest.fst calls [kcall].  That is the shape a launcher
   rule always has -- the rule emits the call, the source never mentions the
   symbol -- and it is why the rule has to pin it with [register_root]: dead
   code elimination has no other reason to keep it.

   It stands for a device launcher: it is handed the lifted kernel, the block
   count with the shared-memory total already folded in, and the value the
   kernel body captured from the launch site. */

#include <stdint.h>

uint32_t kpr_kcall(uint32_t (*f)(uint32_t, uint32_t), uint32_t nblk,
                   uint32_t cap) {
  /* The captures come first in the lifted kernel's parameter list, because
     that is how the rule closed the lambda: the original parameter [tid] is
     last.  3 + 42 + (1 + 7) = 53, which is what main checks. */
  return nblk + f(cap, (uint32_t)1U);
}
