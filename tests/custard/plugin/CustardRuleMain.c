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

/* Section 64.  The realization of a polymorphic external, which is one
   function per instantiation.

   The names are Custard's: CustardRulePlugin's [emit] rule builds an [EQual]
   carrying the argument's type, and the monomorphization pass turns that into
   one declaration per distinct type vector.  Nothing in CustardRuleTest.fst
   calls [sink], so [register_root] is what keeps it alive, exactly as for
   [kcall] above.

   That the two take different C types is the property under test: a single
   shared symbol could not be declared at both, and would not add up to 7. */

static uint32_t kpr_sink_acc = 0;

void CustardRuleTest_sink__uint32(uint32_t x) { kpr_sink_acc += x; }

void CustardRuleTest_sink__uint64(uint64_t x) { kpr_sink_acc += (uint32_t)x; }

uint32_t kpr_sink_total(void) { return kpr_sink_acc; }
