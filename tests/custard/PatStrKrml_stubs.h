/* The target side of PatStrKrml.fst.

   [custard_test_heap_copy] is PatStr's, and is here for the same reason: a
   program whose strings are all literals cannot see a comparison that is
   wrong, because the C compiler pools them (section 44.2).

   [__eq__Prims_string] is krmllib's, realized in [krmllib/c/prims.c] as
   exactly the line below.  The test suite links against krmllib's *minimal*
   distribution, which does not carry it; a real build would link
   [prims.c] and never see this file.  It is a stand-in for a krmllib
   dependency, not a Custard one -- any F* program that compares two strings
   through the krml backend needs the same symbol, string match or not. */

#ifndef __PATSTRKRML_STUBS_H
#define __PATSTRKRML_STUBS_H

#include "PatStr_stubs.h"

#include <stdbool.h>
#include <string.h>

static inline bool __eq__Prims_string(const char *s1, const char *s2) {
  return strcmp(s1, s2) == 0;
}

#endif
