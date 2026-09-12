/* The target side of ChrTy.fst.

   The point of that test is a program that mentions [FStar.Char.char] and
   contains no character *constant*, because the type alone was enough to
   produce a header that would not compile (section 46.2).  So the char has
   to come from somewhere other than a literal. */

#ifndef __CHRTY_STUBS_H
#define __CHRTY_STUBS_H

#include <stdint.h>

static inline uint32_t custard_test_a_char(void) { return 97; }

#endif
