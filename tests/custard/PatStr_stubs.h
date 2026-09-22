/* The target side of PatStr.fst.

   A string equality bug is invisible to a program whose strings are all
   literals: the C compiler pools them, so comparing two of them by address
   happens to give the right answer.  This hands the F* side a string with the
   right contents at the wrong address, which is the only way to see it. */

#ifndef __PATSTR_STUBS_H
#define __PATSTR_STUBS_H

#include <stdlib.h>
#include <string.h>

static inline const char *custard_test_heap_copy(const char *s) {
  size_t n = strlen(s) + 1;
  char *p = (char *)malloc(n);
  if (p) memcpy(p, s, n);
  return p;
}

#endif
