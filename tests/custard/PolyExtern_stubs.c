/* The target side of PolyExtern.fst: the realization of a polymorphic
   external, which is one C function per instantiation.

   The names are Custard's, not this file's choosing -- that is the contract
   being tested.  [identity] at [UInt32.t] is [PolyExtern_identity__t]; at
   [PolyExtern.pair] it is [PolyExtern_identity__pair].  A single shared
   symbol would not type-check here, which is the point: the two
   instantiations really are two functions.

   A separate translation unit rather than static inline definitions in a
   header, because nothing tells the generated .c to include a header for a
   symbol whose name Custard invented. */

#include "PolyExtern.h"

uint32_t PolyExtern_identity__t(uint32_t x) { return x; }

PolyExtern_pair PolyExtern_identity__pair(PolyExtern_pair p) { return p; }
