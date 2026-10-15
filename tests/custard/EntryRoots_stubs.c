/* The target's realizations of EntryRootsLib.  Both are defined, because both
   are declared: the point of the entry module is that the unit offers its
   whole interface and not just the part this program happens to call. */

#include <stdint.h>

int32_t EntryRootsLib_used(int32_t x) { return x; }

int32_t EntryRootsLib_unused(int32_t x) { return x + (int32_t)1; }
