/* Issue 4612.  The [assume val] the propagated constants are passed to. */
#include <stdint.h>
void CConstLet_sink(uint32_t x) { (void)x; }
