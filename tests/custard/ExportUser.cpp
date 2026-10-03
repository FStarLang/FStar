// Section 32.4.  A consumer Custard did not generate, compiled as C++.
//
// Two things are under test and neither is visible in the generated file
// alone: that the names in Export.h are the unqualified ones the F* module
// wrote, and that a C++ translation unit can resolve them -- which it can
// only if the header carries the extern "C" guard, since otherwise these
// calls are mangled and the link fails.

#include <cstdio>
#include <cstdint>

#include "ExportLib.h"

int main(void) {
  uint32_t a = widget_add(2, 3);
  uint32_t d = widget_double(5);
  uint32_t i = widget_id(7);
  // The type and its constructor are spelled the way the F* module wrote
  // them, not with the module prefix: the header is the API.
  widget w = widget_make(4, 9);
  wkind k = widget_kind(w);
  if (a != 6 || d != 12 || i != 7 || w.w_lo != 4 || k != WLARGE) {
    std::printf("FAIL %u %u %u\n", a, d, i);
    return 1;
  }
  std::printf("ok\n");
  return 0;
}
