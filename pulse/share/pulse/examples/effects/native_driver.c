#include "Native_runtime.h"
#include <stdio.h>

static size_t observed;
static bool trace_ok = true;
static const uint32_t prefix[] = {
  100, 2, 1, 101, 2, 1, 102, 2, 1, 200, 3, 5, 4, 5, 201, 8, 7, 300
};

static custard_unit note(cherry_fn self, uint32_t tag) {
  (void)self;
  const size_t start = sizeof(prefix) / sizeof(prefix[0]);
  uint32_t expected = observed < start ? prefix[observed] :
    observed < start + 257 ? (uint32_t)(observed - start) :
    observed == start + 257 ? 400 : 6;
  if (tag != expected) {
    fprintf(stderr, "cleanup event %zu: expected %u, got %u\n",
            observed, expected, tag);
    trace_ok = false;
  }
  ++observed;
  return 0;
}

CHERRY_STATIC_CLOSURE(observer, note, 1);

int main(void) {
  bool ok = Example_Effects_NativeRuntime_test();
  if (CHERRY_EXN_PENDING()) cherry_exn_uncaught();
  if (!ok) {
    fputs("native Pulse exception regression\n", stderr);
    return 1;
  }
  ok = Example_Effects_NativeRuntime_stress((cherry_fn)&observer);
  if (CHERRY_EXN_PENDING()) cherry_exn_uncaught();
  if (!ok || !trace_ok || observed != sizeof(prefix) / sizeof(prefix[0]) + 257 + 1 + 1000) {
    fprintf(stderr, "native Pulse stress/cleanup regression (%zu events)\n", observed);
    return 1;
  }
  puts("native exceptions: all execution checks passed");
  return 0;
}
