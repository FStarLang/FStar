#include "Native_runtime.h"
#include <stdio.h>

int main(void) {
  bool ok = Example_Effects_NativeRuntime_test();
  if (CHERRY_EXN_PENDING()) cherry_exn_uncaught();
  if (!ok) {
    fputs("native Pulse exception regression\n", stderr);
    return 1;
  }
  puts("native exceptions: all execution checks passed");
  return 0;
}
