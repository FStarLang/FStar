/* The C counterpart of driver.ml. */
#include <stdio.h>
#include <stdlib.h>
#include "Quicksort_Task.h"

int main(void) {
  const int nproc = 32, len = 10000;
  cherry_int *a = malloc(len * sizeof *a);
  if (a == NULL) abort();
  srand(42);
  for (int i = 0; i < len; i++) a[i] = CHERRY_INT_SMALL(rand() % (10 * len));
  printf("Calling quicksort... "); fflush(stdout);
  Quicksort_Task_quicksort(CHERRY_INT_SMALL(nproc), a, CHERRY_INT_SMALL(0),
                           CHERRY_INT_SMALL(len));
  for (int i = 1; i < len; i++)
    if (cherry_int_val(a[i - 1]) > cherry_int_val(a[i])) {
      printf("not sorted\n");
      return 1;
    }
  free(a);
  printf("OK!\n");
  return 0;
}
