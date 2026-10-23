/* The primitives Pulse.Lib.Core and Pulse.Lib.Sleep declare and do not
   define, realized for Cherry (doc/ref/cherry.md); ml/ has the OCaml ones.
   Externals borrow their arguments. */
#include <pthread.h>
#include <stdlib.h>
#include <time.h>
#include "cherry.h"

static void *thread_main(void *arg) {
  cherry_fn f = (cherry_fn)arg;
  cherry_call_thunk(f);
  cherry_dec_fn(f);
  return NULL;
}

/* The new thread gets a reference of its own to the closure, and
   everything the closure reaches is marked shared first, since both threads
   may now count it. */
void Pulse_Lib_Core_fork_core(cherry_fn f) {
  cherry_mark_fn(f, CHERRY_SHARE);
  cherry_inc(f);
  pthread_t t;
  if (pthread_create(&t, NULL, thread_main, f) != 0) abort();
  pthread_detach(t);
}

void Pulse_Lib_Sleep_sleep_ms(cherry_int ms) {
  int64_t n = cherry_int_to_i64(ms);
  struct timespec ts = { (time_t)(n / 1000), (long)(n % 1000) * 1000000L };
  nanosleep(&ts, NULL);
}
