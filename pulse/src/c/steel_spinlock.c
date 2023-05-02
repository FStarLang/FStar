#include "Steel_SpinLock.h"
#include <assert.h>
#include <pthread.h>

void Steel_SpinLock_new_lock (Steel_SpinLock_lock____ *dst) {
  int r = pthread_mutex_init(dst, NULL);
  assert(r==0);
}

void Steel_SpinLock_acquire(Steel_SpinLock_lock____ *l) {
  pthread_mutex_lock(l);
}

void Steel_SpinLock_release(Steel_SpinLock_lock____ *l) {
  pthread_mutex_unlock(l);
}
