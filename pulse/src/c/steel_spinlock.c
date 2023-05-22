#include "Steel_SpinLock.h"
#include <pthread.h>

Steel_SpinLock_lock____ Steel_SpinLock_new_lock () {
  pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
  return mutex;
}

void Steel_SpinLock_acquire(Steel_SpinLock_lock____ l) {
  pthread_mutex_lock(&l); 
}

void Steel_SpinLock_release(Steel_SpinLock_lock____ l) {
  pthread_mutex_unlock(&l);
}
