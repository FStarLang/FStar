#include <assert.h>
#include <pthread.h>
#include <stdlib.h>
#include "Pulse_Lib_SpinLock.h"

Pulse_Lib_SpinLock_lock Pulse_Lib_SpinLock_new_lock(void)
{
  pthread_mutex_t *l = malloc(sizeof(pthread_mutex_t));
  assert(l);
  int r = pthread_mutex_init(l, NULL);
  assert (r ==0);
  return l;
}

void Pulse_Lib_SpinLock_acquire(Pulse_Lib_SpinLock_lock l)
{
  pthread_mutex_lock(l);
}

void Pulse_Lib_SpinLock_release(Pulse_Lib_SpinLock_lock l)
{
  pthread_mutex_unlock(l);
}

void Pulse_Lib_SpinLock_free(Pulse_Lib_SpinLock_lock l)
{
  pthread_mutex_destroy(l);
  free(l);
}
