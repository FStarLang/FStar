#include <assert.h>
#include <pthread.h>

typedef pthread_mutex_t Pulse_Lib_SpinLockToken_lock;

Pulse_Lib_SpinLockToken_lock Pulse_Lib_SpinLockToken_new_lock(void)
{
  pthread_mutex_t l;
  int r = pthread_mutex_init(&l, NULL);
  assert (r ==0);
  return l;
}

void Pulse_Lib_SpinLockToken_acquire(Pulse_Lib_SpinLockToken_lock l)
{
  pthread_mutex_lock(&l);
}

void Pulse_Lib_SpinLockToken_release(Pulse_Lib_SpinLockToken_lock l)
{
  pthread_mutex_unlock(&l);
}
