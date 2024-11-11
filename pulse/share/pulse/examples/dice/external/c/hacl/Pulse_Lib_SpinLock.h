#include<pthread.h>

// This must be a pointer, copying mutexes is UB.
typedef pthread_mutex_t *Pulse_Lib_SpinLock_lock;

Pulse_Lib_SpinLock_lock Pulse_Lib_SpinLock_new_lock(void);

void Pulse_Lib_SpinLock_acquire(Pulse_Lib_SpinLock_lock l);

void Pulse_Lib_SpinLock_release(Pulse_Lib_SpinLock_lock l);

void Pulse_Lib_SpinLock_free(Pulse_Lib_SpinLock_lock l);
