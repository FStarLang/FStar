#include<pthread.h>

typedef pthread_mutex_t Pulse_Lib_SpinLockToken_lock;

Pulse_Lib_SpinLockToken_lock Pulse_Lib_SpinLockToken_new_lock(void);

void Pulse_Lib_SpinLockToken_acquire(Pulse_Lib_SpinLockToken_lock l);

void Pulse_Lib_SpinLockToken_release(Pulse_Lib_SpinLockToken_lock l);