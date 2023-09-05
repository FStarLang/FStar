/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __Steel_SpinLock_H
#define __Steel_SpinLock_H

#include <stdbool.h>
#include "steel_types.h"

extern bool Steel_SpinLock_uu___is_Lock(Steel_SpinLock_lock *projectee);

extern bool *Steel_SpinLock___proj__Lock__item__r(Steel_SpinLock_lock *projectee);

extern void Steel_SpinLock___proj__Lock__item__i(Steel_SpinLock_lock *projectee);

extern void Steel_SpinLock_new_lock(Steel_SpinLock_lock *x0);

extern void Steel_SpinLock_acquire(Steel_SpinLock_lock *l);

extern void Steel_SpinLock_release(Steel_SpinLock_lock *l);

extern void Steel_SpinLock_new_s_lock(Steel_SpinLock_lock *x0);

extern void Steel_SpinLock_s_acquire(Steel_SpinLock_lock *l);

extern void Steel_SpinLock_s_release(Steel_SpinLock_lock *l);


#define __Steel_SpinLock_H_DEFINED
#endif
