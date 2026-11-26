/*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

/* The C realization of Pulse.Lib.Atomic (see Pulse.Lib.Atomic-c.fst), for
   code extracted with Custard's direct C backend.  [atomic_t t] is
   [_Atomic(t)], and the operations are the C11 generic functions of
   <stdatomic.h>, all sequentially consistent.  The arguments are
   [_Atomic(t) *] pointers.

   [Pulse_Lib_Atomic_compare_exchange] uses a GNU C statement expression
   (GCC and Clang) for the temporary holding the expected value. */

#ifndef PULSE_LIB_ATOMIC_RUNTIME_H
#define PULSE_LIB_ATOMIC_RUNTIME_H

#include <stdatomic.h>
#include <stdbool.h>

#define Pulse_Lib_Atomic_to_atomic(x) (x)
#define Pulse_Lib_Atomic_of_atomic(x) (x)

#define Pulse_Lib_Atomic_load(p) atomic_load(p)
#define Pulse_Lib_Atomic_store(p, x) atomic_store((p), (x))
#define Pulse_Lib_Atomic_exchange(p, x) atomic_exchange((p), (x))

/* The [(void)0, *(p)] comma expression drops the [_Atomic] qualifier, as in
   GCC's own <stdatomic.h>. */
#define Pulse_Lib_Atomic_compare_exchange(p, expected, desired)              \
  __extension__ ({                                                           \
    __typeof__((void)0, *(p)) pulse_lib_atomic_expected = (expected);        \
    atomic_compare_exchange_strong((p), &pulse_lib_atomic_expected,          \
                                   (desired));                               \
  })

#define Pulse_Lib_Atomic_fetch_add(p, x) atomic_fetch_add((p), (x))
#define Pulse_Lib_Atomic_fetch_sub(p, x) atomic_fetch_sub((p), (x))
#define Pulse_Lib_Atomic_fetch_and(p, x) atomic_fetch_and((p), (x))
#define Pulse_Lib_Atomic_fetch_or(p, x) atomic_fetch_or((p), (x))
#define Pulse_Lib_Atomic_fetch_xor(p, x) atomic_fetch_xor((p), (x))

#endif
