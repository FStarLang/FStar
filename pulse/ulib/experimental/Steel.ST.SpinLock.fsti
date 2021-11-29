(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.ST.SpinLock
open Steel.ST.Util

/// A Steel library to share resources between threads through locks.
/// It is implemented on top of Steel.SpinLock

/// The type of a lock.  This is implemented as a pair of a boolean
/// reference, and an invariant name
val lock_t : Type u#0

/// A predicate relating a lock to a vprop.
val protects (l:lock_t) (p:vprop) : prop

/// The type of locks associated to a given vprop [p]
let lock (p:vprop) = l:lock_t{l `protects` p}

/// If we have vprop [p] in the context, we can create a new lock
/// associated to [p]. [p] is then removed from the context, and only
/// accessible through the newly created lock
val new_lock (p:vprop)
  : STT (lock p) p (fun _ -> emp)

/// Acquires the lock, and adds the associated vprop [p] to the
/// context. This function loops until the lock becomes available
val acquire (#p:vprop) (l:lock p)
  : STT unit emp (fun _ -> p)

/// Releases a lock [l], as long as the caller previously restored the
/// associated vprop [p]
val release (#p:vprop) (l:lock p)
  : STT unit p (fun _ -> emp)
