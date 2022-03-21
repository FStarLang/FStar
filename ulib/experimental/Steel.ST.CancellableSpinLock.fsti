(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: Aseem Rastogi
*)

module Steel.ST.CancellableSpinLock

open Steel.ST.Effect

/// This module provides a cancellable spinlock Steel library
///
/// As with Steel.ST.SpinLock, a cancellable spinlock guards
///   a separation logic assertion
///
/// However, it allows for the cases when the client is not able
///   to maintain the assertion
///
/// At that point, the client may just cancel the lock


/// The lock type that guards the assertion `v`

val cancellable_lock (v:vprop) : Type0

/// A cancellable lock can be created by providing `v`

val new_cancellable_lock (v:vprop)
  : STT (cancellable_lock v) v (fun _ -> emp)


/// `can_release` is the permission to release the lock
///
/// Acquiring the lock, if it succeeds, provides `v`, the protected assertion
///   and `can_release`

val can_release (#v:vprop) (c:cancellable_lock v) : vprop

let maybe_acquired (b:bool) (#v:vprop) (c:cancellable_lock v)
  = if b then (v `star` can_release c) else emp

val acquire (#v:vprop) (c:cancellable_lock v)
  : STT bool emp (fun b -> maybe_acquired b c)


/// The client may provide `v` and `can_release` to release the lock

val release (#v:vprop) (c:cancellable_lock v)
  : STT unit (v `star` can_release c) (fun _ -> emp)

/// If the client is no longer able to maintain `v`,
///   they may just cancel the lock by providing `can_release`

val cancel (#v:vprop) (c:cancellable_lock v)
  : STT unit (can_release c) (fun _ -> emp)
