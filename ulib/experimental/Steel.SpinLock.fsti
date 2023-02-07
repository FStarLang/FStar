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

module Steel.SpinLock
open Steel.Memory
open Steel.Effect

/// A Steel library to share resources between threads through locks.

/// The type of a lock.
/// This is implemented as a pair of a boolean reference, and an invariant name
val lock (p:vprop) : Type u#0


/// If we have vprop [p] in the context, we can create a new lock
/// associated to [p]. [p] is then removed from the context, and only accessible
/// through the newly created lock
val new_lock (p:vprop)
  : SteelT (lock p) p (fun _ -> emp)

/// Acquires the lock, and adds the associated vprop [p] to the context.
/// This function loops until the lock becomes available
val acquire (#p:vprop) (l:lock p)
  : SteelT unit emp (fun _ -> p)

/// Releases a lock [l], as long as the caller previously restored the associated vprop [p]
val release (#p:vprop) (l:lock p)
  : SteelT unit p (fun _ -> emp)

(** Extending locks with selector predicates **)

/// A lock associated to a given vprop [p], and that also ensures the validity
/// of a predicate [pred] on the vprop's selector
val s_lock (p:vprop) (pred:normal (t_of p) -> prop) : Type u#0

/// If we have vprop [p] in the context, and [pred] on its selector, we can create a new lock
/// associated to [p]. [p] is then removed from the context, and only accessible
/// through the newly created lock
val new_s_lock (p:vprop) (pred:normal (t_of p) -> prop)
  : Steel (s_lock p pred)
          p (fun _ -> emp)
          (requires fun h -> pred (h p))
          (ensures fun _ _ _ -> True)

/// Acquires the lock, and adds the associated vprop [p] and predicate [pred] to the context.
/// This function loops until the lock becomes available
val s_acquire (#p:vprop) (#pred:normal (t_of p) -> prop) (l:s_lock p pred)
  : Steel unit emp (fun _ -> p) (requires fun _ -> True) (ensures fun _ _ h1 -> pred (h1 p))

/// Releases a lock [l], as long as the caller previously restored the associated vprop [p]
/// and the associated predicate [pred]
val s_release (#p:vprop) (#pred:normal (t_of p) -> prop) (l:s_lock p pred)
  : Steel unit p (fun _ -> emp) (requires fun h -> pred (h p)) (ensures fun _ _ _ -> True)
