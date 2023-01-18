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

module Steel.MonotonicReference

open FStar.PCM
open FStar.Ghost
open Steel.FractionalPermission

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

module Preorder = FStar.Preorder

/// A library for Steel references that are monotonic with respect to a user-specified preorder.
/// This library builds on top of Steel.HigherReference, and is specialized to values at universe 1.

/// An abstract datatype for monotonic references
val ref (a:Type u#0) (p:Preorder.preorder a)
  : Type u#0

/// The standard points to separation logic predicate
val pts_to_sl (#a:Type)
              (#p:Preorder.preorder a)
              (r:ref a p)
              (f:perm)
              (v:a)
  : slprop u#1

/// Lifting the standard points to predicate to vprop, with a non-informative selector
[@@ __steel_reduce__]
unfold
let pts_to (#a:Type)
           (#p:Preorder.preorder a)
           (r:ref a p)
           (f:perm)
           (v:a)
   : vprop
   = to_vprop (pts_to_sl r f v)

/// Allocates a reference with value [x]. We have full permission on the newly
/// allocated reference.
val alloc (#a:Type) (p:Preorder.preorder a) (v:a)
  : SteelT (ref a p) emp (fun r -> pts_to r full_perm v)

/// Writes value [x] in the reference [r], as long as we have full ownership of [r]
val write (#a:Type) (#p:Preorder.preorder a) (#v:erased a)
          (r:ref a p) (x:a)
  : Steel unit (pts_to r full_perm v)
               (fun v -> pts_to r full_perm x)
               (requires fun _ -> p v x /\ True)
               (ensures fun _ _ _ -> True)

/// A wrapper around a predicate that depends on a value of type [a]
let property (a:Type)
  = a -> prop

/// A wrapper around a property [fact] that has been witnessed to be true and stable
/// with respect to preorder [p]
val witnessed (#a:Type u#0) (#p:Preorder.preorder a) (r:ref a p) (fact:property a)
  : Type0

/// The type of properties depending on values of type [a], and that
/// are stable with respect to the preorder [p]
let stable_property (#a:Type) (p:Preorder.preorder a)
  = fact:property a { Preorder.stable fact p }

/// If [fact] is a stable property for the reference preorder [p], and if
/// it holds for the current value [v] of the reference, then we can witness it
val witness (#inames: _) (#a:Type) (#q:perm) (#p:Preorder.preorder a) (r:ref a p)
            (fact:stable_property p)
            (v:erased a)
            (_:squash (fact v))
  : SteelGhostT (witnessed r fact) inames (pts_to r q v)
               (fun _ -> pts_to r q v)


/// If we previously witnessed the validity of [fact], we can recall its validity
val recall (#inames: _) (#a:Type u#0) (#q:perm) (#p:Preorder.preorder a)
           (fact:property a)
           (r:ref a p) (v:erased a) (w:witnessed r fact)
  : SteelAtomicU unit inames (pts_to r q v)
               (fun _ -> pts_to r q v)
               (requires fun _ -> True)
               (ensures fun _ _ _ -> fact v)

/// Monotonic references are also equipped with the usual fractional permission discipline
/// So, you can split a reference into two read-only shares
val share (#inames:_)
          (#a:Type)
          (#p:Preorder.preorder a)
          (r:ref a p)
          (f:perm)
          (v:Ghost.erased a)
  : SteelGhostT unit inames
    (pts_to r f v)
    (fun _ -> pts_to r (half_perm f) v `star` pts_to r (half_perm f) v)

/// And you can gather back the shares
val gather (#inames:_)
           (#a:Type)
           (#p:Preorder.preorder a)
           (r:ref a p)
           (f g:perm)
           (v:Ghost.erased a)
  : SteelGhostT unit inames
    (pts_to r f v `star` pts_to r g v)
    (fun _ -> pts_to r (sum_perm f g) v)
