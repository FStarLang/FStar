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

module Steel.ST.GhostMonotonicReference
open FStar.Ghost
open Steel.ST.Util
module Preorder = FStar.Preorder

/// A library for references that are monotonic with respect to a
/// user-specified preorder, with ownership controlled using
/// fractional permissions.
///
/// This library builds on top of Steel.MonotonicReference, providing
/// a version of it for the ST effect.
///
/// Its main feature is that it allows "witnessing" the value of a
/// reference and later "recalling" that the current value is related
/// to the prior witnessed value by the preorder.

/// An abstract datatype for monotonic references
/// where [p] constrains how the contents of the reference is allowed to evolve
[@@erasable]
val ref (a:Type u#0) (p:Preorder.preorder a)
  : Type u#0

/// The main representation predicate
val pts_to (#a:Type)
           (#p:Preorder.preorder a)
           (r:ref a p)
           ([@@@smt_fallback]f:perm)
           ([@@@smt_fallback]v:a)
   : vprop

/// Allocates a reference with value [x]. We have full permission on the newly
/// allocated reference.
val alloc (#opened: _) (#a:Type) (p:Preorder.preorder a) (v:a)
  : STGhostT (ref a p) opened emp (fun r -> pts_to r full_perm v)

/// Writes value [x] in the reference [r], as long as we have full
/// ownership of [r], and, importantly, if the new value [x] is
/// related to the old value by [p].
val write (#opened: _) (#a:Type) (#p:Preorder.preorder a) (#v:a)
          (r:ref a p) (x:a)
  : STGhost unit opened
      (pts_to r full_perm v)
      (fun v -> pts_to r full_perm x)
      (requires p v x)
      (ensures fun _ -> True)

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
///
/// The most precise stable fact one can witness if [p v], i.e., that
/// any future value [v'] is related to the current value [v] by [p v
/// v'].
val witness (#inames: _)
            (#a:Type)
            (#q:perm)
            (#p:Preorder.preorder a)
            (r:ref a p)
            (fact:stable_property p)
            (v:erased a)
            (_:squash (fact v))
  : STAtomicUT (witnessed r fact) inames
      (pts_to r q v)
      (fun _ -> pts_to r q v)


/// If we previously witnessed the validity of [fact], we can recall its validity
val recall (#inames: _)
           (#a:Type u#0)
           (#q:perm)
           (#p:Preorder.preorder a)
           (fact:property a)
           (r:ref a p)
           (v:erased a)
           (w:witnessed r fact)
  : STAtomicU unit inames
      (pts_to r q v)
      (fun _ -> pts_to r q v)
      (requires True)
      (ensures fun _ -> fact v)

/// Monotonic references are also equipped with the usual fractional
/// permission discipline So, you can split a reference into two
/// read-only shares
val share (#inames:_)
          (#a:Type)
          (#p:Preorder.preorder a)
          (r:ref a p)
          (f:perm)
          (v:a)
  : STGhostT unit inames
    (pts_to r f v)
    (fun _ -> pts_to r (half_perm f) v `star` pts_to r (half_perm f) v)

/// And you can gather back the shares
val gather (#inames:_)
           (#a:Type)
           (#p:Preorder.preorder a)
           (r:ref a p)
           (f g:perm)
           (v:a)
  : STGhostT unit inames
    (pts_to r f v `star` pts_to r g v)
    (fun _ -> pts_to r (sum_perm f g) v)
