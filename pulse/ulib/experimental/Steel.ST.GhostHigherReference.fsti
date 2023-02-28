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
*)

module Steel.ST.GhostHigherReference
open FStar.Ghost
open Steel.ST.Util

/// The main ref type.
///
/// It's in universe zero, so refs can be stored in the heap, you can
/// have [ref (ref a)] etc.
[@@erasable]
val ref ([@@@ strictly_positive] a:Type u#1)
  : Type0

/// The main representation predicate
///
/// Both the permissions [p] and the value [v] are marked with the
/// [smt_fallback] attribute. This allows the Steel unifier to produce
/// equality goals discharged by SMT to relate instances of the
/// [pts_to] predicate that differ on the [p] and [v] arguments.
///
/// For instance, [pts_to r (sum_perm (half_perm p) (half_perm p)) (v + 1)]
/// is unifiable with [pts_to r p (1 + v)]
val pts_to (#a:Type)
           (r:ref a)
           ([@@@smt_fallback] p:perm)
           ([@@@smt_fallback] v:a)
  : vprop

/// Lemmas to break the abstraction, if one needs to manipulate both
/// ghost and non-ghost references. These lemmas have no SMT patterns
/// so that the normalizer or SMT won't silently unfold the
/// definitions of ref or pts_to. These should be
/// harmless since ref is erasable
val reveal_ref (#a: Type u#1) (r: ref a) : GTot (Steel.ST.HigherReference.ref a)

val hide_ref (#a: Type u#1) (r: Steel.ST.HigherReference.ref a) : Pure (ref a)
  (requires True)
  (ensures (fun r' -> reveal_ref r' == r))

val hide_reveal_ref (#a: Type u#1) (r: ref a) : Lemma
  (hide_ref (reveal_ref r) == r)

val reveal_pts_to
  (#a: _) (r: ref a) (p: perm) (x: a)
: Lemma
  (pts_to r p x `equiv` Steel.ST.HigherReference.pts_to (reveal_ref r) p x)

/// A reference can point to at most one value
val pts_to_injective_eq (#a: Type)
                        (#opened:inames)
                        (#p0 #p1:perm)
                        (#v0 #v1: a)
                        (r: ref a)
  : STGhost unit opened
      (pts_to r p0 v0 `star` pts_to r p1 v1)
      (fun _ -> pts_to r p0 v0 `star` pts_to r p1 v0)
      (requires True)
      (ensures fun _ -> v0 == v1)
                    
/// Allocating a reference returns full-permission to a non-null
/// reference pointing to the initializer [x].
///
/// We do not model memory exhaustion
val alloc (#opened: _) (#a:Type) (x:a)
  : STGhost (ref a) opened
      emp 
      (fun r -> pts_to r full_perm x)
      (requires True)
      (ensures fun r -> True)

/// Writes value `x` in the reference `r`, as long as we have full
/// ownership of `r`
val write (#opened: _) (#a:Type)
          (#v:erased a)
          (r:ref a)
          (x:a)
  : STGhostT unit opened
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm x)

/// Frees reference [r], as long as we have full ownership of [r]
val free (#opened: _) (#a:Type)
         (#v:erased a)
         (r:ref a)
  : STGhostT unit opened
    (pts_to r full_perm v) (fun _ -> emp)

/// Splits the permission on reference [r] into two. This function is
/// computationally irrelevant (it has effect SteelGhost)
val share (#a:Type)
          (#uses:_)
          (#p:perm)
          (#v:erased a)
          (r:ref a)
  : STGhostT unit uses
      (pts_to r p v)
      (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)

/// Combines permissions on reference [r]. This function is
/// computationally irrelevant (it has effect SteelGhost)
val gather (#a:Type)
           (#uses:_) 
           (#p0 p1:perm)
           (#v0 #v1:erased a)
           (r:ref a)
  : STGhost unit uses
      (pts_to r p0 v0 `star` pts_to r p1 v1)
      (fun _ -> pts_to r (sum_perm p0 p1) v0)
      (requires True)
      (ensures fun _ -> v0 == v1)
