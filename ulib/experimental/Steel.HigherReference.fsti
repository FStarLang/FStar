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

module Steel.HigherReference

open Steel.FractionalPermission
open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

module Mem = Steel.Memory

/// A library for Steel references with fractional permissions, storing values at universe 1
/// Under the hood, this library builds upon the PCM-based reference memory model in
/// Steel.PCMReference, by instantiating a specific fractional permission PCM

/// An abstract datatype for references
val ref (a:Type u#1) : Type u#0

/// The null pointer
val null (#a:Type u#1) : ref a

/// Checking whether a pointer is null can be done in a decidable way
val is_null (#a:Type u#1) (r:ref a) : (b:bool{b <==> r == null})

/// The standard points to separation logic assertion, expressing that
/// reference [r] is valid in memory, stores value [v], and that we have
/// permission [p] on it.
val pts_to_sl (#a:Type u#1) (r:ref a) (p:perm) (v:a) : slprop u#1

/// Lifting the standard points to predicate to vprop, with a non-informative selector
[@@ __steel_reduce__]
unfold let pts_to (#a:Type u#1) (r:ref a) (p:perm) (v:a) : vprop =
  to_vprop (pts_to_sl r p v)

/// If two pts_to predicates on the same reference [r] are valid in the memory [m],
/// then the two values [v0] and [v1] are identical
val pts_to_ref_injective
      (#a: Type u#1)
      (r: ref a)
      (p0 p1:perm)
      (v0 v1:a)
      (m:mem)
    : Lemma
      (requires
        interp (pts_to_sl r p0 v0 `Mem.star` pts_to_sl r p1 v1) m)
      (ensures v0 == v1)

/// A valid pts_to predicate implies that the pointer is not the null pointer
val pts_to_not_null (#a:Type u#1)
                    (x:ref a)
                    (p:perm)
                    (v:a)
                    (m:mem)
  : Lemma (requires interp (pts_to_sl x p v) m)
          (ensures x =!= null)

/// Exposing the is_witness_invariant from Steel.Memory for HigherReferences
val pts_to_witinv (#a:Type) (r:ref a) (p:perm) : Lemma (is_witness_invariant (pts_to_sl r p))

/// A stateful version of the pts_to_ref_injective lemma above
val higher_ref_pts_to_injective_eq
      (#a: Type)
      (#opened:inames)
      (#p0 #p1:perm)
      (#v0 #v1: erased a)
      (r: ref a)
  : SteelGhost unit opened
          (pts_to r p0 v0 `star` pts_to r p1 v1)
          (fun _ -> pts_to r p0 v0 `star` pts_to r p1 v0)
          (requires fun _ -> True)
          (ensures fun _ _ _ -> v0 == v1)

/// Allocates a reference with value [x]. We have full permission on the newly
/// allocated reference.
val alloc (#a:Type) (x:a)
  : Steel (ref a) emp (fun r -> pts_to r full_perm x)
             (requires fun _ -> True)
             (ensures fun _ r _ -> not (is_null r))

/// Reads the value in reference [r], as long as it initially is valid
val read (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : Steel a (pts_to r p v) (fun x -> pts_to r p x)
           (requires fun h -> True)
           (ensures fun _ x _ -> x == Ghost.reveal v)

/// Atomic read
///
/// -- This is a little too powerful. We should only allow it on [t]'s
///    that are small enough. E.g., word-sized
val atomic_read (#opened:_) (#a:Type) (#p:perm) (#v:erased a)
  (r:ref a)
  : SteelAtomic a opened
      (pts_to r p v)
      (fun x -> pts_to r p x)
      (requires fun h -> True)
      (ensures fun _ x _ -> x == Ghost.reveal v)

/// A variant of read, useful when an existentially quantified predicate
/// depends on the value stored in the reference
val read_refine (#a:Type) (#p:perm) (q:a -> vprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)

/// Writes value [x] in the reference [r], as long as we have full ownership of [r]
val write (#a:Type) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm x)

/// Atomic write, also requires full ownership of [r]
///
/// -- This is a little too powerful. We should only allow it on [t]'s
///    that are small enough. E.g., word-sized
val atomic_write (#opened:_) (#a:Type) (#v:erased a) (r:ref a) (x:a)
  : SteelAtomicT unit opened (pts_to r full_perm v) (fun _ -> pts_to r full_perm x)

/// Frees reference [r], as long as we have full ownership of [r]
val free (#a:Type) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> emp)

/// Splits the permission on reference [r] into two.
/// This function is computationally irrelevant (it has effect SteelGhost)
val share (#a:Type) (#uses:_) (#p:perm) (#v:erased a) (r:ref a)
  : SteelGhostT unit uses
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)

/// Combines permissions on reference [r].
/// This function is computationally irrelevant (it has effect SteelGhost)
val gather (#a:Type) (#uses:_) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelGhost unit uses
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> v0 == v1)

/// Implementing cas as an action on references.
val cas_action (#t:Type) (eq: (x:t -> y:t -> b:bool{b <==> (x == y)}))
               (#uses:inames)
               (r:ref t)
               (v:erased t)
               (v_old:t)
               (v_new:t)
   : action_except (b:bool{b <==> (Ghost.reveal v == v_old)})
                   uses
                   (pts_to_sl r full_perm v)
                   (fun b -> if b then pts_to_sl r full_perm v_new else pts_to_sl r full_perm v)

(*** Ghost references ***)

/// We also define a ghost variant of references, useful to do proofs relying on a ghost state
/// Ghost references are marked as erasable, ensuring that they are computationally irrelevant,
/// and only used in computationally irrelevant contexts.
/// The functions below are variants of the reference functions defined above,
/// but operating on ghost references, and with the computationally irrelevant SteelGhost effect

[@@ erasable]
val ghost_ref (a:Type u#1) : Type u#0

val ghost_pts_to_sl (#a:_) (r:ghost_ref a) (p:perm) (x:a) : slprop u#1

[@@ __steel_reduce__]
unfold let ghost_pts_to (#a:_) (r:ghost_ref a) (p:perm) (x:a) : vprop =
  to_vprop (ghost_pts_to_sl r p x)

val ghost_pts_to_witinv (#a:Type) (r:ghost_ref a) (p:perm) : Lemma (is_witness_invariant (ghost_pts_to_sl r p))

val ghost_alloc (#a:Type) (#u:_) (x:erased a)
  : SteelGhostT (ghost_ref a) u
                 emp
                 (fun r -> ghost_pts_to r full_perm x)

val ghost_free (#a:Type) (#u:_) (#v:erased a) (r:ghost_ref a)
  : SteelGhostT unit u (ghost_pts_to r full_perm v) (fun _ -> emp)

val ghost_share (#a:Type) (#u:_)
                (#p:perm)
                (#x:erased a)
                (r:ghost_ref a)
  : SteelGhostT unit u
    (ghost_pts_to r p x)
    (fun _ -> ghost_pts_to r (half_perm p) x `star`
           ghost_pts_to r (half_perm p) x)

val ghost_gather (#a:Type) (#u:_)
                 (#p0 #p1:perm)
                 (#x0 #x1:erased a)
                 (r:ghost_ref a)
  : SteelGhost unit u
    (ghost_pts_to r p0 x0 `star`
     ghost_pts_to r p1 x1)
    (fun _ -> ghost_pts_to r (sum_perm p0 p1) x0)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> x0 == x1)

val ghost_pts_to_injective_eq (#a:_) (#u:_) (#p #q:_) (r:ghost_ref a) (v0 v1:Ghost.erased a)
  : SteelGhost unit u
    (ghost_pts_to r p v0 `star` ghost_pts_to r q v1)
    (fun _ -> ghost_pts_to r p v0 `star` ghost_pts_to r q v0)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> v0 == v1)

val ghost_read (#a:Type) (#u:_) (#p:perm) (#v:erased a) (r:ghost_ref a)
  : SteelGhost (erased a) u (ghost_pts_to r p v) (fun x -> ghost_pts_to r p x)
           (requires fun _ -> True)
           (ensures fun _ x _ -> x == v)

val ghost_write (#a:Type) (#u:_) (#v:erased a) (r:ghost_ref a) (x:erased a)
  : SteelGhostT unit u
    (ghost_pts_to r full_perm v)
    (fun _ -> ghost_pts_to r full_perm x)
