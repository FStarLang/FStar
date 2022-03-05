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

module Steel.Reference

open FStar.Ghost
open Steel.FractionalPermission

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect


module U32 = FStar.UInt32
module Mem = Steel.Memory

/// The main user-facing Steel library.
/// This library provides functions to operate on references to values in universe 0, such as uints.
/// This library provides two versions, which can interoperate with each other.
/// The first one uses the standard separation logic pts_to predicate, and has a non-informative selector
/// The second one has a selector which returns the contents of the reference in memory, enabling
/// to better separate reasoning about memory safety and functional correctness when handling references.

/// An abstract datatype for references
val ref (a:Type0) : Type0

/// The null pointer
val null (#a:Type0) : ref a

/// Checking whether a pointer is null can be done in a decidable way
val is_null (#a:Type0) (r:ref a) : (b:bool{b <==> r == null})

(** First version of references: Non-informative selector and standard pts_to predicate.
    All functions names here are postfixed with _pt (for points_to)**)

/// The standard points to separation logic assertion, expressing that
/// reference [r] is valid in memory, stores value [v], and that we have
/// permission [p] on it.
val pts_to_sl (#a:Type0) (r:ref a) (p:perm) (v:a) : slprop u#1

/// Lifting the standard points to predicate to vprop, with a non-informative selector.
/// The permission [p] and the value [v] are annotated with the smt_fallback attribute,
/// enabling SMT rewriting on them during frame inference
[@@ __steel_reduce__]
let pts_to (#a:Type0) (r:ref a) ([@@@smt_fallback] p:perm) ([@@@ smt_fallback] v:a)
  = to_vprop (pts_to_sl r p v)

/// If two pts_to predicates on the same reference [r] are valid in the memory [m],
/// then the two values [v0] and [v1] are identical
val pts_to_ref_injective
      (#a: Type u#0)
      (r: ref a)
      (p0 p1:perm)
      (v0 v1:a)
      (m:mem)
    : Lemma
      (requires
        interp (pts_to_sl r p0 v0 `Mem.star` pts_to_sl r p1 v1) m)
      (ensures v0 == v1)

/// A valid pts_to predicate implies that the pointer is not the null pointer
val pts_to_not_null (#a:Type u#0)
                    (x:ref a)
                    (p:perm)
                    (v:a)
                    (m:mem)
  : Lemma (requires interp (pts_to_sl x p v) m)
          (ensures x =!= null)

/// Exposing the is_witness_invariant from Steel.Memory for references with fractional permissions
val pts_to_witinv (#a:Type) (r:ref a) (p:perm) : Lemma (is_witness_invariant (pts_to_sl r p))

/// A stateful version of the pts_to_ref_injective lemma above
val pts_to_injective_eq
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
val alloc_pt (#a:Type) (x:a)
  : Steel (ref a) emp (fun r -> pts_to r full_perm x)
             (requires fun _ -> True)
             (ensures fun _ r _ -> not (is_null r))

/// Reads the value in reference [r], as long as it initially is valid
val read_pt (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : Steel a (pts_to r p v) (fun x -> pts_to r p x)
           (requires fun _ -> True)
           (ensures fun _ x _ -> x == Ghost.reveal v)

/// A variant of read, useful when an existentially quantified predicate
/// depends on the value stored in the reference
val read_refine_pt (#a:Type0) (#p:perm) (q:a -> vprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)

/// Writes value [x] in the reference [r], as long as we have full ownership of [r]
val write_pt (#a:Type0) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm x)

/// Frees reference [r], as long as we have full ownership of [r]
val free_pt (#a:Type0) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> emp)

/// Splits the permission on reference [r] into two.
/// This function is computationally irrelevant (it has effect SteelGhost)
val share_pt (#a:Type0) (#uses:_) (#p:perm) (#v:erased a) (r:ref a)
  : SteelGhostT unit uses
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)

/// Combines permissions on reference [r].
/// This function is computationally irrelevant (it has effect SteelGhost)
val gather_pt (#a:Type0) (#uses:_) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelGhostT (_:unit{v0 == v1}) uses
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)


/// Atomic operations, read, write, and cas
///
/// These are not polymorphic and are allowed only for small types (e.g. word-sized)
///   For now, exporting only for U32

val atomic_read_pt_u32 (#opened:_) (#p:perm) (#v:erased U32.t) (r:ref U32.t)
  : SteelAtomic U32.t opened
      (pts_to r p v)
      (fun x -> pts_to r p x)
      (requires fun _ -> True)
      (ensures fun _ x _ -> x == Ghost.reveal v)

val atomic_write_pt_u32 (#opened:_) (#v:erased U32.t) (r:ref U32.t) (x:U32.t)
  : SteelAtomicT unit opened
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm x)

val cas_pt_u32 (#uses:inames)
        (r:ref U32.t)
        (v:Ghost.erased U32.t)
        (v_old:U32.t)
        (v_new:U32.t)
  : SteelAtomicT
        (b:bool{b <==> (Ghost.reveal v == v_old)})
        uses
        (pts_to r full_perm v)
        (fun b -> if b then pts_to r full_perm v_new else pts_to r full_perm v)

val cas_pt_bool (#uses:inames)
        (r:ref bool)
        (v:Ghost.erased bool)
        (v_old:bool)
        (v_new:bool)
  : SteelAtomicT
        (b:bool{b <==> (Ghost.reveal v == v_old)})
        uses
        (pts_to r full_perm v)
        (fun b -> if b then pts_to r full_perm v_new else pts_to r full_perm v)

(** Second version of references: The memory contents are available inside the selector, instead of as an index of the predicate **)

/// An abstract separation logic predicate stating that reference [r] is valid in memory.

val ptrp (#a:Type0) (r:ref a) ([@@@smt_fallback] p: perm) : slprop u#1

[@@ __steel_reduce__; __reduce__]
unfold
let ptr (#a:Type0) (r:ref a) : slprop u#1 = ptrp r full_perm

/// A selector for references, returning the value of type [a] stored in memory

val ptrp_sel (#a:Type0) (r:ref a) (p: perm) : selector a (ptrp r p)

[@@ __steel_reduce__; __reduce__]
unfold
let ptr_sel (#a:Type0) (r:ref a) : selector a (ptr r) = ptrp_sel r full_perm

/// Some lemmas to interoperate between the two versions of references

val ptrp_sel_interp (#a:Type0) (r:ref a) (p: perm) (m:mem) : Lemma
  (requires interp (ptrp r p) m)
  (ensures interp (pts_to_sl r p (ptrp_sel r p m)) m)

let ptr_sel_interp (#a:Type0) (r:ref a) (m:mem) : Lemma
  (requires interp (ptr r) m)
  (ensures interp (pts_to_sl r full_perm (ptr_sel r m)) m)
= ptrp_sel_interp r full_perm m

val intro_ptrp_interp (#a:Type0) (r:ref a) (p: perm) (v:erased a) (m:mem) : Lemma
  (requires interp (pts_to_sl r p v) m)
  (ensures interp (ptrp r p) m)

let intro_ptr_interp (#a:Type0) (r:ref a) (v:erased a) (m:mem) : Lemma
  (requires interp (pts_to_sl r full_perm v) m)
  (ensures interp (ptr r) m)
= intro_ptrp_interp r full_perm v m

/// Combining the separation logic predicate and selector into a vprop
[@@ __steel_reduce__]
let vptr' #a r p : vprop' =
  {hp = ptrp r p;
   t = a;
   sel = ptrp_sel r p}

[@@ __steel_reduce__]
unfold
let vptrp (#a: Type) (r: ref a) ([@@@smt_fallback] p: perm) = VUnit (vptr' r p)

[@@ __steel_reduce__; __reduce__]
unfold
let vptr r = vptrp r full_perm

/// A wrapper to access a reference selector more easily.
/// Ensuring that the corresponding ptr vprop is in the context is done by
/// calling a variant of the framing tactic, as defined in Steel.Effect.Common
[@@ __steel_reduce__]
let sel (#a:Type) (#p:vprop) (r:ref a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vptr r) /\ True)})
  = h (vptr r)

/// Moving from indexed pts_to assertions to selector-based vprops and back
val intro_vptr (#a:Type) (#opened:inames) (r:ref a) (p: perm) (v:erased a)
  : SteelGhost unit opened (pts_to r p v) (fun _ -> vptrp r p)
                       (requires fun _ -> True)
                       (ensures fun _ _ h1 -> h1 (vptrp r p)  == reveal v)

val elim_vptr (#a:Type) (#opened:inames) (r:ref a) (p: perm)
  : SteelGhost (erased a) opened (vptrp r p) (fun v -> pts_to r p v)
                       (requires fun _ -> True)
                       (ensures fun h0 v _ -> reveal v == h0 (vptrp r p))


/// Allocates a reference with value [x].
val malloc (#a:Type0) (x:a) : Steel (ref a)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> sel r h1 == x /\ not (is_null r))

/// Frees a reference [r]
val free (#a:Type0) (r:ref a) : Steel unit
  (vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

/// Reads the current value of reference [r]
val readp (#a:Type0) (r:ref a) (p: perm) : Steel a
  (vptrp r p) (fun _ -> vptrp r p)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> h0 (vptrp r p) == h1 (vptrp r p) /\ x == h1 (vptrp r p))

let read (#a:Type0) (r:ref a) : Steel a
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> sel r h0 == sel r h1 /\ x == sel r h1)
= readp r full_perm

/// Writes value [x] in reference [r]
val write (#a:Type0) (r:ref a) (x:a) : Steel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> x == sel r h1)

val share (#a:Type0) (#uses:_) (#p: perm) (r:ref a)
  : SteelGhost unit uses
    (vptrp r p)
    (fun _ -> vptrp r (half_perm p) `star` vptrp r (half_perm p))
    (fun _ -> True)
    (fun h _ h' ->
      h' (vptrp r (half_perm p)) == h (vptrp r p)
    )

val gather_gen (#a:Type0) (#uses:_) (r:ref a) (p0:perm) (p1:perm)
  : SteelGhost perm uses
    (vptrp r p0 `star` vptrp r p1)
    (fun res -> vptrp r res)
    (fun _ -> True)
    (fun h res h' ->
      res == sum_perm p0 p1 /\
      h' (vptrp r res) == h (vptrp r p0) /\
      h' (vptrp r res) == h (vptrp r p1)
    )

val gather (#a: Type0) (#uses: _) (#p: perm) (r: ref a)
  : SteelGhost unit uses
      (vptrp r (half_perm p) `star` vptrp r (half_perm p))
      (fun _ -> vptrp r p)
      (fun _ -> True)
      (fun h _ h' ->
        h' (vptrp r p) == h (vptrp r (half_perm p))
      )

/// A stateful lemma variant of the pts_to_not_null lemma above.
/// This stateful function is computationally irrelevant and does not modify memory
val vptrp_not_null (#opened: _)
  (#a: Type)
  (r: ref a)
  (p: perm)
: SteelGhost unit opened
    (vptrp r p)
    (fun _ -> vptrp r p)
    (fun _ -> True)
    (fun h0 _ h1 ->
      h0 (vptrp r p) == h1 (vptrp r p) /\
      is_null r == false
    )

let vptr_not_null (#opened: _)
  (#a: Type)
  (r: ref a)
: SteelGhost unit opened
    (vptr r)
    (fun _ -> vptr r)
    (fun _ -> True)
    (fun h0 _ h1 ->
      sel r h0 == sel r h1 /\
      is_null r == false
    )
= vptrp_not_null r full_perm

(*** Ghost references ***)

/// We also define a ghost variant of references, useful to do proofs relying on a ghost state
/// Ghost references are marked as erasable, ensuring that they are computationally irrelevant,
/// and only used in computationally irrelevant contexts.
/// The functions below are variants of the reference functions defined above,
/// but operating on ghost references, and with the computationally irrelevant SteelGhost effect

[@@ erasable]
val ghost_ref (a:Type u#0) : Type u#0

(* Textbook separation logic version of ghost references *)

val ghost_pts_to_sl (#a:_) (r:ghost_ref a) (p:perm) (v:a) : slprop u#1

[@@ __steel_reduce__]
let ghost_pts_to (#a:Type0)
  (r:ghost_ref a)
  ([@@@smt_fallback] p:perm)
  ([@@@ smt_fallback] v:a)
  : vprop
  = to_vprop (ghost_pts_to_sl r p v)

val ghost_pts_to_witinv (#a:Type) (r:ghost_ref a) (p:perm)
  : Lemma (is_witness_invariant (ghost_pts_to_sl r p))

val ghost_alloc_pt (#a:Type) (#u:_) (x:erased a)
  : SteelGhostT (ghost_ref a) u
    emp
    (fun r -> ghost_pts_to r full_perm x)

val ghost_free_pt (#a:Type0) (#u:_) (#v:erased a) (r:ghost_ref a)
  : SteelGhostT unit u (ghost_pts_to r full_perm v) (fun _ -> emp)

val ghost_share_pt (#a:Type) (#u:_)
                (#p:perm)
                (#x:erased a)
                (r:ghost_ref a)
  : SteelGhostT unit u
    (ghost_pts_to r p x)
    (fun _ -> ghost_pts_to r (half_perm p) x `star`
           ghost_pts_to r (half_perm p) x)

val ghost_gather_pt (#a:Type) (#u:_)
                 (#p0 #p1:perm)
                 (#x0 #x1:erased a)
                 (r:ghost_ref a)
  : SteelGhost unit u
    (ghost_pts_to r p0 x0 `star`
     ghost_pts_to r p1 x1)
    (fun _ -> ghost_pts_to r (sum_perm p0 p1) x0)
    (requires fun _ -> true)
    (ensures fun _ _ _ -> x0 == x1)

val ghost_pts_to_injective_eq (#a:_) (#u:_) (#p #q:_) (r:ghost_ref a) (v0 v1:Ghost.erased a)
  : SteelGhost unit u
    (ghost_pts_to r p v0 `star` ghost_pts_to r q v1)
    (fun _ -> ghost_pts_to r p v0 `star` ghost_pts_to r q v0)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> v0 == v1)

val ghost_read_pt (#a:Type) (#u:_) (#p:perm) (#v:erased a) (r:ghost_ref a)
  : SteelGhost (erased a) u (ghost_pts_to r p v) (fun x -> ghost_pts_to r p x)
           (requires fun _ -> True)
           (ensures fun _ x _ -> x == v)

val ghost_write_pt (#a:Type) (#u:_) (#v:erased a) (r:ghost_ref a) (x:erased a)
  : SteelGhostT unit u
    (ghost_pts_to r full_perm v)
    (fun _ -> ghost_pts_to r full_perm x)

(* Selector version of ghost references *)

val ghost_ptrp (#a: Type0) (r: ghost_ref a) ([@@@smt_fallback] p: perm) : slprop u#1

[@@ __steel_reduce__; __reduce__]
unfold
let ghost_ptr (#a: Type0) (r: ghost_ref a) : slprop u#1
= ghost_ptrp r full_perm

val ghost_ptrp_sel (#a:Type0) (r:ghost_ref a) (p: perm) : selector a (ghost_ptrp r p)

[@@ __steel_reduce__; __reduce__]
let ghost_ptr_sel (#a:Type0) (r:ghost_ref a) : selector a (ghost_ptr r)
= ghost_ptrp_sel r full_perm

val ghost_ptrp_sel_interp (#a:Type0) (r:ghost_ref a) (p: perm) (m:mem) : Lemma
  (requires interp (ghost_ptrp r p) m)
  (ensures interp (ghost_pts_to_sl r p (ghost_ptrp_sel r p m)) m)

let ghost_ptr_sel_interp (#a:Type0) (r:ghost_ref a) (m:mem) : Lemma
  (requires interp (ghost_ptr r) m)
  (ensures interp (ghost_pts_to_sl r full_perm (ghost_ptr_sel r m)) m)
= ghost_ptrp_sel_interp r full_perm m

[@@ __steel_reduce__]
let ghost_vptr' #a r p : vprop' =
  {hp = ghost_ptrp r p;
   t = a;
   sel = ghost_ptrp_sel r p}

[@@ __steel_reduce__]
unfold
let ghost_vptrp (#a: Type) (r: ghost_ref a) ([@@@smt_fallback] p: perm) = VUnit (ghost_vptr' r p)

[@@ __steel_reduce__; __reduce__]
unfold
let ghost_vptr r = ghost_vptrp r full_perm

[@@ __steel_reduce__]
let ghost_sel (#a:Type) (#p:vprop) (r:ghost_ref a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (ghost_vptr r) /\ True)})
  = h (ghost_vptr r)

val ghost_alloc (#a:Type0) (#opened:inames) (x:Ghost.erased a)
  : SteelGhost (ghost_ref a) opened
  emp (fun r -> ghost_vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> ghost_sel r h1 == Ghost.reveal x)

val ghost_free (#a:Type0) (#opened:inames) (r:ghost_ref a) : SteelGhost unit opened
  (ghost_vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

val ghost_readp (#a:Type0) (#opened:inames) (r:ghost_ref a)
  (p: perm)
  : SteelGhost (Ghost.erased a) opened
    (ghost_vptrp r p) (fun _ -> ghost_vptrp r p)
    (requires fun _ -> True)
    (ensures fun h0 x h1 -> h0 (ghost_vptrp r p) == h1 (ghost_vptrp r p) /\ Ghost.reveal x == h1 (ghost_vptrp r p))

let ghost_read (#a:Type0) (#opened:inames) (r:ghost_ref a)
  : SteelGhost (Ghost.erased a) opened
    (ghost_vptr r) (fun _ -> ghost_vptr r)
    (requires fun _ -> True)
    (ensures fun h0 x h1 -> h0 (ghost_vptr r) == h1 (ghost_vptr r) /\ Ghost.reveal x == h1 (ghost_vptr r))
= ghost_readp r full_perm

val ghost_write (#a:Type0) (#opened:inames) (r:ghost_ref a) (x:Ghost.erased a)
  : SteelGhost unit opened
      (ghost_vptr r) (fun _ -> ghost_vptr r)
      (requires fun _ -> True)
      (ensures fun _ _ h1 -> Ghost.reveal x == h1 (ghost_vptr r))

val ghost_share (#a:Type0) (#uses:_) (#p: perm) (r:ghost_ref a)
  : SteelGhost unit uses
    (ghost_vptrp r p)
    (fun _ -> ghost_vptrp r (half_perm p) `star` ghost_vptrp r (half_perm p))
    (fun _ -> True)
    (fun h res h' ->
      h' (ghost_vptrp r (half_perm p)) == h (ghost_vptrp r p)
    )

val ghost_gather_gen (#a:Type0) (#uses:_) (r:ghost_ref a) (p0:perm) (p1:perm)
  : SteelGhost perm uses
    (ghost_vptrp r p0 `star` ghost_vptrp r p1)
    (fun res -> ghost_vptrp r res)
    (fun _ -> True)
    (fun h res h' ->
      res == sum_perm p0 p1 /\
      h' (ghost_vptrp r res) == h (ghost_vptrp r p0) /\
      h' (ghost_vptrp r res) == h (ghost_vptrp r p1)
    )

let ghost_gather (#a: Type0) (#uses: _) (#p: perm) (r: ghost_ref a)
  : SteelGhost unit uses
      (ghost_vptrp r (half_perm p) `star` ghost_vptrp r (half_perm p))
      (fun _ -> ghost_vptrp r p)
      (fun _ -> True)
      (fun h _ h' ->
        h' (ghost_vptrp r p) == h (ghost_vptrp r (half_perm p))
      )
= let _ = ghost_gather_gen r _ _ in
  change_equal_slprop
    (ghost_vptrp r _)
    (ghost_vptrp r p)
