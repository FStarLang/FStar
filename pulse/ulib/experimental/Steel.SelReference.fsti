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

module Steel.SelReference

open FStar.Ghost
open Steel.FractionalPermission

open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect

module Mem = Steel.Memory

val ref (a:Type0) : Type0

val null (#a:Type0) : ref a
val is_null (#a:Type0) (r:ref a) : (b:bool{b <==> r == null})

(* Standard separation logic assertion *)

val pts_to_sl (#a:Type0) (r:ref a) (p:perm) (v:erased a) : slprop u#1

[@@ __steel_reduce__]
unfold let pts_to (#a:Type0) (r:ref a) ([@@@smt_fallback] p:perm) ([@@@ smt_fallback] v:erased a)
  = to_vprop (pts_to_sl r p v)

val pts_to_ref_injective
      (#a: Type u#0)
      (r: ref a)
      (p0 p1:perm)
      (v0 v1: erased a)
      (m:mem)
    : Lemma
      (requires
        interp (pts_to_sl r p0 v0 `Mem.star` pts_to_sl r p1 v1) m)
      (ensures v0 == v1)

val pts_to_not_null (#a:Type u#0)
                    (x:ref a)
                    (p:perm)
                    (v: erased a)
                    (m:mem)
  : Lemma (requires interp (pts_to_sl x p v) m)
          (ensures x =!= null)

val pts_to_witinv (#a:Type) (r:ref a) (p:perm) : Lemma (is_witness_invariant (pts_to_sl r p))

val pts_to_injective_eq
      (#a: Type)
      (#opened:inames)
      (#p0 #p1:perm)
      (#v0 #v1: erased a)
      (r: ref a)
  : SteelSelGhost unit opened
          (pts_to r p0 v0 `star` pts_to r p1 v1)
          (fun _ -> pts_to r p0 v0 `star` pts_to r p1 v0)
          (requires fun _ -> True)
          (ensures fun _ _ _ -> v0 == v1)

val alloc_pt (#a:Type) (x:a)
  : SteelSel (ref a) emp (fun r -> pts_to r full_perm x)
             (requires fun _ -> True)
             (ensures fun _ r _ -> not (is_null r))

val read_pt (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelSel a (pts_to r p v) (fun x -> pts_to r p x)
           (requires fun _ -> True)
           (ensures fun _ x _ -> x == Ghost.reveal v)

val read_refine_pt (#a:Type0) (#p:perm) (q:a -> vprop) (r:ref a)
  : SteelSelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)

val write_pt (#a:Type0) (#v:erased a) (r:ref a) (x:a)
  : SteelSelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm x)

val free_pt (#a:Type0) (#v:erased a) (r:ref a)
  : SteelSelT unit (pts_to r full_perm v) (fun _ -> emp)

val share_pt (#a:Type0) (#uses:_) (#p:perm) (#v:erased a) (r:ref a)
  : SteelSelGhostT unit uses
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)

val gather_pt (#a:Type0) (#uses:_) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelSelGhostT (_:unit{v0 == v1}) uses
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)

val cas_pt (#t:eqtype)
        (#uses:inames)
        (r:ref t)
        (v:Ghost.erased t)
        (v_old:t)
        (v_new:t)
  : SteelSelAtomicT
        (b:bool{b <==> (Ghost.reveal v == v_old)})
        uses
        (pts_to r full_perm v)
        (fun b -> if b then pts_to r full_perm v_new else pts_to r full_perm v)

(* Ptr version with a selector *)

(* AF: TODO: Should be indexed by a perm *)

val ptr (#a:Type0) (r:ref a) : slprop u#1

val ptr_sel (#a:Type0) (r:ref a) : selector a (ptr r)

val ptr_sel_interp (#a:Type0) (r:ref a) (m:mem) : Lemma
  (requires interp (ptr r) m)
  (ensures interp (pts_to_sl r full_perm (ptr_sel r m)) m)

[@@ __steel_reduce__]
let vptr' #a r : vprop' =
  {hp = ptr r;
   t = a;
   sel = ptr_sel r}

[@@ __steel_reduce__]
unfold
let vptr r = VUnit (vptr' r)

[@@ __steel_reduce__]
let sel (#a:Type) (#p:vprop) (r:ref a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vptr r) /\ True)})
  = h (vptr r)

val alloc (#a:Type0) (x:a) : SteelSel (ref a)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> sel r h1 == x /\ not (is_null r))

val free (#a:Type0) (r:ref a) : SteelSel unit
  (vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

val read (#a:Type0) (r:ref a) : SteelSel a
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> sel r h0 == sel r h1 /\ x == sel r h1)

val write (#a:Type0) (r:ref a) (x:a) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> x == sel r h1)

val vptr_not_null (#opened: _)
  (#a: Type)
  (r: ref a)
: SteelSelGhost unit opened
    (vptr r)
    (fun _ -> vptr r)
    (fun _ -> True)
    (fun h0 _ h1 ->
      sel r h0 == sel r h1 /\
      is_null r == false
    )

(*** Ghost references ***)

[@@ erasable]
val ghost_ref (a:Type u#0) : Type u#0

(* Textbook separation logic version of ghost references *)

val ghost_pts_to_sl (#a:_) (r:ghost_ref a) (p:perm) (v:erased a) : slprop u#1

[@@ __steel_reduce__]
unfold let ghost_pts_to (#a:Type0)
  (r:ghost_ref a)
  ([@@@smt_fallback] p:perm)
  ([@@@ smt_fallback] v:erased a)
  : vprop
  = to_vprop (ghost_pts_to_sl r p v)

val ghost_pts_to_witinv (#a:Type) (r:ghost_ref a) (p:perm)
  : Lemma (is_witness_invariant (ghost_pts_to_sl r p))

val ghost_alloc_pt (#a:Type) (#u:_) (x:erased a)
  : SteelSelGhostT (ghost_ref a) u
    emp
    (fun r -> ghost_pts_to r full_perm x)

val ghost_free_pt (#a:Type0) (#u:_) (#v:erased a) (r:ghost_ref a)
  : SteelSelGhostT unit u (ghost_pts_to r full_perm v) (fun _ -> emp)

val ghost_share_pt (#a:Type) (#u:_)
                (#p:perm)
                (#x:erased a)
                (r:ghost_ref a)
  : SteelSelGhostT unit u
    (ghost_pts_to r p x)
    (fun _ -> ghost_pts_to r (half_perm p) x `star`
           ghost_pts_to r (half_perm p) x)

val ghost_gather_pt (#a:Type) (#u:_)
                 (#p0 #p1:perm)
                 (#x0 #x1:erased a)
                 (r:ghost_ref a)
  : SteelSelGhost unit u
    (ghost_pts_to r p0 x0 `star`
     ghost_pts_to r p1 x1)
    (fun _ -> ghost_pts_to r (sum_perm p0 p1) x0)
    (requires fun _ -> true)
    (ensures fun _ _ _ -> x0 == x1)

val ghost_pts_to_injective_eq (#a:_) (#u:_) (#p #q:_) (r:ghost_ref a) (v0 v1:Ghost.erased a)
  : SteelSelGhost unit u
    (ghost_pts_to r p v0 `star` ghost_pts_to r q v1)
    (fun _ -> ghost_pts_to r p v0 `star` ghost_pts_to r q v0)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> v0 == v1)

val ghost_read_pt (#a:Type) (#u:_) (#p:perm) (#v:erased a) (r:ghost_ref a)
  : SteelSelGhost (erased a) u (ghost_pts_to r p v) (fun x -> ghost_pts_to r p x)
           (requires fun _ -> True)
           (ensures fun _ x _ -> x == v)

val ghost_write_pt (#a:Type) (#u:_) (#v:erased a) (r:ghost_ref a) (x:erased a)
  : SteelSelGhostT unit u
    (ghost_pts_to r full_perm v)
    (fun _ -> ghost_pts_to r full_perm x)

(* Selector version of ghost references *)

val ghost_ptr (#a: Type0) (r: ghost_ref a) : slprop u#1

val ghost_ptr_sel (#a:Type0) (r:ghost_ref a) : selector a (ghost_ptr r)

val ghost_ptr_sel_interp (#a:Type0) (r:ghost_ref a) (m:mem) : Lemma
  (requires interp (ghost_ptr r) m)
  (ensures interp (ghost_pts_to_sl r full_perm (ghost_ptr_sel r m)) m)

[@@ __steel_reduce__]
let ghost_vptr' #a r : vprop' =
  {hp = ghost_ptr r;
   t = a;
   sel = ghost_ptr_sel r}

[@@ __steel_reduce__]
unfold
let ghost_vptr r = VUnit (ghost_vptr' r)

[@@ __steel_reduce__]
let ghost_sel (#a:Type) (#p:vprop) (r:ghost_ref a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (ghost_vptr r) /\ True)})
  = h (ghost_vptr r)

val ghost_alloc (#a:Type0) (#opened:inames) (x:Ghost.erased a)
  : SteelSelGhost (ghost_ref a) opened
  emp (fun r -> ghost_vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> ghost_sel r h1 == Ghost.reveal x)

val ghost_free (#a:Type0) (#opened:inames) (r:ghost_ref a) : SteelSelGhost unit opened
  (ghost_vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

val ghost_read (#a:Type0) (#opened:inames) (r:ghost_ref a)
  : SteelSelGhost (Ghost.erased a) opened
    (ghost_vptr r) (fun _ -> ghost_vptr r)
    (requires fun _ -> True)
    (ensures fun h0 x h1 -> h0 (ghost_vptr r) == h1 (ghost_vptr r) /\ Ghost.reveal x == h1 (ghost_vptr r))

val ghost_write (#a:Type0) (#opened:inames) (r:ghost_ref a) (x:Ghost.erased a)
  : SteelSelGhost unit opened
      (ghost_vptr r) (fun _ -> ghost_vptr r)
      (requires fun _ -> True)
      (ensures fun _ _ h1 -> Ghost.reveal x == h1 (ghost_vptr r))
