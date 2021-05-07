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
   limitations under the License.o
*)

module Steel.SelHigherReference

open Steel.FractionalPermission
open FStar.Ghost

open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect

module Mem = Steel.Memory

val ref (a:Type u#1) : Type u#0

val null (#a:Type u#1) : ref a
val is_null (#a:Type u#1) (r:ref a) : (b:bool{b <==> r == null})

val pts_to_sl (#a:Type u#1) (r:ref a) (p:perm) (v:erased a) : slprop u#1

[@@ __steel_reduce__]
unfold let pts_to (#a:Type u#1) (r:ref a) (p:perm) (v:erased a) : vprop =
  to_vprop (pts_to_sl r p v)

val pts_to_ref_injective
      (#a: Type u#1)
      (r: ref a)
      (p0 p1:perm)
      (v0 v1: erased a)
      (m:mem)
    : Lemma
      (requires
        interp (pts_to_sl r p0 v0 `Mem.star` pts_to_sl r p1 v1) m)
      (ensures v0 == v1)

val pts_to_not_null (#a:Type u#1)
                    (x:ref a)
                    (p:perm)
                    (v: erased a)
                    (m:mem)
  : Lemma (requires interp (pts_to_sl x p v) m)
          (ensures x =!= null)

val pts_to_witinv (#a:Type) (r:ref a) (p:perm) : Lemma (is_witness_invariant (pts_to_sl r p))

val higher_ref_pts_to_injective_eq
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

val alloc (#a:Type) (x:a)
  : SteelSel (ref a) emp (fun r -> pts_to r full_perm x)
             (requires fun _ -> True)
             (ensures fun _ r _ -> not (is_null r))

val read (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelSel a (pts_to r p v) (fun x -> pts_to r p x)
           (requires fun h -> True)
           (ensures fun _ x _ -> x == Ghost.reveal v)

val read_refine (#a:Type) (#p:perm) (q:a -> vprop) (r:ref a)
  : SteelSelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)

val write (#a:Type) (#v:erased a) (r:ref a) (x:a)
  : SteelSelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm x)

val free (#a:Type) (#v:erased a) (r:ref a)
  : SteelSelT unit (pts_to r full_perm v) (fun _ -> emp)

val share (#a:Type) (#uses:_) (#p:perm) (#v:erased a) (r:ref a)
  : SteelSelGhostT unit uses
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)

val gather (#a:Type) (#uses:_) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelSelGhost unit uses
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> v0 == v1)

val cas_action (#t:Type) (eq: (x:t -> y:t -> b:bool{b <==> (x == y)}))
               (#uses:inames)
               (r:ref t)
               (v:Ghost.erased t)
               (v_old:t)
               (v_new:t)
   : action_except (b:bool{b <==> (Ghost.reveal v == v_old)})
                   uses
                   (pts_to_sl r full_perm v)
                   (fun b -> if b then pts_to_sl r full_perm v_new else pts_to_sl r full_perm v)

(*** Ghost references ***)

[@@ erasable]
val ghost_ref (a:Type u#1) : Type u#0

val ghost_pts_to_sl (#a:_) (r:ghost_ref a) (p:perm) (x:erased a) : slprop u#1

[@@ __steel_reduce__]
unfold let ghost_pts_to (#a:_) (r:ghost_ref a) (p:perm) (x:erased a) : vprop =
  to_vprop (ghost_pts_to_sl r p x)

val ghost_pts_to_witinv (#a:Type) (r:ghost_ref a) (p:perm) : Lemma (is_witness_invariant (ghost_pts_to_sl r p))

val ghost_alloc (#a:Type) (#u:_) (x:erased a)
  : SteelSelGhostT (ghost_ref a) u
                 emp
                 (fun r -> ghost_pts_to r full_perm x)

val ghost_free (#a:Type) (#u:_) (#v:erased a) (r:ghost_ref a)
  : SteelSelGhostT unit u (ghost_pts_to r full_perm v) (fun _ -> emp)

val ghost_share (#a:Type) (#u:_)
                (#p:perm)
                (#x:erased a)
                (r:ghost_ref a)
  : SteelSelGhostT unit u
    (ghost_pts_to r p x)
    (fun _ -> ghost_pts_to r (half_perm p) x `star`
           ghost_pts_to r (half_perm p) x)

val ghost_gather (#a:Type) (#u:_)
                 (#p0 #p1:perm)
                 (#x0 #x1:erased a)
                 (r:ghost_ref a)
  : SteelSelGhost unit u
    (ghost_pts_to r p0 x0 `star`
     ghost_pts_to r p1 x1)
    (fun _ -> ghost_pts_to r (sum_perm p0 p1) x0)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> x0 == x1)

val ghost_pts_to_injective_eq (#a:_) (#u:_) (#p #q:_) (r:ghost_ref a) (v0 v1:Ghost.erased a)
  : SteelSelGhost unit u
    (ghost_pts_to r p v0 `star` ghost_pts_to r q v1)
    (fun _ -> ghost_pts_to r p v0 `star` ghost_pts_to r q v0)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> v0 == v1)

val ghost_read (#a:Type) (#u:_) (#p:perm) (#v:erased a) (r:ghost_ref a)
  : SteelSelGhost (erased a) u (ghost_pts_to r p v) (fun x -> ghost_pts_to r p x)
           (requires fun _ -> True)
           (ensures fun _ x _ -> x == v)

val ghost_write (#a:Type) (#u:_) (#v:erased a) (r:ghost_ref a) (x:erased a)
  : SteelSelGhostT unit u
    (ghost_pts_to r full_perm v)
    (fun _ -> ghost_pts_to r full_perm x)
