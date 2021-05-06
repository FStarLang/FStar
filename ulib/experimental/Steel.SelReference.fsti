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

open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect

module R = Steel.Reference
open Steel.FractionalPermission

let ref (a:Type0) : Type0 = R.ref a
let ptr (#a:Type0) (r:ref a) : slprop u#1 = h_exists (R.pts_to r full_perm)

val ptr_sel (#a:Type0) (r:ref a) : selector a (ptr r)

val ptr_sel_interp (#a:Type0) (r:ref a) (m:mem) : Lemma
  (requires interp (ptr r) m)
  (ensures interp (R.pts_to r full_perm (ptr_sel r m)) m)

[@@ __steel_reduce__]
let vptr' #a r : vprop' =
  {hp = ptr r;
   t = a;
   sel = ptr_sel r}

[@@ __steel_reduce__]
unfold
let vptr r = VUnit (vptr' r)

val alloc (#a:Type0) (x:a) : SteelSel (ref a)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> h1 (vptr r) == x /\ not (R.is_null r))

val free (#a:Type0) (r:ref a) : SteelSel unit
  (vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

val read (#a:Type0) (r:ref a) : SteelSel a
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> h0 (vptr r) == h1 (vptr r) /\ x == h1 (vptr r))

val write (#a:Type0) (r:ref a) (x:a) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> x == h1 (vptr r))

val vptr_not_null (#opened: _)
  (#a: Type)
  (r: R.ref a)
: SteelSelGhost unit opened
    (vptr r)
    (fun _ -> vptr r)
    (fun _ -> True)
    (fun h0 _ h1 ->
      h1 (vptr r) == h0 (vptr r) /\
      R.is_null r == false
    )



[@@ __steel_reduce__]
let sel (#a:Type) (#p:vprop) (r:ref a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vptr r) /\ True)})
  = h (vptr r)

(*** Ghost references ***)

[@@ erasable]
let ghost_ref (a:Type u#0) : Type u#0 = R.ghost_ref a
let ghost_ptr (#a: Type0) (r: ghost_ref a) : Tot (slprop u#1) = h_exists (R.ghost_pts_to r full_perm)

val ghost_ptr_sel (#a:Type0) (r:ghost_ref a) : selector a (ghost_ptr r)

val ghost_ptr_sel_interp (#a:Type0) (r:ghost_ref a) (m:mem) : Lemma
  (requires interp (ghost_ptr r) m)
  (ensures interp (R.ghost_pts_to r Steel.FractionalPermission.full_perm (ghost_ptr_sel r m)) m)

[@@ __steel_reduce__]
let ghost_vptr' #a r : vprop' =
  {hp = ghost_ptr r;
   t = a;
   sel = ghost_ptr_sel r}

[@@ __steel_reduce__]
unfold
let ghost_vptr r = VUnit (ghost_vptr' r)

val ghost_alloc (#a:Type0) (#opened:inames) (x:Ghost.erased a) : SteelSelGhost (ghost_ref a) opened
  emp (fun r -> ghost_vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> h1 (ghost_vptr r) == Ghost.reveal x)

val ghost_free (#a:Type0) (#opened:inames) (r:ghost_ref a) : SteelSelGhost unit opened
  (ghost_vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let ghost_read (#a:Type0) (#opened:inames) (r:ghost_ref a) : SteelSelGhost (Ghost.erased a) opened
  (ghost_vptr r) (fun _ -> ghost_vptr r)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> h0 (ghost_vptr r) == h1 (ghost_vptr r) /\ Ghost.reveal x == h1 (ghost_vptr r))
= gget (ghost_vptr r)

val ghost_write (#a:Type0) (#opened:inames) (r:ghost_ref a) (x:Ghost.erased a) : SteelSelGhost unit opened
  (ghost_vptr r) (fun _ -> ghost_vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> Ghost.reveal x == h1 (ghost_vptr r))

[@@ __steel_reduce__]
let ghost_sel (#a:Type) (#p:vprop) (r:ghost_ref a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (ghost_vptr r) /\ True)})
  = h (ghost_vptr r)
