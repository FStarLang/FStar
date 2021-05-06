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
open Steel.SelEffect.Atomic
open Steel.SelEffect
module Mem = Steel.Memory
module Eff = Steel.Effect

(* Simple Reference library, only full permissions.
   AF: Permissions would likely need to be an index of the vprop ptr.
   It cannot be part of a selector, as it is not invariant when joining with a disjoint memory
   Using the value of the ref as a selector is ok because refs with fractional permissions
   all share the same value.
   Refs on PCM are more complicated, and likely not usable with selectors
*)

val ptr_sel' (#a:Type0) (r: ref a) : selector' a (ptr r)
let ptr_sel' #a r = fun h ->
  let x = id_elim_exists #(erased a) (R.pts_to r full_perm) h in
  reveal (reveal x)

let ptr_sel_depends_only_on (#a:Type0) (r:ref a)
  (m0:Mem.hmem (ptr r)) (m1:mem{disjoint m0 m1})
  : Lemma (ptr_sel' r m0 == ptr_sel' r (Mem.join m0 m1))
  = let x = reveal (id_elim_exists #(erased a) (R.pts_to r full_perm) m0) in
    let y = reveal (id_elim_exists #(erased a) (R.pts_to r full_perm) (Mem.join m0 m1)) in
    R.pts_to_witinv r full_perm;
    elim_wi (R.pts_to r full_perm) x y (Mem.join m0 m1)

let ptr_sel_depends_only_on_core (#a:Type0) (r:ref a)
  (m0:Mem.hmem (ptr r))
  : Lemma (ptr_sel' r m0 == ptr_sel' r (core_mem m0))
  = let x = reveal (id_elim_exists #(erased a) (R.pts_to r full_perm) m0) in
    let y = reveal (id_elim_exists #(erased a) (R.pts_to r full_perm) (core_mem m0)) in
    R.pts_to_witinv r full_perm;
    elim_wi (R.pts_to r full_perm) x y (core_mem m0)

let ptr_sel r =
  Classical.forall_intro_2 (ptr_sel_depends_only_on r);
  Classical.forall_intro (ptr_sel_depends_only_on_core r);
  ptr_sel' r

let ptr_sel_interp #a r m = R.pts_to_witinv r full_perm

friend Steel.Effect
friend Steel.SelEffect

let as_steelsel0 (#a:Type)
  (#pre:pre_t) (#post:post_t a)
  (#req:prop) (#ens:a -> prop)
  ($f:Eff.repr a false (hp_of pre) (fun x -> hp_of (post x)) (fun h -> req) (fun _ x _ -> ens x))
: repr a false pre post (fun _ -> req) (fun _ x _ -> ens x)
  = fun frame -> f frame

let as_steelsel1 (#a:Type)
  (#pre:vprop) (#post:a -> vprop)
  (#req:prop) (#ens:a -> prop)
  ($f:Eff.repr a false (hp_of pre) (fun x -> hp_of (post x)) (fun h -> req) (fun _ x _ -> ens x))
: SteelSel a pre post (fun _ -> req) (fun _ x _ -> ens x)
  = SteelSel?.reflect (as_steelsel0 f)

let as_steelsel (#a:Type)
  (#pre:pre_t) (#post:post_t a)
  (#req:prop) (#ens:a -> prop)
  ($f:unit -> Eff.Steel a (hp_of pre) (fun x -> hp_of (post x)) (fun h -> req) (fun _ x _ -> ens x))
: SteelSel a pre post (fun _ -> req) (fun _ x _ -> ens x)
  = as_steelsel1 (Steel.Effect.reify_steel_comp f)

let _:squash (hp_of emp == Mem.emp /\ t_of emp == unit) = reveal_emp ()

unfold
let vptr_tmp' (#a:Type) (r:ref a) (p:perm) (v:erased a) : vprop' =
  { hp = R.pts_to r p v;
    t = unit;
    sel = fun _ -> ()}
unfold
let vptr_tmp r p v : vprop = VUnit (vptr_tmp' r p v)

val alloc0 (#a:Type0) (x:a) : SteelSel (ref a)
  emp (fun r -> vptr_tmp r full_perm x)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> True)

let alloc0 #a x = as_steelsel (fun _ -> R.alloc x)

let intro_vptr (#a:Type) (r:ref a) (v:erased a) (m:mem) : Lemma
  (requires interp (hp_of (vptr_tmp r full_perm v)) m)
  (ensures interp (hp_of (vptr r)) m /\ sel_of (vptr r) m == reveal v)
  = Mem.intro_h_exists v (R.pts_to r full_perm) m;
    R.pts_to_witinv r full_perm

let elim_vptr (#a:Type) (r:ref a) (v:erased a) (m:mem) : Lemma
  (requires interp (hp_of (vptr r)) m /\ sel_of (vptr r) m == reveal v)
  (ensures interp (hp_of (vptr_tmp r full_perm v)) m)
  = Mem.elim_h_exists (R.pts_to r full_perm) m;
    R.pts_to_witinv r full_perm

let alloc x =
  let r = alloc0 x in
  extract_info (vptr_tmp r full_perm x) () (~ (R.is_null r))
    (fun m -> R.pts_to_not_null r full_perm x m);
  change_slprop (vptr_tmp r full_perm x) (vptr r) () x (intro_vptr r x);
  return r

let free r = change_slprop_2 (vptr r) emp () intro_emp

val read0 (#a:Type0) (r:ref a) (v:erased a) : SteelSel a
  (vptr_tmp r full_perm v) (fun x -> vptr_tmp r full_perm x)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> x == reveal v)

let read0 #a r v = as_steelsel (fun _ -> R.read #a #full_perm #v r)

let read (#a:Type0) (r:ref a) : SteelSel a
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> h0 (vptr r) == h1 (vptr r) /\ x == h1 (vptr r))
  = let h0 = get() in
    let v = hide ((reveal h0) (vptr r)) in
    change_slprop (vptr r) (vptr_tmp r full_perm v) v () (elim_vptr r v);
    let x = read0 r v in
    change_slprop (vptr_tmp r full_perm x) (vptr r) () x (intro_vptr r x);
    return x

val write0 (#a:Type0) (v:erased a) (r:ref a) (x:a)
  : SteelSel unit
    (vptr_tmp r full_perm v) (fun _ -> vptr_tmp r full_perm x)
    (fun _ -> True) (fun _ _ _ -> True)

let write0 #a v r x = as_steelsel (fun _ -> R.write #a #v r x)

let write (#a:Type0) (r:ref a) (x:a) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> x == h1 (vptr r))
  = let h0 = get() in
    let v = hide ((reveal h0) (vptr r)) in
    change_slprop (vptr r) (vptr_tmp r full_perm v) v () (elim_vptr r v);
    write0 v r x;
    change_slprop (vptr_tmp r full_perm x) (vptr r) () x (intro_vptr r x)


(*** Lemmas on references *)

let vptr_not_null
  #opened #a r
= change_slprop_rel
    (vptr r)
    (vptr r)
    (fun x y -> x == y /\ R.is_null r == false)
    (fun m -> R.pts_to_not_null r full_perm (ptr_sel r m) m)

(*** Ghost pointers *)

val ghost_ptr_sel' (#a:Type0) (r: ghost_ref a) : selector' a (ghost_ptr r)
let ghost_ptr_sel' #a r = fun h ->
  let x = id_elim_exists #(erased a) (R.ghost_pts_to r full_perm) h in
  reveal (reveal x)

let ghost_ptr_sel_depends_only_on (#a:Type0) (r:ghost_ref a)
  (m0:Mem.hmem (ghost_ptr r)) (m1:mem{disjoint m0 m1})
  : Lemma (ghost_ptr_sel' r m0 == ghost_ptr_sel' r (Mem.join m0 m1))
  = let x = reveal (id_elim_exists #(erased a) (R.ghost_pts_to r full_perm) m0) in
    let y = reveal (id_elim_exists #(erased a) (R.ghost_pts_to r full_perm) (Mem.join m0 m1)) in
    R.ghost_pts_to_witinv r full_perm;
    elim_wi (R.ghost_pts_to r full_perm) x y (Mem.join m0 m1)

let ghost_ptr_sel_depends_only_on_core (#a:Type0) (r:ghost_ref a)
  (m0:Mem.hmem (ghost_ptr r))
  : Lemma (ghost_ptr_sel' r m0 == ghost_ptr_sel' r (core_mem m0))
  = let x = reveal (id_elim_exists #(erased a) (R.ghost_pts_to r full_perm) m0) in
    let y = reveal (id_elim_exists #(erased a) (R.ghost_pts_to r full_perm) (core_mem m0)) in
    R.ghost_pts_to_witinv r full_perm;
    elim_wi (R.ghost_pts_to r full_perm) x y (core_mem m0)

let ghost_ptr_sel r =
  Classical.forall_intro_2 (ghost_ptr_sel_depends_only_on r);
  Classical.forall_intro (ghost_ptr_sel_depends_only_on_core r);
  ghost_ptr_sel' r

let ghost_ptr_sel_interp #a r m = R.ghost_pts_to_witinv r full_perm

friend Steel.Effect.Atomic
friend Steel.SelEffect.Atomic
module Eff = Steel.Effect.Atomic

let as_steelselghost0 (#a:Type) (#opened: _)
  (#pre:pre_t) (#post:post_t a)
  (#req:prop) (#ens:a -> prop)
  ($f:Eff.repr a false opened Eff.Unobservable (hp_of pre) (fun x -> hp_of (post x)) (fun h -> req) (fun _ x _ -> ens x))
: Steel.SelEffect.Atomic.repr a false opened Unobservable pre post (fun _ -> req) (fun _ x _ -> ens x)
  = fun frame -> f frame

let as_steelselghost1 (#a:Type) (#opened: _)
  (#pre:vprop) (#post:a -> vprop)
  (#req:prop) (#ens:a -> prop)
  ($f:Eff.repr a false opened Eff.Unobservable (hp_of pre) (fun x -> hp_of (post x)) (fun h -> req) (fun _ x _ -> ens x))
: SteelSelGhost a opened pre post (fun _ -> req) (fun _ x _ -> ens x)
  = SteelSelGhost?.reflect (as_steelselghost0 f)

let as_steelselghost (#a:Type) (#opened: _)
  (#pre:pre_t) (#post:post_t a)
  (#req:prop) (#ens:a -> prop)
  ($f:unit -> Eff.SteelGhost a opened (hp_of pre) (fun x -> hp_of (post x)) (fun h -> req) (fun _ x _ -> ens x))
: SteelSelGhost a opened pre post (fun _ -> req) (fun _ x _ -> ens x)
  = as_steelselghost1 (Steel.Effect.Atomic.reify_steel_ghost_comp f)

unfold
let ghost_vptr_tmp' (#a:Type) (r:ghost_ref a) (p:perm) (v:erased a) : vprop' =
  { hp = R.ghost_pts_to r p v;
    t = unit;
    sel = fun _ -> ()}
unfold
let ghost_vptr_tmp r p v : vprop = VUnit (ghost_vptr_tmp' r p v)

val ghost_alloc0 (#a:Type0) (#opened: _) (x:a) : SteelSelGhost (ghost_ref a) opened
  emp (fun r -> ghost_vptr_tmp r full_perm x)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> True)

let ghost_alloc0 #a x = as_steelselghost (fun _ -> R.ghost_alloc x)

let intro_ghost_vptr (#a:Type) (r:ghost_ref a) (v:erased a) (m:mem) : Lemma
  (requires interp (hp_of (ghost_vptr_tmp r full_perm v)) m)
  (ensures interp (hp_of (ghost_vptr r)) m /\ sel_of (ghost_vptr r) m == reveal v)
  = Mem.intro_h_exists v (R.ghost_pts_to r full_perm) m;
    R.ghost_pts_to_witinv r full_perm

let elim_ghost_vptr (#a:Type) (r:ghost_ref a) (v:erased a) (m:mem) : Lemma
  (requires interp (hp_of (ghost_vptr r)) m /\ sel_of (ghost_vptr r) m == reveal v)
  (ensures interp (hp_of (ghost_vptr_tmp r full_perm v)) m)
  = Mem.elim_h_exists (R.ghost_pts_to r full_perm) m;
    R.ghost_pts_to_witinv r full_perm

let ghost_alloc x =
  let r = ghost_alloc0 (Ghost.reveal x) in
  change_slprop (ghost_vptr_tmp r full_perm (Ghost.reveal x)) (ghost_vptr r) () x (intro_ghost_vptr r x);
  r

let ghost_free r = change_slprop_rel (ghost_vptr r) emp (fun _ _ -> True) intro_emp

val ghost_write0 (#a:Type0) (#opened: _) (v:erased a) (r:ghost_ref a) (x:a)
  : SteelSelGhost unit opened
    (ghost_vptr_tmp r full_perm v) (fun _ -> ghost_vptr_tmp r full_perm x)
    (fun _ -> True) (fun _ _ _ -> True)

let ghost_write0 #a #opened v r x = as_steelselghost (fun _ -> R.ghost_write #a #opened #v r x)

let ghost_write r x
  = let v = gget (ghost_vptr r) in
    change_slprop (ghost_vptr r) (ghost_vptr_tmp r full_perm v) v () (elim_ghost_vptr r v);
    ghost_write0 v r (Ghost.reveal x);
    change_slprop (ghost_vptr_tmp r full_perm (Ghost.reveal x)) (ghost_vptr r) () x (intro_ghost_vptr r x)
