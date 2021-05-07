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
open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect
module Mem = Steel.Memory
module H = Steel.SelHigherReference
module U = FStar.Universe

#set-options "--ide_id_info_off"

let ref a = H.ref (U.raise_t a)

let null #a = H.null #(U.raise_t a)
let is_null #a r = H.is_null #(U.raise_t a) r

let pts_to_sl r p v = H.pts_to_sl r p (hide (U.raise_val (reveal v)))

val raise_val_inj (#a:Type) (x y:a) : Lemma
  (requires U.raise_val x == U.raise_val y)
  (ensures x == y)

let raise_val_inj x y =
  U.downgrade_val_raise_val x;
  U.downgrade_val_raise_val y


let pts_to_ref_injective
      (#a: Type u#0)
      (r: ref a)
      (p0 p1:perm)
      (v0 v1: erased a)
      (m:mem)
    : Lemma
      (requires
        interp (pts_to_sl r p0 v0 `Mem.star` pts_to_sl r p1 v1) m)
      (ensures v0 == v1)
    = let v0' = hide (U.raise_val (reveal v0)) in
      let v1' = hide (U.raise_val (reveal v1)) in
      H.pts_to_ref_injective r p0 p1 v0' v1' m;
      raise_val_inj (reveal v0) (reveal v1)

let pts_to_not_null (#a:Type u#0)
                    (x:ref a)
                    (p:perm)
                    (v: erased a)
                    (m:mem)
  : Lemma (requires interp (pts_to_sl x p v) m)
          (ensures x =!= null)
  = let v = hide (U.raise_val (reveal v)) in
    H.pts_to_not_null #(U.raise_t a) x p v m

// let pts_to_not_null' (#a:Type u#0)
//                     (x:ref a)
//                     (p:perm)
//                     (v: erased a)
//                     (m:mem)
//                     (m1:mem{disjoint m m1})
//   : Lemma (requires interp (pts_to_sl x p v) m)
//           (ensures interp (pts_to_sl x p v) (Mem.join m m1))
//   = ()


let pts_to_witinv (#a:Type) (r:ref a) (p:perm) : Lemma (is_witness_invariant (pts_to_sl r p)) =
  let aux (x y : erased a) (m:mem)
    : Lemma (requires (interp (pts_to_sl r p x) m /\ interp (pts_to_sl r p y) m))
            (ensures  (x == y))
    = H.pts_to_witinv r p;
      raise_val_inj (reveal x) (reveal y)
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (aux x y))

let pts_to_injective_eq #a #opened #p0 #p1 #v0 #v1 r =
  extract_info_raw (pts_to r p0 v0 `star` pts_to r p1 v1) (v0 == v1)
    (fun m -> pts_to_ref_injective r p0 p1 v0 v1 m);
  rewrite_slprop (pts_to r p1 v1) (pts_to r p1 v0) (fun _ -> ())

let alloc_pt x =
  let r = H.alloc (U.raise_val x) in
  rewrite_slprop (H.pts_to r full_perm (U.raise_val x)) (pts_to r full_perm x) (fun _ -> ());
  return r

let read_pt #a #p #v r =
  let v' = Ghost.hide (U.raise_val (Ghost.reveal v)) in
  rewrite_slprop (pts_to r p v) (H.pts_to r p v') (fun _ -> ());
  let x = H.read r in
  let v':a = U.downgrade_val x in
  rewrite_slprop (H.pts_to r p (hide x)) (pts_to r p v') (fun _ -> ());
  return v'

let read_refine_pt #a #p q r =
  Classical.forall_intro_2 reveal_equiv;
  lift_exists (fun (v:a) -> pts_to r p v `star` q v);
  exists_cong (fun (v:U.raise_t a) -> pts_to r p (U.downgrade_val v) `star` q (U.downgrade_val v))
                (fun (v:U.raise_t a) -> H.pts_to r p v `star` U.lift_dom q v);
  let x = H.read_refine (U.lift_dom q) r in
  rewrite_slprop
    (H.pts_to r p (hide x) `star` U.lift_dom q x)
    (pts_to r p (U.downgrade_val x) `star` q (U.downgrade_val x)) (fun _ -> ());

  return (U.downgrade_val x)

let write_pt #a #v r x =
  let v' = Ghost.hide (U.raise_val (Ghost.reveal v)) in
  rewrite_slprop (pts_to r full_perm v) (H.pts_to r full_perm v') (fun _ -> ());
  let x' = U.raise_val x in
  H.write r x';
  rewrite_slprop (H.pts_to r full_perm (hide x')) (pts_to r full_perm x) (fun _ -> ())

let free_pt #a #v r =
  let v' = Ghost.hide (U.raise_val (Ghost.reveal v)) in
  rewrite_slprop (pts_to r full_perm v) (H.pts_to r full_perm v') (fun _ -> ());
  H.free r

let share_pt #a #uses #p #v r =
  let v' = Ghost.hide (U.raise_val (Ghost.reveal v)) in
  rewrite_slprop (pts_to r p v) (H.pts_to r p v') (fun _ -> ());
  H.share r;
  rewrite_slprop (H.pts_to r (half_perm p) v') (pts_to r (half_perm p) v) (fun _ -> ());
  rewrite_slprop (H.pts_to r (half_perm p) v') (pts_to r (half_perm p) v) (fun _ -> ())

let hide_raise_reveal (#a:Type) (v0:erased a) (v1:erased a)
  : Lemma (hide (U.raise_val (reveal v0)) == hide (U.raise_val (reveal v1)) <==>
           v0 == v1)
           [SMTPat (hide (U.raise_val (reveal v0)));
            SMTPat (hide (U.raise_val (reveal v1)))]
  = let u0 = hide (U.raise_val (reveal v0)) in
    let u1 = hide (U.raise_val (reveal v1)) in
    assert (U.downgrade_val (U.raise_val (reveal v0)) == U.downgrade_val (U.raise_val (reveal v1)) <==>
            v0 == v1)

let gather_pt #a #uses #p0 #p1 #v0 #v1 r =
  let v0' = Ghost.hide (U.raise_val (Ghost.reveal v0)) in
  let v1' = Ghost.hide (U.raise_val (Ghost.reveal v1)) in
  rewrite_slprop (pts_to r p0 v0) (H.pts_to r p0 v0') (fun _ -> ());
  rewrite_slprop (pts_to r p1 v1) (H.pts_to r p1 v1') (fun _ -> ());
  let (u:unit{v0' == v1'}) = H.gather #_ #_ #p0 #p1 #v0' #v1' r in
  rewrite_slprop (H.pts_to r (sum_perm p0 p1) v0') (pts_to r (sum_perm p0 p1) v0) (fun _ -> ());
  u

let raise_equiv (#t:Type) (x y:t)
  : Lemma (U.raise_val x == U.raise_val y <==>
           x == y)
  = assert (U.downgrade_val (U.raise_val x) == x);
    assert (U.downgrade_val (U.raise_val y) == y)


let downgrade_equiv (#t:Type) (x y:U.raise_t t)
  : Lemma (U.downgrade_val x == U.downgrade_val y <==>
           x == y)
  = assert (U.raise_val (U.downgrade_val x) == x);
    assert (U.raise_val (U.downgrade_val y) == y)

let lift_eq (#t:eqtype) (x y:U.raise_t t)
  : b:bool{b <==> x==y}
  = downgrade_equiv x y; U.downgrade_val x = U.downgrade_val y


let cas_action (#t:eqtype)
               (#uses:inames)
               (r:ref t)
               (v:Ghost.erased t)
               (v_old:t)
               (v_new:t)
               (frame:slprop)
   : MstTot (b:bool{b <==> (Ghost.reveal v == v_old)})
             uses
            (pts_to_sl r full_perm v)
            (fun b -> if b then pts_to_sl r full_perm v_new else pts_to_sl r full_perm v)
            frame
            (fun _ -> True)
            (fun _ _ _ -> True)
   = let hv =     (Ghost.hide (U.raise_val (Ghost.reveal v))) in
     let b = H.cas_action #(U.raise_t t)
                  (lift_eq #t)
                  #uses
                  r
                  hv
                  (U.raise_val v_old)
                  (U.raise_val v_new)
                  frame
     in
     assert (b <==> (Ghost.reveal hv == U.raise_val v_old));
     assert (b <==> U.raise_val (Ghost.reveal v) == U.raise_val v_old);
     raise_equiv (Ghost.reveal v) v_old;
     b

let cas_pt #t #uses r v v_old v_new =
  let b = as_atomic_action (cas_action #t #uses r v v_old v_new) in
  rewrite_slprop (to_vprop (if b then pts_to_sl r full_perm v_new else pts_to_sl r full_perm v))
                 (if b then pts_to r full_perm v_new else pts_to r full_perm v)
                 (fun _ -> ());
  return b

(* Simple Reference library, only full permissions.
   AF: Permissions would likely need to be an index of the vprop ptr.
   It cannot be part of a selector, as it is not invariant when joining with a disjoint memory
   Using the value of the ref as a selector is ok because refs with fractional permissions
   all share the same value.
   Refs on PCM are more complicated, and likely not usable with selectors
*)

let ptr r = Mem.h_exists (pts_to_sl r full_perm)

val ptr_sel' (#a:Type0) (r: ref a) : selector' a (ptr r)
let ptr_sel' #a r = fun h ->
  let x = id_elim_exists #(erased a) (pts_to_sl r full_perm) h in
  reveal (reveal x)

let join_preserves_interp (hp:slprop) (m0:hmem hp) (m1:mem{disjoint m0 m1})
: Lemma
  (interp hp (join m0 m1))
  [SMTPat (interp hp (join m0 m1))]
= let open Steel.Memory in
  intro_emp m1;
  intro_star hp emp m0 m1;
  affine_star hp emp (join m0 m1)

let ptr_sel_depends_only_on (#a:Type0) (r:ref a)
  (m0:Mem.hmem (ptr r)) (m1:mem{disjoint m0 m1})
  : Lemma (ptr_sel' r m0 == ptr_sel' r (Mem.join m0 m1))
  = let x = reveal (id_elim_exists #(erased a) (pts_to_sl r full_perm) m0) in
    let y = reveal (id_elim_exists #(erased a) (pts_to_sl r full_perm) (Mem.join m0 m1)) in
    pts_to_witinv r full_perm;
    elim_wi (pts_to_sl r full_perm) x y (Mem.join m0 m1)

let ptr_sel_depends_only_on_core (#a:Type0) (r:ref a)
  (m0:Mem.hmem (ptr r))
  : Lemma (ptr_sel' r m0 == ptr_sel' r (core_mem m0))
  = let x = reveal (id_elim_exists #(erased a) (pts_to_sl r full_perm) m0) in
    let y = reveal (id_elim_exists #(erased a) (pts_to_sl r full_perm) (core_mem m0)) in
    pts_to_witinv r full_perm;
    elim_wi (pts_to_sl r full_perm) x y (core_mem m0)

let ptr_sel r =
  Classical.forall_intro_2 (ptr_sel_depends_only_on r);
  Classical.forall_intro (ptr_sel_depends_only_on_core r);
  ptr_sel' r

let ptr_sel_interp #a r m = pts_to_witinv r full_perm

let intro_vptr_lemma (#a:Type) (r:ref a) (v:erased a) (m:mem) : Lemma
  (requires interp (pts_to_sl r full_perm v) m)
  (ensures interp (ptr r) m /\ ptr_sel r m == reveal v)
  = Mem.intro_h_exists v (pts_to_sl r full_perm) m;
    pts_to_witinv r full_perm

let elim_vptr_lemma (#a:Type) (r:ref a) (v:erased a) (m:mem) : Lemma
  (requires interp (ptr r) m /\ ptr_sel r m == reveal v)
  (ensures interp (pts_to_sl r full_perm v) m)
  = Mem.elim_h_exists (pts_to_sl r full_perm) m;
    pts_to_witinv r full_perm

let intro_vptr (#a:Type) (#opened:inames) (r:ref a) (v:erased a)
  : SteelSelGhost unit opened (pts_to r full_perm v) (fun _ -> vptr r)
                       (requires fun _ -> True)
                       (ensures fun _ _ h1 -> sel r h1 == reveal v)
  = change_slprop_2 (pts_to r full_perm v) (vptr r) v (intro_vptr_lemma r v)

let elim_vptr (#a:Type) (#opened:inames) (r:ref a)
  : SteelSelGhost (erased a) opened (vptr r) (fun v -> pts_to r full_perm v)
                       (requires fun _ -> True)
                       (ensures fun h0 v _ -> reveal v == sel r h0)
  = let v = gget (vptr r) in
    change_slprop (vptr r) (pts_to r full_perm v) v () (elim_vptr_lemma r v);
    v

let alloc x =
  let r = alloc_pt x in
  intro_vptr r (hide x);
  return r

let free r =
  let _ = elim_vptr r in
  free_pt r

let read r =
  let _ = elim_vptr r in
  let x = read_pt r in
  intro_vptr r x;
  return x

let write r x =
  let _ = elim_vptr r in
  write_pt r x;
  intro_vptr r x

(*** Lemmas on references *)

let vptr_not_null
  #opened #a r
= change_slprop_rel
    (vptr r)
    (vptr r)
    (fun x y -> x == y /\ is_null r == false)
    (fun m -> pts_to_not_null r full_perm (ptr_sel r m) m)

(*** Ghost pointers *)

(*** GHOST REFERENCES ***)
let ghost_ref a = H.ghost_ref (U.raise_t a)

let raise_erased (#a:Type0) (x:erased a)
  : erased (U.raise_t u#0 u#1 a)
  = Ghost.hide (U.raise_val (Ghost.reveal x))

[@__reduce__]
let ghost_pts_to_sl #a r p x = H.ghost_pts_to_sl #(U.raise_t a) r p (raise_erased x)

let ghost_pts_to_witinv (#a:Type) (r:ghost_ref a) (p:perm) : Lemma (is_witness_invariant (ghost_pts_to_sl r p)) =
  let aux (x y : erased a) (m:mem)
    : Lemma (requires (interp (ghost_pts_to_sl r p x) m /\ interp (ghost_pts_to_sl r p y) m))
            (ensures  (x == y))
    = H.ghost_pts_to_witinv r p;
      raise_val_inj (reveal x) (reveal y)
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (aux x y))

let ghost_alloc_pt (#a:Type) (#u:_) (x:erased a)
  : SteelSelGhostT (ghost_ref a) u
    emp
    (fun r -> ghost_pts_to r full_perm x)
  = H.ghost_alloc (raise_erased x)

let ghost_free_pt r = H.ghost_free r

let ghost_share_pt (#a:Type) (#u:_)
                (#p:perm)
                (#x:erased a)
                (r:ghost_ref a)
   = H.ghost_share r

let ghost_gather_pt (#a:Type) (#u:_)
                 (#p0 #p1:perm)
                 (#x0 #x1:erased a)
                 (r:ghost_ref a)
  : SteelSelGhost unit u
    (ghost_pts_to r p0 x0 `star`
     ghost_pts_to r p1 x1)
    (fun _ -> ghost_pts_to r (sum_perm p0 p1) x0)
    (requires fun _ -> true)
    (ensures fun _ _ _ -> x0 == x1)
  = H.ghost_gather r

let ghost_pts_to_injective_eq (#a:_) (#u:_) (#p #q:_) (r:ghost_ref a) (v0 v1:Ghost.erased a)
  : SteelSelGhost unit u
    (ghost_pts_to r p v0 `star` ghost_pts_to r q v1)
    (fun _ -> ghost_pts_to r p v0 `star` ghost_pts_to r q v0)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> v0 == v1)
  = H.ghost_pts_to_injective_eq r (raise_erased v0) (raise_erased v1)

let ghost_read_pt #a #u #p #v r =
  let x = H.ghost_read r in
  let x' = hide (U.downgrade_val (reveal x)) in
  rewrite_slprop (H.ghost_pts_to r p x) (ghost_pts_to r p x') (fun _ -> ());
  x'

let ghost_write_pt (#a:Type) (#u:_) (#v:erased a) (r:ghost_ref a) (x:erased a)
  : SteelSelGhostT unit u
    (ghost_pts_to r full_perm v)
    (fun _ -> ghost_pts_to r full_perm x)
  = H.ghost_write r (raise_erased x)

(* Selector version of ghost pointers *)

let ghost_ptr r = Mem.h_exists (ghost_pts_to_sl r full_perm)

val ghost_ptr_sel' (#a:Type0) (r: ghost_ref a) : selector' a (ghost_ptr r)
let ghost_ptr_sel' #a r = fun h ->
  let x = id_elim_exists #(erased a) (ghost_pts_to_sl r full_perm) h in
  reveal (reveal x)

let ghost_ptr_sel_depends_only_on (#a:Type0) (r:ghost_ref a)
  (m0:Mem.hmem (ghost_ptr r)) (m1:mem{disjoint m0 m1})
  : Lemma (ghost_ptr_sel' r m0 == ghost_ptr_sel' r (Mem.join m0 m1))
  = let x = reveal (id_elim_exists #(erased a) (ghost_pts_to_sl r full_perm) m0) in
    let y = reveal (id_elim_exists #(erased a) (ghost_pts_to_sl r full_perm) (Mem.join m0 m1)) in
    ghost_pts_to_witinv r full_perm;
    elim_wi (ghost_pts_to_sl r full_perm) x y (Mem.join m0 m1)

let ghost_ptr_sel_depends_only_on_core (#a:Type0) (r:ghost_ref a)
  (m0:Mem.hmem (ghost_ptr r))
  : Lemma (ghost_ptr_sel' r m0 == ghost_ptr_sel' r (core_mem m0))
  = let x = reveal (id_elim_exists #(erased a) (ghost_pts_to_sl r full_perm) m0) in
    let y = reveal (id_elim_exists #(erased a) (ghost_pts_to_sl r full_perm) (core_mem m0)) in
    ghost_pts_to_witinv r full_perm;
    elim_wi (ghost_pts_to_sl r full_perm) x y (core_mem m0)

let ghost_ptr_sel r =
  Classical.forall_intro_2 (ghost_ptr_sel_depends_only_on r);
  Classical.forall_intro (ghost_ptr_sel_depends_only_on_core r);
  ghost_ptr_sel' r

let ghost_ptr_sel_interp #a r m = ghost_pts_to_witinv r full_perm


let intro_ghost_vptr_lemma (#a:Type) (r:ghost_ref a) (v:erased a) (m:mem) : Lemma
  (requires interp (ghost_pts_to_sl r full_perm v) m)
  (ensures interp (ghost_ptr r) m /\ ghost_ptr_sel r m == reveal v)
  = Mem.intro_h_exists v (ghost_pts_to_sl r full_perm) m;
    ghost_pts_to_witinv r full_perm

let elim_ghost_vptr_lemma (#a:Type) (r:ghost_ref a) (v:erased a) (m:mem) : Lemma
  (requires interp (ghost_ptr r) m /\ ghost_ptr_sel r m == reveal v)
  (ensures interp (ghost_pts_to_sl r full_perm v) m)
  = Mem.elim_h_exists (ghost_pts_to_sl r full_perm) m;
    ghost_pts_to_witinv r full_perm

let intro_ghost_vptr (#a:Type) (#opened:inames) (r:ghost_ref a) (v:erased a)
  : SteelSelGhost unit opened (ghost_pts_to r full_perm v) (fun _ -> ghost_vptr r)
                       (requires fun _ -> True)
                       (ensures fun _ _ h1 -> ghost_sel r h1 == reveal v)
  = change_slprop_2 (ghost_pts_to r full_perm v) (ghost_vptr r) v (intro_ghost_vptr_lemma r v)

let elim_ghost_vptr (#a:Type) (#opened:inames) (r:ghost_ref a)
  : SteelSelGhost (erased a) opened (ghost_vptr r) (fun v -> ghost_pts_to r full_perm v)
                       (requires fun _ -> True)
                       (ensures fun h0 v _ -> reveal v == ghost_sel r h0)
  = let v = gget (ghost_vptr r) in
    change_slprop (ghost_vptr r) (ghost_pts_to r full_perm v) v () (elim_ghost_vptr_lemma r v);
    v

let ghost_alloc x =
  let r = ghost_alloc_pt x in
  intro_ghost_vptr r x;
  r

let ghost_free r =
  let _ = elim_ghost_vptr r in
  ghost_free_pt r

let ghost_read r =
  let _ = elim_ghost_vptr r in
  let x = ghost_read_pt r in
  intro_ghost_vptr r x;
  x

let ghost_write r x =
  let _ = elim_ghost_vptr r in
  ghost_write_pt r x;
  intro_ghost_vptr r x
