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


module Steel.Effect.Atomic

open Steel.EffectX.Atomic
friend Steel.EffectX.Atomic
friend Steel.Effect

#set-options "--warn_error -330"  //turn off the experimental feature warning

let observability = observability
let has_eq_observability = has_eq_observability
let observable = observable
let unobservable = unobservable

let atomic_repr = atomic_repr


let return (a:Type u#a)
   (x:a)
   (opened_invariants:inames)
   (#[@@@ framing_implicit] p:a -> slprop u#1)
  : atomic_repr a opened_invariants unobservable (p x) p (return_req (p x)) (return_ens a x p)
  = fun _ -> x

#push-options "--fuel 0 --ifuel 0"

let interp_trans_left
  (o:inames)
  (p1 p2 frame:slprop)
  (m:full_mem)
  : Lemma
    (requires sl_implies p1 p2 /\
      interp (p1 `star` frame `star` locks_invariant o m) m)
    (ensures interp (p2 `star` frame `star` locks_invariant o m) m)
  = calc (equiv) {
          (p1 `star` frame `star` locks_invariant o m);
          (equiv) { star_associative p1 frame (locks_invariant o m) }
          p1 `star` (frame `star` locks_invariant o m);
    };
    calc (equiv) {
          (p2 `star` frame `star` locks_invariant o m);
          (equiv) { star_associative p2 frame (locks_invariant o m) }
          p2 `star` (frame `star` locks_invariant o m);
    }

let bind (a:Type u#a) (b:Type u#b) opened o1 o2
   #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #post #p1 #p2
   f g
 = fun frame ->
    let m0:full_mem = NMSTTotal.get() in
    let x = f frame in
    let m1:full_mem = NMSTTotal.get() in
    interp_trans_left opened (post_f x) (pre_g x) frame m1;
    let y = g x frame in
    let m2:full_mem = NMSTTotal.get() in
    interp_trans_left opened (post_g x y) (post y) frame m2;
    y

let subcomp (a:Type) opened o1 o2
  #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #p1 #p2 f
 = fun frame ->
     let m0:full_mem = NMSTTotal.get() in
     interp_trans_left opened pre_g pre_f frame m0;
     let x = f frame in
     let m1:full_mem = NMSTTotal.get () in
     interp_trans_left opened (post_f x) (post_g x) frame m1;
     x

let equiv_middle_left_assoc (a b c d:slprop)
  : Lemma (((a `star` b) `star` c `star` d) `equiv` (a `star` (b `star` c) `star` d))
  = star_associative a b c;
    star_congruence ((a `star` b) `star` c) d (a `star` (b `star` c)) d

#push-options "--z3rlimit_factor 2"
let bind_steela_steela a b opened o1 o2
  #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_f #frame_g #post #p #p2
  f g
  = fun frame ->
    let m0:full_mem = NMSTTotal.get() in
    // Initially:
    assert (interp ((pre_f `star` frame_f) `star` frame `star` locks_invariant opened m0) m0);
    // Need following assertion to execute f, by AC-rewriting
    equiv_middle_left_assoc pre_f frame_f frame (locks_invariant opened m0);
    assert (interp (pre_f `star` (frame_f `star` frame) `star` locks_invariant opened m0) m0);

    let x = f (frame_f `star` frame) in
    let m1:full_mem = NMSTTotal.get() in

    // Post-condition of executing f
    assert (interp (post_f x `star` (frame_f `star` frame) `star` locks_invariant opened m1) m1);
    // By AC-rewriting
    equiv_middle_left_assoc (post_f x) frame_f frame (locks_invariant opened m1);
    assert (interp ((post_f x `star` frame_f) `star` frame `star` locks_invariant opened m1) m1);
    // By property of sl-implies
    interp_trans_left opened (post_f x `star` frame_f) (pre_g x `star` frame_g x) frame m1;
    assert (interp ((pre_g x `star` frame_g x) `star` frame `star` locks_invariant opened m1) m1);
    // By AC-rewriting:
    equiv_middle_left_assoc (pre_g x) (frame_g x) frame (locks_invariant opened m1);
    assert (interp (pre_g x `star` (frame_g x `star` frame) `star` locks_invariant opened m1) m1);

    let y = g x (frame_g x `star` frame) in
    let m2:full_mem = NMSTTotal.get() in
    // Post-condition of executing g
    assert (interp (post_g x y `star` (frame_g x `star` frame) `star` locks_invariant opened m2) m2);
    // By AC-rewriting
    equiv_middle_left_assoc (post_g x y) (frame_g x) frame (locks_invariant opened m2);
    assert (interp ((post_g x y `star` frame_g x) `star` frame `star` locks_invariant opened m2) m2);

    interp_trans_left opened (post_g x y `star` frame_g x) (post y) frame m2;

    y
#pop-options

let bind_steela_steelaf a b opened o1 o2
  #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_f #post #p #p2 f g
  = fun frame ->
    let m0:full_mem = NMSTTotal.get() in
    // Initially
    assert (interp ((pre_f `star` frame_f) `star` frame `star` locks_invariant opened m0) m0);
    // By AC-rewriting
    equiv_middle_left_assoc pre_f frame_f frame (locks_invariant opened m0);
    assert (interp (pre_f `star` (frame_f `star` frame) `star` locks_invariant opened m0) m0);
    let x = f (frame_f `star` frame) in
    let m1:full_mem = NMSTTotal.get() in
    // Postcondition of f
    assert (interp (post_f x `star` (frame_f `star` frame) `star` locks_invariant opened m1) m1);
    // By AC-rewriting
    equiv_middle_left_assoc (post_f x) frame_f frame (locks_invariant opened m1);
    assert (interp ((post_f x `star` frame_f) `star` frame `star` locks_invariant opened m1) m1);
    // By property of sl_implies
    interp_trans_left opened (post_f x `star` frame_f) (pre_g x) frame m1;
    assert (interp (pre_g x `star` frame `star` locks_invariant opened m1) m1);
    let y = g x frame in
    let m2:full_mem = NMSTTotal.get() in
    interp_trans_left opened (post_g x y) (post y) frame m2;

    y

let bind_steelaf_steela (a:Type) (b:Type) opened o1 o2
  #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_g #post #p #p2 f g
  = fun frame ->
    let m0:full_mem = NMSTTotal.get() in
    let x = f frame in
    let m1:full_mem = NMSTTotal.get() in

    assert (interp (post_f x `star` frame `star` locks_invariant opened m1) m1);
    // By sl_implies property
    interp_trans_left opened (post_f x) (pre_g x `star` frame_g x) frame m1;
    assert (interp ((pre_g x `star` frame_g x) `star` frame `star` locks_invariant opened m1) m1);
    // By AC-rewriting
    equiv_middle_left_assoc (pre_g x) (frame_g x) frame (locks_invariant opened m1);
    assert (interp (pre_g x `star` (frame_g x `star` frame) `star` locks_invariant opened m1) m1);

    let y = g x (frame_g x `star` frame) in
    let m2:full_mem = NMSTTotal.get() in
    // Post-condition of g
    assert (interp (post_g x y `star` (frame_g x `star` frame) `star` locks_invariant opened m2) m2);
    // By AC-rewriting
    equiv_middle_left_assoc (post_g x y) (frame_g x) frame (locks_invariant opened m2);
    assert (interp ((post_g x y `star` frame_g x) `star` frame `star` locks_invariant opened m2) m2);

    interp_trans_left opened (post_g x y `star` frame_g x) (post y) frame m2;

    y

let bind_pure_steela_ (a:Type) (b:Type) opened o #wp #pre #post #req #ens f g
= fun frame ->
    let x = f () in
    g x frame

module Sems = Steel.Semantics.Hoare.MST
module Ins = Steel.Semantics.Instantiate

let bind_steelatomicf_steelf (a:Type) (b:Type) is_ghost
  #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #post #p1 #p2 f g
= fun frame ->
    let m0:full_mem = NMSTTotal.get() in
    let x = f frame in
    let m1:full_mem = NMSTTotal.get() in
    interp_trans_left Set.empty (post_f x) (pre_g x) frame m1;
    let y = g x frame in
    let m2:full_mem = NMSTTotal.get() in
    interp_trans_left Set.empty (post_g x y) (post y) frame m2;
    y

let bind_steelatomic_steelf (a:Type) (b:Type) o
  #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_f #post #p #p2 f g
= fun frame ->
    let m0:full_mem = NMST.get() in

    // By AC-rewriting
    equiv_middle_left_assoc pre_f frame_f frame (locks_invariant Set.empty m0);
    assert (interp (pre_f `star` (frame_f `star` frame) `star` locks_invariant Set.empty m0) m0);
    let x = f (frame_f `star` frame) in
    let m1:full_mem = NMST.get() in
    // Post-condition
    assert (interp (post_f x `star` (frame_f `star` frame) `star` locks_invariant Set.empty m1) m1);
    // By AC-rewriting
    equiv_middle_left_assoc (post_f x) frame_f frame (locks_invariant Set.empty m1);
    assert (interp ((post_f x `star` frame_f) `star` frame `star` locks_invariant Set.empty m1) m1);
    // Property of sl_implies
    interp_trans_left Set.empty (post_f x `star` frame_f) (pre_g x) frame m1;
    assert (interp (pre_g x `star` frame `star` locks_invariant Set.empty m1) m1);

    let y = g x frame in
    let m2:full_mem = NMST.get() in
    interp_trans_left Set.empty (post_g x y) (post y) frame m2;

    y

#push-options "--z3rlimit 50"

let bind_steelatomic_steel (a:Type) (b:Type) o
  #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_f #frame_g #post #p #p2 f g
= fun frame ->
    let m0:full_mem = NMST.get() in

    // By AC-rewriting
    equiv_middle_left_assoc pre_f frame_f frame (locks_invariant Set.empty m0);
    assert (interp (pre_f `star` (frame_f `star` frame) `star` locks_invariant Set.empty m0) m0);
    let x = f (frame_f `star` frame) in
    let m1:full_mem = NMST.get() in
    // Post-condition
    assert (interp (post_f x `star` (frame_f `star` frame) `star` locks_invariant Set.empty m1) m1);
    // By AC-rewriting
    equiv_middle_left_assoc (post_f x) frame_f frame (locks_invariant Set.empty m1);
    assert (interp ((post_f x `star` frame_f) `star` frame `star` locks_invariant Set.empty m1) m1);
    // Property of sl_implies
    interp_trans_left Set.empty (post_f x `star` frame_f) (pre_g x `star` frame_g x) frame m1;
    assert (interp ((pre_g x `star` frame_g x) `star` frame `star` locks_invariant Set.empty m1) m1);
    equiv_middle_left_assoc (pre_g x) (frame_g x) frame (locks_invariant Set.empty m1);
    assert (interp (pre_g x `star` (frame_g x `star` frame) `star` locks_invariant Set.empty m1) m1);
    let y = g x (frame_g x `star` frame) in
    let m2:full_mem = NMST.get() in


    equiv_middle_left_assoc (post_g x y) (frame_g x) frame (locks_invariant Set.empty m2);
    assert (interp ((post_g x y `star` frame_g x) `star` frame `star` locks_invariant Set.empty m2) m2);
    let aux (f_frame:Sems.fp_prop frame) : Lemma (f_frame (core_mem m0) == f_frame (core_mem m2))
      = assert (f_frame (core_mem m0) == f_frame (core_mem m1));
        let f_frame2:Sems.fp_prop (frame_g x `star` frame) = f_frame in
        assert (f_frame (core_mem m1) == f_frame (core_mem m2))
    in Classical.forall_intro aux;

    interp_trans_left Set.empty (post_g x y `star` frame_g x) (post y) frame m2;

    y

#pop-options

let subcomp_atomic_steel (a:Type) is_ghost
  #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #p1 #p2 f
  = fun frame ->
     let m0:full_mem = NMSTTotal.get() in
     interp_trans_left Set.empty pre_g pre_f frame m0;
     let x = f frame in
     let m1:full_mem = NMSTTotal.get () in
     interp_trans_left Set.empty (post_f x) (post_g x) frame m1;
     x

let as_atomic_action f = SteelAtomic?.reflect f
let new_invariant i p = SteelAtomic?.reflect (Steel.Memory.new_invariant i p)
let with_invariant #a #fp #fp' #opened i f =
  SteelAtomic?.reflect (Steel.Memory.with_invariant #a #fp #fp' #opened i (reify (f())))
let frame frame f = SteelAtomic?.reflect (Steel.Memory.frame frame (reify (f ())))
let change_slprop #opened p q proof =
  SteelAtomic?.reflect (Steel.Memory.change_slprop #opened p q proof)

let h_assert_atomic p = change_slprop p p (fun m -> ())
let h_intro_emp_l p = change_slprop p (emp `star` p) (fun m -> emp_unit p; star_commutative p emp)
let h_elim_emp_l p = change_slprop (emp `star` p) p (fun m -> emp_unit p; star_commutative p emp)
let intro_pure #_ #p q = change_slprop p (p `star` pure q) (fun m -> emp_unit p; pure_star_interp p q m)
let h_commute p q = change_slprop (p `star` q) (q `star` p) (fun m -> star_commutative p q)
let h_assoc_left p q r = change_slprop ((p `star` q) `star` r) (p `star` (q `star` r)) (fun m -> star_associative p q r)
let h_assoc_right p q r = change_slprop (p `star` (q `star` r)) ((p `star` q) `star` r) (fun m -> star_associative p q r)
let intro_h_exists x p = change_slprop (p x) (h_exists p) (fun m -> Steel.Memory.intro_h_exists x p m)
let intro_h_exists_erased x p = change_slprop (p x) (h_exists p) (fun m -> Steel.Memory.intro_h_exists (Ghost.reveal x) p m)
let h_affine p q = change_slprop (p `star` q) p (fun m -> affine_star p q m)

// open NMSTTotal
// open MSTTotal

let witness_h_exists #a #u #p s = SteelAtomic?.reflect (Steel.Memory.witness_h_exists #u p)
let lift_h_exists_atomic #a #u p = SteelAtomic?.reflect (Steel.Memory.lift_h_exists #u p)
let h_exists_cong_atomic p q = change_slprop (h_exists p) (h_exists q) (fun m -> h_exists_cong p q)
let elim_pure #uses p = SteelAtomic?.reflect (Steel.Memory.elim_pure #uses p)
