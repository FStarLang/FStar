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

let observability = observability
let has_eq_observability = has_eq_observability
let observable = observable
let unobservable = unobservable

let atomic_repr = atomic_repr


let return (a:Type u#a)
   (x:a)
   (opened_invariants:inames)
   (#[@@ framing_implicit] p:a -> slprop u#1)
  : atomic_repr a opened_invariants unobservable (p x) p
  = fun _ -> x

#push-options "--fuel 0 --ifuel 0"

let preserves_frame_trans_equiv
      (o:inames)
      (pre p1 p2 post:slprop)
      (m0 m1 m2:full_mem)
    : Lemma
      (requires sl_implies p1 p2 /\
        preserves_frame o pre p1 m0 m1 /\
        preserves_frame o p2 post m1 m2)
      (ensures preserves_frame o pre post m0 m2)
    =
    let aux (frame:slprop)
      : Lemma
        (requires interp ((pre `star` frame) `star` locks_invariant o m0) m0)
        (ensures
          interp ((post `star` frame) `star` locks_invariant o m2) m2 /\
          (forall (f_frame:mprop frame). f_frame (core_mem m0) == f_frame (core_mem m2)))
        [SMTPat ()]
      = assert (interp ((p1 `star` frame) `star` locks_invariant o m1) m1);
        calc (equiv) {
          ((p1 `star` frame) `star` locks_invariant o m1);
          (equiv) { star_associative p1 frame (locks_invariant o m1) }
          p1 `star` (frame `star` locks_invariant o m1);
        };
        calc (equiv) {
          (p2 `star` (frame `star` locks_invariant o m1));
          (equiv) { star_associative p2 frame (locks_invariant o m1) }
          (p2 `star` frame) `star` locks_invariant o m1;
        };
        assert (interp ((p2 `star` frame) `star` locks_invariant o m1) m1);
        assert (interp ((post `star` frame) `star` locks_invariant o m2) m2)
  in
  ()

let bind (a:Type u#a) (b:Type u#b)
   (opened:inames)
   (o1:observability)
   (o2:observability)
   (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
   (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
   (#[@@ framing_implicit] p:squash (can_be_split_forall post_f pre_g))
   (f:atomic_repr a opened o1 pre_f post_f)
   (g:(x:a -> atomic_repr b opened o2 (pre_g x) post_g))
  : Pure (atomic_repr b opened (join_obs o1 o2) pre_f post_g)
         (requires obs_at_most_one o1 o2)
         (ensures fun _ -> True)
  = fun _ ->
    let m0:full_mem = NMSTTotal.get() in
    let x = f () in
    let m1:full_mem = NMSTTotal.get() in
    let y = g x () in
    let m2:full_mem = NMSTTotal.get() in
    preserves_frame_trans_equiv opened pre_f (post_f x) (pre_g x) (post_g y) m0 m1 m2;
    y

let subcomp (a:Type)
  (opened:inames)
  (o1:observability)
  (o2:observability)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:pre_t) (#[@@ framing_implicit] post_g:post_t a)
  (#[@@ framing_implicit] p1:squash (delay (can_be_split pre_g pre_f)))
  (#[@@ framing_implicit] p2:squash (annot_sub_post (can_be_split_forall post_f post_g)))
  (f:atomic_repr a opened o1 pre_f post_f)
: Pure (atomic_repr a opened o2 pre_g post_g)
       (requires o1 == observable ==> o2 == observable)
       (ensures fun _ -> True)
 = fun _ ->
     let m0:full_mem = NMSTTotal.get() in
     let x = f () in
     let m1:full_mem = NMSTTotal.get () in
     preserves_frame_trans_equiv opened pre_g pre_g pre_f (post_f x) m0 m0 m1;
     preserves_frame_trans_equiv opened pre_g (post_f x) (post_g x) (post_g x) m0 m1 m1;
     x

let preserves_frame_extend
      (o:inames)
      (pre post f:slprop)
      (m0 m1:full_mem)
    : Lemma
      (requires
        preserves_frame o pre post m0 m1)
      (ensures preserves_frame o (pre `star` f) (post `star` f) m0 m1)
    = let aux (frame:slprop)
      : Lemma
        (requires interp (((pre `star` f) `star` frame) `star` locks_invariant o m0) m0)
        (ensures
          interp (((post `star` f) `star` frame) `star` locks_invariant o m1) m1 /\
          (forall (f_frame:mprop frame). f_frame (core_mem m0) == f_frame (core_mem m1)))
        [SMTPat ()]
      = calc (equiv) {
          ((pre `star` f) `star` frame) `star` locks_invariant o m0;
          (equiv) { star_associative pre f frame;
                    star_congruence ((pre `star` f) `star` frame) (locks_invariant o m0)
                      (pre `star` (f `star` frame)) (locks_invariant o m0)
                    }
          (pre `star` (f `star` frame)) `star` locks_invariant o m0;
        };
        assert (interp ((post `star` (f `star` frame)) `star` locks_invariant o m1) m1);
        calc (equiv) {
          (post `star` (f `star` frame)) `star` locks_invariant o m1;
          (equiv) { star_associative post f frame;
                    star_congruence ((post `star` f) `star` frame) (locks_invariant o m1)
                      (post `star` (f `star` frame)) (locks_invariant o m1) }
          ((post `star` f) `star` frame) `star` locks_invariant o m1;
        };
        assert (interp (((post `star` f) `star` frame) `star` locks_invariant o m1) m1);
        calc (equiv) {
          ((pre `star` f) `star` frame) `star` locks_invariant o m0;
          (equiv) {
            star_commutative pre f;
            star_congruence (pre `star` f) frame (f `star` pre) frame;
            star_congruence
               ((pre `star` f) `star` frame) (locks_invariant o m0)
               ((f `star` pre) `star` frame) (locks_invariant o m0)
          }
          ((f `star` pre) `star` frame) `star` locks_invariant o m0;
          (equiv) {
            star_associative f pre frame;
            star_congruence
               ((f `star` pre) `star` frame) (locks_invariant o m0)
               (f `star` (pre `star` frame)) (locks_invariant o m0)
            }
          (f `star` (pre `star` frame)) `star` locks_invariant o m0;
          (equiv) {
            star_associative f (pre `star` frame) (locks_invariant o m0);
            star_commutative f ((pre `star` frame) `star` locks_invariant o m0) }
          ((pre `star` frame) `star` locks_invariant o m0) `star` f;
        };
        affine_star ((pre `star` frame) `star` locks_invariant o m0) f m0;
        assert (interp ((pre `star` frame) `star` locks_invariant o m0) m0)
  in
  ()

let interp_affine_middle (p q r:slprop) (m:full_mem)
  : Lemma (requires interp ((p `star` q) `star` r) m)
          (ensures interp (p `star` r) m)
  = calc (equiv) {
         (p `star` q) `star` r;
         (equiv) {
           star_commutative p q;
           star_congruence (p `star` q) r (q `star` p) r }
         (q `star` p) `star` r;
         (equiv) { star_associative q p r }
         q `star` (p `star` r);
     };
     affine_star q (p `star` r) m

let bind_steela_steela (a:Type) (b:Type)
  (opened:inames)
  (o1:observability)
  (o2:observability)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
  (#[@@ framing_implicit] frame_f:slprop) (#[@@ framing_implicit] frame_g:slprop)
  (#[@@ framing_implicit] p:squash (can_be_split_forall
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g)))
  (f:atomic_repr a opened o1 pre_f post_f)
  (g:(x:a -> atomic_repr b opened o2 (pre_g x) post_g))
: Pure (atomic_repr b opened (join_obs o1 o2)
    (pre_f `star` frame_f)
    (fun y -> post_g y `star` frame_g))
    (requires obs_at_most_one o1 o2)
    (ensures fun _ -> True)
  = fun _ ->
    let m0:full_mem = NMSTTotal.get() in
    assert (interp ((pre_f `star` frame_f) `star` locks_invariant opened m0) m0);
    interp_affine_middle pre_f frame_f (locks_invariant opened m0) m0;
    let x = f () in
    let m1:full_mem = NMSTTotal.get() in
    assert (interp ((post_f x `star` frame_f) `star` locks_invariant opened m1) m1);
    assert (interp ((pre_g x `star` frame_g) `star` locks_invariant opened m1) m1);
    interp_affine_middle (pre_g x) frame_g (locks_invariant opened m1) m1;
    let y = g x () in
    let m2:full_mem = NMSTTotal.get() in
    preserves_frame_extend opened pre_f (post_f x) frame_f m0 m1;
    preserves_frame_extend opened (pre_g x) (post_g y) frame_g m1 m2;
    preserves_frame_trans_equiv opened
      (pre_f `star` frame_f) (post_f x `star` frame_f)
      (pre_g x `star` frame_g) (post_g y `star` frame_g) m0 m1 m2;
    y

let bind_steela_steelaf (a:Type) (b:Type)
  (opened:inames)
  (o1:observability)
  (o2:observability)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
  (#[@@ framing_implicit] frame_f:slprop)
  (#[@@ framing_implicit] p:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (f:atomic_repr a opened o1 pre_f post_f)
  (g:(x:a -> atomic_repr b opened o2 (pre_g x) post_g))
: Pure (atomic_repr b opened (join_obs o1 o2)
         (pre_f `star` frame_f)
         post_g)
       (requires obs_at_most_one o1 o2)
       (ensures fun _ -> True)
  = fun _ ->
    let m0:full_mem = NMSTTotal.get() in
    interp_affine_middle pre_f frame_f (locks_invariant opened m0) m0;
    let x = f () in
    let m1:full_mem = NMSTTotal.get() in
    let y = g x () in
    let m2:full_mem = NMSTTotal.get() in
    preserves_frame_extend opened pre_f (post_f x) frame_f m0 m1;
    preserves_frame_trans_equiv opened
      (pre_f `star` frame_f) (post_f x `star` frame_f)
      (pre_g x) (post_g y) m0 m1 m2;
    y

let bind_steelaf_steela (a:Type) (b:Type)
  (opened:inames)
  (o1:observability)
  (o2:observability)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
  (#[@@ framing_implicit] frame_g:slprop)
  (#[@@ framing_implicit] p:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g)))
  (f:atomic_repr a opened o1 pre_f post_f)
  (g:(x:a -> atomic_repr b opened o2 (pre_g x) post_g))
: Pure (atomic_repr b opened (join_obs o1 o2)
        pre_f
        (fun y -> post_g y `star` frame_g))
    (requires obs_at_most_one o1 o2)
    (ensures fun _ -> True)
  = fun _ ->
    let m0:full_mem = NMSTTotal.get() in
    let x = f () in
    let m1:full_mem = NMSTTotal.get() in
    interp_affine_middle (pre_g x) frame_g (locks_invariant opened m1) m1;
    let y = g x () in
    let m2:full_mem = NMSTTotal.get() in
    preserves_frame_extend opened (pre_g x) (post_g y) frame_g m1 m2;
    preserves_frame_trans_equiv opened
      pre_f (post_f x)
      (pre_g x `star` frame_g) (post_g y `star` frame_g) m0 m1 m2;
    y

let bind_pure_steela_ (a:Type) (b:Type)
  (opened_invariants:inames)
  (o:observability)
  (wp:pure_wp a)
  (#[@@ framing_implicit] pre:pre_t) (#[@@ framing_implicit] post:post_t b)
  (f:eqtype_as_type unit -> PURE a wp) (g:(x:a -> atomic_repr b opened_invariants o pre post))
  : atomic_repr b opened_invariants o
    pre
    post
  = fun _ ->
    assume (wp (fun _ -> True));
    let x = f () in
    g x ()
