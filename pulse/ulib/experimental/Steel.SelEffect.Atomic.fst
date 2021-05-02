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

module Steel.SelEffect.Atomic

open Steel.SelEffect
friend Steel.SelEffect



#set-options "--warn_error -330"  //turn off the experimental feature warning

let _ : squash (forall (pre:pre_t) (m0:mem{interp (hp_of pre) m0}) (m1:mem{disjoint m0 m1}).
  mk_rmem pre m0 == mk_rmem pre (join m0 m1)) = Classical.forall_intro rmem_depends_only_on

let req_to_act_req (#pre:vprop) (req:req_t pre) : mprop (hp_of pre) =
  fun m ->
    rmem_depends_only_on pre;
    interp (hp_of pre) m /\ req (mk_rmem pre m)

unfold
let to_post (#a:Type) (post:post_t a) = fun x -> (hp_of (post x))

let ens_to_act_ens (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
: mprop2 (hp_of pre) (to_post post)
= fun m0 x m1 -> interp (hp_of pre) m0 /\ interp (hp_of (post x)) m1 /\
    ens (mk_rmem pre m0) x (mk_rmem (post x) m1)

let repr a framed opened f pre post req ens =
  action_except_full a opened (hp_of pre) (to_post post)
    (req_to_act_req req) (ens_to_act_ens ens)

let return_ a x opened #p = fun _ ->
  let m0:full_mem = NMSTTotal.get () in
  let h0 = mk_rmem (p x) (core_mem m0) in
  lemma_frame_equalities_refl (p x) h0;
  x

#push-options "--fuel 0 --ifuel 0"

let norm_repr (#a:Type) (#framed:bool) (#opened:inames) (#obs:observability)
 (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
 (f:repr a framed opened obs pre post req ens)
 : repr a framed opened obs pre post (fun h -> normal (req h)) (fun h0 x h1 -> normal (ens h0 x h1))
 = f


val bind_aux (a:Type) (b:Type)
  (#opened:inames)
  (#o1:eqtype_as_type observability)
  (#o2:eqtype_as_type observability)
  (#framed_f:eqtype_as_type bool) (#framed_g:eqtype_as_type bool)
  (#pre_f:pre_t) (#post_f:post_t a)
  (#req_f:req_t pre_f) (#ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (#req_g:(x:a -> req_t (pre_g x))) (#ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#frame_f:vprop) (#frame_g:a -> vprop)
  (#post:post_t b)
  (#_ : squash (maybe_emp framed_f frame_f))
  (#_ : squash (maybe_emp_dep framed_g frame_g))
  (#pr:a -> prop)
  (#p:squash (can_be_split_forall_dep pr
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:repr a framed_f opened o1 pre_f post_f req_f ens_f)
  (g:(x:a -> repr b framed_g opened o2 (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    true
    opened
    (join_obs o1 o2)
    (pre_f `star` frame_f)
    post
    (bind_req_unnormal req_f ens_f req_g frame_f frame_g p)
    (bind_ens_unnormal req_f ens_f ens_g frame_f frame_g post p p2)

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"

val frame00 (#a:Type)
          (#framed:bool)
          (#opened:inames)
          (#obs:observability)
          (#pre:pre_t)
          (#post:post_t a)
          (#req:req_t pre)
          (#ens:ens_t pre a post)
          ($f:repr a framed opened obs pre post req ens)
          (frame:vprop)
  : repr a
    true
    opened
    obs
    (pre `star` frame)
    (fun x -> post x `star` frame)
    (fun h -> req (focus_rmem h pre))
    (fun h0 r h1 -> req (focus_rmem h0 pre) /\ ens (focus_rmem h0 pre) r (focus_rmem h1 (post r)) /\
      frame_equalities frame (focus_rmem h0 frame) (focus_rmem h1 frame))

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory

let equiv_middle_left_assoc (a b c d:slprop)
  : Lemma (((a `Mem.star` b) `Mem.star` c `Mem.star` d) `Mem.equiv`
            (a `Mem.star` (b `Mem.star` c) `Mem.star` d))
  = let open Steel.Memory in
    star_associative a b c;
    star_congruence ((a `star` b) `star` c) d (a `star` (b `star` c)) d

let frame00 #a #framed #opened #obs #pre #post #req #ens f frame =
  fun frame' ->
      let m0:full_mem = NMSTTotal.get () in

      let snap:rmem frame = mk_rmem frame (core_mem m0) in
      // Need to define it with type annotation, although unused, for it to trigger
      // the pattern on the framed ensures in the def of MstTot
      let aux:mprop (hp_of frame `Mem.star` frame') = req_frame frame snap in

      focus_is_restrict_mk_rmem (pre `star` frame) pre (core_mem m0);

      assert (interp (hp_of (pre `star` frame) `Mem.star` frame' `Mem.star` locks_invariant opened m0) m0);
      equiv_middle_left_assoc (hp_of pre) (hp_of frame) frame' (locks_invariant opened m0);
      assert (interp (hp_of pre `Mem.star` (hp_of frame `Mem.star` frame') `Mem.star` locks_invariant opened m0) m0);

      let x = f (hp_of frame `Mem.star` frame') in

      let m1:full_mem = NMSTTotal.get () in

      assert (interp (hp_of (post x) `Mem.star` (hp_of frame `Mem.star` frame') `Mem.star` locks_invariant opened m1) m1);
      equiv_middle_left_assoc (hp_of (post x)) (hp_of frame) frame' (locks_invariant opened m1);
      assert (interp ((hp_of (post x) `Mem.star` hp_of frame)
        `Mem.star` frame' `Mem.star` locks_invariant opened m1) m1);

      focus_is_restrict_mk_rmem (pre `star` frame) frame (core_mem m0);
      focus_is_restrict_mk_rmem (post x `star` frame) frame (core_mem m1);

      let h0:rmem (pre `star` frame) = mk_rmem (pre `star` frame) (core_mem m0) in
      let h1:rmem (post x `star` frame) = mk_rmem (post x `star` frame) (core_mem m1) in
      assert (focus_rmem h0 frame == focus_rmem h1 frame);

      focus_is_restrict_mk_rmem (post x `star` frame) (post x) (core_mem m1);

      lemma_frame_equalities_refl frame (focus_rmem h0 frame);

      x

#push-options "--z3rlimit 20"
let bind_aux a b #opened #o1 #o2 #framed_f #framed_g #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_f #frame_g #post #_ #_ #p #p2 f g =
  fun frame ->
    let m0:full_mem = NMSTTotal.get () in

    let h0 = mk_rmem (pre_f `star` frame_f) (core_mem m0) in

    let x = frame00 f frame_f frame  in

    let m1:full_mem = NMSTTotal.get () in

    let h1 = mk_rmem (post_f x `star` frame_f) (core_mem m1) in

    let h1' = mk_rmem (pre_g x `star` frame_g x) (core_mem m1) in

    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
    focus_is_restrict_mk_rmem
      (post_f x `star` frame_f)
      (pre_g x `star` frame_g x)
      (core_mem m1);
    focus_focus_is_focus
      (post_f x `star` frame_f)
      (pre_g x `star` frame_g x)
      (pre_g x)
      (core_mem m1);
    assert (focus_rmem h1' (pre_g x) == focus_rmem h1 (pre_g x));

    can_be_split_3_interp
      (hp_of (post_f x `star` frame_f))
      (hp_of (pre_g x `star` frame_g x))
      frame (locks_invariant opened m1) m1;

    let y = frame00 (g x) (frame_g x) frame in

    let m2:full_mem = NMSTTotal.get () in

    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (frame_g x);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (post_g x y);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (frame_g x);

    let h2' = mk_rmem (post_g x y `star` frame_g x) (core_mem m2) in
    let h2 = mk_rmem (post y) (core_mem m2) in



    // assert (focus_rmem h1' (pre_g x) == focus_rmem h1 (pre_g x));

    focus_focus_is_focus
      (post_f x `star` frame_f)
      (pre_g x `star` frame_g x)
      (frame_g x)
      (core_mem m1);

    focus_is_restrict_mk_rmem
      (post_g x y `star` frame_g x)
      (post y)
      (core_mem m2);

    focus_focus_is_focus
      (post_g x y `star` frame_g x)
      (post y)
      (frame_g x)
      (core_mem m2);
    focus_focus_is_focus
      (post_g x y `star` frame_g x)
      (post y)
      (post_g x y)
      (core_mem m2);

    can_be_split_3_interp
      (hp_of (post_g x y `star` frame_g x))
      (hp_of (post y))
      frame (locks_invariant opened m2) m2;


    y

let bind a b _ _ _ f g = norm_repr (bind_aux a b f g)

unfold
let subcomp_pre_unnormal (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (_:squash (can_be_split pre_g pre_f))
  (_:squash (equiv_forall post_f post_g))
: pure_pre
= ((forall (m0:rmem pre_g). req_g m0 ==> req_f (focus_rmem m0 pre_f)) /\
  (forall (m0:rmem pre_g) (x:a) (m1:rmem (post_g x)). ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) ==> ens_g m0 x m1))

let unnormal (p:prop) : Lemma (requires normal p) (ensures p) = ()

let subcomp a opened o1 o2 #framed_f #framed_g #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #p1 #p2 f =
  fun frame ->
    let m0:full_mem = NMSTTotal.get () in
    let h0 = mk_rmem pre_g (core_mem m0) in
    focus_is_restrict_mk_rmem pre_g pre_f (core_mem m0);

    can_be_split_3_interp (hp_of pre_g) (hp_of pre_f) frame (locks_invariant opened m0) m0;

    let x = f frame in


    let m1:full_mem = NMSTTotal.get () in
    let h1 = mk_rmem (post_g x) (core_mem m1) in

    focus_is_restrict_mk_rmem (post_g x) (post_f x) (core_mem m1);

    unnormal (subcomp_pre_unnormal req_f ens_f req_g ens_g p1 p2);

    can_be_split_3_interp (hp_of (post_f x)) (hp_of (post_g x)) frame (locks_invariant opened m1) m1;

    x

let bind_pure_steela_ a b opened o f g
  = FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun frame ->
      let x = f () in
      g x frame

let lift_ghost_atomic a o f = f

let lift_atomic_steel a o f = f
