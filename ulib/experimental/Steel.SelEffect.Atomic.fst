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

(* Some helpers *)

let get0 (#opened:inames) (#p:vprop) (_:unit) : repr (erased (rmem p))
  true opened Unobservable p (fun _ -> p)
  (requires fun _ -> True)
  (ensures fun h0 r h1 -> normal (frame_equalities p h0 h1 /\ frame_equalities p r h1))
  = fun frame ->
      let m0:full_mem = NMSTTotal.get () in
      let h0 = mk_rmem p (core_mem m0) in
      lemma_frame_equalities_refl p h0;
      h0

let get _ = SteelSelGhostF?.reflect (get0 ())

let intro_star (p q:vprop) (r:slprop) (vp:erased (t_of p)) (vq:erased (t_of q)) (m:mem)
  (proof:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures interp (hp_of q) m)
  )
  : Lemma
   (requires interp ((hp_of p) `Mem.star` r) m /\ sel_of p m == reveal vp)
   (ensures interp ((hp_of q) `Mem.star` r) m)
= let p = hp_of p in
  let q = hp_of q in
  let intro (ml mr:mem) : Lemma
      (requires interp q ml /\ interp r mr /\ disjoint ml mr)
      (ensures disjoint ml mr /\ interp (q `Mem.star` r) (Mem.join ml mr))
  = Mem.intro_star q r ml mr
  in
  elim_star p r m;
  Classical.forall_intro (Classical.move_requires proof);
  Classical.forall_intro_2 (Classical.move_requires_2 intro)

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let change_slprop0 (#opened:inames) (p q:vprop) (vp:erased (t_of p)) (vq:erased (t_of q))
  (proof:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures interp (hp_of q) m /\ sel_of q m == reveal vq)
  ) : repr unit false opened Unobservable p (fun _ -> q) (fun h -> h p == reveal vp) (fun _ _ h1 -> h1 q == reveal vq)
  = fun frame ->
      let m:full_mem = NMSTTotal.get () in
      proof (core_mem m);
      Classical.forall_intro (Classical.move_requires proof);
      Mem.star_associative (hp_of p) frame (locks_invariant opened m);
      intro_star p q (frame `Mem.star` locks_invariant opened m) vp vq m proof;
      Mem.star_associative (hp_of q) frame (locks_invariant opened m)
#pop-options

let change_slprop p q vp vq l  = SteelSelGhost?.reflect (change_slprop0 p q vp vq l)

let change_equal_slprop
  p q
= let m = get () in
  let x : Ghost.erased (t_of p) = hide ((reveal m) p) in
  let y : Ghost.erased (t_of q) = Ghost.hide (Ghost.reveal x) in
  change_slprop
    p
    q
    x
    y
    (fun _ -> ())

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let change_slprop_20 (#opened:inames) (p q:vprop) (vq:erased (t_of q))
  (proof:(m:mem) -> Lemma
    (requires interp (hp_of p) m)
    (ensures interp (hp_of q) m /\ sel_of q m == reveal vq)
  ) : repr unit false opened Unobservable p (fun _ -> q)
           (fun _ -> True) (fun _ _ h1 -> h1 q == reveal vq)
  = fun frame ->
      let m:full_mem = NMSTTotal.get () in
      proof (core_mem m);
      Classical.forall_intro (Classical.move_requires proof);
      Mem.star_associative (hp_of p) frame (locks_invariant opened m);
      intro_star p q (frame `Mem.star` locks_invariant opened m) (sel_of p m) vq m proof;
      Mem.star_associative (hp_of q) frame (locks_invariant opened m)
#pop-options

let change_slprop_2 p q vq l = SteelSelGhost?.reflect (change_slprop_20 p q vq l)

let change_slprop_rel0 (#opened:inames) (p q:vprop)
  (rel : normal (t_of p) -> normal (t_of q) -> prop)
  (proof:(m:mem) -> Lemma
    (requires interp (hp_of p) m)
    (ensures
      interp (hp_of p) m /\
      interp (hp_of q) m /\
      rel (sel_of p m) (sel_of q m))
  ) : repr unit false opened Unobservable p (fun _ -> q)
           (fun _ -> True) (fun h0 _ h1 -> rel (h0 p) (h1 q))
  = fun frame ->
      let m:full_mem = NMSTTotal.get () in

      proof (core_mem m);
      let h0 = mk_rmem p (core_mem m) in
      let h1 = mk_rmem q (core_mem m) in
      reveal_mk_rmem p (core_mem m) p;
      reveal_mk_rmem q (core_mem m) q;

      Mem.star_associative (hp_of p) frame (locks_invariant opened m);
      intro_star p q (frame `Mem.star` locks_invariant opened m) (sel_of p (core_mem m)) (sel_of q (core_mem m)) m proof;
      Mem.star_associative (hp_of q) frame (locks_invariant opened m)

let change_slprop_rel p q rel proof = SteelSelGhost?.reflect (change_slprop_rel0 p q rel proof)

let change_slprop_rel_with_cond0 (#opened:inames) (p q:vprop)
  (cond: t_of p -> prop)
  (rel : (t_of p) -> (t_of q) -> prop)
  (proof:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ cond (sel_of p m))
    (ensures
      interp (hp_of p) m /\
      interp (hp_of q) m /\
      rel (sel_of p m) (sel_of q m))
  ) : repr unit false opened Unobservable p (fun _ -> q)
           (fun m -> cond (m p)) (fun h0 _ h1 -> rel (h0 p) (h1 q))
  = fun frame ->
      let m:full_mem = NMSTTotal.get () in

      proof (core_mem m);
      let h0 = mk_rmem p (core_mem m) in
      let h1 = mk_rmem q (core_mem m) in
      reveal_mk_rmem p (core_mem m) p;
      reveal_mk_rmem q (core_mem m) q;

      Mem.star_associative (hp_of p) frame (locks_invariant opened m);
      intro_star p q (frame `Mem.star` locks_invariant opened m) (sel_of p (core_mem m)) (sel_of q (core_mem m)) m proof;
      Mem.star_associative (hp_of q) frame (locks_invariant opened m)

let change_slprop_rel_with_cond p q cond rel proof
  = SteelSelGhost?.reflect (change_slprop_rel_with_cond0 p q cond rel proof)

let extract_info0 (#opened:inames) (p:vprop) (vp:erased (normal (t_of p))) (fact:prop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures fact)
  ) : repr unit false opened Unobservable p (fun _ -> p)
      (fun h -> h p == reveal vp)
      (fun h0 _ h1 -> normal (frame_equalities p h0 h1) /\ fact)
  = fun frame ->
      let m0:full_mem = NMSTTotal.get () in
      let h0 = mk_rmem p (core_mem m0) in
      lemma_frame_equalities_refl p h0;
      l (core_mem m0)

let extract_info p vp fact l = SteelSelGhost?.reflect (extract_info0 p vp fact l)

let noop _ = change_slprop_rel vemp vemp (fun _ _ -> True) (fun _ -> ())

let sladmit _ = SteelSelGhostF?.reflect (fun _ -> NMSTTotal.nmst_tot_admit ())

let reveal_star0 (#opened:inames) (p1 p2:vprop)
  : repr unit false opened Unobservable (p1 `star` p2) (fun _ -> p1 `star` p2)
   (fun _ -> True)
   (fun h0 _ h1 ->
     h0 p1 == h1 p1 /\ h0 p2 == h1 p2 /\
     h0 (p1 `star` p2) == (h0 p1, h0 p2) /\
     h1 (p1 `star` p2) == (h1 p1, h1 p2)
   )
 = fun frame ->
     let m:full_mem = NMSTTotal.get () in
     let h0 = mk_rmem (p1 `star` p2) (core_mem m) in
     reveal_mk_rmem (p1 `star` p2) m (p1 `star` p2);
     reveal_mk_rmem (p1 `star` p2) m p1;
     reveal_mk_rmem (p1 `star` p2) m p2

let reveal_star p1 p2 = SteelSelGhost?.reflect (reveal_star0 p1 p2)

let reveal_star_30 (#opened:inames) (p1 p2 p3:vprop)
 : repr unit false opened Unobservable (p1 `star` p2 `star` p3) (fun _ -> p1 `star` p2 `star` p3)
   (requires fun _ -> True)
   (ensures fun h0 _ h1 ->
     can_be_split (p1 `star` p2 `star` p3) p1 /\
     can_be_split (p1 `star` p2 `star` p3) p2 /\
     h0 p1 == h1 p1 /\ h0 p2 == h1 p2 /\ h0 p3 == h1 p3 /\
     h0 (p1 `star` p2 `star` p3) == ((h0 p1, h0 p2), h0 p3) /\
     h1 (p1 `star` p2 `star` p3) == ((h1 p1, h1 p2), h1 p3)
   )
 = fun frame ->
     let m:full_mem = NMSTTotal.get () in
     let h0 = mk_rmem (p1 `star` p2 `star` p3) (core_mem m) in
     can_be_split_trans (p1 `star` p2 `star` p3) (p1 `star` p2) p1;
     can_be_split_trans (p1 `star` p2 `star` p3) (p1 `star` p2) p2;
     reveal_mk_rmem (p1 `star` p2 `star` p3) m (p1 `star` p2 `star` p3);
     reveal_mk_rmem (p1 `star` p2 `star` p3) m (p1 `star` p2);
     reveal_mk_rmem (p1 `star` p2 `star` p3) m p3

let reveal_star_3 p1 p2 p3 = SteelSelGhost?.reflect (reveal_star_30 p1 p2 p3)

let intro_vrefine v p =
  let m = get () in
  let x : Ghost.erased (t_of v) = gget v in
  let x' : Ghost.erased (vrefine_t v p) = Ghost.hide (Ghost.reveal x) in
  change_slprop
    v
    (vrefine v p)
    x
    x'
    (fun m ->
      interp_vrefine_hp v p m;
      vrefine_sel_eq v p m
    )

let elim_vrefine v p =
  let h = get() in
  let x : Ghost.erased (vrefine_t v p) = gget (vrefine v p) in
  let x' : Ghost.erased (t_of v) = Ghost.hide (Ghost.reveal x) in
  change_slprop
    (vrefine v p)
    v
    x
    x'
    (fun m ->
      interp_vrefine_hp v p m;
      vrefine_sel_eq v p m
    )

let vdep_cond
  (v: vprop)
  (q: vprop)
  (p: (t_of v -> Tot vprop))
  (x1: t_of (v `star` q))
: Tot prop
= q == p (fst x1)

let vdep_rel
  (v: vprop)
  (q: vprop)
  (p: (t_of v -> Tot vprop))
  (x1: t_of (v `star` q))
  (x2: (t_of (vdep v p)))
: Tot prop
=
  q == p (fst x1) /\
  dfst (x2 <: (dtuple2 (t_of v) (vdep_payload v p))) == fst x1 /\
  dsnd (x2 <: (dtuple2 (t_of v) (vdep_payload v p))) == snd x1

let intro_vdep_lemma
  (v: vprop)
  (q: vprop)
  (p: (t_of v -> Tot vprop))
  (m: mem)
: Lemma
  (requires (
    interp (hp_of (v `star` q)) m /\
    q == p (fst (sel_of (v `star` q) m))
  ))
  (ensures (
    interp (hp_of (v `star` q)) m /\
    interp (hp_of (vdep v p)) m /\
    vdep_rel v q p (sel_of (v `star` q) m) (sel_of (vdep v p) m)
  ))
=
  Mem.interp_star (hp_of v) (hp_of q) m;
  interp_vdep_hp v p m;
  vdep_sel_eq v p m

let intro_vdep
  v q p
=
  reveal_star v q;
  change_slprop_rel_with_cond
    (v `star` q)
    (vdep v p)
    (vdep_cond v q p)
    (vdep_rel v q p)
    (fun m -> intro_vdep_lemma v q p m)

let vdep_cond_recip
  (v: vprop)
  (p: (t_of v -> Tot vprop))
  (q: vprop)
  (x2: t_of (vdep v p))
: Tot prop
= q == p (dfst (x2 <: dtuple2 (t_of v) (vdep_payload v p)))

let vdep_rel_recip
  (v: vprop)
  (q: vprop)
  (p: (t_of v -> Tot vprop))
  (x2: (t_of (vdep v p)))
  (x1: t_of (v `star` q))
: Tot prop
=
  vdep_rel v q p x1 x2

let elim_vdep_lemma
  (v: vprop)
  (q: vprop)
  (p: (t_of v -> Tot vprop))
  (m: mem)
: Lemma
  (requires (
    interp (hp_of (vdep v p)) m /\
    q == p (dfst (sel_of (vdep v p) m <: dtuple2 (t_of v) (vdep_payload v p)))
  ))
  (ensures (
    interp (hp_of (v `star` q)) m /\
    interp (hp_of (vdep v p)) m /\
    vdep_rel v q p (sel_of (v `star` q) m) (sel_of (vdep v p) m)
  ))
=
  Mem.interp_star (hp_of v) (hp_of q) m;
  interp_vdep_hp v p m;
  vdep_sel_eq v p m

let elim_vdep0
  (#opened:inames)
  (v: vprop)
  (p: (t_of v -> Tot vprop))
  (q: vprop)
: SteelSelGhost unit opened
  (vdep v p)
  (fun _ -> v `star` q)
  (requires (fun h -> q == p (dfst (h (vdep v p)))))
  (ensures (fun h _ h' ->
      let fs = h' v in
      let sn = h' q in
      let x2 = h (vdep v p) in
      q == p fs /\
      dfst x2 == fs /\
      dsnd x2 == sn
  ))
= change_slprop_rel_with_cond
    (vdep v p)
    (v `star` q)
    (vdep_cond_recip v p q)
    (vdep_rel_recip v q p)
    (fun m -> elim_vdep_lemma v q p m);
  reveal_star v q

let elim_vdep
  v p
= let r = gget (vdep v p) in
  let res = Ghost.hide (dfst #(t_of v) #(vdep_payload v p) (Ghost.reveal r)) in
  elim_vdep0 v p (p (Ghost.reveal res));
  res

let intro_vrewrite
  v #t f
= let x : Ghost.erased (t_of v) = gget v in
  let x' : Ghost.erased t = Ghost.hide (f (Ghost.reveal x)) in
  change_slprop
    v
    (vrewrite v f)
    x
    x'
    (fun m ->
      vrewrite_sel_eq v f m
    )

let elim_vrewrite
  v #t f
=
  change_slprop_rel
    (vrewrite v f)
    v
    (fun y x -> y == f x)
    (fun m -> vrewrite_sel_eq v f m)


(*** Lemmas on references *)

open Steel.FractionalPermission

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
module Eff = Steel.Effect.Atomic

let as_steelselghost0 (#a:Type) (#opened: _)
  (#pre:pre_t) (#post:post_t a)
  (#req:prop) (#ens:a -> prop)
  ($f:Eff.repr a false opened Eff.Unobservable (hp_of pre) (fun x -> hp_of (post x)) (fun h -> req) (fun _ x _ -> ens x))
: repr a false opened Unobservable pre post (fun _ -> req) (fun _ x _ -> ens x)
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

let _:squash (hp_of vemp == emp /\ t_of vemp == unit) = reveal_vemp ()

unfold
let ghost_vptr_tmp' (#a:Type) (r:ghost_ref a) (p:perm) (v:erased a) : vprop' =
  { hp = R.ghost_pts_to r p v;
    t = unit;
    sel = fun _ -> ()}
unfold
let ghost_vptr_tmp r p v : vprop = VUnit (ghost_vptr_tmp' r p v)

val ghost_alloc0 (#a:Type0) (#opened: _) (x:a) : SteelSelGhost (ghost_ref a) opened
  vemp (fun r -> ghost_vptr_tmp r full_perm x)
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

let ghost_free r = change_slprop_rel (ghost_vptr r) vemp (fun _ _ -> True) intro_emp

val ghost_write0 (#a:Type0) (#opened: _) (v:erased a) (r:ghost_ref a) (x:a)
  : SteelSelGhost unit opened
    (ghost_vptr_tmp r full_perm v) (fun _ -> ghost_vptr_tmp r full_perm x)
    (fun _ -> True) (fun _ _ _ -> True)

let ghost_write0 #a #opened v r x = as_steelselghost (fun _ -> R.ghost_write #a #opened #v r x)

let ghost_write r x
  = 
    let v = gget (ghost_vptr r) in
    change_slprop (ghost_vptr r) (ghost_vptr_tmp r full_perm v) v () (elim_ghost_vptr r v);
    ghost_write0 v r (Ghost.reveal x);
    change_slprop (ghost_vptr_tmp r full_perm (Ghost.reveal x)) (ghost_vptr r) () x (intro_ghost_vptr r x)
