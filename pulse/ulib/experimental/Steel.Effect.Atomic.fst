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

friend Steel.Effect

#set-options "--warn_error -330"  //turn off the experimental feature warning

val join_preserves_interp (hp:slprop) (m0 m1:mem)
  : Lemma
    (requires (interp hp m0 /\ disjoint m0 m1))
    (ensures (interp hp (join m0 m1)))
    [SMTPat (interp hp (join m0 m1))]

let join_preserves_interp hp m0 m1
  = intro_emp m1;
    intro_star hp emp m0 m1;
    affine_star hp emp (join m0 m1)

val respects_fp (#fp:slprop) (p: hmem fp -> prop) : prop
let respects_fp #fp p =
  forall (m0:hmem fp) (m1:mem{disjoint m0 m1}). p m0 <==> p (join m0 m1)

val reveal_respects_fp (#fp:_) (p:hmem fp -> prop)
  : Lemma (respects_fp p <==>
           (forall (m0:hmem fp) (m1:mem{disjoint m0 m1}). p m0 <==> p (join m0 m1)))
          [SMTPat (respects_fp #fp p)]
let reveal_respects_fp p = ()

let fp_mprop (fp:slprop) = p:(hmem fp -> prop) { respects_fp p }

val respects_binary_fp (#a:Type) (#pre:slprop) (#post:a -> slprop)
                       (q:(hmem pre -> x:a -> hmem (post x) -> prop)) : prop
let respects_binary_fp #a #pre #post q
  = (forall x (h_pre:hmem pre) h_post (h:mem{disjoint h_pre h}).
      q h_pre x h_post <==> q (join h_pre h) x h_post) /\
    (forall x h_pre (h_post:hmem (post x)) (h:mem{disjoint h_post h}).
      q h_pre x h_post <==> q h_pre x (join h_post h))

val reveal_respects_binary_fp (#a:Type) (#pre:slprop) (#post:a -> slprop)
                              (q:(hmem pre -> x:a -> hmem (post x) -> prop))
  : Lemma (respects_binary_fp q <==>
            //at this point we need to know interp pre (join h_pre h) -- use join_preserves_interp for that
            (forall x (h_pre:hmem pre) h_post (h:mem{disjoint h_pre h}).
              q h_pre x h_post <==> q (join h_pre h) x h_post) /\
            //can join any disjoint heap to the post-heap and q is still valid
            (forall x h_pre (h_post:hmem (post x)) (h:mem{disjoint h_post h}).
              q h_pre x h_post <==> q h_pre x (join h_post h)))
           [SMTPat (respects_binary_fp #a #pre #post q)]
let reveal_respects_binary_fp q = ()

let fp_binary_mprop #a (pre:slprop) (post: a -> slprop) =
  p:(hmem pre -> x:a -> hmem (post x) -> prop){ respects_binary_fp p }

let req_to_act_req (#pre:slprop) (req:fp_mprop pre) : mprop pre =
  fun m -> interp pre m /\ req m

let ens_to_act_ens (#pre:slprop) (#a:Type) (#post:a -> slprop) (ens:fp_binary_mprop pre post)
: mprop2 pre post
= fun m0 x m1 -> interp pre m0 /\ interp (post x) m1 /\ ens m0 x m1

let repr a framed opened_invariants f pre post req ens =
    action_except_full a opened_invariants pre post (req_to_act_req req) (ens_to_act_ens ens)

let return_ a x opened_invariants #p = fun _ -> x

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

let equiv_middle_left_assoc (a b c d:slprop)
  : Lemma (((a `star` b) `star` c `star` d) `equiv` (a `star` (b `star` c) `star` d))
  = star_associative a b c;
    star_congruence ((a `star` b) `star` c) d (a `star` (b `star` c)) d



#push-options "--z3rlimit_factor 2"
let bind a b opened o1 o2 #framed_f #framed_g
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

let subcomp (a:Type) opened o1 o2 #framed_f #framed_g
  #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #p1 #p2 f
 = fun frame ->
     let m0:full_mem = NMSTTotal.get() in
     interp_trans_left opened pre_g pre_f frame m0;
     let x = f frame in
     let m1:full_mem = NMSTTotal.get () in
     interp_trans_left opened (post_f x) (post_g x) frame m1;
     x

let bind_pure_steela_ (a:Type) (b:Type) opened o #wp #pre #post #req #ens f g
= fun frame ->
    let x = f () in
    g x frame

let lift_ghost_atomic a o f = f

let lift_atomic_steel a o #framed #pre #post #req #ens f = f

let as_atomic_action f = SteelAtomic?.reflect f
let as_atomic_action_ghost f = SteelGhost?.reflect f

let new_invariant #i p = SteelGhost?.reflect (Steel.Memory.new_invariant i p)

(*
 * AR: SteelAtomic and SteelGhost are not marked reifiable since we intend to run Steel programs natively
 *     However to implement the with_inv combinators we need to reify their thunks to reprs
 *     We could implement it better by having support for reification only in the .fst file
 *     But for now assuming a function
 *)
assume val reify_steel_atomic_comp
  (#a:Type) (#already_framed:bool) (#opened_invariants:inames) (#g:observability)
  (#pre:slprop u#1) (#post:a -> slprop u#1) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> SteelAtomicBase a already_framed opened_invariants g pre post req ens)
  : action_except_full a opened_invariants pre post (req_to_act_req req) (ens_to_act_ens ens)

let with_invariant #a #fp #fp' #opened i f =
  SteelAtomic?.reflect (Steel.Memory.with_invariant #a #fp #fp' #opened i (reify_steel_atomic_comp f))

assume val reify_steel_ghost_comp
  (#a:Type) (#already_framed:bool) (#opened_invariants:inames)
  (#pre:slprop u#1) (#post:a -> slprop u#1) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> SteelGhostBase a already_framed opened_invariants Unobservable pre post req ens)
  : action_except_full a opened_invariants pre post (req_to_act_req req) (ens_to_act_ens ens)

let with_invariant_g #a #fp #fp' #opened i f =
  SteelGhost?.reflect (Steel.Memory.with_invariant #a #fp #fp' #opened i (reify_steel_ghost_comp f))

let change_slprop #opened p q proof =
  SteelGhost?.reflect (Steel.Memory.change_slprop #opened p q proof)

let rewrite_context #opened #p #q _ = change_slprop p q (fun _ -> ()); ()

let extract_info0 (#opened:inames) (p:slprop) (fact:prop)
  (proof:(m:mem) -> Lemma (requires interp p m) (ensures fact))
  : repr unit false opened Unobservable p (fun _ -> p)
      (fun _ -> True)
      (fun _ _ _ -> fact)
  = fun frame ->
      let m:full_mem = NMSTTotal.get() in
      proof m

let extract_info #opened p fact proof = SteelGhost?.reflect (extract_info0 #opened p fact proof)

let noop _ = change_slprop emp emp (fun _ -> ())

let sladmit #a #opened #p #q _ = SteelGhostF?.reflect (fun _ -> NMSTTotal.nmst_tot_admit ())

let slassert p = change_slprop p p (fun m -> ())
let intro_pure #_ p = change_slprop emp (pure p) (fun m -> pure_interp p m)
let intro_exists x p = change_slprop (p x) (h_exists p) (fun m -> Steel.Memory.intro_h_exists x p m)
let intro_exists_erased x p = change_slprop (p x) (h_exists p) (fun m -> Steel.Memory.intro_h_exists (Ghost.reveal x) p m)
let drop #_ p = change_slprop p emp (fun m -> emp_unit p; affine_star p emp m)

let witness_h_exists #a #u #p s = SteelGhost?.reflect (Steel.Memory.witness_h_exists #u p)
let lift_h_exists_atomic #a #u p = SteelGhost?.reflect (Steel.Memory.lift_h_exists #u p)
let h_exists_cong_atomic p q = change_slprop (h_exists p) (h_exists q) (fun m -> h_exists_cong p q)

let elim_pure_aux #uses (p:prop)
  : SteelGhostT (_:unit{p}) uses (pure p) (fun _ -> emp)
  = SteelGhost?.reflect (Steel.Memory.elim_pure #uses p)

let elim_pure #uses p = elim_pure_aux p

let sghost #a #opened_invariants #pre #post #req #ens f = SteelAtomicBase?.reflect (reify_steel_ghost_comp f)

let return #a #opened_invariants #p x =
  SteelAtomicBase?.reflect (fun _ -> x)
