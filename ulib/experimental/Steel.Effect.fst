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

module Steel.Effect

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
open Steel.Semantics.Instantiate
module FExt = FStar.FunctionalExtensionality

#set-options "--ide_id_info_off"

let _:squash (forall p q. can_be_split p q == Mem.slimp (hp_of p) (hp_of q)) = reveal_can_be_split ()

#set-options "--warn_error -330"  //turn off the experimental feature warning

let rmem_depends_only_on' (pre:pre_t) (m0:hmem pre) (m1:mem{disjoint m0 m1})
  : Lemma (mk_rmem pre m0 == mk_rmem pre (join m0 m1))
  = Classical.forall_intro (reveal_mk_rmem pre m0);
    Classical.forall_intro (reveal_mk_rmem pre (join m0 m1));
    FExt.extensionality_g
      (r0:vprop{can_be_split pre r0})
      (fun r0 -> normal (t_of r0))
      (mk_rmem pre m0)
      (mk_rmem pre (join m0 m1))

let rmem_depends_only_on (pre:pre_t)
  : Lemma (forall (m0:hmem pre) (m1:mem{disjoint m0 m1}).
    mk_rmem pre m0 == mk_rmem pre (join m0 m1))
  = Classical.forall_intro_2 (rmem_depends_only_on' pre)

let rmem_depends_only_on_post' (#a:Type) (post:post_t a)
    (x:a) (m0:hmem (post x)) (m1:mem{disjoint m0 m1})
  : Lemma (mk_rmem (post x) m0 == mk_rmem (post x) (join m0 m1))
  = rmem_depends_only_on' (post x) m0 m1

let rmem_depends_only_on_post (#a:Type) (post:post_t a)
  : Lemma (forall (x:a) (m0:hmem (post x)) (m1:mem{disjoint m0 m1}).
    mk_rmem (post x) m0 == mk_rmem (post x) (join m0 m1))
  = Classical.forall_intro_3 (rmem_depends_only_on_post' post)

[@@ __steel_reduce__]
let req_to_act_req (#pre:pre_t) (req:req_t pre) : Sem.l_pre #state (hp_of pre) =
  rmem_depends_only_on pre;
  fun m0 -> interp (hp_of pre) m0 /\ req (mk_rmem pre m0)

unfold
let to_post (#a:Type) (post:post_t a) = fun x -> (hp_of (post x))

[@@ __steel_reduce__]
let ens_to_act_ens (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
: Sem.l_post #state #a (hp_of pre) (to_post post)
= rmem_depends_only_on pre;
  rmem_depends_only_on_post post;
  fun m0 x m1 ->
    interp (hp_of pre) m0 /\ interp (hp_of (post x)) m1 /\ ens (mk_rmem pre m0) x (mk_rmem (post x) m1)

let reveal_focus_rmem (#r:vprop) (h:rmem r) (r0:vprop{r `can_be_split` r0}) (r':vprop{r0 `can_be_split` r'})
  : Lemma (
    r `can_be_split` r' /\
    focus_rmem h r0 r' == h r')
  = can_be_split_trans r r0 r';
    FExt.feq_on_domain_g (unrestricted_focus_rmem h r0)

let focus_is_restrict_mk_rmem (fp0 fp1:vprop) (m:hmem fp0)
  : Lemma
    (requires fp0 `can_be_split` fp1)
    (ensures focus_rmem (mk_rmem fp0 m) fp1 == mk_rmem fp1 m)
  = let f0:rmem fp0 = mk_rmem fp0 m in
    let f1:rmem fp1 = mk_rmem fp1 m in
    let f2:rmem fp1 = focus_rmem f0 fp1 in

    let aux (r:vprop{can_be_split fp1 r}) : Lemma (f1 r == f2 r)
      = can_be_split_trans fp0 fp1 r;

        reveal_mk_rmem fp0 m r;
        reveal_mk_rmem fp1 m r;
        reveal_focus_rmem f0 fp1 r
    in Classical.forall_intro aux;

    FExt.extensionality_g
      (r0:vprop{can_be_split fp1 r0})
      (fun r0 -> normal (t_of r0))
      (mk_rmem fp1 m)
      (focus_rmem (mk_rmem fp0 m) fp1)

let focus_focus_is_focus (fp0 fp1 fp2:vprop) (m:hmem fp0)
  : Lemma
    (requires fp0 `can_be_split` fp1 /\ fp1 `can_be_split` fp2)
    (ensures focus_rmem (focus_rmem (mk_rmem fp0 m) fp1) fp2 == focus_rmem (mk_rmem fp0 m) fp2)
  = let f0:rmem fp0 = mk_rmem fp0 m in
    let f1:rmem fp1 = focus_rmem f0 fp1 in
    let f20:rmem fp2 = focus_rmem f0 fp2 in
    let f21:rmem fp2 = focus_rmem f1 fp2 in

    let aux (r:vprop{can_be_split fp2 r}) : Lemma (f20 r == f21 r)
      = reveal_mk_rmem fp0 m r;
        reveal_focus_rmem f0 fp1 r;
        reveal_focus_rmem f0 fp2 r;
        reveal_focus_rmem f1 fp2 r

    in Classical.forall_intro aux;

    FExt.extensionality_g
      (r0:vprop{can_be_split fp2 r0})
      (fun r0 -> normal (t_of r0))
      f20 f21

val can_be_split_3_interp (p1 p2 q r:slprop u#1) (m:mem)
: Lemma
  (requires p1 `slimp` p2 /\  interp (p1 `Mem.star` q `Mem.star` r) m)
  (ensures interp (p2 `Mem.star` q `Mem.star` r) m)

let can_be_split_3_interp p1 p2 q r m =
  Mem.star_associative p1 q r;
  Mem.star_associative p2 q r;
  slimp_star p1 p2 (q `Mem.star` r) (q `Mem.star` r)

let repr (a:Type) (_:bool) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a (hp_of pre) (to_post post)
    ((req_to_act_req req))
    ((ens_to_act_ens ens))

let nmst_get (#st:Sem.st) ()
  : Sem.Mst (Sem.full_mem st)
           (fun _ -> True)
           (fun s0 s s1 -> s0 == s /\ s == s1)
  = NMST.get ()

let rec lemma_frame_equalities_refl (frame:vprop) (h:rmem frame) : Lemma (frame_equalities frame h h) =
  match frame with
  | VUnit _ -> ()
  | VStar p1 p2 ->
        can_be_split_star_l p1 p2;
        can_be_split_star_r p1 p2;

        let h1 = focus_rmem h p1 in
        let h2 = focus_rmem h p2 in

        lemma_frame_equalities_refl p1 h1;
        lemma_frame_equalities_refl p2 h2

let return_ a x #p = fun _ ->
      let m0 = nmst_get () in
      let h0 = mk_rmem (p x) (core_mem m0) in
      lemma_frame_equalities_refl (p x) h0;
      x

#push-options "--fuel 0 --ifuel 0"

val req_frame (frame:vprop) (snap:rmem frame) : mprop (hp_of frame)

let req_frame' (frame:vprop) (snap:rmem frame) (m:mem) : prop =
  interp (hp_of frame) m /\ mk_rmem frame m == snap

let req_frame frame snap =
  rmem_depends_only_on frame;
  req_frame' frame snap

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"

val frame00 (#a:Type)
          (#framed:bool)
          (#pre:pre_t)
          (#post:post_t a)
          (#req:req_t pre)
          (#ens:ens_t pre a post)
          ($f:repr a framed pre post req ens)
          (frame:vprop)
  : repr a
    true
    (pre `star` frame)
    (fun x -> post x `star` frame)
    (fun h -> req (focus_rmem h pre))
    (fun h0 r h1 -> req (focus_rmem h0 pre) /\ ens (focus_rmem h0 pre) r (focus_rmem h1 (post r)) /\
     frame_equalities frame (focus_rmem h0 frame) (focus_rmem h1 frame))

let frame00 #a #framed #pre #post #req #ens f frame =
  fun frame' ->
      let m0 = nmst_get () in

      let snap:rmem frame = mk_rmem frame (core_mem m0) in

      focus_is_restrict_mk_rmem (pre `star` frame) pre (core_mem m0);

      let x = Sem.run #state #_ #_ #_ #_ #_ frame' (Sem.Frame (Sem.Act f) (hp_of frame) (req_frame frame snap)) in

      let m1 = nmst_get () in

      can_be_split_star_r pre frame;
      focus_is_restrict_mk_rmem (pre `star` frame) frame (core_mem m0);
      can_be_split_star_r (post x) frame;
      focus_is_restrict_mk_rmem (post x `star` frame) frame (core_mem m1);

      focus_is_restrict_mk_rmem (post x `star` frame) (post x) (core_mem m1);

      // We proved focus_rmem h0 frame == focus_rmem h1 frame so far

      let h0:rmem (pre `star` frame) = mk_rmem (pre `star` frame) (core_mem m0) in
      lemma_frame_equalities_refl frame (focus_rmem h0 frame);

      x

#pop-options


#push-options "--z3rlimit 20"
let bind a b #framed_f #framed_g #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_f #frame_g #post #_ #_ #p #p2 f g =
  fun frame ->
    let m0 = nmst_get () in

    let h0 = mk_rmem (pre_f `star` frame_f) (core_mem m0) in

    let x = frame00 f frame_f frame  in

    let m1 = nmst_get () in

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
      frame (locks_invariant Set.empty m1) m1;

    let y = frame00 (g x) (frame_g x) frame in

    let m2 = nmst_get () in

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
      frame (locks_invariant Set.empty m2) m2;


    y

#pop-options

/// Need to manually remove the rewrite_with_tactic marker here
let lemma_unfold_subcomp_pre (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (p1:squash (can_be_split pre_g pre_f))
  (p2:squash (equiv_forall post_f post_g))
  : Lemma (requires subcomp_pre req_f ens_f req_g ens_g p1 p2)
          (ensures (
          (forall (h0:hmem pre_g). req_g (mk_rmem pre_g h0) ==> req_f (focus_rmem (mk_rmem pre_g h0) pre_f)) /\
        (forall (h0:hmem pre_g) (x:a) (h1:hmem (post_g x)).
           ens_f (focus_rmem (mk_rmem pre_g h0) pre_f) x (focus_rmem (mk_rmem (post_g x) h1) (post_f x)) ==> ens_g (mk_rmem pre_g h0) x (mk_rmem (post_g x) h1)
        )))
   = T.unfold_rewrite_with_tactic vc_norm (  (forall (h0:hmem pre_g). req_g (mk_rmem pre_g h0) ==> req_f (focus_rmem (mk_rmem pre_g h0) pre_f)) /\
        (forall (h0:hmem pre_g) (x:a) (h1:hmem (post_g x)).
           ens_f (focus_rmem (mk_rmem pre_g h0) pre_f) x (focus_rmem (mk_rmem (post_g x) h1) (post_f x)) ==> ens_g (mk_rmem pre_g h0) x (mk_rmem (post_g x) h1)
        ))

let subcomp a #framed_f #framed_g #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #p1 #p2 f =
  fun frame ->
    let m0 = nmst_get () in
    let h0 = mk_rmem pre_g (core_mem m0) in
    focus_is_restrict_mk_rmem pre_g pre_f (core_mem m0);

    lemma_unfold_subcomp_pre req_f ens_f req_g ens_g p1 p2;

    can_be_split_3_interp (hp_of pre_g) (hp_of pre_f) frame (locks_invariant Set.empty m0) m0;


    let x = f frame in

    let m1 = nmst_get () in
    let h1 = mk_rmem (post_g x) (core_mem m1) in

    focus_is_restrict_mk_rmem (post_g x) (post_f x) (core_mem m1);

    can_be_split_3_interp (hp_of (post_f x)) (hp_of (post_g x)) frame (locks_invariant Set.empty m1) m1;

    x

let bind_pure_steel_ a b #wp #pre #post #req #ens f g
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    fun frame ->
      let x = f () in
      g x frame

(* We need a bind with DIV to implement par, using reification *)

unfold
let bind_div_steel_req (#a:Type) (wp:pure_wp a)
  (#pre_g:pre_t) (req_g:a -> req_t pre_g)
: req_t pre_g
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  fun h -> wp (fun _ -> True) /\ (forall x. (req_g x) h)

unfold
let bind_div_steel_ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre_g:pre_t) (#post_g:post_t b) (ens_g:a -> ens_t pre_g b post_g)
: ens_t pre_g b post_g
= fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. ens_g x h0 r h1)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let bind_div_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (framed:eqtype_as_type bool)
  (pre_g:pre_t) (post_g:post_t b) (req_g:a -> req_t pre_g) (ens_g:a -> ens_t pre_g b post_g)
  (f:eqtype_as_type unit -> DIV a wp) (g:(x:a -> repr b framed pre_g post_g (req_g x) (ens_g x)))
: repr b framed pre_g post_g
    (bind_div_steel_req wp req_g)
    (bind_div_steel_ens wp ens_g)
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  fun frame ->
  let x = f () in
  g x frame
#pop-options

polymonadic_bind (DIV, SteelBase) |> SteelBase = bind_div_steel
#pop-options

let par0 (#aL:Type u#a) (#preL:vprop) (#postL:aL -> vprop)
         (f:repr aL false preL postL (fun _ -> True) (fun _ _ _ -> True))
         (#aR:Type u#a) (#preR:vprop) (#postR:aR -> vprop)
         (g:repr aR false preR postR (fun _ -> True) (fun _ _ _ -> True))
  : SteelT (aL & aR)
    (preL `star` preR)
    (fun y -> postL (fst y) `star` postR (snd y))
  = Steel?.reflect (fun frame -> Sem.run #state #_ #_ #_ #_ #_ frame (Sem.Par (Sem.Act f) (Sem.Act g)))

(*
 * AR: Steel is not marked reifiable since we intend to run Steel programs natively
 *     However to implement the par combinator we need to reify a Steel thunk to its repr
 *     We could implement it better by having support for reification only in the .fst file
 *     But for now assuming a (Dv) function
 *)
assume val reify_steel_comp
  (#a:Type) (#framed:bool) (#pre:vprop) (#post:a -> vprop) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> SteelBase a framed pre post req ens)
  : Dv (repr a framed pre post req ens)

let par f g =
  par0 (reify_steel_comp f) (reify_steel_comp g)

let action_as_repr (#a:Type) (#p:slprop) (#q:a -> slprop) (f:action_except a Set.empty p q)
  : repr a false (to_vprop p) (fun x -> to_vprop (q x)) (fun _ -> True) (fun _ _ _ -> True)
  = Steel.Semantics.Instantiate.state_correspondence Set.empty; f

let as_action #a #p #q f = Steel?.reflect (action_as_repr f)
