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

#set-options "--warn_error -330"  //turn off the experimental feature warning

#push-options "--fuel 0 --ifuel 1 --z3rlimit 20"

module Sem = Steel.Semantics.Hoare.MST
module Ins = Steel.Semantics.Instantiate

open Steel.Semantics.Instantiate

let interp_depends_only_on_post (#a:Type) (hp:a -> slprop)
: Lemma
  (forall (x:a).
     (forall (m0:hmem (hp x)) (m1:mem{disjoint m0 m1}). interp (hp x) m0 <==> interp (hp x) (join m0 m1)))
= let aux (x:a)
    : Lemma
      (forall (m0:hmem (hp x)) (m1:mem{disjoint m0 m1}). interp (hp x) m0 <==> interp (hp x) (join m0 m1))
    = interp_depends_only_on (hp x) in
  Classical.forall_intro aux

let req_to_act_req (#pre:pre_t) (req:req_t pre) : Sem.l_pre #state pre =
  interp_depends_only_on pre;
  fun m -> interp pre m /\ req m

let ens_to_act_ens (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
: Sem.l_post #state #a pre post
= interp_depends_only_on pre;
  interp_depends_only_on_post post;
  fun m0 x m1 -> interp pre m0 /\ interp (post x) m1 /\ ens m0 x m1

let repr (a:Type) (frame:bool) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a pre post (req_to_act_req req) (ens_to_act_ens ens)

let return_ (a:Type) (x:a) (#[@@@ framing_implicit] p:a -> slprop)
: repr a true (return_pre (p x)) p (return_req (p x)) (return_ens a x p)
  = fun _ -> x

(*
 * Keeping f_frame aside for now
 *)
let frame_aux (#a:Type) (#framed:bool)
  (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:repr a framed pre post req ens) (frame:slprop)
: repr a true (pre `star` frame) (fun x -> post x `star` frame) req ens
= fun frame' ->
  Sem.run #state #_ #_ #_ #_ #_ frame' (Sem.Frame (Sem.Act f) frame (fun _ -> True))

let nmst_get (#st:Sem.st) ()
  : Sem.Mst (Sem.full_mem st)
           (fun _ -> True)
           (fun s0 s s1 -> s0 == s /\ s == s1)
  = NMST.get ()

let rewrite_l_3 (p1 p2 q r:slprop) : Lemma
    (requires p1 `equiv` p2)
    (ensures (p1 `star` q `star` r) `equiv` (p2 `star` q `star` r))
    = calc (equiv) {
        p1 `star` q `star` r;
        (equiv) { star_associative p1 q r }
        p1 `star` (q `star` r);
        (equiv) { equiv_extensional_on_star p1 p2 (q `star` r) }
        p2 `star` (q `star` r);
        (equiv) { star_associative p2 q r }
        p2 `star` q `star` r;
      }

#push-options "--z3rlimit_factor 2"
let bind a b #framed_f #framed_g #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_f #frame_g #post f g =
  fun frame' ->
  let x = frame_aux f frame_f frame' in
  let y = frame_aux (g x) (frame_g x) frame' in

  let m1 = nmst_get() in

  // We have the following
  // assert (interp
  //   ((post_g x y `star` frame_g x) `star` frame' `star` locks_invariant Set.empty m1)
  //     m1);

  // We need to prove
  // assert ((post y `star` frame' `star` locks_invariant Set.empty m1) `equiv`
  //   ((post_g x y `star` frame_g x) `star` frame' `star` locks_invariant Set.empty m1));

  // We do this by calling the following lemma
  rewrite_l_3 (post y) (post_g x y `star` frame_g x) frame' (locks_invariant Set.empty m1);

  // To get
  // assert (interp (post y `star` frame' `star` locks_invariant Set.empty m1) m1);

  y

let subcomp a f = f

let bind_pure_steel_ a b f g = fun frame ->
  let x = f () in
  (g x) frame

// unfold
let bind_div_steel_req (#a:Type) (wp:pure_wp a)
  (#pre_g:pre_t) (req_g:a -> req_t pre_g)
: req_t pre_g
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  fun h -> wp (fun _ -> True) /\ (forall x. (req_g x) h)

// unfold
let bind_div_steel_ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre_g:pre_t) (#post_g:post_t b) (ens_g:a -> ens_t pre_g b post_g)
: ens_t pre_g b post_g
= fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. ens_g x h0 r h1)

(*
 * A polymonadic bind between DIV and NMSTATE
 *
 * This is ultimately used when defining par and frame
 * par and frame try to compose reified Steel with Steel, since Steel is non total, its reification
 *   incurs a Div effect, and so, we need a way to compose Div and Steel
 *
 * This polymonadic bind gives us bare minimum to realize that
 * It is quite imprecise, in that it doesn't say anything about the post of the Div computation
 * That's because, the as_ensures combinator is not encoded for Div effect in the SMT,
 *   the way it is done for PURE and GHOST
 *
 * However, since the reification usecase gives us Dv anyway, this is fine for now
 *)
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let bind_div_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_g:pre_t) (#[@@@ framing_implicit] post_g:post_t b)
  (#[@@@ framing_implicit] req_g:a -> req_t pre_g)
  (#[@@@ framing_implicit] ens_g:a -> ens_t pre_g b post_g)
  (f:eqtype_as_type unit -> DIV a wp) (g:(x:a -> repr b framed pre_g post_g (req_g x) (ens_g x)))
: repr b framed pre_g post_g
    (bind_div_steel_req wp req_g)
    (bind_div_steel_ens wp ens_g)
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  fun m0 ->
  let x = f () in
  g x m0
#pop-options

polymonadic_bind (DIV, SteelBase) |> SteelBase = bind_div_steel

let par0 (#aL:Type u#a) (#preL:slprop u#1) (#postL:aL -> slprop u#1)
         (#lpreL:req_t preL) (#lpostL:ens_t preL aL postL)
         (f:repr aL false preL postL lpreL lpostL)
         (#aR:Type u#a) (#preR:slprop u#1) (#postR:aR -> slprop u#1)
         (#lpreR:req_t preR) (#lpostR:ens_t preR aR postR)
         (g:repr aR false preR postR lpreR lpostR)
  : Steel (aL & aR)
    (preL `Mem.star` preR)
    (fun y -> postL (fst y) `Mem.star` postR (snd y))
    (fun h -> lpreL h /\ lpreR h)
    (fun h0 y h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 (fst y) h1 /\ lpostR h0 (snd y) h1)
  = Steel?.reflect (fun frame -> Sem.run #state #_ #_ #_ #_ #_ frame (Sem.Par (Sem.Act f) (Sem.Act g)))

(*
 * AR: Steel is not marked reifiable since we intend to run Steel programs natively
 *     However to implement the par combinator we need to reify a Steel thunk to its repr
 *     We could implement it better by having support for reification only in the .fst file
 *     But for now assuming a (Dv) function
 *)
assume val reify_steel_comp
  (#a:Type) (#pre:slprop u#1) (#post:a -> slprop u#1) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> Steel a pre post req ens)
  : Dv (Sem.action_t #state #a pre post (req_to_act_req req) (ens_to_act_ens ens))

let par f g = par0 (reify_steel_comp f) (reify_steel_comp g)

let action_as_repr (#a:Type) (#p:slprop) (#q:a -> slprop) (f:action_except a Set.empty p q)
  : repr a false p q (fun _ -> True) (fun _ _ _ -> True)
  = Ins.state_correspondence Set.empty; f

val add_action (#a:Type)
               (#p:slprop)
               (#q:a -> slprop)
               (f:action_except a Set.empty p q)
  : SteelT a p q

let add_action f = Steel?.reflect (action_as_repr f)

val change_slprop (p q:slprop)
                  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelT unit p (fun _ -> q)

let change_slprop p q proof =
  Steel?.reflect (Steel.Memory.change_slprop #Set.empty p q proof)

let read r v0 = Steel?.reflect (action_as_repr (sel_action FStar.Set.empty r v0))
let write r v0 v1 = Steel?.reflect (action_as_repr (upd_action FStar.Set.empty r v0 v1))
let alloc x = Steel?.reflect (action_as_repr (alloc_action FStar.Set.empty x))
let free r x = Steel?.reflect (action_as_repr (free_action FStar.Set.empty r x))

val split' (#a:Type)
          (#p:FStar.PCM.pcm a)
          (r:ref a p)
          (v0:Ghost.erased a)
          (v1:Ghost.erased a{FStar.PCM.composable p v0 v1})
  : SteelT unit (pts_to r (FStar.PCM.op p v0 v1))
                (fun _ -> pts_to r v0 `star` pts_to r v1)

let split' #a #p r v0 v1 = Steel?.reflect (action_as_repr (split_action FStar.Set.empty r v0 v1))

let split #a #p r v v0 v1 =
  change_slprop (pts_to r v) (pts_to r (FStar.PCM.op p v0 v1)) (fun _ -> ());
  split' r v0 v1

let gather r v0 v1 = Steel?.reflect (action_as_repr (gather_action FStar.Set.empty r v0 v1))
let witness r fact v _ = Steel?.reflect (action_as_repr (Steel.Memory.witness FStar.Set.empty r fact v ()))
let recall r v = Steel?.reflect (action_as_repr (Steel.Memory.recall FStar.Set.empty r v))

let select_refine #a #p r x f = add_action (Steel.Memory.select_refine Set.empty r x f)

let upd_gen #a #p r x y f = add_action (Steel.Memory.upd_gen Set.empty r x y f)
