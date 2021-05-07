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

open Steel.Memory
include Steel.SelEffect.Common

#set-options "--warn_error -330 --ide_id_info_off"  //turn off the experimental feature warning

type observability : eqtype =
  | Observable
  | Unobservable

unfold
let obs_at_most_one (o1 o2:observability) =
  o1=Unobservable || o2=Unobservable

unfold
let join_obs (o1:observability) (o2:observability) =
  if o1 = Observable || o2 = Observable
  then Observable
  else Unobservable

(*** SteelSelAGCommon effect ***)

val repr (a:Type u#a)
   (already_framed:bool)
   (opened_invariants:inames)
   (g:observability)
   (pre:pre_t)
   (post:post_t a)
   (req:req_t pre)
   (ens:ens_t pre a post)
  : Type u#(max a 2)

unfold
let return_req (p:vprop) : req_t p = fun _ -> True

unfold
let return_ens (a:Type) (x:a) (p:a -> vprop) : ens_t (p x) a p =
  fun h0 r h1 -> normal (r == x /\ frame_equalities (p x) h0 h1)

val return_ (a:Type u#a)
  (x:a)
  (opened_invariants:inames)
  (#[@@@ framing_implicit] p:a -> vprop)
  : repr a true opened_invariants Unobservable
         (return_pre (p x)) p
         (return_req (p x)) (return_ens a x p)

unfold
let bind_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (#pr:a -> prop)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:vprop) (frame_g:a -> vprop)
  (_:squash (can_be_split_forall_dep pr (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
: req_t (pre_f `star` frame_f)
= fun m0 -> normal (
  req_f (focus_rmem m0 pre_f) /\
  (forall (x:a) (m1:rmem (post_f x `star` frame_f)).
    (ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) /\
      frame_equalities frame_f (focus_rmem m0 frame_f) (focus_rmem m1 frame_f))
    ==> pr x /\
      (can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
      (req_g x) (focus_rmem m1 (pre_g x)))))

unfold
let bind_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (#pr:a -> prop)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:vprop) (frame_g:a -> vprop)
  (post:post_t b)
  (_:squash (can_be_split_forall_dep pr (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (_:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
: ens_t (pre_f `star` frame_f) b post
= fun m0 y m2 -> normal (
  req_f (focus_rmem m0 pre_f) /\
  (exists (x:a) (m1:rmem (post_f x `star` frame_f)).
    pr x /\
    (
    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (frame_g x);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (post_g x y);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (frame_g x);
    frame_equalities frame_f (focus_rmem m0 frame_f) (focus_rmem m1 frame_f) /\
    frame_equalities (frame_g x) (focus_rmem m1 (frame_g x)) (focus_rmem m2 (frame_g x)) /\
    ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) /\
    (ens_g x) (focus_rmem m1 (pre_g x)) y (focus_rmem m2 (post_g x y)))))

val bind (a:Type) (b:Type)
  (opened_invariants:inames)
  (o1:eqtype_as_type observability)
  (o2:eqtype_as_type observability)
  (#framed_f:eqtype_as_type bool)
  (#framed_g:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] frame_f:vprop) (#[@@@ framing_implicit] frame_g:a -> vprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] _ : squash (maybe_emp framed_f frame_f))
  (#[@@@ framing_implicit] _ : squash (maybe_emp_dep framed_g frame_g))
  (#[@@@ framing_implicit] pr:a -> prop)
  (#[@@@ framing_implicit] p1:squash (can_be_split_forall_dep pr
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:repr a framed_f opened_invariants o1 pre_f post_f req_f ens_f)
  (g:(x:a -> repr b framed_g opened_invariants o2 (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Pure (repr b true opened_invariants (join_obs o1 o2)
    (pre_f `star` frame_f)
    post
    (bind_req req_f ens_f req_g frame_f frame_g p1)
    (bind_ens req_f ens_f ens_g frame_f frame_g post p1 p2)
    )
    (requires obs_at_most_one o1 o2)
    (ensures fun _ -> True)

unfold
let subcomp_pre (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (_:squash (can_be_split pre_g pre_f))
  (_:squash (equiv_forall post_f post_g))
: pure_pre
= (forall (m0:rmem pre_g). normal (req_g m0 ==> req_f (focus_rmem m0 pre_f))) /\
  (forall (m0:rmem pre_g) (x:a) (m1:rmem (post_g x)). normal (
      ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) ==> ens_g m0 x m1
    )
  )

val subcomp (a:Type)
  (opened_invariants:inames)
  (o1:eqtype_as_type observability)
  (o2:eqtype_as_type observability)
  (#framed_f: eqtype_as_type bool)
  (#framed_g: eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:pre_t) (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] req_g:req_t pre_g) (#[@@@ framing_implicit] ens_g:ens_t pre_g a post_g)
  (#[@@@ framing_implicit] p1:squash (can_be_split pre_g pre_f))
  (#[@@@ framing_implicit] p2:squash (equiv_forall post_f post_g))
  (f:repr a framed_f opened_invariants o1 pre_f post_f req_f ens_f)
: Pure (repr a framed_g opened_invariants o2 pre_g post_g req_g ens_g)
       (requires (o1 = Unobservable || o2 = Observable) /\
         subcomp_pre req_f ens_f req_g ens_g p1 p2)
       (ensures fun _ -> True)

unfold
let if_then_else_req
  (#pre_f:pre_t) (#pre_g:pre_t)
  (s: squash (can_be_split pre_f pre_g))
  (req_then:req_t pre_f) (req_else:req_t pre_g)
  (p:Type0)
: req_t pre_f
= fun h -> normal (
    (p ==> req_then h) /\
    ((~ p) ==> req_else (focus_rmem h pre_g))
  )

unfold
let if_then_else_ens (#a:Type)
  (#pre_f:pre_t) (#pre_g:pre_t) (#post_f:post_t a) (#post_g:post_t a)
  (s1 : squash (can_be_split pre_f pre_g))
  (s2 : squash (equiv_forall post_f post_g))
  (ens_then:ens_t pre_f a post_f) (ens_else:ens_t pre_g a post_g)
  (p:Type0)
: ens_t pre_f a post_f
= fun h0 x h1 -> normal (
    (p ==> ens_then (focus_rmem h0 pre_f) x (focus_rmem h1 (post_f x))) /\
    ((~ p) ==> ens_else (focus_rmem h0 pre_g) x (focus_rmem h1 (post_g x)))
  )

let if_then_else (a:Type)
  (o:inames)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] pre_g:pre_t)
  (#[@@@ framing_implicit] post_f:post_t a) (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] req_then:req_t pre_f) (#[@@@ framing_implicit] ens_then:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] req_else:req_t pre_g) (#[@@@ framing_implicit] ens_else:ens_t pre_g a post_g)
  (#[@@@ framing_implicit] s_pre: squash (can_be_split pre_f pre_g))
  (#[@@@ framing_implicit] s_post: squash (equiv_forall post_f post_g))
  (f:repr a framed o Unobservable pre_f post_f req_then ens_then)
  (g:repr a framed o Unobservable pre_g post_g req_else ens_else)
  (p:bool)
: Type
= repr a framed o Unobservable pre_f post_f
       (if_then_else_req s_pre req_then req_else p)
       (if_then_else_ens s_pre s_post ens_then ens_else p)

total
reflectable
effect {
  SteelSelAGCommon (a:Type)
                   (framed:bool)
                   (opened_invariants:inames)
                   (o:observability)
                   (pre:pre_t)
                   (post:post_t a)
                   (req:req_t pre)
                   (ens:ens_t pre a post)
  with { repr = repr;
         return = return_;
         bind = bind;
         subcomp = subcomp;
         if_then_else = if_then_else }
}

total
reflectable
new_effect SteelSelAtomicBase = SteelSelAGCommon

effect SteelSelAtomic (a:Type)
  (opened:inames)
  (pre:pre_t)
  (post:post_t a)
  (req:req_t pre)
  (ens:ens_t pre a post)
  = SteelSelAtomicBase a false opened Observable pre post req ens

effect SteelSelAtomicF (a:Type)
  (opened:inames)
  (pre:pre_t)
  (post:post_t a)
  (req:req_t pre)
  (ens:ens_t pre a post)
  = SteelSelAtomicBase a true opened Observable pre post req ens

unfold
let bind_pure_steel__req (#a:Type) (wp:pure_wp a)
  (#pre:pre_t) (req:a -> req_t pre)
: req_t pre
= fun m -> normal ((wp (fun x -> (req x) m) /\ as_requires wp))

unfold
let bind_pure_steel__ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre:pre_t) (#post:post_t b) (ens:a -> ens_t pre b post)
: ens_t pre b post
= fun m0 r m1 -> normal ((as_requires wp /\ (exists (x:a). as_ensures wp x /\ ((ens x) m0 r m1))))

val bind_pure_steela_ (a:Type) (b:Type)
  (opened_invariants:inames)
  (o:eqtype_as_type observability)
  (#[@@@ framing_implicit] wp:pure_wp a)
  (#framed: eqtype_as_type bool)
  (#[@@@ framing_implicit] pre:pre_t) (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] req:a -> req_t pre) (#[@@@ framing_implicit] ens:a -> ens_t pre b post)
  (f:eqtype_as_type unit -> PURE a wp)
  (g:(x:a -> repr b framed opened_invariants o pre post (req x) (ens x)))
: repr b framed opened_invariants o
    pre
    post
    (bind_pure_steel__req wp req)
    (bind_pure_steel__ens wp ens)

polymonadic_bind (PURE, SteelSelAtomicBase) |> SteelSelAtomicBase = bind_pure_steela_

effect SteelSelAtomicT (a:Type) (opened:inames) (pre:pre_t) (post:post_t a) =
  SteelSelAtomic a opened pre post (fun _ -> True) (fun _ _ _ -> True)

(*** SteelGhost effect ***)

[@@ erasable]
total
reflectable
new_effect SteelSelGhostBase = SteelSelAGCommon

effect SteelSelGhost (a:Type)
  (opened:inames)
  (pre:pre_t)
  (post:post_t a)
  (req:req_t pre)
  (ens:ens_t pre a post)
  = SteelSelGhostBase a false opened Unobservable pre post req ens

effect SteelSelGhostF (a:Type)
  (opened:inames)
  (pre:pre_t)
  (post:post_t a)
  (req:req_t pre)
  (ens:ens_t pre a post)
  = SteelSelGhostBase a true opened Unobservable pre post req ens

polymonadic_bind (PURE, SteelSelGhostBase) |> SteelSelGhostBase = bind_pure_steela_

effect SteelSelGhostT (a:Type) (opened:inames) (pre:pre_t) (post:post_t a) =
  SteelSelGhost a opened pre post (fun _ -> True) (fun _ _ _ -> True)

(***** Lift relations *****)

val lift_ghost_atomic
  (a:Type)
  (opened:inames)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre:pre_t) (#[@@@ framing_implicit] post:post_t a)
  (#[@@@ framing_implicit] req:req_t pre) (#[@@@ framing_implicit] ens:ens_t pre a post)
  (f:repr a framed opened Unobservable pre post req ens)
  : repr a framed opened Unobservable pre post req ens

sub_effect SteelSelGhostBase ~> SteelSelAtomicBase = lift_ghost_atomic

val lift_atomic_steel
  (a:Type)
  (o:eqtype_as_type observability)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre:pre_t) (#[@@@ framing_implicit] post:post_t a)
  (#[@@@ framing_implicit] req:req_t pre) (#[@@@ framing_implicit] ens:ens_t pre a post)
  (f:repr a framed Set.empty o pre post req ens)
  : Steel.SelEffect.repr a framed pre post req ens

sub_effect SteelSelAtomicBase ~> Steel.SelEffect.SteelSelBase = lift_atomic_steel

[@@warn_on_use "as_atomic_action is a trusted primitive"]
val as_atomic_action (#a:Type u#a)
                     (#opened_invariants:inames)
                     (#fp:slprop)
                     (#fp': a -> slprop)
                     (f:action_except a opened_invariants fp fp')
  : SteelSelAtomicT a opened_invariants (to_vprop fp) (fun x -> to_vprop (fp' x))

[@@warn_on_use "as_atomic_action is a trusted primitive"]
val as_atomic_action_ghost (#a:Type u#a)
                           (#opened_invariants:inames)
                           (#fp:slprop)
                           (#fp': a -> slprop)
                           (f:action_except a opened_invariants fp fp')
  : SteelSelGhostT a opened_invariants (to_vprop fp) (fun x -> to_vprop (fp' x))

(* Some helper functions *)

open FStar.Ghost

val get (#p:vprop) (#opened:inames) (_:unit) : SteelSelGhostF (erased (rmem p))
  opened
  p (fun _ -> p)
  (requires fun _ -> True)
  (ensures fun h0 r h1 -> normal (frame_equalities p h0 h1 /\ frame_equalities p r h1))

let gget (#opened:inames) (p: vprop) : SteelSelGhost (erased (t_of p))
  opened
  p (fun _ -> p)
  (requires (fun _ -> True))
  (ensures (fun h0 res h1 ->
    h1 p == h0 p /\
    reveal res == h0 p /\
    reveal res == h1 p
  ))
=
  let m = get #p () in
  hide ((reveal m) p)

val rewrite_slprop
  (#opened:inames)
  (p q:vprop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m)
    (ensures interp (hp_of q) m)
  ) : SteelSelGhostT unit opened p (fun _ -> q)

val change_slprop
  (#opened:inames)
  (p q:vprop) (vp:erased (normal (t_of p))) (vq:erased (normal (t_of q)))
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures interp (hp_of q) m /\ sel_of q m == reveal vq)
  ) : SteelSelGhost unit opened p (fun _ -> q)
                    (fun h -> h p == reveal vp) (fun _ _ h1 -> h1 q == reveal vq)

val change_equal_slprop (#opened:inames) (p q: vprop)
  : SteelSelGhost unit opened p (fun _ -> q) (fun _ -> p == q) (fun h0 _ h1 -> p == q /\ h1 q == h0 p)

val change_slprop_2 (#opened:inames) (p q:vprop) (vq:erased (t_of q))
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m)
    (ensures interp (hp_of q) m /\ sel_of q m == reveal vq)
  ) : SteelSelGhost unit opened p (fun _ -> q) (fun _ -> True) (fun _ _ h1 -> h1 q == reveal vq)

val change_slprop_rel (#opened:inames) (p q:vprop)
  (rel : normal (t_of p) -> normal (t_of q) -> prop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m)
    (ensures interp (hp_of q) m /\
      rel (sel_of p m) (sel_of q m))
  ) : SteelSelGhost unit opened p (fun _ -> q) (fun _ -> True) (fun h0 _ h1 -> rel (h0 p) (h1 q))

val change_slprop_rel_with_cond (#opened:inames)
  (p q:vprop)
  (cond:  (t_of p) -> prop)
  (rel :  (t_of p) ->  (t_of q) -> prop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ cond (sel_of p m))
    (ensures interp (hp_of q) m /\
      rel (sel_of p m) (sel_of q m))
  ) : SteelSelGhost unit opened p (fun _ -> q) (fun h0 -> cond (h0 p)) (fun h0 _ h1 -> rel (h0 p) (h1 q))

val extract_info (#opened:inames) (p:vprop) (vp:erased (normal (t_of p))) (fact:prop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures fact)
  ) : SteelSelGhost unit opened p (fun _ -> p)
      (fun h -> h p == reveal vp)
      (fun h0 _ h1 -> normal (frame_equalities p h0 h1) /\ fact)

val extract_info_raw (#opened:inames) (p:vprop) (fact:prop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m)
    (ensures fact)
  ) : SteelSelGhost unit opened p (fun _ -> p)
      (fun h -> True)
      (fun h0 _ h1 -> normal (frame_equalities p h0 h1) /\ fact)


val noop (#opened:inames) (_:unit)
  : SteelSelGhost unit opened emp (fun _ -> emp) (requires fun _ -> True) (ensures fun _ _ _ -> True)

val sladmit (#a:Type)
            (#opened:inames)
            (#p:pre_t)
            (#q:post_t a)
            (_:unit)
  : SteelSelGhostF a opened p q (requires fun _ -> True) (ensures fun _ _ _ -> False)

val drop (#opened:inames) (p:vprop) : SteelSelGhostT unit opened p (fun _ -> emp)

val reveal_star (#opened:inames) (p1 p2:vprop)
 : SteelSelGhost unit opened (p1 `star` p2) (fun _ -> p1 `star` p2)
   (requires fun _ -> True)
   (ensures fun h0 _ h1 ->
     h0 p1 == h1 p1 /\
     h0 p2 == h1 p2 /\
     h0 (p1 `star` p2) == (h0 p1, h0 p2) /\
     h1 (p1 `star` p2) == (h1 p1, h1 p2)
   )

val reveal_star_3 (#opened:inames) (p1 p2 p3:vprop)
 : SteelSelGhost unit opened (p1 `star` p2 `star` p3) (fun _ -> p1 `star` p2 `star` p3)
   (requires fun _ -> True)
   (ensures fun h0 _ h1 ->
     can_be_split (p1 `star` p2 `star` p3) p1 /\
     can_be_split (p1 `star` p2 `star` p3) p2 /\
     h0 p1 == h1 p1 /\ h0 p2 == h1 p2 /\ h0 p3 == h1 p3 /\
     h0 (p1 `star` p2 `star` p3) == ((h0 p1, h0 p2), h0 p3) /\
     h1 (p1 `star` p2 `star` p3) == ((h1 p1, h1 p2), h1 p3)
   )

val intro_pure (#opened_invariants:_) (p:prop)
  : SteelSelGhost unit opened_invariants emp (fun _ -> pure p)
                (requires fun _ -> p) (ensures fun _ _ _ -> True)

val elim_pure (#uses:_) (p:prop)
  : SteelSelGhost unit uses (pure p) (fun _ -> emp)
               (requires fun _ -> True) (ensures fun _ _ _ -> p)

let return (#a:Type u#a)
  (#opened_invariants:inames)
  (#p:a -> vprop)
  (x:a)
  : SteelSelAtomicBase a true opened_invariants Unobservable
         (return_pre (p x)) p
         (return_req (p x)) (return_ens a x p)
  = SteelSelAtomicBase?.reflect (return_ a x opened_invariants #p)

(* h_exists combinator *)

let h_exists_sl (#a:Type u#b) (p: (a -> vprop)) : slprop = h_exists (fun x -> hp_of (p x))
[@@__steel_reduce__]
unfold let h_exists #a (p:a -> vprop) : vprop = to_vprop (h_exists_sl p)

val intro_exists (#a:Type) (#opened_invariants:_) (x:a) (p:a -> vprop)
  : SteelSelGhostT unit opened_invariants (p x) (fun _ -> h_exists p)

val witness_exists (#a:Type) (#opened_invariants:_) (#p:a -> vprop) (_:unit)
  : SteelSelGhostT (erased a) opened_invariants
                (h_exists p) (fun x -> p x)

val intro_exists_erased (#a:Type) (#opened_invariants:_) (x:Ghost.erased a) (p:a -> vprop)
  : SteelSelGhostT unit opened_invariants (p x) (fun _ -> h_exists p)

module U = FStar.Universe

val lift_exists (#a:_) (#u:_) (p:a -> vprop)
  : SteelSelGhostT unit u
                (h_exists p)
                (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))

val exists_cong (#a:_) (#u:_) (p:a -> vprop) (q:a -> vprop {forall x. equiv (p x) (q x) })
  : SteelSelGhostT unit u
                (h_exists p)
                (fun _ -> h_exists q)

(* Introduction and elimination principles for vprop combinators *)

val intro_vrefine (#opened:inames)
  (v: vprop) (p: (normal (t_of v) -> Tot prop))
: SteelSelGhost unit opened v (fun _ -> vrefine v p)
  (requires (fun h -> p (h v)))
  (ensures (fun h _ h' -> normal (h' (vrefine v p) == h v)))

val elim_vrefine (#opened:inames)
  (v: vprop) (p: (normal (t_of v) -> Tot prop))
: SteelSelGhost unit opened (vrefine v p) (fun _ -> v)
  (requires (fun _ -> True))
  (ensures (fun h _ h' -> normal (h' v == h (vrefine v p)) /\ p (h' v)))

val intro_vdep (#opened:inames)
  (v: vprop)
  (q: vprop)
  (p: (t_of v -> Tot vprop))
: SteelSelGhost unit opened
    (v `star` q)
    (fun _ -> vdep v p)
    (requires (fun h -> q == p (h v)))
    (ensures (fun h _ h' ->
      let x2 = h' (vdep v p) in
      q == p (h v) /\
      dfst x2 == (h v) /\
      dsnd x2 == (h q)
    ))

val elim_vdep (#opened:inames)
  (v: vprop)
  (p: (t_of v -> Tot vprop))
: SteelSelGhost (Ghost.erased (t_of v)) opened
  (vdep v p)
  (fun res -> v `star` p (Ghost.reveal res))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
      let fs = h' v in
      let sn : t_of (p (Ghost.reveal res)) = h' (p (Ghost.reveal res)) in
      let x2 = h (vdep v p) in
      Ghost.reveal res == fs /\
      dfst x2 == fs /\
      dsnd x2 == sn
  ))

val intro_vrewrite (#opened:inames)
  (v: vprop) (#t: Type) (f: (normal (t_of v) -> GTot t))
: SteelSelGhost unit opened v (fun _ -> vrewrite v f)
                (fun _ -> True) (fun h _ h' -> h' (vrewrite v f) == f (h v))

val elim_vrewrite (#opened:inames)
  (v: vprop)
  (#t: Type)
  (f: (normal (t_of v) -> GTot t))
: SteelSelGhost unit opened (vrewrite v f) (fun _ -> v)
    (fun _ -> True)
    (fun h _ h' -> h (vrewrite v f) == f (h' v))
