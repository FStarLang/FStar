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
open FStar.PCM
open Steel.Memory
include Steel.Effect.Common

#set-options "--warn_error -330"  //turn off the experimental feature warning

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

(*** SteelAGCommon effect ***)

val repr (a:Type u#a)
   (already_framed:bool)
   (opened_invariants:inames)
   (g:observability)
   (pre:slprop u#1)
   (post:a -> slprop u#1)
   (req:req_t pre)
   (ens:ens_t pre a post)
  : Type u#(max a 2)

unfold
let return_req (p:slprop u#1) : req_t p = fun _ -> True

unfold
let return_ens (a:Type) (x:a) (p:a -> slprop u#1) : ens_t (p x) a p = fun _ r _ -> r == x

val return_ (a:Type u#a)
   (x:a)
   (opened_invariants:inames)
   (#[@@@ framing_implicit] p:a -> slprop u#1)
  : repr a true opened_invariants Unobservable
      (return_pre (p x)) p
      (return_req (p x)) (return_ens a x p)

unfold
let bind_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (#pr: a -> prop)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:slprop) (frame_g:a -> slprop)
  (_:squash (can_be_split_forall_dep pr (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
: req_t (pre_f `star` frame_f)
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 ==> pr x /\ (req_g x) m1)

unfold
let bind_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (#pr:a -> prop)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:slprop) (frame_g:a -> slprop)
  (post:post_t b)
  (_:squash (can_be_split_forall_dep pr (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (_:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
: ens_t (pre_f `star` frame_f) b post
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x `star` frame_f)). pr x /\ ens_f m0 x m1 /\ (ens_g x) m1 y m2)

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
  (#[@@@ framing_implicit] frame_f:slprop) (#[@@@ framing_implicit] frame_g:a -> slprop)
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
  (_:squash (can_be_split_forall post_f post_g))
: pure_pre
= (forall (m0:hmem pre_g). req_g m0 ==> req_f m0) /\
  (forall (m0:hmem pre_g) (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 ==> ens_g m0 x m1)

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
  (#[@@@ framing_implicit] p2:squash (can_be_split_forall post_f post_g))
  (f:repr a framed_f opened_invariants o1 pre_f post_f req_f ens_f)
: Pure (repr a framed_g opened_invariants o2 pre_g post_g req_g ens_g)
       (requires (o1 = Unobservable || o2 = Observable) /\
         subcomp_pre req_f ens_f req_g ens_g p1 p2)
       (ensures fun _ -> True)

unfold
let if_then_else_req (#pre_f:pre_t) (#pre_g:pre_t)
  (s: squash (can_be_split pre_f pre_g))
  (req_then:req_t pre_f) (req_else:req_t pre_g)
  (p:Type0)
: req_t pre_f
= fun h -> (p ==> req_then h) /\ ((~ p) ==> req_else h)

unfold
let if_then_else_ens (#a:Type) (#pre_f:pre_t) (#pre_g:pre_t) (#post_f:post_t a) (#post_g:post_t a)
  (s1 : squash (can_be_split pre_f pre_g))
  (s2 : squash (equiv_forall post_f post_g))
  (ens_then:ens_t pre_f a post_f) (ens_else:ens_t pre_g a post_g)
  (p:Type0)
: ens_t pre_f a post_f
= fun h0 x h1 -> (p ==> ens_then h0 x h1) /\ ((~ p) ==> ens_else h0 x h1)

(*
 * The if-then-else combinator is only defined for ghost (Unobservable)
 *   computations
 *
 * The Observable computations are atomic, and composing them using if-then-else
 *   will not be
 *)
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
  SteelAGCommon (a:Type)
                (framed:bool)
                (opened_invariants:inames)
                (o:observability)
                (pre:slprop u#1)
                (post:a -> slprop u#1)
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
new_effect SteelAtomicBase =SteelAGCommon

effect SteelAtomic (a:Type)
  (opened:inames)
  (pre:slprop u#1)
  (post:a -> slprop u#1)
  (req:req_t pre)
  (ens:ens_t pre a post)
  = SteelAtomicBase a false opened Observable pre post req ens

effect SteelAtomicF (a:Type)
  (opened:inames)
  (pre:slprop u#1)
  (post:a -> slprop u#1)
  (req:req_t pre)
  (ens:ens_t pre a post)
  = SteelAtomicBase a true opened Observable pre post req ens

unfold
let bind_pure_steela__req (#a:Type) (wp:pure_wp a)
  (#pre:pre_t) (req:a -> req_t pre)
: req_t pre
= fun m -> wp (fun x -> (req x) m) /\ as_requires wp

unfold
let bind_pure_steela__ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre:pre_t) (#post:post_t b) (ens:a -> ens_t pre b post)
: ens_t pre b post
= fun m0 r m1 -> as_requires wp /\ (exists (x:a). as_ensures wp x /\ (ens x) m0 r m1)

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
    (bind_pure_steela__req wp req)
    (bind_pure_steela__ens wp ens)

polymonadic_bind (PURE, SteelAtomicBase) |> SteelAtomicBase = bind_pure_steela_

effect SteelAtomicT (a:Type) (opened:inames) (pre:pre_t) (post:post_t a) =
  SteelAtomic a opened pre post (fun _ -> True) (fun _ _ _ -> True)

(*** SteelGhost effect ***)

[@@ erasable]
total
reflectable
new_effect SteelGhostBase = SteelAGCommon

effect SteelGhost (a:Type)
  (opened:inames)
  (pre:slprop u#1)
  (post:a -> slprop u#1)
  (req:req_t pre)
  (ens:ens_t pre a post)
  = SteelGhostBase a false opened Unobservable pre post req ens

effect SteelGhostF (a:Type)
  (opened:inames)
  (pre:slprop u#1)
  (post:a -> slprop u#1)
  (req:req_t pre)
  (ens:ens_t pre a post)
  = SteelGhostBase a true opened Unobservable pre post req ens

polymonadic_bind (PURE, SteelGhostBase) |> SteelGhostBase = bind_pure_steela_

effect SteelGhostT (a:Type) (opened:inames) (pre:pre_t) (post:post_t a) =
  SteelGhost a opened pre post (fun _ -> True) (fun _ _ _ -> True)

(***** Lift relations *****)

val lift_ghost_atomic
  (a:Type)
  (opened:inames)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre:pre_t) (#[@@@ framing_implicit] post:post_t a)
  (#[@@@ framing_implicit] req:req_t pre) (#[@@@ framing_implicit] ens:ens_t pre a post)
  (f:repr a framed opened Unobservable pre post req ens)
  : repr a framed opened Unobservable pre post req ens

sub_effect SteelGhostBase ~> SteelAtomicBase = lift_ghost_atomic

val lift_atomic_steel
  (a:Type)
  (o:eqtype_as_type observability)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre:pre_t) (#[@@@ framing_implicit] post:post_t a)
  (#[@@@ framing_implicit] req:req_t pre) (#[@@@ framing_implicit] ens:ens_t pre a post)
  (f:repr a framed Set.empty o pre post req ens)
  : Steel.Effect.repr a framed pre post req ens

sub_effect SteelAtomicBase ~> Steel.Effect.SteelBase = lift_atomic_steel

[@@warn_on_use "as_atomic_action is a trusted primitive"]
val as_atomic_action (#a:Type u#a)
                     (#opened_invariants:inames)
                     (#fp:slprop)
                     (#fp': a -> slprop)
                     (f:action_except a opened_invariants fp fp')
  : SteelAtomicT a opened_invariants fp fp'

[@@warn_on_use "as_atomic_action is a trusted primitive"]
val as_atomic_action_ghost (#a:Type u#a)
                           (#opened_invariants:inames)
                           (#fp:slprop)
                           (#fp': a -> slprop)
                           (f:action_except a opened_invariants fp fp')
  : SteelGhostT a opened_invariants fp fp'

val new_invariant (opened_invariants:inames) (p:slprop)
  : SteelGhostT (inv p) opened_invariants p (fun _ -> emp)

let set_add i o : inames = Set.union (Set.singleton i) o
val with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#p:slprop)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   ($f:unit -> SteelAtomicT a (add_inv opened_invariants i)
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : SteelAtomicT a opened_invariants fp fp'

val with_invariant_g (#a:Type)
                     (#fp:slprop)
                     (#fp':a -> slprop)
                     (#opened_invariants:inames)
                     (#p:slprop)
                     (i:inv p{not (mem_inv opened_invariants i)})
                     ($f:unit -> SteelGhostT a (add_inv opened_invariants i)
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : SteelGhostT a opened_invariants fp fp'

val change_slprop (#opened_invariants:inames)
                  (p q:slprop)
                  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelGhostT unit opened_invariants p (fun _ -> q)

val rewrite_context (#opened:inames)
                    (#p:slprop)
                    (#q:slprop)
                    (_:unit)
  : SteelGhostF unit opened p (fun _ -> q)
                 (requires fun _ -> p `equiv` q) (ensures fun _ _ _ -> True)

val extract_info (#opened_invariants:inames) (p:slprop) (fact:prop)
  (l:(m:mem) -> Lemma (requires interp p m) (ensures fact))
  : SteelGhost unit opened_invariants p (fun _ -> p)
      (fun _ -> True)
      (fun _ _ _ -> fact)

val sladmit (#a:Type)
            (#opened:inames)
            (#p:pre_t)
            (#q:post_t a)
            (_:unit)
  : SteelGhostF a opened (admit_pre p) (admit_post q)
                 (requires fun _ -> True) (ensures fun _ _ _ -> False)

val slassert (#opened_invariants:_) (p:slprop)
  : SteelGhostT unit opened_invariants p (fun _ -> p)

val intro_pure (#opened_invariants:_) (p:prop)
  : SteelGhost unit opened_invariants emp (fun _ -> pure p)
                (requires fun _ -> p) (ensures fun _ _ _ -> True)

val intro_exists (#a:Type) (#opened_invariants:_) (x:a) (p:a -> slprop)
  : SteelGhostT unit opened_invariants (p x) (fun _ -> h_exists p)

val intro_exists_erased (#a:Type) (#opened_invariants:_) (x:Ghost.erased a) (p:a -> slprop)
  : SteelGhostT unit opened_invariants (p x) (fun _ -> h_exists p)

val drop (#opened:inames) (p:slprop) : SteelGhostT unit opened p (fun _ -> emp)

(* Witnessing an existential *)
val witness_h_exists (#a:Type) (#opened_invariants:_) (#p:a -> slprop) (_:unit)
  : SteelGhostT (Ghost.erased a) opened_invariants
                (h_exists p) (fun x -> p x)

module U = FStar.Universe

val lift_h_exists_atomic (#a:_) (#u:_) (p:a -> slprop)
  : SteelGhostT unit u
                (h_exists p)
                (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))

val h_exists_cong_atomic (#a:_) (#u:_) (p:a -> slprop) (q:a -> slprop {forall x. equiv (p x) (q x) })
  : SteelGhostT unit u
                (h_exists p)
                (fun _ -> h_exists q)

val elim_pure (#uses:_) (p:prop)
  : SteelGhost unit uses
               (pure p)
               (fun _ -> emp)
               (fun _ -> True)
               (fun _ _ _ -> p)

let lift_lemma #uses (p:slprop) (q:prop) (l:(hmem p -> Lemma q))
  : SteelGhostT (u:unit{q}) uses p (fun _ -> p)
  = change_slprop p (p `star` pure q) (fun m -> l m; Steel.Memory.pure_star_interp p q m; Steel.Memory.emp_unit p);
    elim_pure q

let drop_f (#opened:inames) (#p #f:slprop) ()
  : SteelGhostF unit opened (p `star` f) (fun _ -> p) (fun _ -> True) (fun _ _ _ -> True)
  = change_slprop (p `star` f) p (fun _ -> ()); ()

val sghost (#a:Type) (#opened_invariants:inames)
  (#pre:slprop u#1) (#post:a -> slprop u#1)
  (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> SteelGhostBase a false opened_invariants Unobservable pre post req ens)
  : SteelAtomicBase a false opened_invariants Unobservable pre post req ens

val return (#a:Type) (#opened_invariants:inames) (#p:a -> slprop) (x:a)
  : SteelAtomicBase a true opened_invariants Unobservable (return_pre (p x)) p (fun _ -> True) (fun _ r _ -> r == x)
