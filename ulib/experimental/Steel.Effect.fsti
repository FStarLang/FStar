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
   limitations under the License.o
*)

module Steel.Effect

open Steel.Memory
module Mem = Steel.Memory
module FExt = FStar.FunctionalExtensionality
open FStar.Ghost
include Steel.Effect.Common

/// This module defines the main Steel effect, with requires and ensures predicates operating on
/// selectors, which will be discharged by SMT

#set-options "--warn_error -330"  //turn off the experimental feature warning

(* Defining the Steel effect with selectors *)

/// The underlying representation of Steel computations.
/// The framed bit indicates whether this computation has already been framed. This corresponds to the |- and |-_F modalities
/// in the ICFP21 paper
val repr (a:Type) (framed:bool) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) : Type u#2

/// Logical precondition of the return combinator
unfold
let return_req (p:vprop) : req_t p = fun _ -> True

/// Logical postcondition of the return combinator:
/// The returned value [r] corresponds to the value passed to the return [x],
/// and return leaves selectors of all resources in [p] unchanged
unfold
let return_ens (a:Type) (x:a) (p:a -> vprop) : ens_t (p x) a p =
  fun h0 r h1 -> normal (r == x /\ frame_equalities (p x) h0 h1)

/// Monadic return combinator for the Steel effect. It is parametric in the postcondition
/// The vprop precondition is annotated with the return_pre predicate to enable special handling,
/// as explained in Steel.Effect.Common
val return_ (a:Type) (x:a) (#[@@@ framing_implicit] p:a -> vprop)
: repr a true (return_pre (p x)) p (return_req (p x)) (return_ens a x p)

/// Logical precondition for the composition (bind) of two Steel computations:
/// The postcondition of the first computation must imply the precondition of the second computation,
/// and also ensure that any equalities abducted during frame inference inside the predicate [pr] are satisfied
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

/// Logical postcondition for the composition (bind) of two Steel computations:
/// The precondition of the first computation was satisfied in the initial state, and there
/// exists an intermediate state where the two-state postcondition of the first computation was
/// satisfied, and which yields the validity of the two-state postcondition of the second computation
/// on the final state [m2] with the returned value [y]
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

/// Steel effect combinator to compose two Steel computations
/// Separation logic VCs are squashed goals passed as implicits, annotated with the framing_implicit
/// attribute. This indicates that they will be discharged by the tactic in Steel.Effect.Common
/// Requires/ensures logical VCs are defined using weakest preconditions combinators defined above,
/// and discharged by SMT.
val bind (a:Type) (b:Type)
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
  (f:repr a framed_f pre_f post_f req_f ens_f)
  (g:(x:a -> repr b framed_g (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    true
    (pre_f `star` frame_f)
    post
    (bind_req req_f ens_f req_g frame_f frame_g p1)
    (bind_ens req_f ens_f ens_g frame_f frame_g post p1 p2)

/// Logical precondition for subtyping relation for Steel computation.
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

/// Subtyping combinator for Steel computations.
/// Computation [f] is given type `repr a framed_g pre_g post_g req_g ens_g`.
/// As for bind, separation logic goals are encoded as squashed implicits which will be discharged
/// by tactic, while logical requires/ensures operating on selectors are discharged by SMT
val subcomp (a:Type)
  (#framed_f:eqtype_as_type bool)
  (#framed_g:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:pre_t) (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] req_g:req_t pre_g) (#[@@@ framing_implicit] ens_g:ens_t pre_g a post_g)
  (#[@@@ framing_implicit] p1:squash (can_be_split pre_g pre_f))
  (#[@@@ framing_implicit] p2:squash (equiv_forall post_f post_g))
  (f:repr a framed_f pre_f post_f req_f ens_f)
: Pure (repr a framed_g pre_g post_g req_g ens_g)
  (requires (subcomp_pre req_f ens_f req_g ens_g p1 p2))
  (ensures fun _ -> True)

/// Logical precondition for the if_then_else combinator
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

/// Logical postcondition for the if_then_else combinator
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

/// If_then_else combinator for Steel computations.
/// The soundness of this combinator is automatically proven with respect to the subcomp
/// subtyping combinator defined above by the F* layered effects framework
let if_then_else (a:Type)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] pre_g:pre_t)
  (#[@@@ framing_implicit] post_f:post_t a) (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] req_then:req_t pre_f) (#[@@@ framing_implicit] ens_then:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] req_else:req_t pre_g) (#[@@@ framing_implicit] ens_else:ens_t pre_g a post_g)
  (#[@@@ framing_implicit] s_pre: squash (can_be_split pre_f pre_g))
  (#[@@@ framing_implicit] s_post: squash (equiv_forall post_f post_g))
  (f:repr a framed pre_f post_f req_then ens_then)
  (g:repr a framed pre_g post_g req_else ens_else)
  (p:bool)
: Type
= repr a framed pre_f post_f
    (if_then_else_req s_pre req_then req_else p)
    (if_then_else_ens s_pre s_post ens_then ens_else p)

/// Assembling the combinators defined above into an actual effect
reflectable
effect {
  SteelBase
    (a:Type) (framed:bool) (pre:pre_t) (post:post_t a) (_:req_t pre) (_:ens_t pre a post)
  with { repr = repr;
         return = return_;
         bind = bind;
         subcomp = subcomp;
         if_then_else = if_then_else }
}

/// The two user-facing effects, corresponding to not yet framed (Steel) and already framed (SteelF)
/// computations. In the ICFP21 paper, this is modeled by the |- and |-_F modalities
effect Steel (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  SteelBase a false pre post req ens
effect SteelF (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  SteelBase a true pre post req ens

(* Composing Steel and Pure computations *)

/// Logical precondition of a Pure and a Steel computation composition.
/// The current state (memory) must satisfy the precondition of the Steel computation,
/// and the wp of the PURE computation `as_requires wp` must also be satisfied
unfold
let bind_pure_steel__req (#a:Type) (wp:pure_wp a)
  (#pre:pre_t) (req:a -> req_t pre)
: req_t pre
= fun m -> normal ((wp (fun x -> (req x) m) /\ as_requires wp))

/// Logical postcondition of a Pure and a Steel composition.
/// There exists an intermediate value (the output of the Pure computation) such that
/// the postcondition of the pure computation is satisfied.
unfold
let bind_pure_steel__ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre:pre_t) (#post:post_t b) (ens:a -> ens_t pre b post)
: ens_t pre b post
= fun m0 r m1 -> normal ((as_requires wp /\ (exists (x:a). as_ensures wp x /\ ((ens x) m0 r m1))))

/// The composition combinator.
val bind_pure_steel_ (a:Type) (b:Type)
  (#[@@@ framing_implicit] wp:pure_wp a)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre:pre_t) (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] req:a -> req_t pre) (#[@@@ framing_implicit] ens:a -> ens_t pre b post)
  (f:eqtype_as_type unit -> PURE a wp) (g:(x:a -> repr b framed pre post (req x) (ens x)))
: repr b
    framed
    pre
    post
    (bind_pure_steel__req wp req)
    (bind_pure_steel__ens wp ens)

/// A polymonadic composition between Pure computations (in the PURE effects) and Steel computations (in the SteelBase effect).
/// Note that the SteelBase, PURE case is not handled here: In this case, a SteelBase return is automatically inserted by the F* typechecked
polymonadic_bind (PURE, SteelBase) |> SteelBase = bind_pure_steel_

/// A version of the Steel effect with trivial requires and ensures clauses
effect SteelT (a:Type) (pre:pre_t) (post:post_t a) =
  Steel a pre post (fun _ -> True) (fun _ _ _ -> True)

(*** Exposing actions as Steel functions ***)

(* AF: Ideally, we would like to provide par with requires/ensures.
   But this currently interacts badly with normalization when trying
   to implement the combinator. Restricting this to SteelT for now,
   a user can always pass necessary req/ens as pure + vrefine vprops *)

val par (#aL:Type u#a)
        (#aR:Type u#a)
        (#preL:vprop)
        (#postL:aL -> vprop)
        // (#lpreL:req_t preL)
        // (#lpostL:ens_t preL aL postL)
        ($f:unit -> SteelT aL preL postL) // lpreL lpostL)
        (#preR:vprop)
        (#postR:aR -> vprop)
        // (#lpreR:req_t preR)
        // (#lpostR:ens_t preR aR postR)
        ($g:unit -> SteelT aR preR postR) // lpreR lpostR)
  : SteelT (aL & aR)
    (preL `star` preR)
    (fun y -> postL (fst y) `star` postR (snd y))
    // (fun h -> lpreL (focus_rmem h preL) /\ lpreR (focus_rmem h preR))
    // (fun h0 y h1 -> lpreL (focus_rmem h0 preL) /\ lpreR (focus_rmem h0 preR) /\
    //   lpostL (focus_rmem h0 preL) (fst y) (focus_rmem h1 (postL (fst y))) /\
    //   lpostR (focus_rmem h0 preR) (snd y) (focus_rmem h1 (postR (snd y))))


/// Lifting an action from the memory model to a Steel computation.
/// Only to be used internally, for the core primitives of the Steel framework
[@@warn_on_use "as_action is a trusted primitive"]
val as_action  (#a:Type)
               (#p:slprop)
               (#q:a -> slprop)
               (f:action_except a Set.empty p q)
  : SteelT a (to_vprop p) (fun x -> to_vprop (q x))
