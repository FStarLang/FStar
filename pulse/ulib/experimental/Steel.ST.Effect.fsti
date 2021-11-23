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

module Steel.ST.Effect
open Steel.Memory
open FStar.Ghost
module Mem = Steel.Memory
module T = FStar.Tactics
include Steel.Effect.Common
#set-options "--warn_error -330"  //turn off the experimental feature warning
#set-options "--ide_id_info_off"


/// The framed bit indicates whether this computation has already been framed. This corresponds to the |- and |-_F modalities
/// in the ICFP21 paper
val repr (a:Type)
         (framed:bool)
         (pre:pre_t)
         (post:post_t a)
         (req:Type0)
         (ens:a -> Type0)
  : Type u#2

val return_ (a:Type)
            (x:a)
            (#[@@@ framing_implicit] p:a -> vprop)
  : repr a true (return_pre (p x)) p True (fun v -> v == x)

unfold
let bind_req (a:Type)
             (req_f:Type)
             (ens_f: a -> Type0)
             (pr:a -> prop)
             (req_g: a -> Type0)
  = req_f /\ (forall (x:a). ens_f x ==> pr x /\ req_g x)


unfold
let bind_ens (a:Type) (b:Type)
             (ens_f: a -> Type0)
             (ens_g: a -> b -> Type0)
  = fun (y:b) -> exists (x:a). ens_f x /\ ens_g x y

val bind (a:Type) (b:Type)
  (#framed_f:eqtype_as_type bool)
  (#framed_g:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t)
  (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:Type0)
  (#[@@@ framing_implicit] ens_f:a -> Type0)
  (#[@@@ framing_implicit] pre_g:a -> pre_t)
  (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(a -> Type0))
  (#[@@@ framing_implicit] ens_g:(a -> b -> Type0))
  (#[@@@ framing_implicit] frame_f:vprop)
  (#[@@@ framing_implicit] frame_g:a -> vprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] _ : squash (maybe_emp framed_f frame_f))
  (#[@@@ framing_implicit] _ : squash (maybe_emp_dep framed_g frame_g))
  (#[@@@ framing_implicit] pr:a -> prop)
  (#[@@@ framing_implicit] p1:squash
    (can_be_split_forall_dep pr
      (fun x -> post_f x `star` frame_f)
      (fun x -> pre_g x `star` frame_g x)))
  (#[@@@ framing_implicit] p2:squash
    (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:repr a framed_f pre_f post_f req_f ens_f)
  (g:(x:a -> repr b framed_g (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    true
    (pre_f `star` frame_f)
    post
    (bind_req a req_f ens_f pr req_g)
    (bind_ens a b ens_f ens_g)

val subcomp (a:Type)
  (#framed_f:eqtype_as_type bool)
  (#framed_g:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t)
  (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:Type0)
  (#[@@@ framing_implicit] ens_f:a -> Type0)
  (#[@@@ framing_implicit] pre_g:pre_t)
  (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] req_g:Type0)
  (#[@@@ framing_implicit] ens_g:a -> Type0)
  (#[@@@ framing_implicit] frame:vprop)
  (#[@@@ framing_implicit] _ : squash (maybe_emp framed_f frame))
  (#[@@@ framing_implicit] p1:squash (can_be_split pre_g (pre_f `star` frame)))
  (#[@@@ framing_implicit] p2:squash (equiv_forall post_g (fun x -> post_f x `star` frame)))
  (f:repr a framed_f pre_f post_f req_f ens_f)
: Pure (repr a framed_g pre_g post_g req_g ens_g)
  (requires
    req_g ==> (req_f /\ (forall x. ens_f x ==> ens_g x)))
  (ensures fun _ -> True)

/// Logical precondition for the if_then_else combinator
unfold
let if_then_else_req (p req_then req_else:Type0)
  : Type0
  =  (p ==> req_then) /\
     ((~ p) ==> req_else)

/// Logical precondition for the if_then_else combinator
unfold
let if_then_else_ens (a:Type)
                      (p:Type0)
                      (ens_then ens_else : a -> Type0)
  : a -> Type0
  = fun (x:a) ->
      (p ==>  ens_then x) /\
      (~p ==> ens_else x)

let if_then_else (a:Type)
  (#framed_f:eqtype_as_type bool)
  (#framed_g:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t)
  (#[@@@ framing_implicit] pre_g:pre_t)
  (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] req_then:Type0)
  (#[@@@ framing_implicit] ens_then:a -> Type0)
  (#[@@@ framing_implicit] req_else:Type0)
  (#[@@@ framing_implicit] ens_else:a -> Type0)
  (#[@@@ framing_implicit] frame_f : vprop)
  (#[@@@ framing_implicit] frame_g : vprop)
  (#[@@@ framing_implicit] me1 : squash (maybe_emp framed_f frame_f))
  (#[@@@ framing_implicit] me2 : squash (maybe_emp framed_g frame_g))
  (#[@@@ framing_implicit] s_pre: squash (can_be_split (pre_f `star` frame_f) (pre_g `star` frame_g)))
  (#[@@@ framing_implicit] s_post: squash (equiv_forall (fun x -> post_f x `star` frame_f) (fun x -> post_g x `star` frame_g)))
  (f:repr a framed_f pre_f post_f req_then ens_then)
  (g:repr a framed_g pre_g post_g req_else ens_else)
  (p:bool)
: Type
= repr a true
       (pre_f `star` frame_f)
       (fun x -> post_f x `star` frame_f)
       (if_then_else_req p req_then req_else)
       (if_then_else_ens a p ens_then ens_else)


/// Assembling the combinators defined above into an actual effect
[@@ite_soundness_by ite_attr]
reflectable
effect {
  STBase
    (a:Type) (framed:bool) (pre:pre_t) (post:post_t a) (req:Type0) (ens:a -> Type0)
  with { repr = repr;
         return = return_;
         bind = bind;
         subcomp = subcomp;
         if_then_else = if_then_else }
}

effect ST (a:Type) (pre:pre_t) (post:post_t a) (req:Type0) (ens:a -> Type0) =
  STBase a false pre post req ens
effect STF (a:Type) (pre:pre_t) (post:post_t a) (req:Type0) (ens:a -> Type0) =
  STBase a true pre post req ens


/// Logical precondition of a Pure and a Steel computation composition.
/// The current state (memory) must satisfy the precondition of the Steel computation,
/// and the wp of the PURE computation `as_requires wp` must also be satisfied
unfold
let bind_pure_st_req (#a:Type)
                     (wp:pure_wp a)
                     (req:a -> Type0)
 : Type0
 = wp req

/// Logical postcondition of a Pure and a Steel composition.
/// There exists an intermediate value (the output of the Pure computation) such that
/// the postcondition of the pure computation is satisfied.
unfold
let bind_pure_st_ens (#a:Type)
                     (#b:Type)
                     (wp:pure_wp a)
                     (ens: a -> b -> Type0)
    : b -> Type0
    = fun (r:b) -> as_requires wp /\ (exists (x:a). as_ensures wp x /\ ens x r)

/// The composition combinator.
val bind_pure_st_ (a:Type) (b:Type)
                  (#[@@@ framing_implicit] wp:pure_wp a)
                  (#framed:eqtype_as_type bool)
                  (#[@@@ framing_implicit] pre:pre_t)
                  (#[@@@ framing_implicit] post:post_t b)
                  (#[@@@ framing_implicit] req:a -> Type0)
                  (#[@@@ framing_implicit] ens:a -> b -> Type0)
                  (f:eqtype_as_type unit -> PURE a wp)
                  (g:(x:a -> repr b framed pre post (req x) (ens x)))
: repr b
    framed
    pre
    post
    (bind_pure_st_req wp req)
    (bind_pure_st_ens wp ens)

/// A polymonadic composition between Pure computations (in the PURE effects) and Steel computations (in the SteelBase effect).
/// Note that the SteelBase, PURE case is not handled here: In this case, a SteelBase return is automatically inserted by the F* typechecked
polymonadic_bind (PURE, STBase) |> STBase = bind_pure_st_

/// A version of the ST effect with trivial requires and ensures clauses
effect STT (a:Type) (pre:pre_t) (post:post_t a) =
  ST a pre post True (fun _ -> True)

val lift_st_steel
      (a:Type)
      (#framed:eqtype_as_type bool)
      (#pre:pre_t)
      (#post:post_t a)
      (#req:Type0)
      (#ens:a -> Type0)
      (f:repr a framed pre post req ens)
  : Steel.Effect.repr a framed pre post (fun _ -> req) (fun _ x _ -> ens x)

sub_effect STBase ~> Steel.Effect.SteelBase = lift_st_steel

val coerce_steel (#a:Type)
                 (#pre:pre_t)
                 (#post:post_t a)
                 (#req:Type0)
                 (#ens:a -> Type0)
                 ($f:unit -> Steel.Effect.SteelBase a false pre post
                          (fun _ -> req)
                          (fun _ x _ -> ens x))
   : ST a pre post req ens
