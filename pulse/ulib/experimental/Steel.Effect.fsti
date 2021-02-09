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
open Steel.Memory
open Steel.Semantics.Instantiate
include Steel.Effect.Common

module Ins = Steel.Semantics.Instantiate

#set-options "--warn_error -330"  //turn off the experimental feature warning

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

val repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) : Type u#2

unfold
let return_req (p:slprop u#1) : req_t p = fun _ -> True

unfold
let return_ens (a:Type) (x:a) (p:a -> slprop u#1) : ens_t (p x) a p = fun _ r _ -> r == x

(*
 * Return is parametric in post (cf. return-scoping.txt)
 *)
val return (a:Type) (x:a) (#[@@ framing_implicit] p:a -> slprop)
: repr a (return_pre (p x)) (return_post p) (return_req (p x)) (return_ens a x p)

(*
 * We allow weakening of post resource of f to pre resource of g
 *)
unfold
let bind_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (pr:a -> prop)
  (_:squash (can_be_split_forall_dep pr post_f pre_g))
: req_t pre_f
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 ==> pr x /\ (req_g x) m1)

unfold
let bind_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (post:post_t b)
  (pr1:a -> prop)
  (_:squash (can_be_split_forall_dep pr1 post_f pre_g))
  (_:squash (can_be_split_post post_g post))
: ens_t pre_f b post
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x)). pr1 x /\ ens_f m0 x m1 /\ (ens_g x) m1 y m2)

val bind (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] pr1:a -> prop)
  (#[@@ framing_implicit] p1:squash (can_be_split_forall_dep pr1 post_f pre_g))
  (#[@@ framing_implicit] p2:squash (can_be_split_post post_g post))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    pre_f
    post
    (bind_req req_f ens_f req_g pr1 p1)
    (bind_ens req_f ens_f ens_g post pr1 p1 p2)


(*
 * TODO: bind should do substitution for pure c1 (if bind c1 c2)
 *         applications might be ok, but let bindings may fail currently
 *)

(*
 * f <: g
 *)

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
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:pre_t) (#[@@ framing_implicit] post_g:post_t a)
  (#[@@ framing_implicit] req_g:req_t pre_g) (#[@@ framing_implicit] ens_g:ens_t pre_g a post_g)
  (#[@@ framing_implicit] p1:squash (can_be_split pre_g pre_f))
  (#[@@ framing_implicit] p2:squash (can_be_split_forall post_f post_g))
  (f:repr a pre_f post_f req_f ens_f)
: Pure (repr a pre_g post_g req_g ens_g)
  (requires subcomp_pre req_f ens_f req_g ens_g p1 p2)
  (ensures fun _ -> True)

unfold
let if_then_else_req (#pre_f:pre_t) (#pre_g:pre_t) (s: squash (can_be_split pre_f pre_g))
  (req_then:req_t pre_f) (req_else:req_t pre_g)
  (p:Type0)
: req_t pre_f
= fun h -> (p ==> req_then h) /\ ((~ p) ==> req_else h)

unfold
let if_then_else_ens (#a:Type) (#pre_f:pre_t) (#pre_g:pre_t) (#post_f:post_t a) (#post_g:post_t a)
  (s1 : squash (can_be_split pre_f pre_g)) (s2 : squash (equiv_forall post_f post_g))
  (ens_then:ens_t pre_f a post_f) (ens_else:ens_t pre_g a post_g)
  (p:Type0)
: ens_t pre_f a post_f
= fun h0 x h1 -> (p ==> ens_then h0 x h1) /\ ((~ p) ==> ens_else h0 x h1)

let if_then_else (a:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] pre_g:pre_t)
  (#[@@ framing_implicit] post_f:post_t a) (#[@@ framing_implicit] post_g:post_t a)
  (#[@@ framing_implicit] req_then:req_t pre_f) (#[@@ framing_implicit] ens_then:ens_t pre_f a post_f)
  (#[@@ framing_implicit] req_else:req_t pre_g) (#[@@ framing_implicit] ens_else:ens_t pre_g a post_g)
  (#[@@ framing_implicit] s_pre: squash (can_be_split pre_f pre_g))
  (#[@@ framing_implicit] s_post: squash (equiv_forall post_f post_g))
  (f:repr a pre_f post_f req_then ens_then)
  (g:repr a pre_g post_g req_else ens_else)
  (p:bool)
: Type
= repr a pre_f post_f
    (if_then_else_req s_pre req_then req_else p)
    (if_then_else_ens s_pre s_post ens_then ens_else p)

[@@allow_informative_binders]
reifiable reflectable
layered_effect {
  SteelF: a:Type -> pre:pre_t -> post:post_t a -> req_t pre -> ens_t pre a post -> Effect
  with repr = repr;
       return = return;
       bind = bind;
       subcomp = subcomp;
       if_then_else = if_then_else
}

[@@allow_informative_binders]
reifiable reflectable
new_effect Steel = SteelF


(*
 * Onto polymonadic binds
 *)

(*
 * First the bind between two unframed computations
 *
 * Add a frame to each
 *)

unfold
let bind_steel_steel_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:slprop) (frame_g:a -> slprop)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
: req_t (pre_f `star` frame_f)
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steel_steel_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:slprop) (frame_g:a -> slprop)
  (post:post_t b)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (_:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
: ens_t (pre_f `star` frame_f) b post
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

val bind_steel_steel (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@ framing_implicit] frame_f:slprop) (#[@@ framing_implicit] frame_g:a -> slprop)
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#[@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    (pre_f `star` frame_f)
    post
    (bind_steel_steel_req req_f ens_f req_g frame_f frame_g p)
    (bind_steel_steel_ens req_f ens_f ens_g frame_f frame_g post p p2)

(*
 * Note that the output is a framed computation, hence SteelF
 *)

polymonadic_bind (Steel, Steel) |> SteelF = bind_steel_steel


(*
 * Steel, SteelF: frame the first computation
 *)

unfold
let bind_steel_steelf_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:slprop)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
: req_t (pre_f `star` frame_f)
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steel_steelf_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:slprop)
  (post:post_t b)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (_: squash (can_be_split_post post_g post))
: ens_t (pre_f `star` frame_f) b post
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

val bind_steel_steelf (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@ framing_implicit] frame_f:slprop)
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (#[@@ framing_implicit] p2: squash (can_be_split_post post_g post))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    (pre_f `star` frame_f)
    post
    (bind_steel_steelf_req req_f ens_f req_g frame_f p)
    (bind_steel_steelf_ens req_f ens_f ens_g frame_f post p p2)

polymonadic_bind (Steel, SteelF) |> SteelF = bind_steel_steelf


(*
 * SteelF, Steel: frame the second computation
 *)

unfold
let bind_steelf_steel_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_g:a -> slprop)
  (_:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
: req_t pre_f
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steelf_steel_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_g:a -> slprop)
  (post:post_t b)
  (_:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
  (_:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
: ens_t pre_f b post
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

val bind_steelf_steel (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@ framing_implicit] frame_g:a -> slprop)
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
  (#[@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    pre_f
    post
    (bind_steelf_steel_req req_f ens_f req_g frame_g p)
    (bind_steelf_steel_ens req_f ens_f ens_g frame_g post p p2)


polymonadic_bind (SteelF, Steel) |> SteelF = bind_steelf_steel


(*
//  * SteelF, SteelF: no framing, use the effect bind
//  *)

(*
//  * PURE, Steel(F) bind
//  *)

assume WP_monotonic :
  forall (a:Type) (wp:pure_wp a).
    (forall p q. (forall x. p x ==>  q x) ==>  (wp p ==>  wp q))


(*
 * The indices of the second computation need not be dependent on a,
 * the result of the first computation, I think ...
 *
 * Since before bind is called, the typechecker has already substituted them
 * with the pure f computation
 *)

unfold
let bind_pure_steel__req (#a:Type) (wp:pure_wp a)
  (#pre:pre_t) (req:a -> req_t pre)
: req_t pre
= fun m -> wp (fun x -> (req x) m) /\ as_requires wp

unfold
let bind_pure_steel__ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre:pre_t) (#post:post_t b) (ens:a -> ens_t pre b post)
: ens_t pre b post
= fun m0 r m1 -> as_requires wp /\ (exists (x:a). as_ensures wp x /\ (ens x) m0 r m1)

val bind_pure_steel_ (a:Type) (b:Type)
  (wp:pure_wp a)
  (#[@@ framing_implicit] pre:pre_t) (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] req:a -> req_t pre) (#[@@ framing_implicit] ens:a -> ens_t pre b post)
  (f:eqtype_as_type unit -> PURE a wp) (g:(x:a -> repr b pre post (req x) (ens x)))
: repr b
    pre
    post
    (bind_pure_steel__req wp req)
    (bind_pure_steel__ens wp ens)

polymonadic_bind (PURE, SteelF) |> SteelF = bind_pure_steel_

polymonadic_bind (PURE, Steel) |> Steel = bind_pure_steel_


(*
//  * subcomp relation from SteelF to Steel
//  *)

polymonadic_subcomp SteelF <: Steel = subcomp


(*
//  * Annotations without the req and ens
//  *)

effect SteelT (a:Type) (pre:pre_t) (post:post_t a) =
  Steel a pre post (fun _ -> True) (fun _ _ _ -> True)



module EffectX = Steel.EffectX

let triv_pre (fp:pre_t) : EffectX.fp_mprop fp = fun _ -> True
let triv_post (fp:pre_t) (#a:Type) (fp':post_t a) : EffectX.fp_binary_mprop fp fp'
  = fun _ _ _ -> True

let triv_pre' (fp:pre_t) : req_t fp = fun _ -> True
let triv_post' (fp:pre_t) (#a:Type) (fp':post_t a) : ens_t fp a fp'
  = fun _ _ _ -> True

val subcomp_x (a:Type)
  (pre:pre_t) (post:post_t a)
  (f:EffectX.repr a pre post (triv_pre pre) (triv_post pre post))
: Pure (repr a pre post (triv_pre' pre) (triv_post' pre post))
  (requires True)
  (ensures fun _ -> True)

polymonadic_subcomp EffectX.SteelX <: Steel = subcomp_x

val as_steelx (#a:Type)
  (#pre:pre_t) (#post:post_t a)
  (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> Steel a pre post req ens)
: EffectX.SteelX a pre post req ens


//scratch space


// (*
//  * How we would like to see the Steel(F)/PURE bind
//  *)

// unfold
// let bind_steel__pure_req (#a:Type) (#pre:pre_t) (#post:post_t a) (req:req_t pre) (ens:ens_t pre a post)
//   (#b:Type) (wp:a -> pure_wp b)
// : req_t pre
// = fun m0 -> req m0 /\ (forall (x:a) (m1:hmem (post x)). ens m0 x m1 ==> as_requires (wp x))

// // unfold
// // let bind_steel__pure_ens (#a:Type) (#pre:pre_t) (#post:post_t a) (req:req_t pre) (ens:ens_t pre a post)
// //   (#b:Type) (wp:a -> pure_wp b) (f:(x:a -> unit -> PURE b (wp x)))
// // : ens_t pre b (fun _ -> post)
// // = fun m0 r m1 ->



// (*
// //  * No Steel(F), PURE bind
// //  *
// //  * Use the steel_ret function below to return the PURE computation
// //  *
// //  * Note it is in SteelF (i.e. framed already)
// //  *)
// let steel_ret (#a:Type) (#[@@ framing_implicit] p:a -> slprop u#1) (x:a)
// : SteelF a (p x) p (fun _ -> True) (fun _ r _ -> r == x)
// = SteelF?.reflect (fun _ -> x)

(* Exposing actions as Steel functions *)

val par (#aL:Type u#a)
        (#preL:slprop u#1)
        (#postL:aL -> slprop u#1)
        (#lpreL:req_t preL)
        (#lpostL:ens_t preL aL postL)
        ($f:unit -> Steel aL preL postL lpreL lpostL)
        (#aR:Type u#a)
        (#preR:slprop u#1)
        (#postR:aR -> slprop u#1)
        (#lpreR:req_t preR)
        (#lpostR:ens_t preR aR postR)
        ($g:unit -> Steel aR preR postR lpreR lpostR)
  : Steel (aL & aR)
    (preL `Mem.star` preR)
    (fun y -> postL (fst y) `Mem.star` postR (snd y))
    (fun h -> lpreL h /\ lpreR h)
    (fun h0 y h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 (fst y) h1 /\ lpostR h0 (snd y) h1)

val ( || ) (#aL:Type u#a)
          (#preL:slprop)
          (#postL:aL -> slprop)
          ($f:unit -> SteelT aL preL postL)
          (#aR:Type u#a)
          (#preR:slprop)
          (#postR:aR -> slprop)
          ($g:unit -> SteelT aR preR postR)
 : SteelT (aL & aR)
          (preL `Mem.star` preR)
          (fun y -> postL (fst y) `Mem.star` postR (snd y))

val add_action (#a:Type)
               (#p:slprop)
               (#q:a -> slprop)
               (f:action_except a Set.empty p q)
  : SteelT a p q

val change_slprop (p q:slprop)
                  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelT unit p (fun _ -> q)

val rewrite_context (#[@@framing_implicit] p:slprop)
                    (#[@@framing_implicit] q:slprop)
                    (_:unit)
  : SteelF unit p (fun _ -> q) (requires fun _ -> p == q) (ensures fun _ _ _ -> True)

val sladmit (#a:Type)
            (#[@@framing_implicit] p:pre_t)
            (#[@@framing_implicit] q:post_t a)
            (_:unit)
  : SteelF a p q (requires fun _ -> True) (ensures fun _ _ _ -> False)

val intro_pure (p:prop)
  : Steel unit emp (fun _ -> pure p) (requires fun _ -> p) (ensures fun _ _ _ -> True)

val read (#a:Type)
         (#pcm:_)
         (r:ref a pcm)
         (v0:Ghost.erased a)
  : SteelT (v:a { FStar.PCM.compatible pcm v0 v })
           (pts_to r v0)
           (fun _ -> pts_to r v0)

val write (#a:Type)
          (#pcm:_)
          (r:ref a pcm)
          (v0:Ghost.erased a)
          (v1:a{FStar.PCM.frame_preserving pcm v0 v1 /\ pcm.FStar.PCM.refine v1})
  : SteelT unit
           (pts_to r v0)
           (fun _ -> pts_to r v1)

val alloc (#a:Type)
          (#pcm:_)
          (x:a{FStar.PCM.compatible pcm x x /\ pcm.FStar.PCM.refine x })
  : SteelT (ref a pcm)
           emp
           (fun r -> pts_to r x)

val free (#a:Type)
         (#p:FStar.PCM.pcm a)
         (r:ref a p)
         (x:Ghost.erased a{FStar.PCM.exclusive p x /\ FStar.PCM.(p.refine p.p.one)})
  : SteelT unit (pts_to r x) (fun _ -> pts_to r FStar.PCM.(p.p.one))

val split (#a:Type)
          (#p:FStar.PCM.pcm a)
          (r:ref a p)
          (v:Ghost.erased a)
          (v0:Ghost.erased a)
          (v1:Ghost.erased a)
  : Steel unit (pts_to r v)
               (fun _ -> pts_to r v0 `star` pts_to r v1)
               (requires fun _ ->
                 FStar.PCM.composable p v0 v1 /\
                 v == Ghost.hide (FStar.PCM.op p v0 v1))
               (ensures fun _ _ _ -> True)

val gather (#a:Type)
           (#p:FStar.PCM.pcm a)
           (r:ref a p)
           (v0:Ghost.erased a)
           (v1:Ghost.erased a)
  : SteelT (_:unit{FStar.PCM.composable p v0 v1})
           (pts_to r v0 `star` pts_to r v1)
           (fun _ -> pts_to r (FStar.PCM.op p v0 v1))

let fact_valid_compat (#a:Type) (#pcm:FStar.PCM.pcm a)
                      (fact:stable_property pcm)
                      (v:Ghost.erased a)
  = squash (forall z. FStar.PCM.compatible pcm v z ==> fact z)

val witness (#a:Type) (#pcm:FStar.PCM.pcm a)
            (r:ref a pcm)
            (fact:stable_property pcm)
            (v:Ghost.erased a)
            (_:fact_valid_compat fact v)
  : SteelT unit (pts_to r v)
                (fun _ -> pts_to r v `star` pure (witnessed r fact))

val recall (#a:Type u#1) (#pcm:FStar.PCM.pcm a) (#fact:property a)
           (r:ref a pcm)
           (v:Ghost.erased a)
  : SteelT (v1:Ghost.erased a{FStar.PCM.compatible pcm v v1})
           (pts_to r v `star` pure (witnessed r fact))
           (fun v1 -> pts_to r v `star` pure (fact v1))

val cond (#a:Type)
         (b:bool)
         (p: (b':bool{b == b'}) -> slprop)
         (q: bool -> a -> slprop)
         (then_: (squash (b == true) -> SteelT a (p true) (q true)))
         (else_: (squash (b == false) -> SteelT a (p false) (q false)))
  : SteelT a (p b) (q b)


val drop (p:slprop) : SteelT unit p (fun _ -> emp)

val intro_exists (#a:Type) (x:a) (p:a -> slprop)
  : SteelT unit (p x) (fun _ -> h_exists p)

val noop (#[@@ framing_implicit] p:slprop) (u:unit) : SteelT unit p (fun _ -> p)

/// Operations on PCM Refs

open FStar.PCM

val select_refine (#a:Type u#1) (#p:pcm a)
                  (r:ref a p)
                  (x:Ghost.erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  frame_compatible p x v y})))
   : SteelT  (v:a{compatible p x v /\ p.refine v})
             (pts_to r x)
             (fun v -> pts_to r (f v))

val upd_gen (#a:Type) (#p:pcm a) (r:ref a p) (x y:Ghost.erased a)
            (f:FStar.PCM.frame_preserving_upd p x y)
  : SteelT unit
           (pts_to r x)
           (fun _ -> pts_to r y)
