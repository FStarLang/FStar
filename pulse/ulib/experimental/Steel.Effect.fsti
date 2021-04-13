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

module Mem = Steel.Memory
open Steel.Memory
include Steel.Effect.Common

#set-options "--warn_error -330"  //turn off the experimental feature warning

val repr (a:Type) (already_framed:bool) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) : Type u#2

unfold
let return_req (p:slprop u#1) : req_t p = fun _ -> True

unfold
let return_ens (a:Type) (x:a) (p:a -> slprop u#1) : ens_t (p x) a p = fun _ r _ -> r == x

(*
 * Return is parametric in post (cf. return-scoping.txt)
 * The return is already framed (the post captures the full context)
 *)
val return (a:Type) (x:a) (#[@@@ framing_implicit] p:a -> slprop)
: repr a true (return_pre (p x)) p (return_req (p x)) (return_ens a x p)

(*
 * We allow weakening of post resource of f to pre resource of g
 *)

unfold
let bind_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (#pr:a -> prop)
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
  (#[@@@ framing_implicit] p:squash (can_be_split_forall_dep pr
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:repr a framed_f pre_f post_f req_f ens_f)
  (g:(x:a -> repr b framed_g (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    true
    (pre_f `star` frame_f)
    post
    (bind_req req_f ens_f req_g frame_f frame_g p)
    (bind_ens req_f ens_f ens_g frame_f frame_g post p p2)

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
  (#framed_f:eqtype_as_type bool)
  (#framed_g:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:pre_t) (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] req_g:req_t pre_g) (#[@@@ framing_implicit] ens_g:ens_t pre_g a post_g)
  (#[@@@ framing_implicit] p1:squash (can_be_split pre_g pre_f))
  (#[@@@ framing_implicit] p2:squash (can_be_split_forall post_f post_g))
  (f:repr a framed_f pre_f post_f req_f ens_f)
: Pure (repr a framed_g pre_g post_g req_g ens_g)
  (requires subcomp_pre req_f ens_f req_g ens_g p1 p2)
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

let if_then_else (a:Type)
  (#framed:eqtype_as_type bool)// (#framed_g:eqtype_as_type bool)
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

[@@allow_informative_binders]
reifiable reflectable
effect {
  SteelBase (a:Type) (framed:bool) (pre:pre_t) (post:post_t a) (_:req_t pre) (_:ens_t pre a post)
  with { repr; return; bind; subcomp; if_then_else }
}

effect Steel (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  SteelBase a false pre post req ens
effect SteelF (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  SteelBase a true pre post req ens


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

polymonadic_bind (PURE, SteelBase) |> SteelBase = bind_pure_steel_

// AF: The lift below works, but the framing tactic currently requires annotations
// when scope restriction occurs (i.e. during returns). See for instance the comment
// on test7 in Steel.FramingTestSuite. When a lift is available, returns are not inserted,
// which leads to errors

// unfold
// let lift_pure_steel__req (#a:Type) (wp:pure_wp a)
// : req_t emp
// = fun m -> as_requires wp /\ True

// unfold
// let lift_pure_steel__ens (#a:Type) (wp:pure_wp a)
// : ens_t emp a (fun _ -> emp)
// = fun m0 r m1 -> as_requires wp /\ as_ensures wp r

// val lift_pure_steel
//   (a:Type)
//   (#[@@@ framing_implicit] wp:pure_wp a)
//   (f:eqtype_as_type unit -> PURE a wp)
//   : repr a false emp (fun _ -> emp) (lift_pure_steel__req wp) (lift_pure_steel__ens wp)

// sub_effect PURE ~> SteelBase = lift_pure_steel

(*
//  * Annotations without the req and ens
//  *)

effect SteelT (a:Type) (pre:pre_t) (post:post_t a) =
  SteelBase a false pre post (fun _ -> True) (fun _ _ _ -> True)

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

val noop (u:unit) : SteelT unit emp (fun _ -> emp)

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
