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

module Steel.Effect.M
//Note: This file is standalone and not used anywhere else in the Steel codebase
module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory

open Steel.Semantics.Instantiate

module Ins = Steel.Semantics.Instantiate

open Steel.Memory

(*
 * This module defines a layered effect over the CSL semantics
 * from Steel.Semantics.Hoare.MST
 *
 * The effect is defined with action trees as the underlying representation
 * for computations in the effect
 *
 * The effect combinators export the same specs as proved in the semantics
 *
 * The state typeclass in the semantics is instantiated with
 * Steel.Semantics.Instantiate
 *
 * This module is for illustration, our examples rely on Steel.Effect.fst
 * See the discussion towards the end of this file
 *)

type pre_t = slprop u#1
type post_t (a:Type) = a -> slprop u#1
type req_t (pre:pre_t) = Sem.l_pre #state pre
type ens_t (pre:pre_t) (a:Type) (post:post_t a) = Sem.l_post #state #a pre post


/// Sem.m is the type of action trees in the semantics

type repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.m state a pre post req ens


/// Effect return

let return (a:Type) (x:a) (p:a -> slprop) (post:ens_t (p x) a p)
: repr a (p x) p (Sem.return_lpre #state #a #p x post)  post
= Sem.Ret p x post


/// Effect bind

let bind (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (post_g:post_t b) (req_g:(x:a -> req_t (post_f x))) (ens_g:(x:a -> ens_t (post_f x) b post_g))
  (f:repr a pre_f post_f req_f ens_f) (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
: repr b pre_f post_g
  (Sem.bind_lpre req_f ens_f req_g)
  (Sem.bind_lpost req_f ens_f ens_g)
= Sem.Bind f g


/// A combinator for parallel computations

let par
  (aL:Type) (preL:pre_t) (postL:post_t aL) (reqL:req_t preL) (ensL:ens_t preL aL postL)
  (f:repr aL preL postL reqL ensL)
  (aR:Type) (preR:pre_t) (postR:post_t aR) (reqR:req_t preR) (ensR:ens_t preR aR postR)
  (g:repr aR preR postR reqR ensR)
: repr (aL & aR)
  (preL `star` preR)
  (fun (xL, xR) -> postL xL `star` postR xR)
  (Sem.par_lpre reqL reqR)
  (Sem.par_lpost reqL ensL reqR ensR)
= Sem.Par f g


/// Framing combinator

let frame (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post)
  (f:repr a pre post req ens)
  (frame:slprop) (f_frame:Sem.fp_prop frame)
: repr a
  (pre `star` frame)
  (fun x -> post x `star` frame)
  (Sem.frame_lpre req f_frame)
  (Sem.frame_lpost req ens f_frame)
= Sem.Frame f frame f_frame


(*
 * However, the effect defined this way is not immediately usable from F*
 *
 * To see the issue, consider again the `bind` combinator we defined above with
 * explicit universe annotations:
 *)
let bind_explicit_univs (a:Type u#a) (b:Type u#a)
  (pre_f:pre_t) (post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (post_g:post_t b) (req_g:(x:a -> req_t (post_f x))) (ens_g:(x:a -> ens_t (post_f x) b post_g))
  (f:repr a pre_f post_f req_f ens_f) (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
: repr u#a b pre_f post_g
  (Sem.bind_lpre req_f ens_f req_g)
  (Sem.bind_lpost req_f ens_f ens_g)
= Sem.Bind f g


(*
 * In the combinator, both the computation return types are in the same universe,
 * and the combinator itself is polymorphic in that single universe
 *
 * However, composing computations whose result types are in different universes
 * is useful. For example, composition of a computation returning an existential
 * (p:Type0 & x:int{p}) that lives in u#1 with a continuation that projects and returns
 * the int that lives in u#0.
 *
 * Hence, as with other F* effects, we would like to support a bind that is doubly
 * polymorphic in the result type of both the computations, e.g. something like
 *
 * let bind_double_univs (a:Type u#a) (b:Type u#b)
 *   (pre_f:pre_t) (post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
 *   (post_g:post_t b)
 *   (req_g:(x:a -> req_t (post_f x))) (ens_g:(x:a -> ens_t (post_f x) b post_g))
 *   (f:repr a pre_f post_f req_f ens_f)
 *   (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
 * : repr u#(max a b) b pre_f post_g
 *   (Sem.bind_lpre req_f ens_f req_g)
 *   (Sem.bind_lpost req_f ens_f ens_g) = ...
 *
 * But F*, like Lean and Agda, and unlike Coq, lacks cumulativity of universes.
 * So the result type (repr u#(max a b) b ...) is not well-formed, since b has
 * universe u#b and not u#(max a b)
 *
 * We could explicitly lift the universes to get the following type:
 *
 * let bind_double_univs_raise (a:Type u#a) (b:Type u#b)
 *   (pre_f:pre_t) (post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
 *   (post_g:post_t b)
 *   (req_g:(x:a -> req_t (post_f x))) (ens_g:(x:a -> ens_t (post_f x) b post_g))
 *   (f:repr a pre_f post_f req_f ens_f)
 *   (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
 * : repr u#(max a b) (raise_t b) ...
 *
 * (In the file below, we sketch this in actual code.)
 *
 * But this results in other complications:
 * 1. The user programs now have to explicitly eliminate raise_t (by downgrading)
 * 2. F* effect system will reject this bind definition, since it is unaware of the
 *    universe lifting
 *
 * To get around this, we chose a different, more restrictive representation for the
 * Steel effect in Steel.Effect.fst. That definition is suitably doubly universe 
 * polymorphic, at the expense of hiding the structure of the computation trees
 * needed for a full fidelity interleaving semantics.
 *
 * Please see that file for further discussions on the limitations of that 
 * representation.
 *
 * In the meantime, we are working on adding universe cumulativity to F* that will
 * allow bind_double_univs to be defined and then we can switch to the action trees
 * based representation for the effect.
 *)


/// Sketch for supporting different universes in the two computations

module U = FStar.Universe
module T = FStar.Tactics


/// Auxiliary functions for lifting post, ens, etc.

let lift_post #a (post:post_t u#a a)
: post_t u#(max a b) (U.raise_t a)
= fun x -> post (U.downgrade_val x)

let lift_ens #pre #a #post (ens:ens_t u#a pre a post)
: ens_t u#(max a b) pre (U.raise_t a) (lift_post post)
= fun m0 x m1 -> ens m0 (U.downgrade_val x) m1

let lift_req_x (#a:Type u#a) (#pre:a -> slprop) (req:(x:a -> req_t (pre x)))
: x:U.raise_t u#a u#b a -> req_t ((lift_post pre) x)
= fun x -> req (U.downgrade_val x)

let lift_ens_x (#a:Type u#a) (#pre:a -> slprop)
  (#b:Type u#b) (#post:_)
  (ens:(x:a -> ens_t u#b (pre x) b post))
: x:U.raise_t u#a u#b a ->
  ens_t u#(max a b) ((lift_post pre) x) (U.raise_t b) (lift_post post)
= fun x -> (fun m0 y m1 -> (ens (U.downgrade_val x)) m0 (U.downgrade_val y) m1)


/// Lifting `m` terms, implementing only the Ret case

//NS, AR: This is failure since the patch to 2635
//It fails because:
// we got the problem ?u:t = e <: t, i.e. ascription on RHS,
// but when solving we removed the ascription, so we solved ?u = e
// and then retypechecking e did not succeed
//Some possibilities for restoring this:
// 1. Patch Rel to retain ascriptions?
// 2. Maybe using PR 2482 we can do the rewrite at a weaker type and then conclude
[@@expect_failure] 
let lift_m (#a:Type u#a) (#pre:pre_t) (#post:post_t u#a a)
  (#req:req_t pre) (#ens:ens_t pre a post)
  (f:repr u#a a pre post req ens)
: repr u#(max a b) (FStar.Universe.raise_t a) pre (lift_post post) req (lift_ens ens)
= match f with
  | Sem.Ret #_ #_ post x lpost ->

    assert ((Sem.return_lpre #_ #_ #(lift_post post) (U.raise_val u#a u#b x) (lift_ens lpost)) ==
             Sem.return_lpre #_ #_ #post x lpost) by
      T.(norm [delta_only [`%Sem.return_lpre; `%lift_post; `%lift_ens]];
         FStar.Tactics.Derived.l_to_r [`U.downgrade_val_raise_val ];
         trefl());
    Sem.Ret (lift_post post) (U.raise_val x) (lift_ens lpost)

  | _ -> admit ()


let lift_m_x (#a:Type u#a) (#pre:a -> slprop)
  (#b:Type u#b) (#post:post_t b) (#req:(x:a -> req_t (pre x))) (#ens:(x:a -> ens_t (pre x) b post))
  (f:(x:a -> repr u#b b (pre x) post (req x) (ens x)))
: x:U.raise_t u#a u#b a ->
  repr u#(max a b) (U.raise_t b)
  ((lift_post pre) x)
  (lift_post post)
  ((lift_req_x req) x) 
  ((lift_ens_x ens) x)
= fun x -> lift_m (f (U.downgrade_val x))


/// Finally a lifted bind

let bind_lift (a:Type u#a) (b:Type u#b)
  (pre_f:pre_t) (post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (post_g:post_t b)
  (req_g:(x:a -> req_t (post_f x))) (ens_g:(x:a -> ens_t (post_f x) b post_g))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
: repr u#(max a b) (U.raise_t b)
  pre_f
  (lift_post post_g)
  (Sem.bind_lpre req_f (lift_ens ens_f) (lift_req_x req_g))
  (Sem.bind_lpost u#(max a b) u#(max a b)
     #state #(U.raise_t u#a u#b a) #pre_f #(lift_post post_f)
     req_f (lift_ens ens_f)
     #(U.raise_t b) #(lift_post post_g)
     (lift_ens_x ens_g))
= let f = lift_m f in
  let g = lift_m_x g in
  Sem.Bind f g
