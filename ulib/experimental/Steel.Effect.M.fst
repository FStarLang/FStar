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

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
module Act = Steel.Actions

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

type pre_t = hprop u#1
type post_t (a:Type) = a -> hprop u#1
type req_t (pre:pre_t) = Sem.l_pre #state pre
type ens_t (pre:pre_t) (a:Type) (post:post_t a) = Sem.l_post #state #a pre post


/// Sem.m is the type of action trees in the semantics

type repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.m state a pre post req ens


/// Effect return

let return (a:Type) (x:a) (p:a -> hprop) (post:ens_t (p x) a p)
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
  (frame:hprop) (f_frame:Sem.fp_prop frame)
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
 * In the combinator, both the computations return types are in the same universe,
 * and the combinator itself is polymorphic in that single universe
 *
 * On the other hand, F*'s existing effect system requires the effect bind
 * to be polymorphic in two universes (the universes of the two computations)
 * This comes in handy, for example,
 * when writing code that performs an (erasable) `get` to
 * get its hands on the ghost memory and use it in assertions etc. The ghost memory
 * typically lives in one universe higher than the computational types (e.g. int)
 *
 * So there are two issues with the bind:
 * (a) both the computations have the same universe
 * (b) the bind itself is polymorphic in a single universe
 *
 * To solve the first one, we can explicitly raise the two universes to max(a b)
 * (F* does not have universe cumulativity yet)
 * This will support two computations in different universes, but in the absence of
 * cumulativity, this will be hard to work with at the level of source programs,
 * since the programmers (or some heuristic) will have to insert the universe
 * lifts/downgrades
 * (see a sketch below about how this lift might look like)
 *
 * For the second problem, even if F* had cumulativity,
 * we still need F* to support single universe polymorphic binds
 *
 * With all this in mind, we choose to define the effect using an alternate
 * representation -- as NMST computations
 *
 * The effect definition with this representation is in Steel.Effect.fst
 *
 * The resulting effect does not have these drawbacks, and is immediately
 * usable for F* programs (see our examples written using this effect)
 *
 * However, the implementation of par combinator using this representation
 * does not allow fine-grained interleaving that our semantics supports
 *
 * In practical terms, this is not a problem because we don't intend to run
 * Steel programs using the effect combinators directly
 * Rather, in ongoing work, we are working on an extraction pipeline to extract
 * Steel concurrency natively to OCaml or C, and run there
 *
 * However, this is still unsatisfactory from the modeling perspective,
 * we plan to extend F* on the lines above and switch to the action trees
 * representation for the effect
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

let lift_req_x (#a:Type u#a) (#pre:a -> hprop) (req:(x:a -> req_t (pre x)))
: x:U.raise_t u#a u#b a -> req_t ((lift_post pre) x)
= fun x -> req (U.downgrade_val x)

let lift_ens_x (#a:Type u#a) (#pre:a -> hprop)
  (#b:Type u#b) (#post:_)
  (ens:(x:a -> ens_t u#b (pre x) b post))
: x:U.raise_t u#a u#b a ->
  ens_t u#(max a b) ((lift_post pre) x) (U.raise_t b) (lift_post post)
= fun x -> (fun m0 y m1 -> (ens (U.downgrade_val x)) m0 (U.downgrade_val y) m1)


/// Lifting `m` terms, implementing only the Ret case

let lift_m (#a:Type u#a) (#pre:pre_t) (#post:post_t u#a a)
  (#req:req_t pre) (#ens:ens_t pre a post)
  (f:repr u#a a pre post req ens)
: repr u#(max a b) (FStar.Universe.raise_t a) pre (lift_post post) req (lift_ens ens)
= match f with
  | Sem.Ret #_ #_ post x lpost ->

    assert ((Sem.return_lpre #_ #_ #(lift_post post) (U.raise_val u#a u#b x) (lift_ens lpost)) ==
             Sem.return_lpre #_ #_ #post x lpost) by
      (T.norm [delta_only [`%Sem.return_lpre; `%lift_post; `%lift_ens]];
       FStar.Tactics.Derived.l_to_r [
         `U.downgrade_val_raise_val;
         `U.raise_val_downgrade_val ]);

    Sem.Ret (lift_post post) (U.raise_val x) (lift_ens lpost)

  | _ -> admit ()


let lift_m_x (#a:Type u#a) (#pre:a -> hprop)
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
