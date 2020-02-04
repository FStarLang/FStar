(*
   Copyright 2019 Microsoft Research

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
module Act = Steel.Actions

open Steel.Semantics.Instantiate

module Ins = Steel.Semantics.Instantiate

#set-options "--print_implicits --print_universes"

let mem_affine_star_smt (p q:Mem.hprop) (m:Mem.heap)
: Lemma (Mem.interp (p `Mem.star` q) m ==> Mem.interp p m /\ Mem.interp q m)
  [SMTPat (Mem.interp (p `Mem.star` q) m)]
= Mem.affine_star p q m

let ens_depends_only_on (#a:Type)
  (q:Mem.heap -> a -> Mem.heap -> prop) (pre:Mem.hprop) (post:a -> Mem.hprop)

= //can join any disjoint heap to the pre-heap and q is still valid
  (forall x (h_pre:Mem.hheap pre) h_post (h:Mem.heap{Mem.disjoint h_pre h}).
     q h_pre x h_post <==> q (Mem.join h_pre h) x h_post) /\

  //can join any disjoint heap to the post-heap and q is still valid
  (forall x h_pre (h_post:Mem.hheap (post x)) (h:Mem.heap{Mem.disjoint h_post h}).
     q h_pre x h_post <==> q h_pre x (Mem.join h_post h))

type pre_t = Mem.hprop
type post_t (a:Type) = a -> Mem.hprop
type req_t (pre:pre_t) = q:(Mem.heap -> prop){q `Act.depends_only_on_without_affinity` pre}
type ens_t (pre:pre_t) (a:Type) (post:post_t a) =
  q:(Mem.heap -> a -> Mem.heap -> prop){ens_depends_only_on q pre post}

// let preserves_frame (pre post:Mem.hprop) (m0 m1:Mem.mem) =
//   forall (frame:Mem.hprop).
//     Mem.interp (Mem.locks_invariant m0 `Mem.star` (pre `Mem.star` frame)) (Mem.heap_of_mem m0) ==>
//     (Mem.interp (Mem.locks_invariant m1 `Mem.star` (post `Mem.star` frame)) (Mem.heap_of_mem m1) /\
//      (forall (f_frame:req_t frame). f_frame (Mem.heap_of_mem m0) <==> f_frame (Mem.heap_of_mem m1)))

type repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a pre post req ens

  // m0:Mem.mem ->
  // Div (a & Mem.mem)
  // (requires
  //   Mem.interp (Mem.locks_invariant m0 `Mem.star` pre) (Mem.heap_of_mem m0) /\
  //   req (Mem.heap_of_mem m0))
  // (ensures fun (x, m1) ->
  //   Mem.interp (Mem.locks_invariant m1 `Mem.star` post x) (Mem.heap_of_mem m1) /\
  //   ens (Mem.heap_of_mem m0) x (Mem.heap_of_mem m1) /\
  //   preserves_frame pre (post x) m0 m1)

let return (a:Type u#a) (x:a) (post:post_t a) (ens:ens_t (post x) a post)
: repr a (post x) post (fun h -> ens h x h) ens
= fun _ -> x

#push-options "--z3rlimit 50"
let bind (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (post_g:post_t b) (req_g:(x:a -> req_t (post_f x))) (ens_g:(x:a -> ens_t (post_f x) b post_g))
  (f:repr a pre_f post_f req_f ens_f) (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
: repr b pre_f post_g
    (fun h -> req_f h /\ (forall (x:a) h1. ens_f h x h1 ==> req_g x h1))
    (fun h0 y h2 -> req_f h0 /\ (exists x h1. ens_f h0 x h1 /\ (ens_g x) h1 y h2))
= fun m0 ->
  let x = f () in
  g x ()
#pop-options

let subcomp (a:Type) (pre:pre_t) (post:post_t a)
  (req_f:req_t pre) (ens_f:ens_t pre a post)
  (req_g:req_t pre) (ens_g:ens_t pre a post)
  (f:repr a pre post req_f ens_f)
: Pure (repr a pre post req_g ens_g)
  (requires
    (forall h. req_g h ==> req_f h) /\
    (forall h0 x h1. ens_f h0 x h1 ==> ens_g h0 x h1))
  (ensures fun _ -> True)
= f

let if_then_else (a:Type) (pre:pre_t) (post:post_t a)
  (req_then:req_t pre) (ens_then:ens_t pre a post)
  (req_else:req_t pre) (ens_else:ens_t pre a post)
  (f:repr a pre post req_then ens_then)
  (g:repr a pre post req_else ens_else)
  (p:Type0)
: Type
= repr a pre post
    (fun h -> (p ==> req_then h) /\ ((~ p) ==> req_else h))
    (fun h0 x h1 -> (p ==> ens_then h0 x h1) /\ ((~ p) ==> ens_else h0 x h1))

reifiable reflectable
layered_effect {
  Steel : a:Type -> pre:pre_t -> post:post_t a -> req:req_t pre -> ens:ens_t pre a post -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

let par (#aL:Type) (#preL:pre_t) (#postL:post_t aL) (#lpreL:req_t preL) (#lpostL:ens_t preL aL postL)
  (f:repr aL preL postL lpreL lpostL)
  (#aR:Type) (#preR:pre_t) (#postR:post_t aR) (#lpreR:req_t preR) (#lpostR:ens_t preR aR postR)
  (g:repr aR preR postR lpreR lpostR)
: Steel (aL & aR)
  (preL `Mem.star` preR)
  (fun (xL, xR) -> postL xL `Mem.star` postR xR)
  (fun h -> lpreL h /\ lpreR h)
  (fun h0 (xL, xR) h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 xL h1 /\ lpostR h0 xR h1)
= Steel?.reflect (fun _ -> Sem.run #state 0 #_ #_ #_ #_ #_ (Sem.Par (Sem.Act f) (Sem.Act g)))

#push-options "--admit_smt_queries true"  //the h0 =!= h1 part is not `depends_only_on`
let lift_pure_steel (a:Type) (wp:pure_wp a) (p:Mem.hprop) (f:unit -> PURE a wp)
: repr a p (fun _ -> p)
  (fun _ -> wp (fun _ -> True) /\ True)
  (fun h0 r h1 -> ~ (wp (fun x -> x =!= r \/ h0 =!= h1)))
= admit ()
#pop-options

assume WP_monotonic_pure:
  forall (a:Type) (wp:pure_wp a).
    (forall (p q:pure_post a).
       (forall x. p x ==> q x) ==>
       (wp p ==> wp q))

let bind_PURE_M (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre_g:pre_t) (post_g:post_t b) (req_g:a -> req_t pre_g) (ens_g:a -> ens_t pre_g b post_g)
  (f:unit -> PURE a wp) (g:(x:a -> repr b pre_g post_g (req_g x) (ens_g x)))
: repr b pre_g post_g
    (fun h -> wp (fun x -> req_g x h) /\ wp (fun _ -> True))
    (fun h0 r h1 -> exists x. (~ (wp (fun r -> r =!= x))) /\ ens_g x h0 r h1)
= fun m0 ->
  let x = f () in
  g x m0
