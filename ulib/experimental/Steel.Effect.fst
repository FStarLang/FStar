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

type fp_prop (hp:Mem.hprop) =
  q:(Mem.heap -> prop){q `Mem.depends_only_on_without_affinity` hp}

type pre_t = Mem.hprop
type post_t (a:Type) = a -> Mem.hprop
type req_t (pre:pre_t) = fp_prop pre
type ens_t (pre:pre_t) (a:Type) (post:post_t a) =
  q:(Mem.heap -> a -> Mem.heap -> prop){ens_depends_only_on q pre post}

type repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a pre post req ens

let returnc (a:Type u#a) (x:a)
: repr a Mem.emp (fun _ -> Mem.emp) (fun _ -> True) (fun _ r _ -> r == x)
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
    (forall h0 x h1. (req_g h0 /\ ens_f h0 x h1) ==> ens_g h0 x h1))
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

reflectable
layered_effect {
  Steel : a:Type -> pre:pre_t -> post:post_t a -> req:req_t pre -> ens:ens_t pre a post -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

assume WP_monotonic_pure:
  forall (a:Type) (wp:pure_wp a).
    (forall (p q:pure_post a).
       (forall x. p x ==> q x) ==>
       (wp p ==> wp q))

let bind_pure_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre_g:pre_t) (post_g:post_t b) (req_g:a -> req_t pre_g) (ens_g:a -> ens_t pre_g b post_g)
  (f:unit -> PURE a wp) (g:(x:a -> repr b pre_g post_g (req_g x) (ens_g x)))
: repr b pre_g post_g
    (fun h -> wp (fun x -> req_g x h) /\ wp (fun _ -> True))
    (fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. (~ (wp (fun r -> r =!= x))) /\ ens_g x h0 r h1))
= fun m0 ->
  let x = f () in
  g x m0

polymonadic_bind (PURE, Steel) |> Steel = bind_pure_steel

unfold
let polymonadic_bind_steel_pure_pre (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:Mem.hprop) (req_f:req_t pre_f) (ens_f:ens_t pre_f a (fun _ -> post_f))
  (wp_g:a -> pure_wp b)
: req_t pre_f
= // assert (forall x (h0:Mem.hheap pre_f) h1 (h2:Mem.heap{Mem.disjoint h0 h2}).
  //           ens_f h0 x h1 <==> ens_f (Mem.join h0 h2) x h1);
  // assert (forall x h1 (h0:Mem.hheap pre_f) (h2:Mem.heap{Mem.disjoint h0 h2}).
  //         (ens_f h0 x h1 ==> p) <==> (ens_f (Mem.join h0 h2) x h1 ==> p));
  admit ();          
  fun h -> req_f h /\ (forall x h1. ens_f h x h1 ==> (wp_g x) (fun _ -> True))

let bind_steel_pure (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:Mem.hprop) (req_f:req_t pre_f) (ens_f:ens_t pre_f a (fun _ -> post_f))
  (wp_g:a -> pure_wp b)
  (f:repr a pre_f (fun _ -> post_f) req_f ens_f) (g:(x:a -> unit -> PURE b (wp_g x)))
: repr b pre_f (fun _ -> post_f)
    (polymonadic_bind_steel_pure_pre req_f ens_f wp_g)
    (fun h0 r h1 -> exists x. ens_f h0 x h1 /\ (~ ((wp_g x) (fun y -> y =!= r))))
= fun m0 ->
  let x = f () in
  g x ()


polymonadic_bind (Steel, PURE) |> Steel = bind_steel_pure


// let return_emp (#a:Type) (x:a)
// : Steel a Mem.emp (fun _ -> Mem.emp) (fun _ -> True) (fun _ r _ -> r == x)
// = Steel?.reflect (returnc a x)

assume val steel_reify (#a:Type) (#pre:pre_t) (#post:post_t a)
  (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> Steel a pre post req ens)
: repr a pre post req ens

let par0 (#aL:Type) (#preL:pre_t) (#postL:post_t aL) (#lpreL:req_t preL) (#lpostL:ens_t preL aL postL)
  (f:repr aL preL postL lpreL lpostL)
  (#aR:Type) (#preR:pre_t) (#postR:post_t aR) (#lpreR:req_t preR) (#lpostR:ens_t preR aR postR)
  (g:repr aR preR postR lpreR lpostR)
: Steel (aL & aR)
  (preL `Mem.star` preR)
  (fun (xL, xR) -> postL xL `Mem.star` postR xR)
  (fun h -> lpreL h /\ lpreR h)
  (fun h0 (xL, xR) h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 xL h1 /\ lpostR h0 xR h1)
= Steel?.reflect (fun _ -> Sem.run #state 0 #_ #_ #_ #_ #_ (Sem.Par (Sem.Act f) (Sem.Act g)))

let par (#aL:Type) (#preL:pre_t) (#postL:post_t aL) (#lpreL:req_t preL) (#lpostL:ens_t preL aL postL)
  ($f:unit -> Steel aL preL postL lpreL lpostL)
  (#aR:Type) (#preR:pre_t) (#postR:post_t aR) (#lpreR:req_t preR) (#lpostR:ens_t preR aR postR)
  ($g:unit -> Steel aR preR postR lpreR lpostR)
: Steel (aL & aR)
  (preL `Mem.star` preR)
  (fun (xL, xR) -> postL xL `Mem.star` postR xR)
  (fun h -> lpreL h /\ lpreR h)
  (fun h0 (xL, xR) h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 xL h1 /\ lpostR h0 xR h1)
= par0 (steel_reify f) (steel_reify g)

let frame0 (#a:Type) (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
  (f:repr a pre post req ens)
  (frame:Mem.hprop)
  (f_frame:fp_prop frame)
: Steel a
  (pre `Mem.star` frame)
  (fun x -> post x `Mem.star` frame)
  (fun h -> req h /\ f_frame h)
  (fun h0 r h1 -> req h0 /\ ens h0 r h1 /\ f_frame h1)
= Steel?.reflect (fun _ -> Sem.run #state 0 #_ #_ #_ #_ #_ (Sem.Frame (Sem.Act f) frame f_frame))

let frame (#a:Type) (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> Steel a pre post req ens)
  (frame:Mem.hprop)
  (f_frame:fp_prop frame)
: Steel a
  (pre `Mem.star` frame)
  (fun x -> post x `Mem.star` frame)
  (fun h -> req h /\ f_frame h)
  (fun h0 r h1 -> req h0 /\ ens h0 r h1 /\ f_frame h1)
= frame0 (steel_reify f) frame f_frame

open Steel.Memory
open Steel.Permissions

assume val upd (#a:Type) (r:ref a) (prev:a) (v:a)
: Steel unit (pts_to r full_permission prev) (fun _ -> pts_to r full_permission v)
    (fun _ -> True) (fun _ _ _ -> True)

assume val alloc (#a:Type) (v:a)
: Steel (ref a) emp (fun x -> pts_to x full_permission v)
    (fun _ -> True) (fun _ _ _ -> True)

assume val return (#a:Type) (#hp:a -> hprop) (x:a)
: Steel a (hp x) hp (fun _ -> True) (fun _ r _ -> r == x)


let alloc_and_upd (n:int)
: Steel (ref int) emp (fun x -> pts_to x full_permission (n+1))
    (fun _ -> True) (fun _ _ _ -> True)
= let r = alloc n in
  upd r n (n+1);
  return r

effect SteelT (a:Type) (pre:pre_t) (post:post_t a) =
  Steel a pre post (fun _ -> True) (fun _ _ _ -> True)

let ( || ) (#aL:Type) (#preL:pre_t) (#postL:post_t aL)
  ($f:unit -> SteelT aL preL postL)
  (#aR:Type) (#preR:pre_t) (#postR:post_t aR)
  ($g:unit -> SteelT aR preR postR)
: SteelT (aL & aR)
  (preL `Mem.star` preR)
  (fun (xL, xR) -> postL xL `Mem.star` postR xR)
= par f g

let incr (r:ref int) (prev:int) ()
: SteelT unit (pts_to r full_permission prev) (fun _ -> pts_to r full_permission (prev+1))
= upd r prev (prev+1)

let incr2 (r1 r2:ref int) (prev1 prev2:int)
: SteelT (unit & unit)
  (pts_to r1 full_permission prev1 `star` pts_to r2 full_permission prev2)
  (fun _ -> pts_to r1 full_permission (prev1+1) `star` pts_to r2 full_permission (prev2+1))
= incr r1 prev1 || incr r2 prev2
