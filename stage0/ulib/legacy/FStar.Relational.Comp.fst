(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Relational.Comp
open FStar.ST
open FStar.All
open FStar.Heap
open FStar.Relational.Relational

type heap2 = double heap

new_effect STATE2 = STATE_h heap2
let st2_Pre = st_pre_h heap2
let st2_Post' (a:Type) (pre:Type) = st_post_h' heap2 a pre
let st2_Post  (a:Type) = st_post_h heap2 a
let st2_WP (a:Type) = st_wp_h heap2 a
effect ST2 (a:Type) (pre:st2_Pre) (post: (h:heap2 -> Tot (st2_Post' a (pre h)))) =
    STATE2 a
      (fun (p:st2_Post a) (h:heap2) -> pre h /\ (forall a h1. pre h /\ post h a h1 ==> p a h1)) (* WP *)
effect St2 (a:Type) = ST2 a (fun h -> True) (fun h0 r h1 -> True)
sub_effect
  DIV    ~> STATE2 = (fun (a:Type) (wp:pure_wp a) (p:st2_Post a) -> (fun h2 -> wp (fun a0 -> p a0 h2)))

(* construct a st2_WP from 2 st_wps *)
val comp : (a:Type) -> (b:Type) -> (wp0:st_wp a) -> (wp1:st_wp b) -> Tot (st2_WP (rel a b)) 
let comp a b wp0 wp1 p h2 =
    wp0 (fun y0 h0 ->
      wp1 (fun y1 h1 -> p (R y0 y1) (R h0 h1))
      (R?.r h2))
    (R?.l h2)

//TODO: this should be conditional on the monotonicity of the wps
assume Monotone_comp: forall a b wp1 wp2 p1 p2. (forall x h. p1 x h ==> p2 x h)
			==> (forall h. comp a b wp1 wp2 p1 h
			    ==> comp a b wp1 wp2 p2 h)


assume val compose2: #a0:Type -> #b0:Type -> #wp0:(a0 -> Tot (st_wp b0))
                  -> #a1:Type -> #b1:Type -> #wp1:(a1 -> Tot (st_wp b1))
                  -> $c0:(x0:a0 -> STATE b0 (wp0 x0))
                  -> $c1:(x1:a1 -> STATE b1 (wp1 x1))
                  -> x: rel a0 a1
                  -> STATE2 (rel b0 b1)
                            (comp b0 b1 (wp0 (R?.l x)) (wp1 (R?.r x)))

val compose2_self : #a:Type -> #b:Type -> #wp:(a -> Tot (st_wp b))
                -> $c:(x:a -> STATE b (wp x))
                -> x: double a
                -> STATE2 (double b)
                          (comp b b (wp (R?.l x)) (wp (R?.r x)))
let compose2_self #a #b #wp f x = compose2 #a #b #wp #a #b #wp f f x

(* Combine two ST2 statements A and B to create a new ST2 statement C where
   the left side of C is equivalent to the left side of A and
   the right side of C is equivalent to the right side of B *)
assume val cross : #a:Type -> #b:Type -> #c:Type -> #d:Type
                -> #p:(heap2 -> Type)
                -> #p':(heap2 -> Type)
                -> #q:(heap2 -> rel a b -> heap2 -> Type)
                -> #q':(heap2 -> rel c d -> heap2 -> Type)
                -> $c1:(double unit -> ST2 (rel a b)
                                           (requires (fun h -> p h))
                                           (ensures (fun h1 r h2 -> q h1 r h2)))
                -> $c2:(double unit -> ST2 (rel c d)
                                           (requires (fun h -> p' h))
                                           (ensures (fun h1 r h2 -> q' h1 r h2)))
                -> ST2 (rel a d) (requires (fun h -> (exists (hl:heap) (hr:heap).
                                                             p (R (R?.l h) hr)
                                                          /\ p' (R hl (R?.r h)))))
                                 (ensures (fun h1 r h2 -> (exists (h2l:heap) (h2r:heap) (rl:c) (rr:b).
                                                                  q h1 (R (R?.l r) rr) (R (R?.l h2) (h2r))
                                                               /\ q' h1 (R rl (R?.r r)) (R h2l (R?.r h2)))))


(* Create a ST statement from a ST2 statement by projection *)
val decomp_l : (a0:Type) -> (a1:Type) -> (b0:Type) -> (b1:Type) -> (al:a0) -> (wp:(rel a0 a1 -> Tot (st2_WP (rel b0 b1))))
	     -> Tot (st_wp_h heap b0)
let decomp_l a0 a1 b0 b1 al wp =
  fun p hl ->
    (exists (ar:a1) (hr:heap).
      wp (R al ar) (fun y2 h2 -> p (R?.l y2) (R?.l h2))
         (R hl hr))

val decomp_r : (a0:Type) -> (a1:Type) -> (b0:Type) -> (b1:Type) -> (ar:a1) -> (wp:(rel a0 a1 -> Tot (st2_WP (rel b0 b1))))
	     -> Tot (st_wp_h heap b1)
let decomp_r a0 a1 b0 b1 ar wp =
  fun p hr ->
    (exists (al:a0) (hl:heap).
      wp (R al ar) (fun y2 h2 -> p (R?.r y2) (R?.r h2))
         (R hl hr))

assume val project_l : #a0:Type -> #b0:Type -> #a1:Type -> #b1:Type
                    -> #wp:(rel a0 a1 -> Tot (st2_WP (rel b0 b1)))
                    -> $c:(x:rel a0 a1 -> STATE2 (rel b0 b1) (wp x))
                    -> x:a0
                    -> STATE b0 (decomp_l a0 a1 b0 b1 x wp)

assume val project_r : #a0:Type -> #b0:Type -> #a1:Type -> #b1:Type
                    -> #wp:(rel a0 a1 -> Tot (st2_WP (rel b0 b1)))
                    -> $c:(x:rel a0 a1 -> STATE2 (rel b0 b1) (wp x))
                    -> x:a1
                    -> STATE b1 (decomp_r a0 a1 b0 b1 x wp)


