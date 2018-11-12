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
module GMST

(* 
   A proof-of-concept example of a Graded Dijkstra Monad---the MST monad graded by the relation/preorder on states 

   In other words, this is a demonstration how using writer monad like structure in the underlying representation of
   effects allows one to use the resulting WPs to encode indexed effects in F* (as long as the indexes form a magma)
*)

open FStar.Preorder

(* The graded MST effect *)

let gmst_post (s:Type) (a:Type) (s0:s) = rel:relation s -> a -> s1:s{rel s0 s1} -> GTot Type0
let gmst_wp   (s:Type) (a:Type)        = s0:s -> gmst_post s a s0 -> GTot Type0

let (@) (#a:Type) (rel1:relation a) (rel0:relation a) : relation a
  = fun x z -> exists y . rel0 x y /\ rel1 y z

unfold
let gmst_return (s:Type) (a:Type) (x:a) (s0:s) (p:gmst_post s a s0) 
  = forall v. v == x ==> p (fun s0 s1 -> s0 == s1) v s0

unfold
let gmst_bind (s:Type) (r:range) (a:Type) (b:Type)
              (wp1:gmst_wp s a) (wp2: (a -> GTot (gmst_wp s b)))
              (s0:s) (p:gmst_post s b s0) 
  = wp1 s0 (fun rel1 x s1 -> wp2 x s1 (fun rel2 -> p (rel2 @ rel1)))

unfold
let gmst_if_then_else (s:Type) (a:Type) (p:Type) 
                      (wp_then:gmst_wp s a) (wp_else:gmst_wp s a) (s0:s) (post:gmst_post s a s0)
  = l_ITE p (wp_then s0 post) (wp_else s0 post)

unfold
let gmst_ite (s:Type) (a:Type) (wp:gmst_wp s a) (s0:s) (post:gmst_post s a s0) =
  wp s0 post

unfold
let gmst_stronger (s:Type) (a:Type) (wp1:gmst_wp s a) (wp2:gmst_wp s a) =
  forall s0 p. wp1 s0 p ==> wp2 s0 p

unfold
let gmst_close (s:Type) (a:Type) (b:Type) 
               (wp:(b -> GTot (gmst_wp s a))) (s0:s) (p:gmst_post s a s0) =
  forall x. wp x s0 p

unfold
let gmst_assert_p (s:Type) (a:Type) (p:Type) 
                  (wp:gmst_wp s a) (s0:s) (q:gmst_post s a s0) =
  p /\ wp s0 q

unfold
let gmst_assume_p (s:Type) (a:Type) (p:Type) 
                  (wp:gmst_wp s a) (s0:s) (q:gmst_post s a s0) =
  p ==> wp s0 q

unfold
let gmst_null (s:Type) (a:Type) (s0:s) (p:gmst_post s a s0) =
  forall rel x s. p rel x s

unfold
let gmst_trivial (s:Type) (a:Type) (wp:gmst_wp s a) =
  forall s0. wp s0 (fun _ _ _ -> True)

new_effect {
  GMST_h (s:Type) : result:Type -> wp:gmst_wp s result -> Effect
  with 
     //repr         = s0:s -> M (rel:relation a & a * s1:s{rel s0 s1})
       return_wp    = gmst_return s
     ; bind_wp      = gmst_bind s
     ; if_then_else = gmst_if_then_else s
     ; ite_wp       = gmst_ite s
     ; stronger     = gmst_stronger s
     ; close_wp     = gmst_close s
     ; assert_p     = gmst_assert_p s
     ; assume_p     = gmst_assume_p s
     ; null_wp      = gmst_null s
     ; trivial      = gmst_trivial s
}

(*
   DA: For some reason, DM4F didn't accept the representation

     s -> M ((s -> s -> Type0) * a * s)

   thus the explicit effect definition for time being
*)


(* Instatiating the graded MST with int as a proof-of-concept *)

let state = int

new_effect GMST = GMST_h state

let lift_div_gmst (a:Type) (wp:pure_wp a) (s0:state) (p:gmst_post state a s0) = wp (fun x -> p (fun s0 s1 -> s0 == s1) x s0)
sub_effect DIV ~> GMST = lift_div_gmst


(* Syntactic sugar packaging a relation index and MST WP *)

let mst_wp    (s:Type) (a:Type) (rel:relation s) = s0:s -> (a -> s1:s{rel s0 s1} -> Type0) -> Type0

unfold
let (><) (#a:Type) (rel:relation state) (wp:mst_wp state a rel) : gmst_wp state a
  = fun s0 post -> wp s0 (post rel)


(* Actions with specs defined in terms of (><) *)

assume val gst_get: unit -> GMST state ((fun s0 s1 -> s0 == s1) >< (fun s0 post -> post s0 s0))
assume val gst_put: #rel:relation state -> s1:state -> GMST unit (rel >< (fun s0 post -> rel s0 s1 /\ post () s1))

assume val witnessed: predicate state -> Type0

let stable (#a:Type) (p:predicate a) (rel:preorder a) 
  = forall x y . p x /\ rel x y ==> p y

assume val gst_witness: #rel:preorder state -> p:predicate state -> GMST unit (rel >< (fun s0 post -> stable p rel /\ p s0 /\ (witnessed p ==> post () s0)))
assume val gst_recall:  #rel:preorder state -> p:predicate state -> GMST unit (rel >< (fun s0 post -> stable p rel /\ witnessed p /\ (p s0 ==> post () s0)))


(* Sequential composition results in composition of relations *)

let app (#a:Type) (#b:Type)
        (#rel1:relation state)
        (#rel2:relation state)
        (#wp1:mst_wp state a rel1) 
        (#wp2:a -> mst_wp state b rel2)
        (f:unit -> GMST a (rel1 >< wp1))
        (g:(x:a -> GMST b (rel2 >< wp2 x)))
  : GMST b ((rel2 @ rel1) >< (fun s0 p -> wp1 s0 (fun x s1 -> wp2 x s1 p)))
  = g (f ())


(* 
   In case the relations are the same, and moreover preorders, we ought to get the usual MST typing for app 

   However, currently we don't get this result because of the lack of proper prop (one that would also soundly 
   support propositional extensionality). 
*)


(* 
   Temporarily assuming propositional extensionality for rel's.  

   As preorder is defined using Type0 not the (upcoming) prop, 
   then this can actually lead to an inconsistency, e.g., see 
   examples/paradoxes/PropositionalExtensionalityInconsistent.fst
*)

let lemma_preorder_comp_equiv (a:Type) (rel:preorder a)
  : Lemma (forall x y . (rel @ rel) x y <==> rel x y)
  = ()

let lemma_preorder_comp_equal (a:Type) (rel:preorder a)
  : Lemma (rel @ rel == rel)
    [SMTPat (rel @ rel)]
  = admit ()


(* The inferred type of app *)

let preorder_app' (#a:Type) (#b:Type)
                  (#rel:preorder state)
                  (#wp1:mst_wp state a rel) 
                  (#wp2:a -> mst_wp state b rel)
                  (f:unit -> GMST a (rel >< wp1))
                  (g:(x:a -> GMST b (rel >< wp2 x)))
  : GMST b (rel @ rel >< (fun s0 p -> wp1 s0 (fun x s1 -> wp2 x s1 p)))
  = g (f ())


(* Deriving the usual typing of MST for preorders *)

let transport_gmst_rel (#a:Type) (#rel1:relation state) (#rel2:relation state{rel1 == rel2})
                       (#wp:mst_wp state a rel1) 
                       (f:unit -> GMST a (rel1 >< wp)) : GMST a (rel2 >< wp)
  = f ()

let preorder_app (#a:Type) (#b:Type)
                 (#rel:preorder state)
                 (#wp1:mst_wp state a rel) 
                 (#wp2:a -> mst_wp state b rel)
                 (f:unit -> GMST a (rel >< wp1))
                 (g:(x:a -> GMST b (rel >< wp2 x)))
  : GMST b (rel @ rel >< (fun s0 p -> wp1 s0 (fun x s1 -> wp2 x s1 p)))
  = assert (rel @ rel == rel); //follows from the assumed propositional extensionality above
    admit (); //DA: not sure what's happening here, transport_gmst_rel below simply times out
    transport_gmst_rel #b #(rel @ rel) #rel 
                       #(fun s0 p -> wp1 s0 (fun x s1 -> wp2 x s1 p)) 
                       (fun _ -> preorder_app' #a #b #rel #wp1 #wp2 f g) 
