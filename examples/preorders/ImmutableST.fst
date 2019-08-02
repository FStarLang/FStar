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
module ImmutableST

open NatHeap

open FStar.Preorder
open FStar.Monotonic.Witnessed

(* Swapping the reference and heap arguments of (NatHeap.contains_ref) to 
   use it in point-free style in calls to (witness) and (recall). *)

let contains (#a:Type) (r:ref a) (h:heap) = NatHeap.contains h r

val contains_lemma : #a:Type -> 
                     h:heap -> 
	             r:ref a ->
	             Lemma (requires (contains r h)) 
			   (ensures  (NatHeap.contains h r))
	             [SMTPat (contains r h)]
let contains_lemma #a h r = ()


(* Two heaps are related if the latter differs from the former only by new 
   allocated references and all existing content is preserved unchanged. *)

let heap_rel (h0:heap) (h1:heap) = 
  (forall a (r:ref a) . contains r h0 ==> contains r h1) /\
  (forall a (r:ref a{contains r h0}) . sel h0 r == sel h1 r)

(* *************************************************** *)

(* 
   A temporary definition of preorder-indexed state 
   monads specialized to the immutable references 
   instance, in order to make sub-effecting to work. 
   Using (heap) and (heap_rel) for the statespace and 
   the relation on it, which otherwise would be given 
   by parameters to the preorder-idndexed state monad.
*)


(* Preconditions, postconditions and WPs for the preorder-indexed state monad. *)

let ist_pre  (state:Type)          = state -> Type0
let ist_post (state:Type) (a:Type) = a -> state -> Type0
let ist_wp   (state:Type) (a:Type) = ist_post state a -> Tot (ist_pre state)


(* A WP-style preorder-indexed state monad specialised for the immutable references instance. *)

new_effect ISTATE = STATE_h heap


(* DIV is a sub-effect/sub-monad of the immutable references instance of the preorder-indexed monad. *)

unfold let lift_div_istate (state:Type) (rel:preorder state)
                           (a:Type) (wp:pure_wp a) (p:ist_post state a) (s:state) = wp (fun x -> p x s)
sub_effect DIV ~> ISTATE = lift_div_istate heap heap_rel


(* A pre- and postcondition version of this preorder-indexed state monad. *)

effect IST    (a:Type) 
              (pre:ist_pre heap) 
	      (post:(heap -> Tot (ist_post heap a))) 
       =
       ISTATE a (fun p s0 -> pre s0 /\ (forall x s1 . pre s0 /\ post s0 x s1 ==> p x s1))


(* A box-like modality for witnessed stable predicates for IST. *)

let ist_witnessed (p:predicate heap{stable p heap_rel}) = witnessed heap_rel p


(* Generic effects (operations) for IST. *)

assume val ist_get :     unit -> IST heap (fun s0 -> True) (fun s0 s s1 -> s0 == s /\ s == s1)

assume val ist_put :     x:heap ->
		         IST unit (fun s0 -> heap_rel s0 x) (fun s0 _ s1 -> s1 == x)

assume val ist_witness : p:predicate heap{stable p heap_rel} ->
		         IST unit (fun s0 -> p s0) (fun s0 _ s1 -> s0 == s1 /\ ist_witnessed p)

assume val ist_recall :  p:predicate heap{stable p heap_rel} -> 
		         IST unit (fun _ -> ist_witnessed p) (fun s0 _ s1 -> s0 == s1 /\ p s1)


(* *************************************************** *)

(* References, a refinement of references provided by NatHeap. *)

type ref (a:Type) = r:ref a{ist_witnessed (contains r)}


(* Pre- and postconditions for the immutable references instance of IST. *)

let st_pre           = heap -> Type0
let st_post (a:Type) = a -> heap -> Type0
let st_wp   (a:Type) = st_post a -> Tot st_pre


(* The immutable references instance of IST. *)

effect ImmutableST (a:Type) 
                   (pre:st_pre) 
	           (post:heap -> Tot (st_post a)) 
       =
       IST     a pre post


(* Allocation, reading and writing operations. *)

val alloc : #a:Type -> 
            x:a -> 
	    ImmutableST (ref a) (fun _       -> True)
                                (fun h0 r h1 -> ~(contains r h0) /\ 
					        fst (alloc_ref h0 a x) == r /\ 
						snd (alloc_ref h0 a x) == h1)
let alloc #a x = 
  let h0 = ist_get () in
  let rh1 = alloc_ref h0 a x in 
  ist_put (snd rh1); 
  ist_witness (contains (fst rh1));    //witnessing that the current heap contains the generated reference
  fst rh1


val read : #a:Type -> 
           r:ref a -> 
	   ImmutableST a (fun _      -> True) 
                         (fun h0 x h1 -> h0 == h1 /\ 
			                 contains r h1 /\ 
					 sel h1 r == x)
let read #a r =
  let h = ist_get () in
  ist_recall (contains r);        //recalling that the current heap must contain the given reference
  sel h r                         //the above call to (recall) is crucial for being able to use (sel)


val write : #a:Type -> 
            r:ref a -> 
	    x:a -> 
	    ImmutableST unit (fun h0      -> contains r h0 /\ 
	                                     sel h0 r == x)
                             (fun h0 _ h1 -> h0 == h1)
let write #a r x = 
  let h = ist_get () in
  ist_put h


(* Two additional alternative definitions of write, doing absolutely nothing. *)

val write_nop : #a:Type -> 
                r:ref a -> 
		x:a -> 
		ImmutableST unit (fun h0      -> contains r h0 /\ 
		                                 sel h0 r == x)
                                 (fun h0 _ h1 -> h0 == h1)
let write_nop #a r x = ()


(* Recall operation for recalling that any reference allocated in the past will still be allocated now. *)
(* This is a bonus feature to the basic immutable behaviour of ImmutableST, resuling from the chosen encoding. *)

val recall : #a:Type -> 
             r:ref a -> 
	     ImmutableST unit (fun h0      -> True) 
                              (fun h0 _ h1 -> h0 == h1 /\ 
			                      contains r h1)
let recall #a r = 
  ist_recall (contains r)     //recalling that the current heap must contain the given reference
