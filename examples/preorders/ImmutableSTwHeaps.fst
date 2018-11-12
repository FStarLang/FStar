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
module ImmutableSTwHeaps

open FStar.Heap
open FStar.Preorder
open FStar.Monotonic.Witnessed

//giving ourselves two non-ghost versions of the heap sel/upd functions
assume val sel: h:heap -> r:ref 'a -> Tot (x:'a{x == Heap.sel h r})
assume val upd: h:heap -> r:ref 'a -> v:'a -> Tot (h':heap{h' == Heap.upd h r v})

(* Two heaps are related if the latter differs from the former only by new 
   allocated references and all existing content is preserved unchanged. *)

let heap_rel (h0:heap) (h1:heap) = 
  forall a (r: ref a) . contains h0 r ==> contains h1 r /\ sel h0 r == sel h1 r


(* *************************************************** *)

(* 
   A temporary definition of preorder-indexed state 
   monads specialized to the immutable references 
   instance, in order to make sub-effecting to work. 
   Using (FStar.Heap.heap) and (heap_rel) for the 
   statespace and the relation on it, which otherwise 
   would be given by parameters.
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


(*A pre- and postcondition version of this preorder-indexed state monad. *)

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


(* Assuming a source of freshness for references for a given heap. 
   We need this in order to implement allocation in terms of the 
   IST monad, which is a global state monad in its nature. *)

assume val gen_ref : #a:Type -> h:heap -> Tot (r:ref a{r `unused_in` h})


(* Pre- and postconditions for the immutable references instance of IST. *)

let st_pre           = heap -> Type0
let st_post (a:Type) = a -> heap -> Type0
let st_wp   (a:Type) = st_post a -> Tot st_pre


(* The immutable references instance of IST. *)

effect ImmutableST (a:Type) 
                   (pre:st_pre) 
	           (post:heap -> Tot (st_post a)) 
       =
       IST         a pre post


(* Allocation and reading operations. *)

val alloc : #a:Type -> 
            x:a -> 
	    ImmutableST (ref a) (fun _ -> True)
                                (fun h0 r h1 -> r `unused_in` h0 /\
					        contains h1 r /\
						h1 == upd h0 r x)
let alloc #a x = 
  let h = ist_get () in
  let r = gen_ref h in
  ist_put (upd h r x);
  r                          


val read : #a:Type -> 
           r:ref a -> 
	   ImmutableST a (fun _       -> True) 
                         (fun h0 x h1 -> h0 == h1 /\ 
					 x == sel h1 r)
let read #a r = 
  let h = ist_get () in
  sel h r


(* Writing operation which allows the user to write only the same value that is already in the store. *)

val write : #a:Type -> 
            r:ref a -> 
	    x:a -> 
	    ImmutableST unit (fun h0      -> sel h0 r == x /\ h0 `contains` r)
                             (fun h0 _ h1 -> h1 == upd h0 r x)
let write #a r x =
  let h = ist_get () in
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ();
  ist_put (upd h r x)
