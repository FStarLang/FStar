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
module AllocSTwHeaps
open FStar.ST
open FStar.Preorder
open FStar.Monotonic.Witnessed

//giving ourselves two non-ghost versions of the heap sel/upd functions
assume val sel: h:FStar.Heap.heap -> r:ref 'a -> Tot (x:'a{x == FStar.Heap.sel h r})
assume val upd: h:FStar.Heap.heap -> r:ref 'a -> v:'a -> Tot (h':FStar.Heap.heap{h' == FStar.Heap.upd h r v})


(* The preorder on heaps for recalling that allocated 
   references remain allocated in all future heaps. *)
   
//NB: needed to restrict a:Type0, so that IST doesn't become
//    too universe polymorphic. This restriction is probably ok in practice ...
//    ... i don't imagine storing things beyond Type0 in the heap
//    Besides, if we allow that, then we may need to account for non-termination
let heap_rel (h0:FStar.Heap.heap) (h1:FStar.Heap.heap) = 
  forall (a:Type0) (r:ref a) . FStar.Heap.contains h0 r ==> FStar.Heap.contains h1 r


(* *************************************************** *)

(* 
   A temporary definition of preorder-indexed state 
   monads specialized to the allocated references 
   instance, in order to make sub-effecting to work. 
   Using (FStar.Heap.heap) and (heap_rel) for the 
   statespace and the relation on it, which otherwise 
   would be given by parameters.
*)


(* Preconditions, postconditions and WPs for the preorder-indexed state monad. *)

let ist_pre  (state:Type)          = state -> Type0
let ist_post (state:Type) (a:Type) = a -> state -> Type0
let ist_wp   (state:Type) (a:Type) = ist_post state a -> Tot (ist_pre state)


(* A WP-style preorder-indexed state monad specialised for the allocated references instance. *)

new_effect ISTATE = STATE_h FStar.Heap.heap


(* DIV is a sub-effect/sub-monad of the allocated references instance of the preorder-indexed monad. *)

unfold let lift_div_istate (state:Type) (rel:preorder state)
                           (a:Type) (wp:pure_wp a) (p:ist_post state a) (s:state) = wp (fun x -> p x s)
sub_effect DIV ~> ISTATE = lift_div_istate FStar.Heap.heap heap_rel



(*A pre- and postcondition version of this preorder-indexed state monad. *)

effect IST    (a:Type) 
              (pre:ist_pre FStar.Heap.heap) 
	      (post:(FStar.Heap.heap -> Tot (ist_post FStar.Heap.heap a))) 
       =
       ISTATE a (fun p s0 -> pre s0 /\ (forall x s1 . pre s0 /\ post s0 x s1 ==> p x s1))


(* A box-like modality for witnessed stable predicates for IST. *)

let ist_witnessed (p:predicate FStar.Heap.heap{stable p heap_rel}) = witnessed heap_rel p


(* Generic effects (operations) for IST. *)

assume val ist_get :     unit -> IST FStar.Heap.heap (fun s0 -> True) (fun s0 s s1 -> s0 == s /\ s == s1)

assume val ist_put :     x:FStar.Heap.heap ->
		         IST unit (fun s0 -> heap_rel s0 x) (fun s0 _ s1 -> s1 == x)

assume val ist_witness : p:predicate FStar.Heap.heap{stable p heap_rel} ->
		         IST unit (fun s0 -> p s0) (fun s0 _ s1 -> s0 == s1 /\ ist_witnessed p)

assume val ist_recall :  p:predicate FStar.Heap.heap{stable p heap_rel} -> 
		         IST unit (fun _ -> ist_witnessed p) (fun s0 _ s1 -> s0 == s1 /\ p s1)

(* *************************************************** *)


(* Swapping the reference and heap arguments of (FStar.Heap.contains) 
   to use it in point-free style in (witness) and (recall). *)

let contains (#a:Type) (r:ref a) (h:FStar.Heap.heap) =
  b2t (FStar.StrongExcludedMiddle.strong_excluded_middle (FStar.Heap.contains h r))


val contains_lemma : #a:Type -> 
                     h:FStar.Heap.heap -> 
		     r:ref a -> 
		     Lemma (requires (contains r h)) 
		           (ensures  (FStar.Heap.contains h r))
		     [SMTPat (contains r h)]
let contains_lemma #a h r = ()


(* Type of references that refines the standard notion of references by
   witnessing that the given reference is allocated in every future heap. *)

type ref a = r:ref a{ist_witnessed (contains r)}


(* Assuming a source of freshness for references for a given heap. *)

assume val gen_ref : #a:Type -> 
                     h:FStar.Heap.heap -> 
		     Tot (r:ref a{r `Heap.unused_in` h})


(* Pre- and postconditions for the allocated references instance of IST. *)

let st_pre           = FStar.Heap.heap -> Type0
let st_post (a:Type) = a -> FStar.Heap.heap -> Type0
let st_wp   (a:Type) = st_post a -> Tot st_pre


(* The allocated references instance of IST. *)

effect AllocST (a:Type) 
               (pre:st_pre) 
	       (post:FStar.Heap.heap -> Tot (st_post a)) 
       =
       IST     a pre post


(* Allocation, reading and writing operations. *)

val alloc : #a:Type -> 
            x:a -> 
	    AllocST (ref a) (fun _ -> True)
                            (fun h0 r h1 -> r `Heap.unused_in` h0 /\
					    FStar.Heap.contains h1 r /\
				            h1 == FStar.Heap.upd h0 r x)
let alloc #a x = 
  let h = ist_get () in
  let r = gen_ref h in
  ist_put (upd h r x);
  ist_witness (contains r);
  r                          


val read : #a:Type -> 
           r:ref a -> 
	   AllocST a (fun _       -> True) 
                     (fun h0 x h1 -> h0 == h1 /\ 
		                     x == FStar.Heap.sel h1 r)
let read #a r = 
  let h = ist_get () in
  sel h r


val write : #a:Type -> 
            r:ref a -> 
	    x:a -> 
	    AllocST unit (fun h0       -> FStar.Heap.contains h0 r)
                         (fun h0 _ h1 -> h1 == FStar.Heap.upd h0 r x)
let write #a r x =
  let h = ist_get () in
  ist_put (upd h r x)


(* Write operation with a more precise type. *)

val precise_write : #a:Type -> 
                    r:ref a -> 
		    x:a -> 
		    AllocST unit (fun h0      -> FStar.Heap.contains h0 r)
                                 (fun h0 _ h1 -> h1 == FStar.Heap.upd h0 r x)
let precise_write #a r x =
  let h = ist_get () in
  ist_put (upd h r x)


(* Operation for recalling that the current heap contains any reference we can apply this operation to. *)

val recall : #a:Type -> 
             r:ref a -> 
	     AllocST unit (fun h0      -> True) 
			  (fun h0 _ h1 -> h0 == h1 /\ 
			                  FStar.Heap.contains h1 r)
let recall #a r = 
  ist_recall (contains r)
