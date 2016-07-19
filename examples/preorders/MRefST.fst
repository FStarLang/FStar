module MRefST

open Preorder
open MRefHeap


(* Swapping the reference and heap arguments of (NatHeap.contains) to 
   use it in point-free style in calls to (witness) and (recall). *)

let contains (#a:Type) (#r:relation a{preorder r}) (m:mref a r) (h:heap) = contains h m

val contains_lemma : #a:Type -> 
                     #r:relation a{preorder r} ->
                     h:heap -> 
		     m:mref a r ->
		     Lemma (requires (contains m h)) 
			   (ensures  (MRefHeap.contains h m))
		     [SMTPat (contains m h)]
let contains_lemma #a #r h m = ()


(* Relating two heaps using the preorders associated with allocated monotonic references. *)

abstract type heap_rel (h0:heap) (h1:heap) = 
  (forall a r (m:mref a r) . contains m h0  ==> contains m h1) /\  
  (forall a r (m:mref a r{contains m h0}) . r (sel h0 m) (sel h1 m))


(* *************************************************** *)

(* 
   A temporary definition of preorder-indexed state 
   monads specialized to the allocated references 
   instance, in order to make sub-effecting to work. 
   Using (heap) and (heap_rel) for the statespace and 
   the relation on it, which otherwise would be given 
   by parameters to the preorder-idndexed state monad.
*)


(* Preconditions, postconditions and WPs for the preorder-indexed state monad. *)

let ist_pre  (state:Type)          = state -> Type0
let ist_post (state:Type) (a:Type) = a -> state -> Type0
let ist_wp   (state:Type) (a:Type) = ist_post state a -> Tot (ist_pre state)


(* A WP-style preorder-indexed state monad specialised for the allocated references instance. *)

new_effect ISTATE = STATE_h heap


(* DIV is a sub-effect/sub-monad of the allocated references instance of the preorder-indexed monad. *)

inline let lift_div_istate (state:Type) (rel:relation state{preorder rel}) 
                           (a:Type) (wp:pure_wp a) (p:ist_post state a) (s:state) = wp (fun x -> p x s)
sub_effect DIV ~> ISTATE = lift_div_istate heap heap_rel


(* A pre- and postcondition version of this preorder-indexed state monad. *)

effect IST    (a:Type) 
              (pre:ist_pre heap) 
	      (post:(heap -> Tot (ist_post heap a))) 
       =
       ISTATE a (fun p s0 -> pre s0 /\ (forall x s1 . 
                                          pre s0 /\ 
					  heap_rel s0 s1 /\
					  post s0 x s1 
					  ==> 
					  p x s1))


(* A box-like modality for witnessed stable predicates for IST. *)

assume type ist_witnessed : p:predicate heap{stable heap_rel p} -> Type0


(* Generic effects (operations) for IST. *)

assume val ist_get :     unit -> IST heap (fun s0 -> True) (fun s0 s s1 -> s0 == s /\ s == s1)

assume val ist_put :     x:heap ->
		         IST unit (fun s0 -> heap_rel s0 x) (fun s0 _ s1 -> s1 == x)

assume val ist_witness : p:predicate heap{stable heap_rel p} ->
		         IST unit (fun s0 -> p s0) (fun s0 _ s1 -> s0 == s1 /\ ist_witnessed p)

assume val ist_recall :  p:predicate heap{stable heap_rel p} -> 
		         IST unit (fun _ -> ist_witnessed p) (fun s0 _ s1 -> s0 == s1 /\ p s1)


(* *************************************************** *)

(* References. *)

type mref (a:Type) (r:relation a{preorder r}) = m:mref a r{ist_witnessed (contains m)}

  
(* Pre- and postconditions for the allocated references instance of IST. *)

let st_pre           = heap -> Type0
let st_post (a:Type) = a -> heap -> Type0
let st_wp   (a:Type) = st_post a -> Tot st_pre


(* The allocated references instance of IST. *)

effect MRefST (a:Type) 
               (pre:st_pre) 
	       (post:heap -> Tot (st_post a)) 
       =
       IST     a pre post


(* Allocation, reading and writing operations. *)

val alloc : #a:Type -> 
            r:relation a{preorder r} -> 
	    x:a -> 
	    MRefST (mref a r) (fun _       -> True)
                              (fun h0 m h1 -> ~(contains m h0) /\ 
					      fst (alloc_ref h0 a r x) == m /\
					      snd (alloc_ref h0 a r x) == h1)
let alloc #a r x = 
  let h0 = ist_get () in
  let mh1 = alloc_ref h0 a r x in 
  ist_put (snd mh1); 
  ist_witness (contains (fst mh1));    //witnessing that the current heap contains the generated reference
  fst mh1
  

val read : #a:Type -> 
           #r:relation a{preorder r} -> 
	   m:mref a r -> 
	   MRefST a (fun _      -> True) 
                    (fun h0 x h1 -> h0 == h1 /\ 
		                    contains m h1 /\ 
				    sel h1 m == x)
let read #a #r m =
  let h = ist_get () in
  ist_recall (contains m);    //recalling that the current heap must contain the given reference
  sel h m


val write : #a:Type -> 
            #r:relation a{preorder r} -> 
	    m:mref a r -> 
	    x:a -> 
	    MRefST unit (fun h0      -> contains m h0 /\ 
	                                r (sel h0 m) x)
                        (fun h0 _ h1 -> contains m h0 /\ 
			                h1 == upd h0 m x)
let write #a #r m x = 
  let h0 = ist_get () in
  ist_recall (contains m);    //recalling that the current heap must contain the given reference
  let h1 = upd h0 m x in
  ist_put h1


(* Stability property on heaps for monotonic references. *)

let stable_on_heap_aux (#a:Type) (#r:relation a{preorder r}) (m:mref a r) (p:predicate heap) (h0:heap) (h1:heap) = 
  p h0 /\ 
  (contains m h0 ==> contains m h1 /\ r (sel h0 m) (sel h1 m))
  ==> 
  p h1


let stable_on_heap (#a:Type) (#r:relation a{preorder r}) (m:mref a r) (p:predicate heap) = 
  forall h0 h1 . stable_on_heap_aux m p h0 h1


val stable_on_heap_stable : #a:Type -> 
                            #r:relation a{preorder r} -> 
			    m:mref a r -> 
			    p:predicate heap -> 
			    Lemma (requires (True))
			          (ensures  (forall h0 h1 . 
				               stable_on_heap_aux m p h0 h1
					       ==>
					       (p h0 /\ heap_rel h0 h1 ==> p h1)))
		            [SMTPat (stable_on_heap m p); SMTPat (stable heap_rel p)]
let stable_on_heap_stable #a #r m p = ()


(* Witnessing and recalling operations. *)

val witness : #a:Type -> 
              #r:relation a{preorder r} -> 
	      m:mref a r ->
	      p:predicate heap{stable_on_heap m p} -> 
	      MRefST unit (fun h0      -> p h0)
	                  (fun h0 _ h1 -> h0 == h1 /\ 
			                  ist_witnessed p)
let witness #a #r m p =
  ist_witness p


val recall : #a:Type -> 
             #r:relation a{preorder r} -> 
	     m:mref a r ->
	     p:predicate heap{stable_on_heap m p} -> 
	     MRefST unit (fun h0      -> ist_witnessed p)
	                 (fun h0 _ h1 -> h0 == h1 /\ 
			                 p h1)
let recall #a #r m p =
  ist_recall p

