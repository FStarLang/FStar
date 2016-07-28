module FStar.SGX
open FStar.Heap

(* The basic idea is to define a combination of an exception and state monad, 
   with an additional bit of boolean state to record when a send may have failed.

   If this were using the Dm4Free construction, we would have written the monad as:

   STX (a:Type) = h0:heap                 //the input state
		-> send_failed:bool       //an input flag, recording whether or not a send has failed so far
		-> Tot (option (a * heap) //the output state is an optional pair, because throwing an exception discards (and resets) the state
		        * bool)           //the output flag, recording whether this computation has a failed send

   with

   return (a:Type) (x:a) : STX a = 
     fun h0 b0 -> Some (x, h0), b0

   bind (a:Type) (b:Type) (f:STX a) (g:a -> STX b) : STX b = 
     fun h0 b0 ->
	 match f h0 b0 with
	 | None, b1 -> None, b1 //if the first computation throws, the state is gone, but the flag remains
	 | Some (x, h1), b1 -> g x h1 b1  //otherwise, we run the second computation with the new state and flag


  Much of what follows is this basic idea, but it's a bit convoluted
  because of the WP style. We should make this work with Dm4Free so
  that we can really write what's above instead of the verbose stuff
  that follows.

  One wrinkle is that I define everything first generically over the
  type of the state, and then instantiate the state to FStar.Heap.heap.
  That should allow us to plug in whatever memory model you like, later.
*)

(* You can mostly skip reading from here ...
   <skip> *)
let stx_pre_h  (h:Type)           = h                //input state is pair of the state h 
				  -> bool             //and a flag recording the status of the last send
				  -> GTot Type0
let stx_post_h (h:Type) (a:Type)  = option (a * h)   //an exceptional result and final state
				  -> bool             //pair of final state and output flag
				  -> GTot Type0
let stx_wp_h   (h:Type) (a:Type)  = stx_post_h h a 
				  -> Tot (est_pre_h h)

inline let stx_ite_wp (heap:Type) (a:Type)
                      (wp:est_wp_h heap a)
                      (post:est_post_h heap a) (h0:heap) (b:bool) =
    forall (k:est_post_h heap a).
       (forall (x:option (a * heap)) (b:bool).{:pattern (guard_free (k x b))} k x b <==> post x b)
       ==> wp k h0 b
inline let stx_return  (heap:Type) (a:Type) (x:a) (p:est_post_h heap a) (h0:heap) (b:bool)= p (Some (x, h0)) b
inline let stx_bind_wp (heap:Type) (r1:range) (a:Type) (b:Type)
                       (wp1:est_wp_h heap a)
                       (wp2:(a -> GTot (est_wp_h heap b)))
                       (p:est_post_h heap b) (h0:heap) (b0:bool) : GTot Type0 =
   labeled r1 "push" unit
   /\ wp1 (fun ra b1 ->
       labeled r1 "pop" unit
	 /\ (match ra with 
	    | None -> p None b1 //if the 1st computation throws, then we don't run the 2nd one
	    | Some (x, h1) -> wp2 x p h1 b1))
     h0 b0
inline let stx_if_then_else (heap:Type) (a:Type) (p:Type)
                             (wp_then:est_wp_h heap a) (wp_else:est_wp_h heap a)
                             (post:est_post_h heap a) (h0:heap) (b:bool) =
   l_ITE p
       (wp_then post h0 b)
       (wp_else post h0 b)
inline let stx_stronger (heap:Type) (a:Type) (wp1:est_wp_h heap a)
                        (wp2:est_wp_h heap a) =
    (forall (p:est_post_h heap a) (h:heap) (b:bool). wp1 p h b ==> wp2 p h b)

inline let stx_close_wp (heap:Type) (a:Type) (b:Type)
                        (wp:(b -> GTot (est_wp_h heap a)))
                        (p:est_post_h heap a) (h:heap) (f:bool) =
    (forall (b:b). wp b p h f)
inline let stx_assert_p (heap:Type) (a:Type) (p:Type)
                        (wp:est_wp_h heap a) (q:est_post_h heap a) (h:heap) (b:bool) =
    p /\ wp q h b
inline let stx_assume_p (heap:Type) (a:Type) (p:Type)
                         (wp:est_wp_h heap a) (q:est_post_h heap a) (h:heap) (b:bool) =
    p ==> wp q h b
inline let stx_null_wp (heap:Type) (a:Type)
                       (p:est_post_h heap a) (h0:heap) (b:bool) =
    (forall (a:option (a * heap)) (b1:bool). p a b1)
inline let stx_trivial (heap:Type) (a:Type) (wp:est_wp_h heap a) =
    (forall (h0:heap) (b:bool). wp (fun r b -> True) h0 b)

new_effect {
  STX_h (heap:Type) : a:Type -> wp:est_wp_h heap a -> Effect
  with
    return_wp    = stx_return       heap
  ; bind_wp      = stx_bind_wp      heap
  ; if_then_else = stx_if_then_else heap
  ; ite_wp       = stx_ite_wp       heap
  ; stronger     = stx_stronger     heap
  ; close_wp     = stx_close_wp     heap
  ; assert_p     = stx_assert_p     heap
  ; assume_p     = stx_assume_p     heap
  ; null_wp      = stx_null_wp      heap
  ; trivial      = stx_trivial      heap
}
(* </skip> until here *)
////////////////////////////////////////////////////////////////////////////////
open FStar.Heap 
new_effect STX = STX_h heap //Define a instance of ES, specializing the memory to heaps

(* Eth is our effect, in Hoare triple style with pre-conditions and post-conditions *)
effect Eth (a:Type) 
	   (pre:heap -> bool -> Type0)
	   (post:heap -> bool -> option (a * heap) -> bool -> Type0)
       = STX a (fun (q:option (a * heap) -> bool -> Type0) (h0:heap) (b0:bool) -> 
		  pre h0 b0
		  /\ (forall r b1. post h0 b0 r b1 ==> q r b1))
	 

(* operations for STX *)
(* This is my best guess so far at the desired semantics of the operations.
   We should discuss further to see if that matches reality *)
assume val throw : unit -> Eth unit 
  (requires (fun _ _ -> True))
  (ensures (fun h0 b0 r b1 -> b0=b1 /\ r==None)) //state is reset; flag doesn't change

assume val send: msg:nat -> Eth bool
  (requires (fun _ b0 -> not b0))      //can only send if we are not already in a "failed send" state
  (ensures (fun h0 b0 r b1 -> 
		 r==Some (b1, h0))) //the return value is the flag and the heap doesn't change

assume val alloc:  #a:Type -> init:a -> Eth (ref a)
  (requires (fun _ _ -> True)) //allocation effects are always permitted
  (ensures (fun h0 b0 r b1 -> 
	      b0=b1 /\ //the flag doesn't change
	      (match r with 
 	       | None -> False
	       | Some (x, h1) -> 
	  	  not(contains h0 x)  //the returned ref is fresh
		/\ contains h1 x
		/\ h1==upd h0 x init))) //and the heap is updated appropriately

assume val recall:  #a:Type -> x:ref a -> Eth unit
   (requires (fun h0 b0 -> True)) 
   (ensures (fun h0 b0 r b1 ->  r == Some ((), h0)
			  /\ b0 = b1
			  /\ Heap.contains h0 x))

assume val read:  #a:Type -> x:ref a -> Eth a
   (requires (fun _ _ -> True)) //read effects are always permitted
   (ensures (fun h0 b0 r b1 -> 
	       b0=b1 /\ //the flag doesn't change
	       r==Some (sel h0 x, h0)))

