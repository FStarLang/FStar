module FStar.SGX
open FStar.Heap

(* The basic idea is to define a combination of an exception and state monad, 
   with an additional bit of boolean state to record when a send may have failed.

   If this were using the Dm4Free construction, we would have written the monad as:

   STX (a:Type) = h0:sgxmem		//the input state
		-> rw_failed:bool       //an input flag, recording whether or not a read/write has failed so far
		-> Tot (option (a * sgxmem) //the output state is an optional pair, because throwing an exception discards (and resets) the state
		        * bool)           //the output flag, recording whether this computation has a failed read/write

   with

   return (a:Type) (x:a) : STX a = 
     fun h0 b0 -> Some (x, h0), b0

   bind (a:Type) (b:Type) (f:STX a) (g:a -> STX b) : STX b = 
     fun h0 b0 ->
	 match f h0 b0 with
	 | None, b1 -> None, b1 //if the first computation throws, the state is gone, but the flag remains
	 | Some (x, h1), b1 -> g x h1 b1  //otherwise, we run the second computation with the new state and flag

*)

(* You can mostly skip reading from here ...
   <skip> *)
let stx_pre_h  (h:Type)           = h                //input state is pair of the state h 
				  -> bool             //and a flag recording the status of the last read/write
				  -> GTot Type0
let stx_post_h (h:Type) (a:Type)  = option (a * h)   //an exceptional result and final state
				  -> bool             //pair of final state and output flag
				  -> GTot Type0
let stx_wp_h   (h:Type) (a:Type)  = stx_post_h h a 
				  -> Tot (est_pre_h h)

unfold let stx_ite_wp (sgxmem:Type) (a:Type)
                      (wp:stx_wp_h sgxmem a)
                      (post:stx_post_h sgxmem a) (h0:sgxmem) (b:bool) =
    forall (k:stx_post_h sgxmem a).
       (forall (x:option (a * sgxmem)) (b:bool).{:pattern (guard_free (k x b))} k x b <==> post x b)
       ==> wp k h0 b
unfold let stx_return  (sgxmem:Type) (a:Type) (x:a) (p:stx_post_h sgxmem a) (h0:sgxmem) (b:bool)= p (Some (x, h0)) b
unfold let stx_bind_wp (sgxmem:Type) (r1:range) (a:Type) (b:Type)
                       (wp1:stx_wp_h sgxmem a)
                       (wp2:(a -> GTot (est_wp_h sgxmem b)))
                       (p:stx_post_h sgxmem b) (h0:sgxmem) (b0:bool) : GTot Type0 =
   labeled r1 "push" unit
   /\ wp1 (fun ra b1 ->
       labeled r1 "pop" unit
	 /\ (match ra with 
	    | None -> p None b1 //if the 1st computation throws, then we don't run the 2nd one
	    | Some (x, h1) -> wp2 x p h1 b1))
     h0 b0
unfold let stx_if_then_else (sgxmem:Type) (a:Type) (p:Type)
                             (wp_then:stx_wp_h sgxmem a) (wp_else:stx_wp_h sgxmem a)
                             (post:stx_post_h sgxmem a) (h0:sgxmem) (b:bool) =
   l_ITE p
       (wp_then post h0 b)
       (wp_else post h0 b)
unfold let stx_stronger (sgxmem:Type) (a:Type) (wp1:stx_wp_h sgxmem a)
                        (wp2:stx_wp_h sgxmem a) =
    (forall (p:stx_post_h sgxmem a) (h:sgxmem) (b:bool). wp1 p h b ==> wp2 p h b)

unfold let stx_close_wp (sgxmem:Type) (a:Type) (b:Type)
                        (wp:(b -> GTot (est_wp_h sgxmem a)))
                        (p:stx_post_h sgxmem a) (h:sgxmem) (f:bool) =
    (forall (b:b). wp b p h f)
unfold let stx_assert_p (sgxmem:Type) (a:Type) (p:Type)
                        (wp:stx_wp_h sgxmem a) (q:stx_post_h sgxmem a) (h:sgxmem) (b:bool) =
    p /\ wp q h b
unfold let stx_assume_p (sgxmem:Type) (a:Type) (p:Type)
                         (wp:stx_wp_h sgxmem a) (q:stx_post_h sgxmem a) (h:sgxmem) (b:bool) =
    p ==> wp q h b
unfold let stx_null_wp (sgxmem:Type) (a:Type)
                       (p:stx_post_h sgxmem a) (h0:sgxmem) (b:bool) =
    (forall (a:option (a * sgxmem)) (b1:bool). p a b1)
unfold let stx_trivial (sgxmem:Type) (a:Type) (wp:stx_wp_h sgxmem a) =
    (forall (h0:sgxmem) (b:bool). wp (fun r b -> True) h0 b)

new_effect {
  STX_h (sgxmem:Type) : a:Type -> wp:stx_wp_h sgxmem a -> Effect
  with
    return_wp    = stx_return       sgxmem
  ; bind_wp      = stx_bind_wp      sgxmem
  ; if_then_else = stx_if_then_else sgxmem
  ; ite_wp       = stx_ite_wp       sgxmem
  ; stronger     = stx_stronger     sgxmem
  ; close_wp     = stx_close_wp     sgxmem
  ; assert_p     = stx_assert_p     sgxmem
  ; assume_p     = stx_assume_p     sgxmem
  ; null_wp      = stx_null_wp      sgxmem
  ; trivial      = stx_trivial      sgxmem
}
(* </skip> until here *)
////////////////////////////////////////////////////////////////////////////////

open FStar.SGX

new_effect STX = STX_h sgxmem //Define a instance of STX_h, specializing the memory to sgxmem

(* Sth is our effect, in Hoare triple style with pre-conditions and post-conditions *)
effect Sth (a:Type) 
	   (pre:sgxmem -> bool -> Type0)
	   (post:sgxmem -> bool -> option (a * sgxmem) -> bool -> Type0)
       = STX a (fun (q:option (a * sgxmem) -> bool -> Type0) (h0:sgxmem) (b0:bool) -> 
		  pre h0 b0
		  /\ (forall r b1. post h0 b0 r b1 ==> q r b1))
	 

(* operations for STX. In Progress *)
assume val throw : unit -> Sth unit 
  (requires (fun _ _ -> True))
  (ensures (fun h0 b0 r b1 -> b0=b1 /\ r==None)) //state is reset; flag doesn't change

assume val store: addr:sgxref a->value:nat -> Sth bool
  (requires (fun h0 b0 -> not b0 /\ 		//can only write if we are not already in a "failed read/write" state 
		isbitmapset h0 addr))		//and if the corresponding address is protected in bitmap 
  (ensures (fun h0 b0 r b1 -> 
		 r==Some (b1, h0))) //the return value is the flag and the modified heap. FIXME: How to return modified heap 

assume val load:  #a:Type -> x:ref a -> Sth a
   (requires (fun _ b0 -> not b0 		//can only read if we are not already in a "failed read/write" state
		isbitmapset h0 addr))		//and if the corresponding address is protected in bitmap 
   (ensures (fun h0 b0 r b1 -> 
	       r==Some (sel h0 x, h0)))

