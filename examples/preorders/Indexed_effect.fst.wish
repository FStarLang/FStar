module IST

(* 
   A library for programming with preorder-indexed state monads. 
   
   Currently implemented on top of F*'s STATE monad.

   At the moment these preorder-indexed state monads lack sub-
   effecting because of how it is currently implemented in F*,
   making it impossible to say that 

     forall state rel . DIV ~> ISTATE state rel

   Therefore, the various examples of such preorder-indexed 
   state monads include concrete instances of this file.
*)

open Preorder

(* Pre- and postconditions for preorder-indexed state monads. *)

let ist_pre  (state:Type)          = state -> Type0

let ist_post (state:Type) (a:Type) = a -> state -> Type0

let ist_wp   (state:Type) (a:Type) = ist_post state a -> Tot (ist_pre state)


(* A WP-style preorder-indexed state monad. *)

new_effect  ISTATE (state:Type0) (rel:relation state{preorder rel}) = STATE_h state //typechecks with --lax flag on
//new_effect  ISTATE (state:Type) (rel:relation state{preorder rel}) = STATE_h state //does not typecheck with --lax flag on


(* Currently not possible, but at this point one would like to show that 
   PURE and DIV are sub-effects of ISTATE, for all states and relations. *)


(*A pre- and postcondition style preorder-indexed state monad. *)

effect IST    (state:Type)
	      (rel:relation state{preorder rel})
	      (a:Type)
	      (pre:ist_pre state)
	      (post:(state -> Tot (ist_post state a))) 
       =
       ISTATE state rel a (fun p s0 -> pre s0 /\ (forall x s1 . pre s0 /\ rel s0 s1 ==> p x s1))


(* An abstract (box-style) modality for witnessed stable predicates. *)

assume abstract type witnessed: #state:Type -> 
				#rel:relation state{preorder rel} -> 
				p:predicate state{stable rel p} -> 
				Type0

(* Generic effects (operations) for preorder-indexed state monads. *)

assume val get:     #state:Type -> 
		    #rel:relation state{preorder rel} -> 
		    IST state rel state (fun s0 -> True) 
					(fun s0 s s1 -> s0 == s /\ s == s1)

assume val put:     #state:Type ->
		    #rel:relation state{preorder rel} ->
		    s:state ->
		    IST state rel unit (fun s0 -> rel s0 s) 
				       (fun s0 _ s1 -> s1 == s)

assume val witness: #state:Type ->
		    #rel:relation state{preorder rel} ->
		    p:predicate state{stable rel p} ->
		    IST state rel unit (fun s0 -> p s0) 
				       (fun s0 _ s1 -> s0 == s1 /\ witnessed #state #rel p)

assume val recall:  #state:Type ->
		    #rel:relation state{preorder rel} ->
		    p:predicate state{stable rel p} -> 
		    IST state rel unit (fun _ -> witnessed #state #rel p) 
				       (fun s0 _ s1 -> s0 == s1 /\ p s1)



