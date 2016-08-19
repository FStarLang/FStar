module TSST

(* 
   Timestamped preorder-indexed state monads. 
   
   Currently implemented on top of F*'s STATE monad.

   At the moment these state monads lack sub-effecting 
   because of how it is currently implemented in F*, 
   making it impossible to say that 

     forall state rel . DIV ~> ISTATE state rel

   Therefore, the various examples of such state monads 
   include concrete instances of this file.
*)

open Preorder

(* Timestamps. *)

abstract type timestamp = nat

abstract type timestamped_state (state:Type) = timestamp * state

val get_timestamp : #state:Type -> timestamped_state state -> Tot timestamp
let get_timestamp #state tss = fst tss


val get_state : #state:Type -> timestamped_state state -> Tot state
let get_state #state tss = snd tss


val older_than : relation timestamp
let older_than ts0 ts1 = ts0 < ts1


val older_than_transitive : ts0:timestamp ->
                            ts1:timestamp ->
			    ts2:timestamp ->
                            Lemma (requires (older_than ts0 ts1 /\ older_than ts1 ts2))
			          (ensures  (older_than ts0 ts2))
		            [SMTPat (older_than ts0 ts1); SMTPat (older_than ts1 ts2)]
let older_than_transitive ts0 ts1 ts2 = ()


val older_than_antisymmetric : ts0:timestamp ->
                               ts1:timestamp ->
	                       Lemma (requires (~(older_than ts0 ts1) /\ ~(older_than ts1 ts0)))
	                             (ensures  (ts0 == ts1))
			       [SMTPat (~(older_than ts0 ts1)); SMTPat (~(older_than ts1 ts0))]
let older_than_antisymmetric ts0 ts1 = ()


(* Pre- and postconditions for timestamped preorder-indexed state monads. *)

let tsst_pre  (state:Type)          = timestamped_state (state) -> Type0

let tsst_post (state:Type) (a:Type) = a -> timestamped_state (state) -> Type0

let tsst_wp   (state:Type) (a:Type) = tsst_post (state) a -> Tot (tsst_pre (state))


(* A WP-style timestamped preorder-indexed state monad. *)

effect TSSTATE (state:Type)
	       (rel:relation state{preorder rel})
	       (a:Type)
	       (wp: tsst_wp state a)
       =
       STATE_h (timestamped_state (state)) a wp


(* Currently not possible, but at this point one would like to state 
   that DIV is a sub-effect of TSSTATE, for all states and relations. *)


(*A pre- and postcondition style preorder-indexed state monad. *)

effect TSST    (state:Type)
	       (rel:relation state{preorder rel})
	       (a:Type)
	       (pre:tsst_pre state)
	       (post:(timestamped_state (state) -> Tot (tsst_post state a))) 
       =
       TSSTATE state rel a (fun p s0 -> pre s0 /\ (forall x s1 . pre s0 /\ post s0 x s1 ==> p x s1))
(*
       TSSTATE state rel a (fun p s0 -> pre s0 /\ (forall x s1 . 
                                                     (pre s0 /\ 
					             rel (get_state s0) (get_state s1) /\ 
					             (older_than (get_timestamp s0) (get_timestamp s1) \/ 
					                get_timestamp s0 == get_timestamp s1) /\
						     post s0 x s1) 
						     ==> 
						     p x s1))
*)


(* An abstract (box-style) modality for witnessed stable predicates. *)

assume abstract type witnessed: #state:Type -> 
				#rel:relation state{preorder rel} -> 
				ts:timestamp ->
				p:predicate state{stable rel p} -> 
				Type0


(* Generic effects (operations) for preorder-indexed state monads. *)

assume val get:     #state:Type -> 
		    #rel:relation state{preorder rel} -> 
		    TSST state rel (timestamped_state state) (fun s0 -> True) 
					                     (fun s0 s s1 -> s0 == s /\
						                             s1 == s)


assume val put:     #state:Type ->
		    #rel:relation state{preorder rel} ->
		    s:state ->
		    TSST state rel unit (fun s0 -> rel (get_state s0) s) 
				        (fun s0 _ s1 -> get_state s1 == s /\
					                older_than (get_timestamp s0) (get_timestamp s1))


assume val witness: #state:Type ->
		    #rel:relation state{preorder rel} ->
		    p:predicate state{stable rel p} ->
		    TSST state rel unit (fun s0 -> p (get_state s0)) 
				        (fun s0 _ s1 -> get_state s0 == get_state s1 /\
				                        get_timestamp s0 == get_timestamp s1 /\
						        witnessed #state #rel (get_timestamp s1) p)


assume val recall:  #state:Type ->
		    #rel:relation state{preorder rel} ->
		    p:predicate state{stable rel p} -> 
		    TSST state rel unit (fun s0 -> exists ts . 
		                                     (older_than ts (get_timestamp s0) \/ 
						        ts == get_timestamp s0) /\
		                                     witnessed #state #rel ts p) 
				        (fun s0 _ s1 -> get_state s0 == get_state s1 /\ 
					                get_timestamp s0 == get_timestamp s1 /\
					                p (get_state s1))
