module SnapshotST

(*
   An example of preorder-indexed state monads in which 
   it is possible for the state to temporarily invalidate 
   the given preorder. Witnessing and recalling of stable 
   predicates is only possible when the state is consistent.
*)

open FStar.Preorder


(* The state space and the preorder on it for the snapshot instance of IST. *)

let snapshot_state (state:Type) = state * (option state)

let snapshot_rel (#state:Type) (rel:preorder state) (s0:snapshot_state state) (s1:snapshot_state state) = 
     ((snd s0 == None #state /\ snd s1 == None #state) ==> rel (fst s0) (fst s1))
  /\ (forall s . (snd s0 == None #state /\ snd s1 == Some s) ==> rel (fst s0) s)
  /\ (forall s . (snd s0 == Some s /\ snd s1 == None #state) ==> rel s (fst s1))
  /\ (forall s s' . (snd s0 == Some s /\ snd s1 == Some s') ==> rel s s')  


(* Proof that the relation of the snapshot instance of IST is associative. *)
val snapshot_rel_assoc : #state:Type -> 
			 rel:preorder state -> 
			 s0:snapshot_state state -> 
			 s1:snapshot_state state -> 
			 s2:snapshot_state state ->
			 Lemma (requires (snapshot_rel rel s0 s1 /\ snapshot_rel rel s1 s2))
			       (ensures  (snapshot_rel rel s0 s2))
			 [SMTPat (snapshot_rel rel s0 s1); SMTPat (snapshot_rel rel s1 s2)]
let snapshot_rel_assoc #state rel s0 s1 s2 = 
  match snd s0 with
  | None -> 
      (match snd s1 with
       | None -> 
          (match snd s2 with
           | None -> ()
	   | Some s2' -> ())
       | Some s1' -> 
           (match snd s2 with
	    | None -> ()
	    | Some s2' -> assert (rel (fst s0) s1'); assert (rel s1' s2')))
  | Some s0' -> 
      (match snd s1 with
       | None -> 
           (match snd s2 with
	    | None -> ()
	    | Some s2' -> ())
       | Some s1' -> 
           (match snd s2 with
	    | None -> assert (rel s0' s1'); assert (rel s1' (fst s2))
	    | Some s2' -> assert (rel s0' s1'); assert (rel s1' s2')))


(* Witnessing predicate for the snapshot instance of IST. *)

let witnessing_predicate (#state:Type) (#rel:preorder state) (p:predicate state{stable p rel}) (s:snapshot_state state) =
  (snd s == None ==> p (fst s)) /\ 
  (forall s' . snd s == Some s' ==> p s')


val witnessing_predicate_stable : #state:Type ->
		                  rel:preorder state -> 
		                  p:predicate state{stable p rel} ->
		                  s0:snapshot_state state ->
		                  s1:snapshot_state state ->
		                  Lemma (requires (witnessing_predicate #state #rel p s0 /\ snapshot_rel rel s0 s1))
		                        (ensures  (witnessing_predicate #state #rel p s1))
		                  [SMTPat (witnessing_predicate #state #rel p s0); SMTPat (snapshot_rel rel s0 s1)]
let witnessing_predicate_stable #state rel p s0 s1 = 
  match snd s0 with
  | None -> ()
  | Some s0' ->
      (match snd s1 with
       | None -> ()
       | Some s1' -> assert(rel s0' s1'))


(* ************************************************************************************************** *)

(* 
   A temporary definition of preorder-indexed state 
   monads specialized to the snapshot example, in 
   order to make sub-effecting to work. Using tmp_state 
   and tmp_rel for the statespace and the relation on 
   it, which otherwise would be given by parameters.
*)

(* Temporarily assuming the type of the states and the preorder on them. *)

assume type tmp_state
assume type tmp_rel : rel:preorder tmp_state


(* Preconditions, postconditions and WPs for the preorder-indexed state monad. *)

let ist_pre  (state:Type)          = state -> Type0
let ist_post (state:Type) (a:Type) = a -> state -> Type0
let ist_wp   (state:Type) (a:Type) = ist_post state a -> Tot (ist_pre state)


(* A WP-style preorder-indexed state monad specialised for snapshots. *)

new_effect ISTATE = STATE_h (snapshot_state tmp_state)


(* DIV is a sub-effect/sub-monad of the snapshot instance of the preorder-indexed monad. *)

unfold let lift_div_istate (state:Type) (rel:preorder state) 
                           (a:Type) (wp:pure_wp a) (p:ist_post state a) (s:state) = wp (fun x -> p x s)
sub_effect DIV ~> ISTATE = lift_div_istate (snapshot_state tmp_state) (snapshot_rel tmp_rel)


(*A pre- and postcondition version of this preorder-indexed state monad. *)

effect IST    (a:Type) 
              (pre:ist_pre (snapshot_state tmp_state)) 
	      (post:(snapshot_state tmp_state -> Tot (ist_post (snapshot_state tmp_state) a))) 
       =
       ISTATE a (fun p s0 -> pre s0 /\ (forall x s1 . pre s0 /\ post s0 x s1 ==> p x s1))


(* A box-like modality for witnessed stable predicates for IST. *)

assume type ist_witnessed: p:predicate (snapshot_state tmp_state){stable p (snapshot_rel tmp_rel)} -> Type0


(* Generic effects (operations) for IST. *)

assume val ist_get :     unit -> IST (snapshot_state tmp_state) (fun s0 -> True) (fun s0 s s1 -> s0 == s /\ s == s1)

assume val ist_put :     x:snapshot_state tmp_state ->
		         IST unit (fun s0 -> snapshot_rel tmp_rel s0 x) (fun s0 _ s1 -> s1 == x)

assume val ist_witness : p:predicate (snapshot_state tmp_state){stable p (snapshot_rel tmp_rel)} ->
		         IST unit (fun s0 -> p s0) (fun s0 _ s1 -> s0 == s1 /\ ist_witnessed p)

assume val ist_recall :  p:predicate (snapshot_state tmp_state){stable p (snapshot_rel tmp_rel)} -> 
		         IST unit (fun _ -> ist_witnessed p) (fun s0 _ s1 -> s0 == s1 /\ p s1)

(* ************************************************************************************************** *)


(* Pre- and postconditions for the snapshot instance of IST. *)

let snapshot_pre           = snapshot_state tmp_state -> Type0
let snapshot_post (a:Type) = a -> (snapshot_state tmp_state) -> Type0
let snapshot_wp   (a:Type) = snapshot_post a -> Tot snapshot_pre


(* The snapshot instance of IST. *)

effect SnapshotST (a:Type)
		  (pre:snapshot_pre)
		  (post:snapshot_state tmp_state -> Tot (snapshot_post a)) 
       = 
       IST        a pre post


(* The box-like modality for witnessed stable predicates for the snapshot instance of IST. *)

let witnessed (p:predicate tmp_state{stable p tmp_rel}) = 
  ist_witnessed (fun s -> witnessing_predicate #tmp_state #tmp_rel p s)


(* Read and write operations. These only work on the "observable" part of the state. *)

val read : unit -> 
           SnapshotST tmp_state (fun s0      -> True)
				(fun s0 s s1 -> fst s0 == s /\ 
				                fst s1 == s /\ 
						snd s0 == snd s1)
let read _ = 
  let s = ist_get () in
  fst s


val write : x:tmp_state -> 
            SnapshotST unit (fun s0      -> snapshot_rel tmp_rel s0 (x, snd s0))
		            (fun s0 _ s1 -> s1 == (x, snd s0))
let write x = 
  let s = ist_get () in
  ist_put (x, snd s)


(* Witness and recall operations. These are applicable only when the state is "consistent" (any better terminology???) wrt. the preorder. *)

val witness : p:predicate tmp_state{stable p tmp_rel} -> 
              SnapshotST unit (fun s0      -> p (fst s0) /\ 
	                                      snd s0 == None)
			      (fun s0 _ s1 -> s0 == s1 /\ 
			                      witnessed p)
let witness p = 
  ist_witness (fun s -> witnessing_predicate #tmp_state #tmp_rel p s)


val recall : p:predicate tmp_state{stable p tmp_rel} -> 
             SnapshotST unit (fun s0      -> witnessed p /\ 
	                                     snd s0 == None)
			     (fun s0 _ s1 -> s0 == s1 /\ 
			                     p (fst s0))
let recall p =
  ist_recall (fun s -> witnessing_predicate #tmp_state #tmp_rel p s)


(* Operation for making a snapshot of the current "consistent" state, allowing the future state updates to temporarily invalidate the preorder. *)

val make_snapshot : unit -> 
                    SnapshotST unit (fun s0      -> snd s0 == None) 
			            (fun s0 _ s1 -> fst s0 == fst s1 /\ 
				                    snd s1 == Some (fst s0))
let make_snapshot _ = 
  let s = ist_get () in 
  ist_put (fst s, Some (fst s))


(* Operation for restoring "consistency" when the current state is related to the snapshot that was made of an earlier "consistent" state. *)

val restore_consistency : unit -> 
                          SnapshotST unit (fun s0      -> exists s . 
			                                    snd s0 == Some s /\ 
							    tmp_rel s (fst s0))
                                          (fun s0 _ s1 -> fst s0 == fst s1 /\ 
					                  snd s1 == None)
let restore_consistency _ = 
  let s = ist_get () in
  ist_put (fst s, None)

