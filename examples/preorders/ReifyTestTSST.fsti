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
module ReifyTestTSST

open FStar.Preorder
open FStar.Monotonic.Witnessed

(* *************************************************************************************************** *)
(* A nat-valued instance of time-stamped preorder-indexed state monads for reify-recall demonstration. *)
(* *************************************************************************************************** *)

(* Timestamps. *)

val timestamp : Type0

val timestamped_state (state:Type u#a) : Type u#a

val get_timestamp : #state:Type -> timestamped_state state -> timestamp

val get_state : #state:Type -> timestamped_state state -> Tot state

val older_than : relation timestamp

val older_than_transitive : ts0:timestamp ->
                            ts1:timestamp ->
			    ts2:timestamp ->
                            Lemma (requires (older_than ts0 ts1 /\ older_than ts1 ts2))
			          (ensures  (older_than ts0 ts2))
		            [SMTPat (older_than ts0 ts1); SMTPat (older_than ts1 ts2)]

val older_than_antisymmetric : ts0:timestamp ->
                               ts1:timestamp ->
	                       Lemma (requires (~(older_than ts0 ts1) /\ ~(older_than ts1 ts0)))
	                             (ensures  (ts0 == ts1))
			       [SMTPat (~(older_than ts0 ts1)); SMTPat (~(older_than ts1 ts0))]


(* Pre- and postconditions for timestamped preorder-indexed state monads. *)

let tsst_pre  (state:Type)          = timestamped_state (state) -> Type0

let tsst_post (state:Type) (a:Type) = a -> timestamped_state (state) -> Type0

let tsst_wp   (state:Type) (a:Type) = tsst_post (state) a -> Tot (tsst_pre (state))


(* Temporary definitions of state and a preorder on it. *)

let state = nat

let state_rel : preorder state = fun s0 s1 -> b2t (s0 <= s1)


(* A WP-style timestamped preorder-indexed state monad. *)

new_effect TSSTATE = STATE_h (timestamped_state state)


(* Sub-effecting, works only because we have fixed the state and a preorder on it. *)

unfold let lift_div_tsstate (state:Type) (rel:preorder state)
                            (a:Type) (wp:pure_wp a) (p:tsst_post state a) (s:timestamped_state state) = wp (fun x -> p x s)
sub_effect DIV ~> TSSTATE = lift_div_tsstate state state_rel


(*A pre- and postcondition style preorder-indexed state monad. *)

effect TSST    (a:Type)
	       (pre:tsst_pre state)
	       (post:(timestamped_state (state) -> Tot (tsst_post state a))) 
       =
       TSSTATE a (fun p s0 -> pre s0 /\ (forall x s1 . 
                                          (pre s0 /\ 
					  state_rel (get_state s0) (get_state s1) /\ 
					  (older_than (get_timestamp s0) (get_timestamp s1) \/ 
					     get_timestamp s0 == get_timestamp s1) /\
					  post s0 x s1) 
					  ==> 
					  p x s1))


(* An abstract (box-style) modality for witnessed stable predicates. *)

let witnessed (ts:timestamp) (p:predicate state{stable p state_rel}) = witnessed state_rel p


(* Generic effects (operations) for preorder-indexed state monads. *)

val get:     unit -> 
		    TSST (timestamped_state state) (fun s0 -> True)
		                                   (fun s0 s s1 -> s0 == s /\
						                   s1 == s)


val put:     s:state ->
		    TSST unit (fun s0 -> state_rel (get_state s0) s) 
			      (fun s0 _ s1 -> get_state s1 == s /\
					      older_than (get_timestamp s0) (get_timestamp s1))


val witness: p:predicate state{stable p state_rel} ->
		    TSST unit (fun s0 -> p (get_state s0)) 
			      (fun s0 _ s1 -> get_state s0 == get_state s1 /\
				              get_timestamp s0 == get_timestamp s1 /\
					      witnessed (get_timestamp s1) p)


val recall:  p:predicate state{stable p state_rel} -> 
		    TSST unit (fun s0 -> exists ts . 
		                           (older_than ts (get_timestamp s0) \/ 
					      ts == get_timestamp s0) /\
		                              witnessed ts p) 
			      (fun s0 _ s1 -> get_state s0 == get_state s1 /\ 
					      get_timestamp s0 == get_timestamp s1 /\
					      p (get_state s1))


(* Signature of reify for TSST. *)

val reify_ : #a:Type ->
		   #pre:tsst_pre state ->
		   #post:(timestamped_state (state) -> Tot (tsst_post state a)) ->
		   e:(unit -> TSST a pre post) ->
		   s0:timestamped_state state ->
		   Pure (a & timestamped_state state) (pre s0)
		                                      (fun xs1 -> (older_than (get_timestamp s0) (get_timestamp (snd xs1)) \/
						                     get_timestamp s0 == get_timestamp (snd xs1)) /\
						                  state_rel (get_state s0) (get_state (snd xs1)) /\
						                  post s0 (fst xs1) (snd xs1))


(* Example program demonstrating reify_-recall interaction. *)

let reify_recall_test : unit -> TSST unit (fun _ -> True) (fun _ _ _ -> True) = fun _ ->
  let s0 = get () in 

  assume (state_rel (get_state s0) (get_state s0 + 1));  //temporary, because F* does not unroll the def. of state_rel

  let _ = put (get_state s0 + 1) in

  let _ = witness (fun s -> s > 0) in

  let s1 = get () in 

  let f = fun (x:unit) -> recall (fun s -> s > 0) in

  let v = reify_ #unit #(fun s0 -> exists ts . 
		                    (older_than ts (get_timestamp s0) \/ 
				       ts == get_timestamp s0) /\
		                       witnessed ts (fun s -> s > 0)) 
		      #(fun _ _ _ -> True) f in

  let _ = v s1 in   //accepted, as expected

  //let _ = v s0 in   //rejected, as expected

  ()
