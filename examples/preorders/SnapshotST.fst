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
module SnapshotST

(*
   An example of preorder-indexed state monads in which 
   it is possible for the state to temporarily invalidate 
   the given preorder. Witnessing and recalling of stable 
   predicates is only possible when the state is consistent.
*)

open FStar.Preorder
open FStar.Monotonic.Witnessed

(* The original type of states and a preorder on it *)

assume type state
assume val rel_s : preorder state

(* The richer state type that allows us to temporarily violate rel *)

noeq type t = 
  | Ok  : state -> t
  | Tmp : state -> state -> t

(* The lifting of rel to the richer state type *)

let rel_t (t0:t) (t1:t) 
 = match t0 , t1 with
   | Ok s0    , Ok s1    -> rel_s s0 s1
   | Ok s0    , Tmp s1 _ -> rel_s s0 s1
   | Tmp s0 _ , Ok s1    -> rel_s s0 s1
   | Tmp s0 _ , Tmp s1 _ -> rel_s s0 s1

(* Lifting predicates from state to t *)

let lift_predicate (p:predicate state{stable p rel_s}) (t:t) 
  = match t with
    | Ok s -> p s
    | Tmp s _ -> p s

(* Lifting stability from state to t *)

val lift_stability : p:predicate state{stable p rel_s}
		  -> t0:t
		  -> t1:t
		  -> Lemma (requires (lift_predicate p t0 /\ rel_t t0 t1))
		           (ensures  (lift_predicate p t1))
let lift_stability p t0 t1 = ()


(* ************************************************************************************************** *)

(* 
   A temporary definition of monotonic-state monad specialized to 
   this snapshots example, in order to make sub-effecting to work.
*)

(* Preconditions, postconditions, and WPs for the monotonic-state monad. *)

let mst_pre          = t -> Type0
let mst_post (a:Type) = a -> t -> Type0
let mst_wp   (a:Type) = mst_post a -> Tot mst_pre

(* A WP-style monotonic-state monad specialised for this example. *)

new_effect MSTATE = STATE_h t

(* DIV is a sub-effect of the snapshots instance of the monotonic-state monad. *)

(* AR: this failed when inline, investigate more *)
unfold let div_lift (a:Type) (wp:pure_wp a) (p:mst_post a) (x:t) = wp (fun y -> p y x)
sub_effect DIV ~> MSTATE = div_lift

(* A pre- and postcondition version of this monotonic-state monad. *)

effect MST (a:Type) (pre:mst_pre) (post:(t -> Tot (mst_post a))) 
       =
       MSTATE a (fun p t0 -> pre t0 /\ (forall x t1 . pre t0 /\ post t0 x t1 ==> p x t1))

(* The logical witnessed capability for the richer type of states *)

let witnessed (p:predicate t) = witnessed rel_t p

(* Actions of MST. *)

assume val get :     unit 
                  -> MST t (fun _ -> True) (fun t0 v t1 -> t0 == v /\ v == t1)

assume val put :     t:t 
                  -> MST unit (fun t0 -> rel_t t0 t) (fun _ _ t1 -> t1 == t)

assume val witness : p:predicate t{stable p rel_t} 
                  -> MST unit (fun t0 -> p t0) (fun t0 _ t1 -> t0 == t1 /\ witnessed p)

assume val recall :  p:predicate t{stable p rel_t} 
                  -> MST unit (fun _ -> witnessed p) (fun t0 _ t1 -> t0 == t1 /\ p t1)

(* ************************************************************************************************** *)


(* Logical witnessed capability for the original type of states *)

let witnessed_s (p:predicate state{stable p rel_s}) = 
  witnessed (fun s -> lift_predicate p s)

(* Get and put actions for the original type of states *)

val get_s : unit 
         -> MST state (fun _ -> True)
	              (fun t0 s t1 -> t0 == t1 /\ (match t1 with 
                                                   | Ok s1    -> s1 == s
                                                   | Tmp _ s1 -> s1 == s))
let get_s _ = 
  let t = get () in
  match t with
  | Ok s    -> s
  | Tmp _ s -> s

val put_s : s:state -> 
            MST unit (fun t0      -> match t0 with
                                     | Ok s0    -> rel_s s0 s
                                     | Tmp s0 _ -> rel_s s0 s)
		     (fun t0 _ t1 -> match t0 with
                                     | Ok _       -> t1 == Ok s
                                     | Tmp s0 s0' -> t1 == Tmp s0 s)
let put_s s = 
  let t = get () in
  match t with
  | Ok _     -> put (Ok s)
  | Tmp s' _ -> put (Tmp s' s)

(* Witness and recall operations for the original type of states *)

val witness_s : p:predicate state{stable p rel_s}
             -> MST unit (fun t0      -> Ok? t0 /\ (let Ok s = t0 in p s))
			 (fun t0 _ t1 -> t0 == t1 /\ witnessed_s p)
let witness_s p = 
  witness (fun s -> lift_predicate p s)

val recall_s : p:predicate state{stable p rel_s} 
            -> MST unit (fun t0       -> Ok? t0 /\ witnessed_s p)
			 (fun t0 _ t1 -> Ok? t0 /\ t0 == t1 /\ (let Ok s = t1 in p s))
let recall_s p =
  recall (fun s -> lift_predicate p s)

(* Actions for temporarily breaking and restoring the original preorder *)

val break : unit 
         -> MST unit (fun t0      -> Ok? t0) 
		     (fun t0 _ t1 -> Ok? t0 /\ (let Ok s = t0 in t1 == Tmp s s))
let break _ = 
  let Ok s = get () in 
  put (Tmp s s)

val restore : unit 
           -> MST unit (fun t0      -> Tmp? t0 /\ (let Tmp s0 s1 = t0 in rel_s s0 s1))
                       (fun t0 _ t1 -> Tmp? t0 /\ (let Tmp _ s1 = t0 in t1 == Ok s1))
let restore _ = 
  let Tmp _ s = get () in
  put (Ok s)
