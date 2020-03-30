module Bug1170

open FStar.HyperStack
open FStar.HyperStack.ST

let action = unit -> St unit

(* action_id 1 through 4 work *)

let action_id1 (a: action) : action = fun u -> a u

let action_id2 (a: action) : action = a

let action_id3 (a: action) : Tot action = fun u -> a u

let action_id4 (a: action) : Pure action
  (requires True)
  (ensures (fun r -> True)) = a

(* this doesn't work (and also gives an unhelpful error location inside the
definition of the PURE effect) *)
let action_id5 (a: action) : Pure action
  (requires True)
  (ensures (fun r -> True)) = fun u -> a u
