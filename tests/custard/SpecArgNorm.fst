module SpecArgNorm
open FStar.All
open FStar.IO

(* Issue #4828.  An argument in a position extraction erases -- here an
   implicit [prop] -- is not normalized.  [q12 1] unfolds to 4096 conjuncts,
   which exceeds the small --custard_norm_budget the Makefile sets, though
   the extracted code never mentions it. *)
unfold let q0 (x:int) : prop = x == x
unfold let q1 (x:int) : prop = q0 x /\ q0 (x + 1)
unfold let q2 (x:int) : prop = q1 x /\ q1 (x + 1)
unfold let q3 (x:int) : prop = q2 x /\ q2 (x + 1)
unfold let q4 (x:int) : prop = q3 x /\ q3 (x + 1)
unfold let q5 (x:int) : prop = q4 x /\ q4 (x + 1)
unfold let q6 (x:int) : prop = q5 x /\ q5 (x + 1)
unfold let q7 (x:int) : prop = q6 x /\ q6 (x + 1)
unfold let q8 (x:int) : prop = q7 x /\ q7 (x + 1)
unfold let q9 (x:int) : prop = q8 x /\ q8 (x + 1)
unfold let q10 (x:int) : prop = q9 x /\ q9 (x + 1)
unfold let q11 (x:int) : prop = q10 x /\ q10 (x + 1)
unfold let q12 (x:int) : prop = q11 x /\ q11 (x + 1)

let id_with_spec (#p:prop) (x:int) : int = x

let main () : ML unit =
  print_string (string_of_int (id_with_spec #(q12 1) 42) ^ "\n")
