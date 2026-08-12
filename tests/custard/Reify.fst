module Reify
open FStar.Tactics.V2

(* Section 7.4: [Tac] is compiled through its representation type
   [ref_proofstate -> Dv a], not by dropping the effect.  The proofstate has to
   be threaded, or the compiler's tactic engine and the tactics it runs would
   disagree about the calling convention of every metaprogram. *)
let add (x:int) : Tac int = x + 1

let twice (x:int) : Tac int = add (add x)

let main () : FStar.All.ML unit = FStar.IO.print_string "ok\n"

(* Section 7.5: a local [let rec] is not a monadic node, so [reify] is stuck on
   it; unless the reify is pushed through by hand, everything after the
   [let rec] stays unreified and its effectful calls compile as pure values. *)
let after_letrec (l:list int) : Tac int =
  let rec sum (l:list int) : int =
    match l with
    | [] -> 0
    | x :: xs -> x + sum xs
  in
  let a = add (sum l) in
  a + 1
