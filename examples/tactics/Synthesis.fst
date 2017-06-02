module Synthesis

open FStar.Tactics

(* Use a tactic to build an actual computing term! *)
(* we don't have a hook yet, so we do the following horrible thing
 * to get an `int` goal and run the `fib` tactic.
 *
 * Run with --debug Synthesis --debug_level Tac, you should see the witness
 * is `lem 34` (after normalization)
 *)

abstract let lem (x:int) : Lemma True = ()

let rec fib (n : int) : tactic unit =
    if n < 2
    then
        exact (quote 1)
    else (
        apply (quote op_Addition);;
        fib (n - 1);;
        fib (n - 2)
    )

let tau : tactic unit =
    apply_lemma (quote lem);;
    fib 8

let _ = assert_by_tactic tau True
