module Caller

open FStar.Tactics

(*
 * Testing tactics for requires clauses
 *
 * Seems to work, but might too brittle... what if the axiom spawns off a VC?
 *)

let tau : tactic unit =
    let proof : b2t (3 > 0) = magic () in
    exact (quote proof)

assume val ax : i:int -> Pure int (requires (by_tactic tau (i > 0)))
                                  (ensures (fun i' -> i' == i + 1))

(* No tactic should run before this line *)

(* Will call tau to discharge the `b2t (3 > 0)` goal. We might want a way to specify the tactic on each call site *)
let f () : int =
    ax 3
