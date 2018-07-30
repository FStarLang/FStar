module Caller

open FStar.Tactics

(* Testing tactics for requires clauses *)

assume val ax : tau:(unit -> Tac unit) ->
                i:int -> Pure int (requires (with_tactic tau (squash (i > 0))))
                                  (ensures (fun i' -> i' == i + 1))

(* No tactic should run before this line *)

(* Will call tau to discharge the `b2t (3 > 0)` goal. *)
let f () : int =
    ax (fun () -> debug "Hello!"; trivial ()) 3
