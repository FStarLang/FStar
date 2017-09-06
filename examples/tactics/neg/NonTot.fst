module NonTot

open FStar.Tactics

val h : unit -> Pure (squash False) (requires False) (ensures (fun _ -> True))
let h x = ()

let _ =
    assert_by_tactic (apply (quote h)) False
