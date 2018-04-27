module NonTot

open FStar.Tactics

val h : unit -> Pure (squash False) (requires False) (ensures (fun _ -> True))
let h x = ()

[@(fail_errs [23])]
let _ =
    assert_by_tactic False (fun () -> apply (quote h))
