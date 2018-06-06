module NonTot

open FStar.Tactics

val h : unit -> Pure (squash False) (requires False) (ensures (fun _ -> True))
let h x = ()

[@(Pervasives.fail [228])]
let _ =
    assert_by_tactic False (fun () -> apply (quote h))
