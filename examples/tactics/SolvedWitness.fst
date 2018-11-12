module SolvedWitness

open FStar.Tactics

(* Error 217 is tactic left uninstantiated goals, so we're also checking that `qed` succeeds *)
[@ (expect_failure [217])]
let _ = assert_by_tactic True (fun () -> dup (); flip (); trefl (); qed ())
