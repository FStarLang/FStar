module SolvedWitness

open FStar.Tactics

(* Error 217 is tactic left uninstantiated goals (which is raised twice), so we're checking the `qed` succeeds *)
[@ (fail [217; 217])]
let _ = assert_by_tactic True (fun () -> dup (); flip (); trefl (); qed ())
