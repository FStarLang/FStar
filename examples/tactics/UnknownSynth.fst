module UnknownSynth

open FStar.Tactics

(* We cannot determine the type of `x` a-priori, so this should fail
 * before running. Currently it runs and fails, we should fix that. *)
[@expect_failure]
let x = synth_by_tactic (fun () -> exact (`42))

(* These are fine *)
let y : int = synth_by_tactic (fun () -> exact (`42))
let z = synth_by_tactic #int (fun () -> exact (`42))
