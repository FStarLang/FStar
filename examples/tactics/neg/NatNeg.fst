module NatNeg

open FStar.Tactics

let n : nat = synth_by_tactic (fun () -> exact (quote (-1)))
