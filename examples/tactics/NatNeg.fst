module NatNeg

open FStar.Tactics

[@(expect_failure [19])]
let n : nat = synth_by_tactic (fun () -> exact (quote (-1)))
