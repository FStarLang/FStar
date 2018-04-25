module NatNeg

open FStar.Tactics

[@(fail_errs [19])]
let n : nat = synth_by_tactic (fun () -> exact (quote (-1)))
