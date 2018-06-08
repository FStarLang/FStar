module NatNeg

open FStar.Tactics

[@(Pervasives.fail [19])]
let n : nat = synth_by_tactic (fun () -> exact (quote (-1)))
