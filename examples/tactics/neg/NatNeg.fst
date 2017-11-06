module NatNeg

open FStar.Tactics

let n : nat = synth_by_tactic (exact (quote (-1)))
