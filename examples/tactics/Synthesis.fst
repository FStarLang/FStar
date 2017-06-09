module Synthesis

open FStar.Tactics

let a : unit = synth_by_tactic (exact (quote ()))

let _ = assert (a == ())

let rec fib (n : int) : tactic unit =
    if n < 2
    then
        exact (quote 1)
    else (
        apply (quote op_Addition);;
        fib (n - 1);;
        fib (n - 2)
    )

let f8 : int = synth_by_tactic (fib 8)

let _ = assert (f8 == 34)
