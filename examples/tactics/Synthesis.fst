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
        iseq [fib (n - 1); fib (n - 2)]
    )

let f8 : int = synth_by_tactic (fib 8)
let _ = assert (f8 == 34) // equal after normalization

let rec fib_norm (n : int) : tactic unit =
    if n < 2
    then
        exact (quote 1)
    else (
        dup;;
        apply (quote op_Addition);;
        iseq [fib_norm (n - 1); fib_norm (n - 2)];;
        norm [primops];;
        trefl
    )

let fn8 : int = synth_by_tactic (fib_norm 8)
let _ = assert (fn8 == 34) // syntactically equal

let iszero (x : int) : int =
    synth_by_tactic (
        x <-- quote x;
        t_int <-- quote int;
        let _f = fresh_binder t_int in
        let t = Tv_Match x
                    [(Pat_Constant (C_Int 0), pack (Tv_Const (C_Int 1)));
                     (Pat_Wild _f, pack (Tv_Const (C_Int 0)))] in
        exact (return (pack t)))

let _ = assert (iszero 0 = 1)
let _ = assert (iszero 1 = 0)
let _ = assert (iszero 2 = 0)
