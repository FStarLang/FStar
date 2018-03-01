module Synthesis

open FStar.Tactics

let a : unit = synth_by_tactic (fun () -> exact (`()))

let _ = assert (a == ())

let rec fib (n : int) : Tac unit =
    if n < 2
    then
        exact (`1)
    else (
        apply (`op_Addition);
        iseq [ (fun () -> fib (n - 1)) ;
               (fun () -> fib (n - 2)) ]
    )

let f8 : int = synth_by_tactic (fun () -> fib 8)
let _ = assert (f8 == 34) // equal after normalization

let rec fib_norm (n : int) : Tac unit =
    if n < 2
    then
        exact (`1)
    else (
        dup ();
        apply (`op_Addition);
        iseq [ (fun () -> fib_norm (n - 1)) ;
               (fun () -> fib_norm (n - 2)) ];
        norm [primops];
        trefl ()
    )

let fn8 : int = synth_by_tactic (fun () -> fib_norm 8)
let _ = assert (fn8 == 34) // syntactically equal

#set-options "--use_two_phase_tc false"  //AR: need to check
let iszero (x : int) : int =
    synth_by_tactic (fun () ->
        let x = quote x in
        let t_int = quote int in
        let _f = fresh_binder t_int in
        let t = Tv_Match x
                    [(Pat_Constant (C_Int 0), pack (Tv_Const (C_Int 1)));
                     (Pat_Wild _f, pack (Tv_Const (C_Int 0)))] in
        exact_guard (pack t);
        smt ())

let _ = assert (iszero 0 = 1)
let _ = assert (iszero 1 = 0)
let _ = assert (iszero 2 = 0)
