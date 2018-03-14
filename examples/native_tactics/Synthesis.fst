module Synthesis

open FStar.Tactics

[@plugin]
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

[@plugin]
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

[@plugin]
let mk_let () : Tac unit =
   match (inspect (`( let f x = if x<=1 then 1 else x - 1 in f 5 ))) with
   | Tv_Let r b t1 t2 ->
     let t = pack (Tv_Let r b t1 t2) in
     exact_guard t
   | _ -> dump "uh oh"; exact (`0)

let f2 : int = synth_by_tactic mk_let
let _ = assert (f2 == 4)

[@plugin]
let mk_let_rec () : Tac unit =
   match (inspect (`( let rec fr x = if x <= 1 then 1 else fr (x-1) in fr 5 ))) with
   | Tv_Let r b t1 t2 ->
     let t = pack (Tv_Let r b t1 t2) in
     exact_guard t
   | _ -> dump "uh oh"; exact (`0)

let f3 : int = synth_by_tactic mk_let_rec
let _ = assert_norm (f3 == 1)
let ascribe : int = synth_by_tactic (fun () -> exact (pack (Tv_AscribedT (`0) (`int) None)))

