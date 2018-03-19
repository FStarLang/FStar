module SolveThen

open FStar.Tactics

let rec fib n : Tac unit = if n < 2 then exact (`1) else (apply (`(+)); fib (n - 1); fib (n - 2))

let f3 : int = synth_by_tactic (fun () -> fib 3)

let f8 : int = synth_by_tactic (fun () -> solve_then (fun () -> fib 8) compute)
