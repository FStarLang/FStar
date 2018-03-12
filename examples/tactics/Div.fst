module Div

open FStar.Tactics

let rec f0 (x : int) : Dv int = f0 x
let g0 (x : int) : Tac int = f0 x

(* Testing that a non-diverging example works *)
let rec f (x : int) : Dv int = 25
let g (x : int) : Tac int = f x
let _ = assert_by_tactic True (fun () -> let x = g 2 in trivial ())
