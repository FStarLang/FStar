module Test.LaxTermEq

open FStar.Tactics.V2

let _ = assert True by guard (lax_term_eq (`1) (`1))
let _ = assert True by guard (not (lax_term_eq (`1) (`2)))

let x = 1

let _ = assert True by guard (lax_term_eq (`x) (`x))
let _ = assert True by guard (not (lax_term_eq (`x) (`1)))

let _ = assert True by guard (lax_term_eq (`(fun x -> x)) (`(fun y -> y)))

// Binder type mismatch
let _ = assert True by guard (not (lax_term_eq (`(fun x -> x)) (`(fun (y:int) -> y))))
