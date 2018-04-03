module Bug1390

open FStar.Tactics

let f : int -> Tot int = fun x -> x
let g : #a:Type -> #b:Type -> (a -> Tac b) -> a -> Tac b = fun #a #b f x -> f x

let tau () = let x = g f 2 in ()

let _ = assert_by_tactic True tau
