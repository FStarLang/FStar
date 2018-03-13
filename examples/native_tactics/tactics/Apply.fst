module Apply

open FStar.Mul
open FStar.Tactics

assume val x : int

val refl : (a:Type) -> (x:a) -> Lemma (x == x)
let refl a x = ()

[@plugin]
let tau () : Tac unit =
    apply_lemma (`refl)

let lem1 = assert_by_tactic (x == x) tau
