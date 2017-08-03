module Apply

#reset-options "--eager_inference"

//

open FStar.Mul
open FStar.Tactics
open FStar.Tactics.Arith
open FStar.Reflection.Arith

assume val x : int

val refl : (a:Type) -> (x:a) -> Lemma (x == x)
let refl a x = ()

let tau : tactic unit =
    apply_lemma (quote refl)

let lem1 = assert_by_tactic (x == x) tau
