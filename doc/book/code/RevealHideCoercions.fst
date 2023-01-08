module RevealHideCoercions
open FStar.Ghost

let auto_hide (x:nat) : erased nat = x
let auto_reveal (x:erased nat) : GTot nat = x

[@@expect_failure] //Expect GTot
let auto_reveal_2 (x:erased nat) : Tot nat = x

let incr (x:nat) : nat = x + 1
let incr_e (x:erased nat) : erased nat = incr x

let incr' (x:nat) : GTot nat = incr_e x

[@@expect_failure]
let poly (x:nat) (y:erased nat) = x == y



