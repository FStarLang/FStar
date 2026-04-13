module ShortCircuitEffect

open FStar.Tactics.V2

let f (x:int) : Tot (b:bool{b ==> x >= 0}) = x > 0
let g (x:int) : Tac bool = true

// Effectful arguments to &&/|| are automatically lifted
let test (i:int) : Tac bool =
  f i && g i