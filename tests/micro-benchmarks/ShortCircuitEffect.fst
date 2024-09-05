module ShortCircuitEffect

open FStar.Tactics.V2

let f (x:int) : Tot (b:bool{b ==> x >= 0}) = x > 0
let g (x:int) : Tac bool = true

// This should fail to check, even when admitting queries. We require
// explicit letbinding of effectful results.
#push-options "--admit_smt_queries true"
[@@expect_lax_failure [58]]
let test (i:int) : Tac bool =
  f i && g i
#pop-options
