module TermEq

open FStar.Reflection.Types

let _ = assert_norm ((`1) = (`1))
let _ = assert_norm ((`1) <> (`2))
