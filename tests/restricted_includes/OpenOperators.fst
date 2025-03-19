module OpenOperators

open FStar.Mul { ( * ) }

let _ = assert (2 * 3 == 6)

open FStar.Mul { ( * ) as ( ++ ) }

let _ = assert (2 ++ 3 == 6)

open FStar.Mul { ( * ) as (-) }

let _ = assert (2 - 3 == 6)
