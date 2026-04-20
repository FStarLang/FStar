module OpenOperators


open Prims { ( * ) }
 
let _ = assert (2 * 3 == 6)

open Prims { ( * ) as ( ++ ) }

let _ = assert (2 ++ 3 == 6)

open Prims { ( * ) as (-) }

let _ = assert (2 - 3 == 6)
