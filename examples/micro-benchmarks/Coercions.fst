module Coercions

open FStar.Ghost

[@(expect_failure [34])]
let test0 (x: erased int) : Tot int = x

let test1 (x: erased int) : GTot int = x

let test2 (x:int) : erased int = x

let test3 (x:erased int) : erased int = x

let test4 (x:erased int) : GTot (erased int) = x

let test5 (x:int) : GTot (erased int) = x

let test6 (x:erased int) : GTot int = x
