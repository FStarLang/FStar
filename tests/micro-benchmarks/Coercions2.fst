module Coercions2

let f1 (h: 0 > 1) : (0 == 1) = ()

val f2 (h: 0 > 1) : (0 == 1)
let f2 = fun (h: 0 > 1) -> ()