module Bug4455
open FStar.SizeT

[@@coercion]
let sizet_to_nat (x: SizeT.t) : GTot int = SizeT.v x

let test (x y : int) : int = x * y
