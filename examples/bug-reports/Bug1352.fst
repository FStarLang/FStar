module Bug1352

open FStar.Preorder
open FStar.Heap

val evolve : x:int -> Tot (preorder int)
let evolve x = trivial_preorder int

let y = evolve 1 2 3
