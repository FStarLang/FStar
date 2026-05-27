(* cannot redefine bool=bool, it's cyclic *)
type bool' = bool
type bool = bool'
type int' = int
type int = int'

let of_int x = x 
let int_zero = 0
let int_one = 1

type nat = int
type pos = int
