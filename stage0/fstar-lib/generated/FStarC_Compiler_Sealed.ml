open Prims
type 'a sealed = 'a
let seal : 'a . 'a -> 'a sealed = fun x -> x
let unseal : 'a . 'a sealed -> 'a = fun x -> x