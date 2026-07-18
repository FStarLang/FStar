open Prims
type 'a sealed = 'a
let seal (x : 'a) : 'a sealed= x
let unseal (x : 'a sealed) : 'a= x
