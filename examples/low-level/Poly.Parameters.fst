module Poly.Parameters

(* Standard platform integer size *)
let platform_size = 64
(* Integer size after multiplication *)
let platform_wide = 64
(* Canonical number of limbs *)
let norm_length = 5
let nlength = 5ul
(* Canonical number of bytes *)
let bytes_length = 17
let blength = 17ul
(* Representation template *)
val templ: nat -> Tot pos
let templ = fun x -> 26
