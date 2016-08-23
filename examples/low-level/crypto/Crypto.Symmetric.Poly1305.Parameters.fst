module Crypto.Symmetric.Poly1305.Parameters

(* Standard platform integer size *)
let platform_size : pos = 64
(* Integer size after multiplication *)
let platform_wide : pos = 64
(* Canonical number of limbs *)
let norm_length : pos = 5
let nlength : FStar.UInt32.t = 5ul
(* Canonical number of bytes *)
let bytes_length : pos = 17
let blength : FStar.UInt32.t = 17ul
(* Representation template *)
val templ: nat -> Tot pos
let templ = fun x -> 26
