module Parameters

(* Standard platform integer size *)
let platform_size = 63
(* Integer size after multiplication *)
let platform_wide = 63
(* Canonical number of limbs *)
let norm_length = 5
(* Canonical number of bytes *)
let bytes_length = 17
(* Representation template *)
val templ: nat -> Tot pos
let templ = fun x -> 26
(* Max of the template *)
let ndiff' = 26
(* Max when the bigint is filled so as to not underflow in subtraction *)
let ndiff = 28
