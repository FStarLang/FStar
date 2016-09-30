module HyE.Plain

open Platform.Bytes
open CoreCrypto
open HyE.Ideal


abstract type t = bytes

assume Plain_hasEq: hasEq t

type r = bytes

(* two pure functions, never called when ideal *)
val repr:    p:t{not conf} -> Tot r
let repr t = t       (* a pure function from t to RSA.plain *)

val coerce: x:r -> Tot t //(y:t{y = x}))
let coerce t =t (* a function from r to t *)

val length: t -> Tot nat
let length p = length p
