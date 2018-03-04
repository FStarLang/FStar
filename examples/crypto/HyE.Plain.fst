module HyE.Plain

open Platform.Bytes
open CoreCrypto
open HyE.Ideal


abstract type t = bytes

assume Plain_hasEq: hasEq t

type r = bytes

(* two pure functions, never called when ideal *)
abstract val repr:    p:t{not conf} -> Tot r
let repr t = t       (* a pure function from t to RSA.plain *)

abstract val coerce: x:r -> Tot t //(y:t{y = x}))
let coerce t =t (* a function from r to t *)

abstract val length: p:t -> Tot nat
let length p = length p
