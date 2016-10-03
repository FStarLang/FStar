module CCA2.Plain
open CCA2

(* private  *)type t = RSA.plain
type r = RSA.plain

(* two pure functions, never called when ideal *)
val repr:    t -> Tot r
let repr t = t       (* a pure function from t to RSA.plain *)

val coerce: x:r -> Tot (option (y:t{repr y = x}))
let coerce t = Some t (* a partial function from RSA.plain to t *)
