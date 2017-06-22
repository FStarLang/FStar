module HyE.PlainPKE

open HyE.RSA
open HyE.Ideal

type t = HyE.AE.key // This should be abstract
type r = HyE.RSA.plain

(* two pure functions, never called when ideal *)
val repr:    p:t{not conf} -> Tot r
let repr t = HyE.AE.leak t       (* a pure function from t to RSA.plain *)

assume val coerce: x:r -> Tot (option (y:t)) //MK changed from t{repr y = x}
//let coerce t = Some t (* a partial function from RSA.plain to t *)
