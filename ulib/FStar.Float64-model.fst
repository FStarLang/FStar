(* Model implementation of FStar.Float64: verified, but never extracted (the real implementation is native).
   Floats are modeled as mathematical integers. *)
module FStar.Float64

type t = | F : v:int -> t

let of_int x = F (Int64.v x)
let add x y = F (F?.v x + F?.v y)
let sub x y = F (F?.v x - F?.v y)
let mul x y = F (F?.v x * F?.v y)
let div x y = if F?.v y = 0 then F 0 else F (F?.v x / F?.v y)
let lt x y = F?.v x < F?.v y
let lte x y = F?.v x <= F?.v y
let ieee_eq x y = F?.v x = F?.v y
let bit_eq x y = F?.v x = F?.v y
let of_literal _ = F 0
let to_string x = string_of_int (F?.v x)
