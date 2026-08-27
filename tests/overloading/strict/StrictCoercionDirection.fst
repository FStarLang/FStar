module StrictCoercionDirection
module SizeT = FStar.SizeT
open FStar.SizeT

(* #4455 under 'strict': the coercion below goes from [FStar.SizeT.t] to
   [int] and not back, so [FStar.SizeT.op_Star] is not a candidate for a
   multiplication of two [int]s and there is no ambiguity to report. *)

[@@coercion]
let sizet_to_int (x: SizeT.t) : GTot int = SizeT.v x

let mul_int (x y : int) : int = x * y

(* And with [FStar.SizeT.t] arguments both candidates are applicable
   until the expected type rules out [Prims.op_Star]. *)
let mul_sizet (x y : SizeT.t) : Pure SizeT.t (requires SizeT.fits (SizeT.v x * SizeT.v y)) (ensures fun _ -> True) = x * y
