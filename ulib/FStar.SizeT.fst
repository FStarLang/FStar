module FStar.SizeT

module I64 = FStar.Int64
module Cast = FStar.Int.Cast

(* This is only intended as a model, but will be extracted natively by Krml
   with the correct C semantics *)

let t = U64.t

let fits x =
  FStar.UInt.fits x U64.n == true

let v x =
  U64.v x

let size_v_inj (x1 x2: t) = ()

let uint_to_t x =
  U64.uint_to_t x

let mk (x: U16.t) : Pure t
  (requires True)
  (ensures (fun y -> v y == U16.v x))
= uint_to_t (U16.v x)

let mk_checked x = uint_to_t (U64.v x)

let fits_lte x y = ()

let add = U64.add
let sub = U64.sub
let mul = U64.mul
let rem x y = U64.rem x y
let gt x y = U64.gt x y
let gte x y = U64.gte x y
let lt x y = U64.lt x y
let lte x y = U64.lte x y
