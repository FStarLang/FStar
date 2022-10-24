module FStar.SizeT

module I64 = FStar.Int64
module Cast = FStar.Int.Cast

(* This is only intended as a model, but will be extracted natively by Krml
   with the correct C semantics *)

let size_t = U64.t

let fits x =
  FStar.UInt.fits x U64.n == true

let v x =
  U64.v x

let size_v_inj (x1 x2: size_t) = ()

let mk (x: U16.t) : Pure size_t
  (requires True)
  (ensures (fun y -> v y == U16.v x))
= Cast.uint16_to_uint64 x

let mk_checked x = x

let int_to_size_t x =
  U64.uint_to_t x

let fits_le x y = ()

let add x y = x `U64.add` y

let sub x y = x `U64.sub` y

let mul x y = x `U64.mul` y

let le x y = x `U64.lte` y
