module FStar.SizeT

module I64 = FStar.Int64

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

/// These two predicates are only used for modeling purposes, and their definitions must
/// remain abstract to ensure they can only be introduced through a static assert.
/// We simply define them as True here
let fits_u32 = True
let fits_u64 = True

let of_u32 (x: U32.t)
  = uint_to_t (U32.v x)

let of_u64 (x: U64.t)
  = uint_to_t (U64.v x)

let uint32_to_sizet x = uint_to_t (U32.v x)
let uint64_to_sizet x = uint_to_t (U64.v x)

let fits_lte x y = ()

let add = U64.add
let sub = U64.sub
let mul = U64.mul
let div = U64.div
let rem x y = U64.rem x y
let gt x y = U64.gt x y
let gte x y = U64.gte x y
let lt x y = U64.lt x y
let lte x y = U64.lte x y
