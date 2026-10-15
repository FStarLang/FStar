(* The OCaml realization of [FStar.SizeT], which Custard's OCaml backend
   treats as a machine-integer width of its own (see [machine_int_of_module]
   and [PrintOCaml.int_module]): every operation on a [size_t] becomes a call
   into this module.  It is 64 bits wide, as in [FStar.SizeT.fst], and boxed
   so that it is a type distinct from [FStar_UInt64.t]. *)

type t = Sz of FStar_UInt64.t

let lift f (Sz x) (Sz y) = Sz (f x y)
let lift_cmp f (Sz x) (Sz y) : bool = f x y

let v (Sz x) : Prims.int = FStar_UInt64.v x
let uint_to_t (x : Prims.int) : t = Sz (FStar_UInt64.uint_to_t x)
let __uint_to_t = uint_to_t

let zero = Sz FStar_UInt64.zero
let one = Sz FStar_UInt64.one

let uint16_to_sizet (x : FStar_UInt16.t) : t = uint_to_t (FStar_UInt16.v x)
let uint32_to_sizet (x : FStar_UInt32.t) : t = uint_to_t (FStar_UInt32.v x)
let uint64_to_sizet (x : FStar_UInt64.t) : t = Sz x
let of_u32 = uint32_to_sizet
let of_u64 = uint64_to_sizet
let sizet_to_uint32 (Sz x) : FStar_UInt32.t =
  FStar_UInt32.uint_to_t (Z.extract (FStar_UInt64.v x) 0 32)
let sizet_to_uint64 (Sz x) : FStar_UInt64.t = x

let add = lift FStar_UInt64.add
let add_underspec = add
let add_mod = add
let sub = lift FStar_UInt64.sub
let sub_underspec = sub
let sub_mod = sub
let mul = lift FStar_UInt64.mul
let mul_underspec = mul
let mul_mod = mul
let div = lift FStar_UInt64.div
let rem = lift FStar_UInt64.rem
let logand = lift FStar_UInt64.logand
let logor = lift FStar_UInt64.logor
let logxor = lift FStar_UInt64.logxor
let lognot (Sz x) = Sz (FStar_UInt64.lognot x)
let shift_left (Sz x) s = Sz (FStar_UInt64.shift_left x s)
let shift_right (Sz x) s = Sz (FStar_UInt64.shift_right x s)

let eq = lift_cmp FStar_UInt64.eq
let ne = lift_cmp FStar_UInt64.ne
let gt = lift_cmp FStar_UInt64.gt
let gte = lift_cmp FStar_UInt64.gte
let lt = lift_cmp FStar_UInt64.lt
let lte = lift_cmp FStar_UInt64.lte

let to_string (Sz x) = FStar_UInt64.to_string x
let of_string s = Sz (FStar_UInt64.of_string s)
