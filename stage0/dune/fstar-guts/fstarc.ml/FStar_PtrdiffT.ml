open Prims
type t = FStar_Int64.t
let v (x : t) : Prims.int= FStar_Int64.v x
let int_to_t (x : Prims.int) : t= FStar_Int64.int_to_t x
let ptrdifft_to_sizet (x : t) : FStar_SizeT.t=
  FStar_SizeT.Sz (FStar_Int_Cast.int64_to_uint64 x)
let add (x : t) (y : t) : t= FStar_Int64.add x y
let div (x : t) (y : t) : t= FStar_Int64.div x y
let rem (x : t) (y : t) : t= FStar_Int64.rem x y
let gt (x : t) (y : t) : Prims.bool= FStar_Int64.gt x y
let gte (x : t) (y : t) : Prims.bool= FStar_Int64.gte x y
let lt (x : t) (y : t) : Prims.bool= FStar_Int64.lt x y
let lte (x : t) (y : t) : Prims.bool= FStar_Int64.lte x y
let op_Plus_Hat : t -> t -> t= add
let op_Greater_Hat : t -> t -> Prims.bool= gt
let op_Greater_Equals_Hat : t -> t -> Prims.bool= gte
let op_Less_Hat : t -> t -> Prims.bool= lt
let op_Less_Equals_Hat : t -> t -> Prims.bool= lte
