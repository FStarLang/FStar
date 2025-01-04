open Prims
type t = FStar_Int64.t
type 'x fits = unit
let (v : t -> Prims.int) = fun x -> FStar_Int64.v x
let (int_to_t : Prims.int -> t) = fun x -> FStar_Int64.int_to_t x
let (ptrdifft_to_sizet : t -> FStar_SizeT.t) =
  fun x -> FStar_SizeT.Sz (FStar_Int_Cast.int64_to_uint64 x)
let (add : t -> t -> t) = fun x -> fun y -> FStar_Int64.add x y
let (div : t -> t -> t) = fun x -> fun y -> FStar_Int64.div x y
let (rem : t -> t -> t) = fun x -> fun y -> FStar_Int64.rem x y
let (gt : t -> t -> Prims.bool) = fun x -> fun y -> FStar_Int64.gt x y
let (gte : t -> t -> Prims.bool) = fun x -> fun y -> FStar_Int64.gte x y
let (lt : t -> t -> Prims.bool) = fun x -> fun y -> FStar_Int64.lt x y
let (lte : t -> t -> Prims.bool) = fun x -> fun y -> FStar_Int64.lte x y
let (op_Plus_Hat : t -> t -> t) = add
let (op_Greater_Hat : t -> t -> Prims.bool) = gt
let (op_Greater_Equals_Hat : t -> t -> Prims.bool) = gte
let (op_Less_Hat : t -> t -> Prims.bool) = lt
let (op_Less_Equals_Hat : t -> t -> Prims.bool) = lte