open Prims
type t =
  | Sz of FStar_UInt64.t 
let (uu___is_Sz : t -> Prims.bool) = fun projectee -> true
let (__proj__Sz__item__x : t -> FStar_UInt64.t) =
  fun projectee -> match projectee with | Sz x -> x
type 'x fits = unit
let (v : t -> Prims.nat) = fun x -> FStar_UInt64.v (__proj__Sz__item__x x)
let (uint_to_t : Prims.nat -> t) = fun x -> Sz (FStar_UInt64.uint_to_t x)
type fits_u32 = unit
type fits_u64 = unit
let (uint16_to_sizet : FStar_UInt16.t -> t) =
  fun x -> uint_to_t (FStar_UInt16.v x)
let (uint32_to_sizet : FStar_UInt32.t -> t) =
  fun x -> uint_to_t (FStar_UInt32.v x)
let (uint64_to_sizet : FStar_UInt64.t -> t) =
  fun x -> uint_to_t (FStar_UInt64.v x)
let (sizet_to_uint32 : t -> FStar_UInt32.t) =
  fun x -> FStar_Int_Cast.uint64_to_uint32 (__proj__Sz__item__x x)
let (sizet_to_uint64 : t -> FStar_UInt64.t) = fun x -> __proj__Sz__item__x x
let (add : t -> t -> t) =
  fun x ->
    fun y ->
      Sz (FStar_UInt64.add (__proj__Sz__item__x x) (__proj__Sz__item__x y))
let (sub : t -> t -> t) =
  fun x ->
    fun y ->
      Sz (FStar_UInt64.sub (__proj__Sz__item__x x) (__proj__Sz__item__x y))
let (mul : t -> t -> t) =
  fun x ->
    fun y ->
      Sz (FStar_UInt64.mul (__proj__Sz__item__x x) (__proj__Sz__item__x y))
let (div : t -> t -> t) =
  fun x ->
    fun y ->
      let res_n =
        FStar_UInt64.div (__proj__Sz__item__x x) (__proj__Sz__item__x y) in
      let res = Sz res_n in res
let (rem : t -> t -> t) =
  fun x ->
    fun y ->
      Sz (FStar_UInt64.rem (__proj__Sz__item__x x) (__proj__Sz__item__x y))
let (gt : t -> t -> Prims.bool) =
  fun x ->
    fun y -> FStar_UInt64.gt (__proj__Sz__item__x x) (__proj__Sz__item__x y)
let (gte : t -> t -> Prims.bool) =
  fun x ->
    fun y -> FStar_UInt64.gte (__proj__Sz__item__x x) (__proj__Sz__item__x y)
let (lt : t -> t -> Prims.bool) =
  fun x ->
    fun y -> FStar_UInt64.lt (__proj__Sz__item__x x) (__proj__Sz__item__x y)
let (lte : t -> t -> Prims.bool) =
  fun x ->
    fun y -> FStar_UInt64.lte (__proj__Sz__item__x x) (__proj__Sz__item__x y)
let (op_Plus_Hat : t -> t -> t) = add
let (op_Subtraction_Hat : t -> t -> t) = sub
let (op_Star_Hat : t -> t -> t) = mul
let (op_Percent_Hat : t -> t -> t) = rem
let (op_Greater_Hat : t -> t -> Prims.bool) = gt
let (op_Greater_Equals_Hat : t -> t -> Prims.bool) = gte
let (op_Less_Hat : t -> t -> Prims.bool) = lt
let (op_Less_Equals_Hat : t -> t -> Prims.bool) = lte
let (__uint_to_t : Prims.int -> t) = fun x -> uint_to_t x