open Prims
type t =
  | Sz of FStar_UInt64.t 
let uu___is_Sz (projectee : t) : Prims.bool= true
let __proj__Sz__item__x (projectee : t) : FStar_UInt64.t=
  match projectee with | Sz x -> x
let v (x : t) : Prims.nat= FStar_UInt64.v (__proj__Sz__item__x x)
let uint_to_t (x : Prims.int) : t= Sz (FStar_UInt64.uint_to_t x)
let uint16_to_sizet (x : FStar_UInt16.t) : t= uint_to_t (FStar_UInt16.v x)
let uint32_to_sizet (x : FStar_UInt32.t) : t= uint_to_t (FStar_UInt32.v x)
let uint64_to_sizet (x : FStar_UInt64.t) : t= uint_to_t (FStar_UInt64.v x)
let sizet_to_uint32 (x : t) : FStar_UInt32.t=
  FStar_Int_Cast.uint64_to_uint32 (__proj__Sz__item__x x)
let sizet_to_uint64 (x : t) : FStar_UInt64.t= __proj__Sz__item__x x
let add (x : t) (y : t) : t=
  Sz (FStar_UInt64.add (__proj__Sz__item__x x) (__proj__Sz__item__x y))
let sub (x : t) (y : t) : t=
  Sz (FStar_UInt64.sub (__proj__Sz__item__x x) (__proj__Sz__item__x y))
let mul (x : t) (y : t) : t=
  Sz (FStar_UInt64.mul (__proj__Sz__item__x x) (__proj__Sz__item__x y))
let div (x : t) (y : t) : t=
  let res_n =
    FStar_UInt64.div (__proj__Sz__item__x x) (__proj__Sz__item__x y) in
  let res = Sz res_n in res
let rem (x : t) (y : t) : t=
  Sz (FStar_UInt64.rem (__proj__Sz__item__x x) (__proj__Sz__item__x y))
let eq (x : t) (y : t) : Prims.bool=
  FStar_UInt64.eq (__proj__Sz__item__x x) (__proj__Sz__item__x y)
let ne (x : t) (y : t) : Prims.bool=
  FStar_UInt64.ne (__proj__Sz__item__x x) (__proj__Sz__item__x y)
let gt (x : t) (y : t) : Prims.bool=
  FStar_UInt64.gt (__proj__Sz__item__x x) (__proj__Sz__item__x y)
let gte (x : t) (y : t) : Prims.bool=
  FStar_UInt64.gte (__proj__Sz__item__x x) (__proj__Sz__item__x y)
let lt (x : t) (y : t) : Prims.bool=
  FStar_UInt64.lt (__proj__Sz__item__x x) (__proj__Sz__item__x y)
let lte (x : t) (y : t) : Prims.bool=
  FStar_UInt64.lte (__proj__Sz__item__x x) (__proj__Sz__item__x y)
let op_Plus_Hat : t -> t -> t= add
let op_Subtraction_Hat : t -> t -> t= sub
let op_Star_Hat : t -> t -> t= mul
let op_Slash_Hat : t -> t -> t= div
let op_Percent_Hat : t -> t -> t= rem
let op_Equals_Hat : t -> t -> Prims.bool= eq
let op_Less_Greater_Hat : t -> t -> Prims.bool= ne
let op_Greater_Hat : t -> t -> Prims.bool= gt
let op_Greater_Equals_Hat : t -> t -> Prims.bool= gte
let op_Less_Hat : t -> t -> Prims.bool= lt
let op_Less_Equals_Hat : t -> t -> Prims.bool= lte
let __uint_to_t (x : Prims.int) : t= uint_to_t x
