open Prims
type t =
  | Sz of FStar_UInt64.t 
let uu___is_Sz (projectee : t) : Prims.bool= true
let __proj__Sz__item__x (projectee : t) : FStar_UInt64.t=
  match projectee with | Sz x -> x
let v (x : t) : Prims.nat= FStar_UInt64.v (match x with | Sz x1 -> x1)
let uint_to_t (x : Prims.int) : t= Sz (FStar_UInt64.uint_to_t x)
let uint16_to_sizet (x : FStar_UInt16.t) : t= uint_to_t (FStar_UInt16.v x)
let uint32_to_sizet (x : FStar_UInt32.t) : t= uint_to_t (FStar_UInt32.v x)
let uint64_to_sizet (x : FStar_UInt64.t) : t= uint_to_t (FStar_UInt64.v x)
let sizet_to_uint32 (x : t) : FStar_UInt32.t=
  FStar_Int_Cast.uint64_to_uint32 (match x with | Sz x1 -> x1)
let sizet_to_uint64 (x : t) : FStar_UInt64.t= match x with | Sz x1 -> x1
let add (x : t) (y : t) : t=
  Sz
    (FStar_UInt64.add (match x with | Sz x1 -> x1)
       (match y with | Sz x1 -> x1))
let sub (x : t) (y : t) : t=
  Sz
    (FStar_UInt64.sub (match x with | Sz x1 -> x1)
       (match y with | Sz x1 -> x1))
let mul (x : t) (y : t) : t=
  Sz
    (FStar_UInt64.mul (match x with | Sz x1 -> x1)
       (match y with | Sz x1 -> x1))
let div (x : t) (y : t) : t=
  let res_n =
    FStar_UInt64.div (match x with | Sz x1 -> x1)
      (match y with | Sz x1 -> x1) in
  let res = Sz res_n in res
let rem (x : t) (y : t) : t=
  Sz
    (FStar_UInt64.rem (match x with | Sz x1 -> x1)
       (match y with | Sz x1 -> x1))
let eq (x : t) (y : t) : Prims.bool=
  FStar_UInt64.eq (match x with | Sz x1 -> x1) (match y with | Sz x1 -> x1)
let ne (x : t) (y : t) : Prims.bool=
  FStar_UInt64.ne (match x with | Sz x1 -> x1) (match y with | Sz x1 -> x1)
let gt (x : t) (y : t) : Prims.bool=
  FStar_UInt64.gt (match x with | Sz x1 -> x1) (match y with | Sz x1 -> x1)
let gte (x : t) (y : t) : Prims.bool=
  FStar_UInt64.gte (match x with | Sz x1 -> x1) (match y with | Sz x1 -> x1)
let lt (x : t) (y : t) : Prims.bool=
  FStar_UInt64.lt (match x with | Sz x1 -> x1) (match y with | Sz x1 -> x1)
let lte (x : t) (y : t) : Prims.bool=
  FStar_UInt64.lte (match x with | Sz x1 -> x1) (match y with | Sz x1 -> x1)
let op_Plus_Hat : t -> t -> t= add
let op_Minus_Hat : t -> t -> t= sub
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
