open Prims
let n : Prims.int= Prims.of_int 128
type t =
  | Mk of Obj.t FStar_Int.int_t 
let uu___is_Mk (projectee : t) : Prims.bool= true
let __proj__Mk__item__v (projectee : t) : Obj.t FStar_Int.int_t=
  match projectee with | Mk v -> v
let v (x : t) : Obj.t FStar_Int.int_t= __proj__Mk__item__v x
let int_to_t (x : Obj.t FStar_Int.int_t) : t= Mk x
let zero : t= int_to_t Prims.int_zero
let one : t= int_to_t Prims.int_one
let add (a : t) (b : t) : t=
  Mk (FStar_Int.add (Prims.of_int 128) (v a) (v b))
let sub (a : t) (b : t) : t=
  Mk (FStar_Int.sub (Prims.of_int 128) (v a) (v b))
let mul (a : t) (b : t) : t=
  Mk (FStar_Int.mul (Prims.of_int 128) (v a) (v b))
let div (a : t) (b : t) : t=
  Mk (FStar_Int.div (Prims.of_int 128) (v a) (v b))
let rem (a : t) (b : t) : t=
  Mk (FStar_Int.mod1 (Prims.of_int 128) (v a) (v b))
let logand (x : t) (y : t) : t=
  Mk (FStar_Int.logand (Prims.of_int 128) (v x) (v y))
let logxor (x : t) (y : t) : t=
  Mk (FStar_Int.logxor (Prims.of_int 128) (v x) (v y))
let logor (x : t) (y : t) : t=
  Mk (FStar_Int.logor (Prims.of_int 128) (v x) (v y))
let lognot (x : t) : t= Mk (FStar_Int.lognot (Prims.of_int 128) (v x))
let shift_right (a : t) (s : FStar_UInt32.t) : t=
  Mk (FStar_Int.shift_right (Prims.of_int 128) (v a) (FStar_UInt32.v s))
let shift_left (a : t) (s : FStar_UInt32.t) : t=
  Mk (FStar_Int.shift_left (Prims.of_int 128) (v a) (FStar_UInt32.v s))
let shift_arithmetic_right (a : t) (s : FStar_UInt32.t) : t=
  Mk
    (FStar_Int.shift_arithmetic_right (Prims.of_int 128) (v a)
       (FStar_UInt32.v s))
let rotate_right (a : t) (s : FStar_UInt32.t) : t=
  Mk (FStar_Int.rotate_right (Prims.of_int 128) (v a) (FStar_UInt32.v s))
let rotate_left (a : t) (s : FStar_UInt32.t) : t=
  Mk (FStar_Int.rotate_left (Prims.of_int 128) (v a) (FStar_UInt32.v s))
let eq (a : t) (b : t) : Prims.bool=
  FStar_Int.eq (Prims.of_int 128) (v a) (v b)
let ne (a : t) (b : t) : Prims.bool=
  FStar_Int.ne (Prims.of_int 128) (v a) (v b)
let gt (a : t) (b : t) : Prims.bool=
  FStar_Int.gt (Prims.of_int 128) (v a) (v b)
let gte (a : t) (b : t) : Prims.bool=
  FStar_Int.gte (Prims.of_int 128) (v a) (v b)
let lt (a : t) (b : t) : Prims.bool=
  FStar_Int.lt (Prims.of_int 128) (v a) (v b)
let lte (a : t) (b : t) : Prims.bool=
  FStar_Int.lte (Prims.of_int 128) (v a) (v b)
let op_Plus_Hat : t -> t -> t= add
let op_Subtraction_Hat : t -> t -> t= sub
let op_Star_Hat : t -> t -> t= mul
let op_Slash_Hat : t -> t -> t= div
let op_Percent_Hat : t -> t -> t= rem
let op_Hat_Hat : t -> t -> t= logxor
let op_Amp_Hat : t -> t -> t= logand
let op_Bar_Hat : t -> t -> t= logor
let op_Less_Less_Hat : t -> FStar_UInt32.t -> t= shift_left
let op_Greater_Greater_Hat : t -> FStar_UInt32.t -> t= shift_right
let op_Greater_Greater_Greater_Hat : t -> FStar_UInt32.t -> t=
  shift_arithmetic_right
let op_Equals_Hat : t -> t -> Prims.bool= eq
let op_Less_Greater_Hat : t -> t -> Prims.bool= ne
let op_Greater_Hat : t -> t -> Prims.bool= gt
let op_Greater_Equals_Hat : t -> t -> Prims.bool= gte
let op_Less_Hat : t -> t -> Prims.bool= lt
let op_Less_Equals_Hat : t -> t -> Prims.bool= lte
let ct_abs (a : t) : t=
  let mask =
    shift_arithmetic_right a (FStar_UInt32.uint_to_t (Prims.of_int 127)) in
  sub (logxor a mask) mask
let to_string (uu___ : t) : Prims.string= Prims.admit ()
let of_string (uu___ : Prims.string) : t= Prims.admit ()
let __int_to_t (x : Prims.int) : t= int_to_t x
let mul_wide (a : FStar_Int64.t) (b : FStar_Int64.t) : t=
  Mk ((FStar_Int64.v a) * (FStar_Int64.v b))
