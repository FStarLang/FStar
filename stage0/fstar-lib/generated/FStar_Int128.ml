open Prims
let (n : Prims.int) = (Prims.of_int (128))
type t =
  | Mk of unit FStar_Int.int_t 
let (uu___is_Mk : t -> Prims.bool) = fun projectee -> true
let (__proj__Mk__item__v : t -> unit FStar_Int.int_t) =
  fun projectee -> match projectee with | Mk v -> v
let (v : t -> unit FStar_Int.int_t) = fun x -> __proj__Mk__item__v x
let (int_to_t : unit FStar_Int.int_t -> t) = fun x -> Mk x
let (zero : t) = int_to_t Prims.int_zero
let (one : t) = int_to_t Prims.int_one
let (add : t -> t -> t) =
  fun a -> fun b -> Mk (FStar_Int.add (Prims.of_int (128)) (v a) (v b))
let (sub : t -> t -> t) =
  fun a -> fun b -> Mk (FStar_Int.sub (Prims.of_int (128)) (v a) (v b))
let (mul : t -> t -> t) =
  fun a -> fun b -> Mk (FStar_Int.mul (Prims.of_int (128)) (v a) (v b))
let (div : t -> t -> t) =
  fun a -> fun b -> Mk (FStar_Int.div (Prims.of_int (128)) (v a) (v b))
let (rem : t -> t -> t) =
  fun a -> fun b -> Mk (FStar_Int.mod1 (Prims.of_int (128)) (v a) (v b))
let (logand : t -> t -> t) =
  fun x -> fun y -> Mk (FStar_Int.logand (Prims.of_int (128)) (v x) (v y))
let (logxor : t -> t -> t) =
  fun x -> fun y -> Mk (FStar_Int.logxor (Prims.of_int (128)) (v x) (v y))
let (logor : t -> t -> t) =
  fun x -> fun y -> Mk (FStar_Int.logor (Prims.of_int (128)) (v x) (v y))
let (lognot : t -> t) =
  fun x -> Mk (FStar_Int.lognot (Prims.of_int (128)) (v x))
let (shift_right : t -> FStar_UInt32.t -> t) =
  fun a ->
    fun s ->
      Mk
        (FStar_Int.shift_right (Prims.of_int (128)) (v a) (FStar_UInt32.v s))
let (shift_left : t -> FStar_UInt32.t -> t) =
  fun a ->
    fun s ->
      Mk (FStar_Int.shift_left (Prims.of_int (128)) (v a) (FStar_UInt32.v s))
let (shift_arithmetic_right : t -> FStar_UInt32.t -> t) =
  fun a ->
    fun s ->
      Mk
        (FStar_Int.shift_arithmetic_right (Prims.of_int (128)) (v a)
           (FStar_UInt32.v s))
let (eq : t -> t -> Prims.bool) =
  fun a -> fun b -> FStar_Int.eq (Prims.of_int (128)) (v a) (v b)
let (gt : t -> t -> Prims.bool) =
  fun a -> fun b -> FStar_Int.gt (Prims.of_int (128)) (v a) (v b)
let (gte : t -> t -> Prims.bool) =
  fun a -> fun b -> FStar_Int.gte (Prims.of_int (128)) (v a) (v b)
let (lt : t -> t -> Prims.bool) =
  fun a -> fun b -> FStar_Int.lt (Prims.of_int (128)) (v a) (v b)
let (lte : t -> t -> Prims.bool) =
  fun a -> fun b -> FStar_Int.lte (Prims.of_int (128)) (v a) (v b)
let (op_Plus_Hat : t -> t -> t) = add
let (op_Subtraction_Hat : t -> t -> t) = sub
let (op_Star_Hat : t -> t -> t) = mul
let (op_Slash_Hat : t -> t -> t) = div
let (op_Percent_Hat : t -> t -> t) = rem
let (op_Hat_Hat : t -> t -> t) = logxor
let (op_Amp_Hat : t -> t -> t) = logand
let (op_Bar_Hat : t -> t -> t) = logor
let (op_Less_Less_Hat : t -> FStar_UInt32.t -> t) = shift_left
let (op_Greater_Greater_Hat : t -> FStar_UInt32.t -> t) = shift_right
let (op_Greater_Greater_Greater_Hat : t -> FStar_UInt32.t -> t) =
  shift_arithmetic_right
let (op_Equals_Hat : t -> t -> Prims.bool) = eq
let (op_Greater_Hat : t -> t -> Prims.bool) = gt
let (op_Greater_Equals_Hat : t -> t -> Prims.bool) = gte
let (op_Less_Hat : t -> t -> Prims.bool) = lt
let (op_Less_Equals_Hat : t -> t -> Prims.bool) = lte
let (ct_abs : t -> t) =
  fun a ->
    let mask =
      shift_arithmetic_right a (FStar_UInt32.uint_to_t (Prims.of_int (127))) in
    sub (logxor a mask) mask
let (to_string : t -> Prims.string) = fun uu___ -> Prims.admit ()
let (of_string : Prims.string -> t) = fun uu___ -> Prims.admit ()
let (__int_to_t : Prims.int -> t) = fun x -> int_to_t x
let (mul_wide : FStar_Int64.t -> FStar_Int64.t -> t) =
  fun a -> fun b -> Mk ((FStar_Int64.v a) * (FStar_Int64.v b))