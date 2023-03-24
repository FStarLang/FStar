open Prims
let (max_int : Prims.pos -> Prims.int) =
  fun n -> (Prims.pow2 (n - Prims.int_one)) - Prims.int_one
let (min_int : Prims.pos -> Prims.int) =
  fun n -> - (Prims.pow2 (n - Prims.int_one))
let (fits : Prims.int -> Prims.pos -> Prims.bool) =
  fun x -> fun n -> ((min_int n) <= x) && (x <= (max_int n))
type ('x, 'n) size = unit
type 'n int_t = Prims.int
let (op_Slash : Prims.int -> Prims.int -> Prims.int) =
  fun a ->
    fun b ->
      if
        ((a >= Prims.int_zero) && (b < Prims.int_zero)) ||
          ((a < Prims.int_zero) && (b >= Prims.int_zero))
      then - ((Prims.abs a) / (Prims.abs b))
      else (Prims.abs a) / (Prims.abs b)
let (op_At_Percent : Prims.int -> Prims.int -> Prims.int) =
  fun v ->
    fun p ->
      let m = v mod p in
      if m >= (op_Slash p (Prims.of_int (2))) then m - p else m
let (zero : Prims.pos -> unit int_t) = fun n -> Prims.int_zero
let (pow2_n : Prims.pos -> Prims.nat -> unit int_t) =
  fun n -> fun p -> Prims.pow2 p
let (pow2_minus_one : Prims.pos -> Prims.nat -> unit int_t) =
  fun n -> fun m -> (Prims.pow2 m) - Prims.int_one
let (one : Prims.pos -> unit int_t) = fun n -> Prims.int_one
let (ones : Prims.pos -> unit int_t) = fun n -> (Prims.of_int (-1))
let (incr : Prims.pos -> unit int_t -> unit int_t) =
  fun n -> fun a -> a + Prims.int_one
let (decr : Prims.pos -> unit int_t -> unit int_t) =
  fun n -> fun a -> a - Prims.int_one
let (incr_underspec : Prims.pos -> unit int_t -> unit int_t) =
  fun n ->
    fun a -> if a < (max_int n) then a + Prims.int_one else Prims.int_zero
let (decr_underspec : Prims.pos -> unit int_t -> unit int_t) =
  fun n ->
    fun a -> if a > (min_int n) then a - Prims.int_one else Prims.int_zero
let (incr_mod : Prims.pos -> unit int_t -> unit int_t) =
  fun n -> fun a -> (a + Prims.int_one) mod (Prims.pow2 (n - Prims.int_one))
let (decr_mod : Prims.pos -> unit int_t -> unit int_t) =
  fun n -> fun a -> (a - Prims.int_one) mod (Prims.pow2 (n - Prims.int_one))
let (add : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> a + b
let (add_underspec : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> if fits (a + b) n then a + b else Prims.int_zero
let (add_mod : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> op_At_Percent (a + b) (Prims.pow2 n)
let (sub : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> a - b
let (sub_underspec : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> if fits (a - b) n then a - b else Prims.int_zero
let (sub_mod : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> op_At_Percent (a - b) (Prims.pow2 n)
let (mul : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> a * b
let (mul_underspec : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> if fits (a * b) n then a * b else Prims.int_zero
let (mul_mod : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> op_At_Percent (a * b) (Prims.pow2 n)
let (div : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> op_Slash a b
let (div_underspec : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n ->
    fun a ->
      fun b -> if fits (op_Slash a b) n then op_Slash a b else Prims.int_zero
let (udiv : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> op_Slash a b
let (mod1 : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n -> fun a -> fun b -> a - ((op_Slash a b) * b)
let (eq : Prims.pos -> unit int_t -> unit int_t -> Prims.bool) =
  fun n -> fun a -> fun b -> a = b
let (gt : Prims.pos -> unit int_t -> unit int_t -> Prims.bool) =
  fun n -> fun a -> fun b -> a > b
let (gte : Prims.pos -> unit int_t -> unit int_t -> Prims.bool) =
  fun n -> fun a -> fun b -> a >= b
let (lt : Prims.pos -> unit int_t -> unit int_t -> Prims.bool) =
  fun n -> fun a -> fun b -> a < b
let (lte : Prims.pos -> unit int_t -> unit int_t -> Prims.bool) =
  fun n -> fun a -> fun b -> a <= b
let (to_uint : Prims.pos -> unit int_t -> unit FStar_UInt.uint_t) =
  fun n -> fun x -> if Prims.int_zero <= x then x else x + (Prims.pow2 n)
let (from_uint : Prims.pos -> unit FStar_UInt.uint_t -> unit int_t) =
  fun n -> fun x -> if x <= (max_int n) then x else x - (Prims.pow2 n)
let (to_int_t : Prims.pos -> Prims.int -> unit int_t) =
  fun m -> fun a -> op_At_Percent a (Prims.pow2 m)
let (to_vec : Prims.pos -> unit int_t -> unit FStar_BitVector.bv_t) =
  fun n -> fun num -> FStar_UInt.to_vec n (to_uint n num)
let (from_vec : Prims.pos -> unit FStar_BitVector.bv_t -> unit int_t) =
  fun n ->
    fun vec ->
      let x = FStar_UInt.from_vec n vec in
      if (max_int n) < x then x - (Prims.pow2 n) else x
let (nth : Prims.pos -> unit int_t -> Prims.nat -> Prims.bool) =
  fun n -> fun a -> fun i -> FStar_Seq_Base.index (to_vec n a) i
let (logand : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n ->
    fun a ->
      fun b ->
        from_vec n (FStar_BitVector.logand_vec n (to_vec n a) (to_vec n b))
let (logxor : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n ->
    fun a ->
      fun b ->
        from_vec n (FStar_BitVector.logxor_vec n (to_vec n a) (to_vec n b))
let (logor : Prims.pos -> unit int_t -> unit int_t -> unit int_t) =
  fun n ->
    fun a ->
      fun b ->
        from_vec n (FStar_BitVector.logor_vec n (to_vec n a) (to_vec n b))
let (lognot : Prims.pos -> unit int_t -> unit int_t) =
  fun n -> fun a -> from_vec n (FStar_BitVector.lognot_vec n (to_vec n a))
let (minus : Prims.pos -> unit int_t -> unit int_t) =
  fun n -> fun a -> add_mod n (lognot n a) Prims.int_one
let (shift_left : Prims.pos -> unit int_t -> Prims.nat -> unit int_t) =
  fun n ->
    fun a ->
      fun s -> from_vec n (FStar_BitVector.shift_left_vec n (to_vec n a) s)
let (shift_right : Prims.pos -> unit int_t -> Prims.nat -> unit int_t) =
  fun n ->
    fun a ->
      fun s -> from_vec n (FStar_BitVector.shift_right_vec n (to_vec n a) s)
let (shift_arithmetic_right :
  Prims.pos -> unit int_t -> Prims.nat -> unit int_t) =
  fun n ->
    fun a ->
      fun s ->
        from_vec n
          (FStar_BitVector.shift_arithmetic_right_vec n (to_vec n a) s)