open Prims
let (max_int : Prims.nat -> Prims.int) =
  fun n -> (Prims.pow2 n) - Prims.int_one
let (min_int : Prims.nat -> Prims.int) = fun n -> Prims.int_zero
let (fits : Prims.int -> Prims.nat -> Prims.bool) =
  fun x -> fun n -> ((min_int n) <= x) && (x <= (max_int n))
type ('x, 'n) size = unit
type 'n uint_t = Prims.int
let (zero : Prims.nat -> unit uint_t) = fun n -> Prims.int_zero
let (pow2_n : Prims.pos -> Prims.nat -> unit uint_t) =
  fun n -> fun p -> Prims.pow2 p
let (one : Prims.pos -> unit uint_t) = fun n -> Prims.int_one
let (ones : Prims.nat -> unit uint_t) = fun n -> max_int n
let (incr : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> a + Prims.int_one
let (decr : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> a - Prims.int_one
let (incr_underspec : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n ->
    fun a -> if a < (max_int n) then a + Prims.int_one else Prims.int_zero
let (decr_underspec : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n ->
    fun a -> if a > (min_int n) then a - Prims.int_one else Prims.int_zero
let (incr_mod : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> (a + Prims.int_one) mod (Prims.pow2 n)
let (decr_mod : Prims.nat -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> (a - Prims.int_one) mod (Prims.pow2 n)
let (add : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> fun b -> a + b
let (add_underspec : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t)
  =
  fun n -> fun a -> fun b -> if fits (a + b) n then a + b else Prims.int_zero
let (add_mod : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> fun b -> (a + b) mod (Prims.pow2 n)
let (sub : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> fun b -> a - b
let (sub_underspec : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t)
  =
  fun n -> fun a -> fun b -> if fits (a - b) n then a - b else Prims.int_zero
let (sub_mod : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> fun b -> (a - b) mod (Prims.pow2 n)
let (mul : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> fun b -> a * b
let (mul_underspec : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t)
  =
  fun n -> fun a -> fun b -> if fits (a * b) n then a * b else Prims.int_zero
let (mul_mod : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> fun b -> (a * b) mod (Prims.pow2 n)
let (mul_div : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> fun b -> (a * b) / (Prims.pow2 n)
let (div : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> fun b -> a / b
let (div_underspec : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t)
  =
  fun n -> fun a -> fun b -> if fits (a / b) n then a / b else Prims.int_zero
let (udiv : Prims.pos -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> fun b -> a / b
let (mod1 : Prims.nat -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> fun b -> a - ((a / b) * b)
let (eq : Prims.nat -> unit uint_t -> unit uint_t -> Prims.bool) =
  fun n -> fun a -> fun b -> a = b
let (gt : Prims.nat -> unit uint_t -> unit uint_t -> Prims.bool) =
  fun n -> fun a -> fun b -> a > b
let (gte : Prims.nat -> unit uint_t -> unit uint_t -> Prims.bool) =
  fun n -> fun a -> fun b -> a >= b
let (lt : Prims.nat -> unit uint_t -> unit uint_t -> Prims.bool) =
  fun n -> fun a -> fun b -> a < b
let (lte : Prims.nat -> unit uint_t -> unit uint_t -> Prims.bool) =
  fun n -> fun a -> fun b -> a <= b
let (to_uint_t : Prims.nat -> Prims.int -> unit uint_t) =
  fun m -> fun a -> a mod (Prims.pow2 m)
let rec (to_vec : Prims.nat -> unit uint_t -> unit FStar_BitVector.bv_t) =
  fun n ->
    fun num ->
      if n = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        FStar_Seq_Base.append
          (to_vec (n - Prims.int_one) (num / (Prims.of_int (2))))
          (FStar_Seq_Base.create Prims.int_one
             ((num mod (Prims.of_int (2))) = Prims.int_one))
let rec (from_vec : Prims.nat -> unit FStar_BitVector.bv_t -> unit uint_t) =
  fun n ->
    fun vec ->
      if n = Prims.int_zero
      then Prims.int_zero
      else
        ((Prims.of_int (2)) *
           (from_vec (n - Prims.int_one)
              (FStar_Seq_Base.slice vec Prims.int_zero (n - Prims.int_one))))
          +
          (if FStar_Seq_Base.index vec (n - Prims.int_one)
           then Prims.int_one
           else Prims.int_zero)
let (nth : Prims.pos -> unit uint_t -> Prims.nat -> Prims.bool) =
  fun n -> fun a -> fun i -> FStar_Seq_Base.index (to_vec n a) i
let (logand : Prims.pos -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n ->
    fun a ->
      fun b ->
        from_vec n (FStar_BitVector.logand_vec n (to_vec n a) (to_vec n b))
let (logxor : Prims.pos -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n ->
    fun a ->
      fun b ->
        from_vec n (FStar_BitVector.logxor_vec n (to_vec n a) (to_vec n b))
let (logor : Prims.pos -> unit uint_t -> unit uint_t -> unit uint_t) =
  fun n ->
    fun a ->
      fun b ->
        from_vec n (FStar_BitVector.logor_vec n (to_vec n a) (to_vec n b))
let (lognot : Prims.pos -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> from_vec n (FStar_BitVector.lognot_vec n (to_vec n a))
let (minus : Prims.pos -> unit uint_t -> unit uint_t) =
  fun n -> fun a -> add_mod n (lognot n a) Prims.int_one
let (xor : Prims.bool -> Prims.bool -> Prims.bool) =
  fun b -> fun b' -> b <> b'
let (shift_left : Prims.pos -> unit uint_t -> Prims.nat -> unit uint_t) =
  fun n ->
    fun a ->
      fun s -> from_vec n (FStar_BitVector.shift_left_vec n (to_vec n a) s)
let (shift_right : Prims.pos -> unit uint_t -> Prims.nat -> unit uint_t) =
  fun n ->
    fun a ->
      fun s -> from_vec n (FStar_BitVector.shift_right_vec n (to_vec n a) s)
let (msb : Prims.pos -> unit uint_t -> Prims.bool) =
  fun n -> fun a -> nth n a Prims.int_zero
let (zero_extend_vec :
  Prims.pos -> unit FStar_BitVector.bv_t -> unit FStar_BitVector.bv_t) =
  fun n ->
    fun a ->
      FStar_Seq_Base.append (FStar_Seq_Base.create Prims.int_one false) a
let (one_extend_vec :
  Prims.pos -> unit FStar_BitVector.bv_t -> unit FStar_BitVector.bv_t) =
  fun n ->
    fun a ->
      FStar_Seq_Base.append (FStar_Seq_Base.create Prims.int_one true) a
let (zero_extend : Prims.pos -> unit uint_t -> unit uint_t) =
  fun n ->
    fun a -> from_vec (n + Prims.int_one) (zero_extend_vec n (to_vec n a))
let (one_extend : Prims.pos -> unit uint_t -> unit uint_t) =
  fun n ->
    fun a -> from_vec (n + Prims.int_one) (one_extend_vec n (to_vec n a))