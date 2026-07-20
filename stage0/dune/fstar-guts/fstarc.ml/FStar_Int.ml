open Prims
let max_int (n : Prims.pos) : Prims.int=
  (Prims.pow2 (n - Prims.int_one)) - Prims.int_one
let min_int (n : Prims.pos) : Prims.int= - (Prims.pow2 (n - Prims.int_one))
let fits (x : Prims.int) (n : Prims.pos) : Prims.bool=
  ((min_int n) <= x) && (x <= (max_int n))
type 'n int_t = Prims.int
let op_Slash_Subtraction (a : Prims.int) (b : Prims.int) : Prims.int=
  if
    ((a >= Prims.int_zero) && (b < Prims.int_zero)) ||
      ((a < Prims.int_zero) && (b >= Prims.int_zero))
  then - ((Prims.abs a) / (Prims.abs b))
  else (Prims.abs a) / (Prims.abs b)
let op_At_Percent (v : Prims.int) (p : Prims.int) : Prims.int=
  let m = (mod) v p in if m >= (p / (Prims.of_int 2)) then m - p else m
let zero (n : Prims.pos) : Obj.t int_t= Prims.int_zero
let pow2_n (n : Prims.pos) (p : Prims.nat) : Obj.t int_t= Prims.pow2 p
let pow2_minus_one (n : Prims.pos) (m : Prims.nat) : Obj.t int_t=
  (Prims.pow2 m) - Prims.int_one
let one (n : Prims.pos) : Obj.t int_t= Prims.int_one
let ones (n : Prims.pos) : Obj.t int_t= Prims.of_int (-1)
let incr (n : Prims.pos) (a : Obj.t int_t) : Obj.t int_t= a + Prims.int_one
let decr (n : Prims.pos) (a : Obj.t int_t) : Obj.t int_t= a - Prims.int_one
let incr_mod (n : Prims.pos) (a : Obj.t int_t) : Obj.t int_t=
  (mod) (a + Prims.int_one) (Prims.pow2 (n - Prims.int_one))
let decr_mod (n : Prims.pos) (a : Obj.t int_t) : Obj.t int_t=
  (mod) (a - Prims.int_one) (Prims.pow2 (n - Prims.int_one))
let add (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Obj.t int_t=
  a + b
let add_mod (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) :
  Obj.t int_t= op_At_Percent (a + b) (Prims.pow2 n)
let sub (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Obj.t int_t=
  a - b
let sub_mod (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) :
  Obj.t int_t= op_At_Percent (a - b) (Prims.pow2 n)
let mul (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Obj.t int_t=
  a * b
let mul_mod (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) :
  Obj.t int_t= op_At_Percent (a * b) (Prims.pow2 n)
let div (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Obj.t int_t=
  op_Slash_Subtraction a b
let udiv (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Obj.t int_t=
  op_Slash_Subtraction a b
let mod1 (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Obj.t int_t=
  a - ((op_Slash_Subtraction a b) * b)
let eq (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Prims.bool=
  a = b
let ne (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Prims.bool=
  a <> b
let gt (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Prims.bool=
  a > b
let gte (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Prims.bool=
  a >= b
let lt (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Prims.bool=
  a < b
let lte (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Prims.bool=
  a <= b
let to_uint (n : Prims.pos) (x : Obj.t int_t) : Obj.t FStar_UInt.uint_t=
  if Prims.int_zero <= x then x else x + (Prims.pow2 n)
let from_uint (n : Prims.pos) (x : Obj.t FStar_UInt.uint_t) : Obj.t int_t=
  if x <= (max_int n) then x else x - (Prims.pow2 n)
let to_int_t (m : Prims.pos) (a : Prims.int) : Obj.t int_t=
  op_At_Percent a (Prims.pow2 m)
let to_vec (n : Prims.pos) (num : Obj.t int_t) : Obj.t FStar_BitVector.bv_t=
  FStar_UInt.to_vec n (to_uint n num)
let from_vec (n : Prims.pos) (vec : Obj.t FStar_BitVector.bv_t) :
  Obj.t int_t=
  let x = FStar_UInt.from_vec n vec in
  if (max_int n) < x then x - (Prims.pow2 n) else x
let nth (n : Prims.pos) (a : Obj.t int_t) (i : Prims.nat) : Prims.bool=
  FStar_Seq_Base.index (to_vec n a) i
let logand (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Obj.t int_t=
  from_vec n (FStar_BitVector.logand_vec n (to_vec n a) (to_vec n b))
let logxor (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Obj.t int_t=
  from_vec n (FStar_BitVector.logxor_vec n (to_vec n a) (to_vec n b))
let logor (n : Prims.pos) (a : Obj.t int_t) (b : Obj.t int_t) : Obj.t int_t=
  from_vec n (FStar_BitVector.logor_vec n (to_vec n a) (to_vec n b))
let lognot (n : Prims.pos) (a : Obj.t int_t) : Obj.t int_t=
  from_vec n (FStar_BitVector.lognot_vec n (to_vec n a))
let minus (n : Prims.pos) (a : Obj.t int_t) : Obj.t int_t=
  add_mod n (lognot n a) Prims.int_one
let shift_left (n : Prims.pos) (a : Obj.t int_t) (s : Prims.nat) :
  Obj.t int_t= from_vec n (FStar_BitVector.shift_left_vec n (to_vec n a) s)
let shift_right (n : Prims.pos) (a : Obj.t int_t) (s : Prims.nat) :
  Obj.t int_t= from_vec n (FStar_BitVector.shift_right_vec n (to_vec n a) s)
let shift_arithmetic_right (n : Prims.pos) (a : Obj.t int_t) (s : Prims.nat)
  : Obj.t int_t=
  from_vec n (FStar_BitVector.shift_arithmetic_right_vec n (to_vec n a) s)
let rotate_left (n : Prims.pos) (a : Obj.t int_t) (s : Prims.nat) :
  Obj.t int_t= from_vec n (FStar_BitVector.rotate_left_vec n (to_vec n a) s)
let rotate_right (n : Prims.pos) (a : Obj.t int_t) (s : Prims.nat) :
  Obj.t int_t= from_vec n (FStar_BitVector.rotate_right_vec n (to_vec n a) s)
