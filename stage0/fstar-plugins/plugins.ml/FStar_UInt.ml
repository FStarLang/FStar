open Fstarcompiler
open Prims
let max_int (n : Prims.nat) : Prims.int= (Prims.pow2 n) - Prims.int_one
let min_int (n : Prims.nat) : Prims.int= Prims.int_zero
let fits (x : Prims.int) (n : Prims.nat) : Prims.bool=
  ((min_int n) <= x) && (x <= (max_int n))
type ('x, 'n) size = unit
type 'n uint_t = Prims.int
let zero (n : Prims.nat) : Obj.t uint_t= Prims.int_zero
let pow2_n (n : Prims.pos) (p : Prims.nat) : Obj.t uint_t= Prims.pow2 p
let one (n : Prims.pos) : Obj.t uint_t= Prims.int_one
let ones (n : Prims.nat) : Obj.t uint_t= max_int n
let incr (n : Prims.nat) (a : Obj.t uint_t) : Obj.t uint_t= a + Prims.int_one
let decr (n : Prims.nat) (a : Obj.t uint_t) : Obj.t uint_t= a - Prims.int_one
let incr_underspec (n : Prims.nat) (a : Obj.t uint_t) : Obj.t uint_t=
  if a < (max_int n) then a + Prims.int_one else Prims.int_zero
let decr_underspec (n : Prims.nat) (a : Obj.t uint_t) : Obj.t uint_t=
  if a > (min_int n) then a - Prims.int_one else Prims.int_zero
let incr_mod (n : Prims.nat) (a : Obj.t uint_t) : Obj.t uint_t=
  (mod) (a + Prims.int_one) (Prims.pow2 n)
let decr_mod (n : Prims.nat) (a : Obj.t uint_t) : Obj.t uint_t=
  (mod) (a - Prims.int_one) (Prims.pow2 n)
let add (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) : Obj.t uint_t=
  a + b
let add_underspec (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t= if fits (a + b) n then a + b else Prims.int_zero
let add_mod (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t= (mod) (a + b) (Prims.pow2 n)
let sub (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) : Obj.t uint_t=
  a - b
let sub_underspec (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t= if fits (a - b) n then a - b else Prims.int_zero
let sub_mod (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t= (mod) (a - b) (Prims.pow2 n)
let mul (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) : Obj.t uint_t=
  a * b
let mul_underspec (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t= if fits (a * b) n then a * b else Prims.int_zero
let mul_mod (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t= (mod) (a * b) (Prims.pow2 n)
let mul_div (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t= (a * b) / (Prims.pow2 n)
let div (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) : Obj.t uint_t=
  a / b
let div_underspec (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t= if fits (a / b) n then a / b else Prims.int_zero
let udiv (n : Prims.pos) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t= a / b
let mod1 (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t= a - ((a / b) * b)
let eq (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) : Prims.bool=
  a = b
let ne (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) : Prims.bool=
  a <> b
let gt (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) : Prims.bool=
  a > b
let gte (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) : Prims.bool=
  a >= b
let lt (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) : Prims.bool=
  a < b
let lte (n : Prims.nat) (a : Obj.t uint_t) (b : Obj.t uint_t) : Prims.bool=
  a <= b
let to_uint_t (m : Prims.nat) (a : Prims.int) : Obj.t uint_t=
  (mod) a (Prims.pow2 m)
let rec to_vec (n : Prims.nat) (num : Obj.t uint_t) :
  Obj.t FStar_BitVector.bv_t=
  if n = Prims.int_zero
  then FStar_Seq_Base.empty ()
  else
    FStar_Seq_Base.append
      (to_vec (n - Prims.int_one) (num / (Prims.of_int (2))))
      (FStar_Seq_Base.create Prims.int_one
         (((mod) num (Prims.of_int (2))) = Prims.int_one))
let rec from_vec (n : Prims.nat) (vec : Obj.t FStar_BitVector.bv_t) :
  Obj.t uint_t=
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
let nth (n : Prims.pos) (a : Obj.t uint_t) (i : Prims.nat) : Prims.bool=
  FStar_Seq_Base.index (to_vec n a) i
let logand (n : Prims.pos) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t=
  from_vec n (FStar_BitVector.logand_vec n (to_vec n a) (to_vec n b))
let logxor (n : Prims.pos) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t=
  from_vec n (FStar_BitVector.logxor_vec n (to_vec n a) (to_vec n b))
let logor (n : Prims.pos) (a : Obj.t uint_t) (b : Obj.t uint_t) :
  Obj.t uint_t=
  from_vec n (FStar_BitVector.logor_vec n (to_vec n a) (to_vec n b))
let lognot (n : Prims.pos) (a : Obj.t uint_t) : Obj.t uint_t=
  from_vec n (FStar_BitVector.lognot_vec n (to_vec n a))
let minus (n : Prims.pos) (a : Obj.t uint_t) : Obj.t uint_t=
  add_mod n (lognot n a) Prims.int_one
let xor (b : Prims.bool) (b' : Prims.bool) : Prims.bool= b <> b'
let shift_left (n : Prims.pos) (a : Obj.t uint_t) (s : Prims.nat) :
  Obj.t uint_t= from_vec n (FStar_BitVector.shift_left_vec n (to_vec n a) s)
let shift_right (n : Prims.pos) (a : Obj.t uint_t) (s : Prims.nat) :
  Obj.t uint_t= from_vec n (FStar_BitVector.shift_right_vec n (to_vec n a) s)
let msb (n : Prims.pos) (a : Obj.t uint_t) : Prims.bool=
  nth n a Prims.int_zero
let zero_extend_vec (n : Prims.pos) (a : Obj.t FStar_BitVector.bv_t) :
  Obj.t FStar_BitVector.bv_t=
  FStar_Seq_Base.append (FStar_Seq_Base.create Prims.int_one false) a
let zero_extends_vec (n : Prims.pos) (m : Prims.pos)
  (a : Obj.t FStar_BitVector.bv_t) : Obj.t FStar_BitVector.bv_t=
  FStar_Seq_Base.append (FStar_BitVector.zero_vec m) a
let one_extend_vec (n : Prims.pos) (a : Obj.t FStar_BitVector.bv_t) :
  Obj.t FStar_BitVector.bv_t=
  FStar_Seq_Base.append (FStar_Seq_Base.create Prims.int_one true) a
let zero_extend (n : Prims.pos) (a : Obj.t uint_t) : Obj.t uint_t=
  from_vec (n + Prims.int_one) (zero_extend_vec n (to_vec n a))
let zero_extends (n : Prims.pos) (m : Prims.pos) (a : Obj.t uint_t) :
  Obj.t uint_t= from_vec (n + m) (zero_extends_vec n m (to_vec n a))
let one_extend (n : Prims.pos) (a : Obj.t uint_t) : Obj.t uint_t=
  from_vec (n + Prims.int_one) (one_extend_vec n (to_vec n a))
