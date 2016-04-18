module FStar.Int.Int64

open FStar.Int

let n = 64

abstract type int64 = | MkInt64: v:int_t 64 -> int64

let v (x:int64) : Tot (x':int{size x' n}) = x.v

val add: a:int64 -> b:int64{size (v a + v b) n} -> Tot int64
let add a b = MkInt64 (add (v a) (v b))
val add_underspec: a:int64 -> b:int64 -> Tot int64
let add_underspec a b = MkInt64 (add_underspec #n a.v b.v)
val add_mod: int64 -> int64 -> Tot int64
let add_mod a b = MkInt64 (add_mod #n (v a) (v b))
val sub: a:int64 -> b:int64{size (v a - v b) n} -> Tot int64
let sub a b = MkInt64 (sub (v a) (v b))
val sub_underspec: a:int64 -> b:int64 -> Tot int64
let sub_underspec a b = MkInt64 (sub_underspec (v a) (v b))
val sub_mod: a:int64 -> b:int64 -> Tot int64
let sub_mod a b = MkInt64 (sub_mod (v a) (v b))
val mul: a:int64 -> b:int64{size (v a * v b) n} -> Tot int64
let mul a b = MkInt64(mul (v a) (v b))
val mul_underspec: a:int64 -> b:int64 -> Tot int64
let mul_underspec a b = MkInt64(mul_underspec (v a) (v b))
val mul_mod: a:int64 -> b:int64 -> Tot int64
let mul_mod a b = MkInt64 (mul_mod (v a) (v b))

(* Division primitives *)
val div: a:int64 -> b:int64{v b <> 0} -> Tot int64
let div a b = MkInt64(div (v a) (v b))

(* Modulo primitives *)
val mod: a:int64 -> b:int64{v b <> 0} -> Tot int64
let mod a b = MkInt64 (mod (v a) (v b))

(* Bitwise operators *)
val logand: int64 -> int64 -> Tot int64
let logand a b = MkInt64 (logand (v a) (v b))
val logxor: int64 -> int64 -> Tot int64
let logxor a b = MkInt64 (logxor (v a) (v b))
val logor: int64 -> int64 -> Tot int64
let logor a b = MkInt64 (logor (v a) (v b))
val lognot: int64 -> Tot int64
let lognot a = MkInt64 (lognot (v a))

val int_to_int64: x:int -> Tot int64
let int_to_int64 x = MkInt64 (to_int_t 64 x)

(* Shift operators *)
val shift_right: a:int64 -> s:nat -> Tot int64
let shift_right a s = MkInt64 (shift_right (v a) s)

val shift_left: a:int64 -> s:nat -> Tot int64
let shift_left a s = MkInt64 (shift_left (v a) s)

(* Comparison operators *)
let eq (a:int64) (b:int64) : Tot bool = (eq #n (v a) (v b))
let gt (a:int64) (b:int64) : Tot bool = (gt #n (v a) (v b))
let gte (a:int64) (b:int64) : Tot bool = (gte #n (v a) (v b))
let lt (a:int64) (b:int64) : Tot bool = (lt #n (v a) (v b))
let lte (a:int64) (b:int64) : Tot bool = (lte #n (v a) (v b))

(* Infix notations *)
let op_Hat_Plus = add
let op_Hat_Plus_Question = add_underspec
let op_Hat_Plus_Percent = add_mod
let op_Hat_Subtraction = sub
let op_Hat_Subtraction_Question = sub_underspec
let op_Hat_Subtraction_Percent = sub_mod
let op_Hat_Star = mul
let op_Hat_Star_Question = mul_underspec
let op_Hat_Star_Percent = mul_mod
let op_Hat_Slash = div
let op_Hat_Percent = mod
let op_Hat_Hat = logxor  
let op_Hat_Amp = logand
let op_Hat_Bar = logor
let op_Hat_Less_Less = shift_left
let op_Hat_Greater_Greater = shift_right
let op_Hat_Equal = eq
let op_Hat_Greater = gt
let op_Hat_Greater_Equal = gte
let op_Hat_Less = gt
let op_Hat_Less_Equal = gte
