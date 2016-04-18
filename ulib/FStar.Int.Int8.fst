module FStar.Int.Int8

open FStar.Int

let n = 8

abstract type int8 = | MkInt8: v:int_t n -> int8

let v (x:int8) : Tot (x':int{size x' n}) = x.v

val add: a:int8 -> b:int8{size (v a + v b) n} -> Tot int8
let add a b = MkInt8 (add (v a) (v b))
val add_underspec: a:int8 -> b:int8 -> Tot int8
let add_underspec a b = MkInt8 (add_underspec #n a.v b.v)
val add_mod: int8 -> int8 -> Tot int8
let add_mod a b = MkInt8 (add_mod #n (v a) (v b))
val sub: a:int8 -> b:int8{size (v a - v b) n} -> Tot int8
let sub a b = MkInt8 (sub (v a) (v b))
val sub_underspec: a:int8 -> b:int8 -> Tot int8
let sub_underspec a b = MkInt8 (sub_underspec (v a) (v b))
val sub_mod: a:int8 -> b:int8 -> Tot int8
let sub_mod a b = MkInt8 (sub_mod (v a) (v b))
val mul: a:int8 -> b:int8{size (v a * v b) n} -> Tot int8
let mul a b = MkInt8(mul (v a) (v b))
val mul_underspec: a:int8 -> b:int8 -> Tot int8
let mul_underspec a b = MkInt8(mul_underspec (v a) (v b))
val mul_mod: a:int8 -> b:int8 -> Tot int8
let mul_mod a b = MkInt8 (mul_mod (v a) (v b))

(* Division primitives *)
val div: a:int8 -> b:int8{v b <> 0} -> Tot int8
let div a b = MkInt8(div (v a) (v b))

(* Modulo primitives *)
val mod: a:int8 -> b:int8{v b <> 0} -> Tot int8
let mod a b = MkInt8 (mod (v a) (v b))

(* Bitwise operators *)
val logand: int8 -> int8 -> Tot int8
let logand a b = MkInt8 (logand (v a) (v b))
val logxor: int8 -> int8 -> Tot int8
let logxor a b = MkInt8 (logxor (v a) (v b))
val logor: int8 -> int8 -> Tot int8
let logor a b = MkInt8 (logor (v a) (v b))
val lognot: int8 -> Tot int8
let lognot a = MkInt8 (lognot (v a))

val int_to_int8: x:int -> Tot int8
let int_to_int8 x = MkInt8 (to_int_t 8 x)

(* Shift operators *)
val shift_right: a:int8 -> s:nat -> Tot int8
let shift_right a s = MkInt8 (shift_right (v a) s)

val shift_left: a:int8 -> s:nat -> Tot int8
let shift_left a s = MkInt8 (shift_left (v a) s)

(* Comparison operators *)
let eq (a:int8) (b:int8) : Tot bool = (eq #n (v a) (v b))
let gt (a:int8) (b:int8) : Tot bool = (gt #n (v a) (v b))
let gte (a:int8) (b:int8) : Tot bool = (gte #n (v a) (v b))
let lt (a:int8) (b:int8) : Tot bool = (lt #n (v a) (v b))
let lte (a:int8) (b:int8) : Tot bool = (lte #n (v a) (v b))

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
