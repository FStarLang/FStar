module FStar.Int.Int16

open FStar.Int

let n = 16

abstract type int16 = | MkInt16: v:int_t n -> int16

let v (x:int16) : Tot (x':int{size x' n}) = x.v

val add: a:int16 -> b:int16{size (v a + v b) n} -> Tot int16
let add a b = MkInt16 (add (v a) (v b))
val add_underspec: a:int16 -> b:int16 -> Tot int16
let add_underspec a b = MkInt16 (add_underspec #n a.v b.v)
val add_mod: int16 -> int16 -> Tot int16
let add_mod a b = MkInt16 (add_mod #n (v a) (v b))
val sub: a:int16 -> b:int16{size (v a - v b) n} -> Tot int16
let sub a b = MkInt16 (sub (v a) (v b))
val sub_underspec: a:int16 -> b:int16 -> Tot int16
let sub_underspec a b = MkInt16 (sub_underspec (v a) (v b))
val sub_mod: a:int16 -> b:int16 -> Tot int16
let sub_mod a b = MkInt16 (sub_mod (v a) (v b))
val mul: a:int16 -> b:int16{size (v a * v b) n} -> Tot int16
let mul a b = MkInt16(mul (v a) (v b))
val mul_underspec: a:int16 -> b:int16 -> Tot int16
let mul_underspec a b = MkInt16(mul_underspec (v a) (v b))
val mul_mod: a:int16 -> b:int16 -> Tot int16
let mul_mod a b = MkInt16 (mul_mod (v a) (v b))

(* Division primitives *)
val div: a:int16 -> b:int16{v b <> 0} -> Tot int16
let div a b = MkInt16(div (v a) (v b))

(* Modulo primitives *)
val mod: a:int16 -> b:int16{v b <> 0} -> Tot int16
let mod a b = MkInt16 (mod (v a) (v b))

(* Bitwise operators *)
val logand: int16 -> int16 -> Tot int16
let logand a b = MkInt16 (logand (v a) (v b))
val logxor: int16 -> int16 -> Tot int16
let logxor a b = MkInt16 (logxor (v a) (v b))
val logor: int16 -> int16 -> Tot int16
let logor a b = MkInt16 (logor (v a) (v b))
val lognot: int16 -> Tot int16
let lognot a = MkInt16 (lognot (v a))

val int_to_int16: x:int -> Tot int16
let int_to_int16 x = MkInt16 (to_int_t 16 x)

(* Shift operators *)
val shift_right: a:int16 -> s:nat -> Tot int16
let shift_right a s = MkInt16 (shift_right (v a) s)

val shift_left: a:int16 -> s:nat -> Tot int16
let shift_left a s = MkInt16 (shift_left (v a) s)

(* Comparison operators *)
let eq (a:int16) (b:int16) : Tot bool = (eq #n (v a) (v b))
let gt (a:int16) (b:int16) : Tot bool = (gt #n (v a) (v b))
let gte (a:int16) (b:int16) : Tot bool = (gte #n (v a) (v b))
let lt (a:int16) (b:int16) : Tot bool = (lt #n (v a) (v b))
let lte (a:int16) (b:int16) : Tot bool = (lte #n (v a) (v b))

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
