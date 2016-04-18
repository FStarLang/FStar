module FStar.UInt.UInt63

open FStar.UInt

let n = 63

abstract type uint63 = | MkUInt63: v:uint 63 -> uint63

let v (x:uint63) : Tot (x':int{uSize x' n}) = x.v

val add: a:uint63 -> b:uint63{v a + v b < max_int n} -> Tot uint63
let add a b = MkUInt63 (add (v a) (v b))
val add_underspec: a:uint63 -> b:uint63 -> Tot uint63
let add_underspec a b = MkUInt63 (add_underspec #n a.v b.v)
val add_mod: uint63 -> uint63 -> Tot uint63
let add_mod a b = MkUInt63 (add_mod #n (v a) (v b))
val sub: a:uint63 -> b:uint63{v a - v b >= 0} -> Tot uint63
let sub a b = MkUInt63 (sub (v a) (v b))
val sub_underspec: a:uint63 -> b:uint63 -> Tot uint63
let sub_underspec a b = MkUInt63 (sub_underspec (v a) (v b))
val sub_mod: a:uint63 -> b:uint63 -> Tot uint63
let sub_mod a b = MkUInt63 (sub_mod (v a) (v b))
val mul: a:uint63 -> b:uint63{v a * v b < pow2 n} -> Tot uint63
let mul a b = MkUInt63(mul (v a) (v b))
val mul_underspec: a:uint63 -> b:uint63 -> Tot uint63
let mul_underspec a b = MkUInt63(mul_underspec (v a) (v b))
val mul_mod: a:uint63 -> b:uint63 -> Tot uint63
let mul_mod a b = MkUInt63 (mul_mod (v a) (v b))

(* Division primitives *)
val div: a:uint63 -> b:uint63{v b <> 0} -> Tot uint63
let div a b = MkUInt63(div (v a) (v b))

(* Modulo primitives *)
val mod: a:uint63 -> b:uint63{v b <> 0} -> Tot uint63
let mod a b = MkUInt63 (mod (v a) (v b))

(* Bitwise operators *)
val logand: uint63 -> uint63 -> Tot uint63
let logand a b = MkUInt63 (logand (v a) (v b))
val logxor: uint63 -> uint63 -> Tot uint63
let logxor a b = MkUInt63 (logxor (v a) (v b))
val logor: uint63 -> uint63 -> Tot uint63
let logor a b = MkUInt63 (logor (v a) (v b))
val lognot: uint63 -> Tot uint63
let lognot a = MkUInt63 (lognot (v a))

val int_to_uint63: x:int -> Tot uint63
let int_to_uint63 x = MkUInt63 (to_uint 63 x)

(* Shift operators *)
val shift_right: a:uint63 -> s:nat -> Tot uint63
let shift_right a s = MkUInt63 (shift_right (v a) s)

val shift_left: a:uint63 -> s:nat -> Tot uint63
let shift_left a s = MkUInt63 (shift_left (v a) s)

(* Comparison operators *)
let eq (a:uint63) (b:uint63) : Tot bool = (eq #n (v a) (v b))
let gt (a:uint63) (b:uint63) : Tot bool = (gt #n (v a) (v b))
let gte (a:uint63) (b:uint63) : Tot bool = (gte #n (v a) (v b))
let lt (a:uint63) (b:uint63) : Tot bool = (lt #n (v a) (v b))
let lte (a:uint63) (b:uint63) : Tot bool = (lte #n (v a) (v b))

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
