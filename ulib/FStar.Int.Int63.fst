module FStar.Int.Int63

open FStar.Int

let n = 63

abstract type int63 = | MkInt63: v:int_t 63 -> int63

let v (x:int63) : Tot (x':int{size x' n}) = x.v

val add: a:int63 -> b:int63{size (v a + v b) n} -> Tot int63
let add a b = MkInt63 (add (v a) (v b))
val add_underspec: a:int63 -> b:int63 -> Tot int63
let add_underspec a b = MkInt63 (add_underspec #n a.v b.v)
val add_mod: int63 -> int63 -> Tot int63
let add_mod a b = MkInt63 (add_mod #n (v a) (v b))
val sub: a:int63 -> b:int63{size (v a - v b) n} -> Tot int63
let sub a b = MkInt63 (sub (v a) (v b))
val sub_underspec: a:int63 -> b:int63 -> Tot int63
let sub_underspec a b = MkInt63 (sub_underspec (v a) (v b))
val sub_mod: a:int63 -> b:int63 -> Tot int63
let sub_mod a b = MkInt63 (sub_mod (v a) (v b))
val mul: a:int63 -> b:int63{size (v a * v b) n} -> Tot int63
let mul a b = MkInt63(mul (v a) (v b))
val mul_underspec: a:int63 -> b:int63 -> Tot int63
let mul_underspec a b = MkInt63(mul_underspec (v a) (v b))
val mul_mod: a:int63 -> b:int63 -> Tot int63
let mul_mod a b = MkInt63 (mul_mod (v a) (v b))

(* Division primitives *)
val div: a:int63 -> b:int63{v b <> 0} -> Tot int63
let div a b = MkInt63(div (v a) (v b))

(* Modulo primitives *)
val mod: a:int63 -> b:int63{v b <> 0} -> Tot int63
let mod a b = MkInt63 (mod (v a) (v b))

(* Bitwise operators *)
val logand: int63 -> int63 -> Tot int63
let logand a b = MkInt63 (logand (v a) (v b))
val logxor: int63 -> int63 -> Tot int63
let logxor a b = MkInt63 (logxor (v a) (v b))
val logor: int63 -> int63 -> Tot int63
let logor a b = MkInt63 (logor (v a) (v b))
val lognot: int63 -> Tot int63
let lognot a = MkInt63 (lognot (v a))

val int_to_int63: x:int -> Tot int63
let int_to_int63 x = MkInt63 (to_int_t 63 x)

(* Shift operators *)
val shift_right: a:int63 -> s:nat -> Tot int63
let shift_right a s = MkInt63 (shift_right (v a) s)

val shift_left: a:int63 -> s:nat -> Tot int63
let shift_left a s = MkInt63 (shift_left (v a) s)

(* Comparison operators *)
let eq (a:int63) (b:int63) : Tot bool = (eq #n (v a) (v b))
let gt (a:int63) (b:int63) : Tot bool = (gt #n (v a) (v b))
let gte (a:int63) (b:int63) : Tot bool = (gte #n (v a) (v b))
let lt (a:int63) (b:int63) : Tot bool = (lt #n (v a) (v b))
let lte (a:int63) (b:int63) : Tot bool = (lte #n (v a) (v b))

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
