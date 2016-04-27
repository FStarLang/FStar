module FStar.Int.Int32

open FStar.Int

let n = 32

abstract type int32 = | MkInt32: v:int_t n -> int32

let v (x:int32) : Tot (x':int{size x' n}) = x.v

val add: a:int32 -> b:int32{size (v a + v b) n} -> Tot (c:int32{v c = v a + v b})
let add a b = MkInt32 (add (v a) (v b))
val add_underspec: a:int32 -> b:int32 -> Tot (c:int32{size (v a + v b) n ==> v c = v a + v b})
let add_underspec a b = MkInt32 (add_underspec #n a.v b.v)
val add_mod: a:int32 -> b:int32 -> Tot (c:int32{v c = ((v a + v b) @% pow2 n)})
let add_mod a b = MkInt32 (add_mod #n (v a) (v b))
val sub: a:int32 -> b:int32{size (v a - v b) n} -> Tot (c:int32{v c = v a - v b})
let sub a b = MkInt32 (sub (v a) (v b))
val sub_underspec: a:int32 -> b:int32 -> Tot (c:int32{size (v a - v b) n ==> v c = v a - v b})
let sub_underspec a b = MkInt32 (sub_underspec (v a) (v b))
val sub_mod: a:int32 -> b:int32 -> Tot (c:int32{v c = ((v a - v b) @% pow2 n)})
let sub_mod a b = MkInt32 (sub_mod (v a) (v b))
val mul: a:int32 -> b:int32{size (v a * v b) n} -> Tot (c:int32{v c = v a * v b})
let mul a b = MkInt32(mul (v a) (v b))
val mul_underspec: a:int32 -> b:int32 -> Tot (c:int32{size (v a * v b) n ==> v c = v a * v b})
let mul_underspec a b = MkInt32(mul_underspec (v a) (v b))
val mul_mod: a:int32 -> b:int32 -> Tot (c:int32{v c = ((v a * v b) @% pow2 n)})
let mul_mod a b = MkInt32 (mul_mod (v a) (v b))

(* Division primitives *)
val div: a:int32 -> b:int32{v b <> 0} -> Tot (c:int32{v c = v a / v b})
let div a b = MkInt32(div (v a) (v b))

(* Modulo primitives *)
val mod: a:int32 -> b:int32{v b <> 0} -> Tot (c:int32{v c = v a - ((v a / v b) * v b)})
let mod a b = MkInt32 (mod (v a) (v b))

(* Bitwise operators *)
val logand: int32 -> int32 -> Tot int32
let logand a b = MkInt32 (logand (v a) (v b))
val logxor: int32 -> int32 -> Tot int32
let logxor a b = MkInt32 (logxor (v a) (v b))
val logor: int32 -> int32 -> Tot int32
let logor a b = MkInt32 (logor (v a) (v b))
val lognot: int32 -> Tot int32
let lognot a = MkInt32 (lognot (v a))

val int_to_int32: x:int -> Tot int32
let int_to_int32 x = MkInt32 (to_int_t 32 x)

(* Shift operators *)
val shift_right: a:int32 -> s:nat -> Tot (c:int32{v c = (v a /% (pow2 s))})
let shift_right a s = MkInt32 (shift_right (v a) s)

val shift_left: a:int32 -> s:nat -> Tot (c:int32{v c = ((v a * pow2 s) @% pow2 n)})
let shift_left a s = MkInt32 (shift_left (v a) s)

(* Comparison operators *)
let eq (a:int32) (b:int32) : Tot bool = (eq #n (v a) (v b))
let gt (a:int32) (b:int32) : Tot bool = (gt #n (v a) (v b))
let gte (a:int32) (b:int32) : Tot bool = (gte #n (v a) (v b))
let lt (a:int32) (b:int32) : Tot bool = (lt #n (v a) (v b))
let lte (a:int32) (b:int32) : Tot bool = (lte #n (v a) (v b))

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
