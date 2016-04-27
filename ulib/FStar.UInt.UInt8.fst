module FStar.UInt.UInt8

open FStar.UInt

let n = 8

abstract type uint8 = | MkUInt8: v:uint 8 -> uint8

let v (x:uint8) : Tot (x':int{uSize x' n}) = x.v

let zero: z:uint8{v z = 0} = MkUInt8 (zero n)
let one: z:uint8{v z = 1} = MkUInt8 (one n)
let ones: z:uint8{v z = pow2 n - 1} = MkUInt8 (ones n)

val add: a:uint8 -> b:uint8{v a + v b <= max_int n} -> Tot (c:uint8{v c = v a + v b})
let add a b = MkUInt8 (add (v a) (v b))
val add_underspec: a:uint8 -> b:uint8 -> Tot (c:uint8{v a + v b <= max_int n ==> v c = v a + v b})
let add_underspec a b = MkUInt8 (add_underspec #n a.v b.v)
val add_mod: a:uint8 -> b:uint8 -> Tot (c:uint8{v c = (v a + v b) % pow2 n})
let add_mod a b = MkUInt8 (add_mod #n (v a) (v b))
val sub: a:uint8 -> b:uint8{v a - v b >= min_int n} -> Tot (c:uint8{v c = v a - v b})
let sub a b = MkUInt8 (sub (v a) (v b))
val sub_underspec: a:uint8 -> b:uint8 -> Tot (c:uint8{v a - v b >= min_int n ==> v c = v a - v b})
let sub_underspec a b = MkUInt8 (sub_underspec (v a) (v b))
val sub_mod: a:uint8 -> b:uint8 -> Tot (c:uint8{v c = (v a - v b) % pow2 n})
let sub_mod a b = MkUInt8 (sub_mod (v a) (v b))
val mul: a:uint8 -> b:uint8{v a * v b <= max_int n} -> Tot (c:uint8{v c = v a * v b})
let mul a b = MkUInt8(mul (v a) (v b))
val mul_underspec: a:uint8 -> b:uint8 -> Tot (c:uint8{v a * v b <= max_int n ==> v c = v a * v b})
let mul_underspec a b = MkUInt8(mul_underspec (v a) (v b))
val mul_mod: a:uint8 -> b:uint8 -> Tot (c:uint8{v c = (v a * v b) % pow2 n})
let mul_mod a b = MkUInt8 (mul_mod (v a) (v b))

(* Division primitives *)
val div: a:uint8 -> b:uint8{v b <> 0} -> Tot (c:uint8{v c = v a / v b})
let div a b = MkUInt8(div (v a) (v b))

(* Modulo primitives *)
val mod: a:uint8 -> b:uint8{v b <> 0} -> Tot (c:uint8{v c = v a % v b})
let mod a b = MkUInt8 (mod (v a) (v b))

(* Bitwise operators *)
val logand: uint8 -> uint8 -> Tot uint8
let logand a b = MkUInt8 (logand (v a) (v b))
val logxor: uint8 -> uint8 -> Tot uint8
let logxor a b = MkUInt8 (logxor (v a) (v b))
val logor: uint8 -> uint8 -> Tot uint8
let logor a b = MkUInt8 (logor (v a) (v b))
val lognot: uint8 -> Tot uint8
let lognot a = MkUInt8 (lognot (v a))

val int_to_uint8: x:int{x >= min_int n /\ x <= max_int n} -> Tot (y:uint8{v y = x})
let int_to_uint8 x = MkUInt8 (to_uint 8 x)

(* Shift operators *)
val shift_right: a:uint8 -> s:nat -> Tot (b:uint8{v b = v a / pow2 s})
let shift_right a s = MkUInt8 (shift_right (v a) s)

val shift_left: a:uint8 -> s:nat -> Tot (b:uint8{v b = (v a * pow2 s) % pow2 n})
let shift_left a s = MkUInt8 (shift_left (v a) s)

(* Comparison operators *)
let eq (a:uint8) (b:uint8) : Tot bool = (eq #n (v a) (v b))
let gt (a:uint8) (b:uint8) : Tot bool = (gt #n (v a) (v b))
let gte (a:uint8) (b:uint8) : Tot bool = (gte #n (v a) (v b))
let lt (a:uint8) (b:uint8) : Tot bool = (lt #n (v a) (v b))
let lte (a:uint8) (b:uint8) : Tot bool = (lte #n (v a) (v b))

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
let op_Hat_Equals = eq
let op_Hat_Greater = gt
let op_Hat_Greater_Equals = gte
let op_Hat_Less = gt
let op_Hat_Less_Equals = gte
