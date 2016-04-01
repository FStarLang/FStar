type uint64 = Stdint.uint64
type native_int = uint64

let (zero:uint64) = Stdint.Uint64.zero
let (one:uint64) = Stdint.Uint64.one

let bits = 64

(* Standard operators *)
let add_mod a b = Stdint.Uint64.add a b
(* let add a b = a + b *)
let sub_mod a b = Stdint.Uint64.sub a b
(* let sub a b = a - b *)
let mul_mod a b = Stdint.Uint64.mul a b
(* let mul a b = a * b *)
let div a b = Stdint.Uint64.div a b
let rem a b = Stdint.Uint64.rem a b

let logand a b = Stdint.Uint64.logand a b
let logxor a b = Stdint.Uint64.logxor a b
let logor a b = Stdint.Uint64.logor a b
let lognot a = Stdint.Uint64.lognot a

let shift_left a s = Stdint.Uint64.shift_left a s
let shift_right a s = Stdint.Uint64.shift_right a s
let shift_right_logical a s = Stdint.Uint64.shift_right_logical a s

let rotate_left a s =
  logor (shift_left a s)
        (shift_right_logical a (64 - s))
let rotate_right a s =
  logor (shift_right_logical a s)
        (shift_left a (64 - s))
(*
val to_uint64: sint -> Tot uint64
let to_uint64 s = to_usint n s
 *)

let op_Hat_Plus = add
let op_Hat_Subtraction = sub
let op_Hat_Star = mul
let op_Hat_Slash = div
let op_Hat_Less_Less = shift_left
let op_Hat_Greater_Greater = shift_right
let op_Hat_Amp = logand
let op_Hat_Bar = logor
let op_Hat_Hat = logxor
let (ones:uint64) = lognot zero


let of_uint32 s = s

(* TODO *)
let eq x y = if x = y then -1 else 0
let gte x y = if x >= y then -1 else 0
