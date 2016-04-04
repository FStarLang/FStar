module FStar.UInt.UInt64

open FStar.Ghost
open FStar.UInt

let n = 64

type uint64 = uint n

val zero: uint64
let zero = zero n
val one: uint64
let one = one n
val ones: uint64
let ones = ones n

val max_int: uint64
let max_int = max_int n
val min_int: uint64
let min_int = min_int n

(* Standard operators *)
val add: a:uint64 -> b:uint64{a + b < max_int} -> Tot uint64
let add a b = add #n a b
val add_mod: uint64 -> uint64 -> Tot uint64
let add_mod a b = add_mod #n a b
val sub: a:uint64 -> b:uint64{a - b >= min_int} -> Tot uint64
let sub a b = sub #n a b
val sub_mod: uint64 -> uint64 -> Tot uint64
let sub_mod a b = sub_mod #n a b
val mul: a:uint64 -> b:uint64{op_Multiply a b < max_int} -> Tot uint64
let mul a b = mul #n a b
val mul_mod: a:uint64 -> b:uint64 -> Tot uint64
let mul_mod a b = mul_mod #n a b
val div: uint64 -> b:uint64{b <> 0} -> Tot uint64
let div a b = div #n a b
val rem: uint64 -> b:uint64{b <> 0} -> Tot uint64
let rem a b = mod #n a b

val logand: uint64 -> uint64 -> Tot uint64
let logand a b = logand #n a b
val logxor: uint64 -> uint64 -> Tot uint64
let logxor a b = logxor #n a b
val logor: uint64 -> uint64 -> Tot uint64
let logor a b = logor #n a b
val lognot: uint64 -> Tot uint64
let lognot a = lognot #n a

val shift_left: uint64 -> nat -> Tot uint64
let shift_left a s = shift_left #n a s
val shift_right: uint64 -> nat -> Tot uint64
let shift_right a s = shift_right #n a s

let rotate_left a s = rotate_left #n a s
let rotate_right a s = rotate_right #n a s

let to_uint64 s = to_uint n s

(*
(* Infix operators *)
let op_Hat_Less_Less = shift_left
let op_Hat_Greater_Greater = shift_right
let op_Hat_Plus = add
let op_Hat_Plus_Percent = add_mod
let op_Hat_Subtraction = sub
let op_Hat_Subtraction_Percent = sub_mod
let op_Hat_Star = mul
let op_Hat_Star_Percent = mul_mod
let op_Hat_Star_Hat = mul_wide
let op_Hat_Hat = logxor  
let op_Hat_Amp = logand
let op_Hat_Bar = logor
let op_Less_Less_Less = rotate_left 
let op_Greater_Greater_Greater = rotate_right

assume val of_string: string -> Tot uint64
*)
