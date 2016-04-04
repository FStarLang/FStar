module FStar.UInt.UInt64

open FStar.Ghost
open FStar.UInt

let n = 64

type uint64 = uint n

let zero = zero n
let one = one n
let ones = ones n

let max_int = max_int n
let min_int = min_int n

(* Standard operators *)
let add = add #n
let add_mod = add_mod #n 
let sub = sub #n 
let sub_mod = sub_mod #n
let mul = mul #n
let mul_mod = mul_mod #n
let div = div #n
let rem = mod #n

let logand = logand #n
let logxor = logxor #n
let logor = logor #n
let lognot = lognot #n

let shift_left a s = shift_left #n a s
let shift_right a s = shift_right #n a s

let rotate_left = rotate_left #n
let rotate_right = rotate_right #n

let to_uint64 = to_uint n

(* Infix operators *)
let op_Hat_Less_Less = shift_left
let op_Hat_Greater_Greater = shift_right
let op_Hat_Plus = add
let op_Hat_Plus_Percent = add_mod
let op_Hat_Subtraction = sub
let op_Hat_Subtraction_Percent = sub_mod
let op_Hat_Star = mul
let op_Hat_Star_Percent = mul_mod
let op_Hat_Hat = logxor  
let op_Hat_Amp = logand
let op_Hat_Bar = logor
let op_Less_Less_Less = rotate_left 
let op_Greater_Greater_Greater = rotate_right

assume val of_string: string -> Tot (option uint64)
