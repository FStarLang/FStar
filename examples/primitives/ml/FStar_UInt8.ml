open Char

type uint8 = int
type native_int = uint8

let (zero:uint8) = 0
let (one:uint8) = 1
let (ones:uint8) = 255

let bits = 8

(* Standard operators *)
let add a b = ((a + b) land 255)
let add_mod a b =  (( a +  b) land 255)
let sub a b = (( a -  b) land 255)
let sub_mod a b =  (( a -  b) land 255)
let mul a b =  (( a *  b) land 255)
let mul_mod a b =  (( a *  b) land 255)
let div a b =  (( a /  b) land 255)
let rem a b =  ( a mod  b)

let logand a b =  ( a land  b)
let logxor a b =  ( a lxor  b)
let logor a b =  ( a lor  b)
let lognot a =  (lnot ( a land 255))

let shift_left a s = a lsl s
let shift_right a s = a lsr s

let rotate_left a s =  ((( a lsl s) + ( a lsr (8-s))) land 255)
let rotate_right a s =  ((( a lsl (8-s)) + ( a lsr s)) land 255)
                                          
let of_uint32 s =  (s land 255)
let of_int s =  (s land 255)
let of_native_int s =  (s land 255)                 
                    
(* TODO *)
let eq x y = if x = y then -1 else 0
let gte x y = if x >= y then -1 else 0

let op_Hat_Plus = add
let op_Hat_Star = mul
let op_Hat_Slash = div
let op_Hat_Subtraction = sub 
let op_Hat_Less_Less  = shift_left 
let op_Hat_Greater_Greater  = shift_right 
let op_Hat_Amp = logand
let op_Hat_Hat = logxor
let op_Hat_Bar = logor
