open Char

type uint8 = char
type native_int = uint8

let (zero:uint8) = chr 0
let (one:uint8) = chr 1
let (ones:uint8) = chr 255

let bits = 8

(* Standard operators *)
let add a b = chr ((code a + code b) land 255)
let add_mod a b = chr ((code a + code b) land 255)
let sub a b = chr ((code a - code b) land 255)
let sub_mod a b = chr ((code a - code b) land 255)
let mul a b = chr ((code a * code b) land 255)
let mul_mod a b = chr ((code a * code b) land 255)
let div a b = chr ((code a / code b) land 255)
let rem a b = chr (code a mod code b)

let logand a b = chr (code a land code b)
let logxor a b = chr (code a lxor code b)
let logor a b = chr (code a lor code b)
let lognot a = chr (lnot (code a land 255))

let shift_left a s = a lsl s
let shift_right a s = a lsr s

let rotate_left a s = chr (((code a lsl s) + (code a lsr (8-s))) land 255)
let rotate_right a s = chr (((code a lsl (8-s)) + (code a lsr s)) land 255)
                                          
let of_uint32 s = chr (s land 255)
let of_int s = chr (s land 255)
let of_native_int s = chr (s land 255)                 
                    
(* TODO *)
let eq x y = if x = y then -1 else 0
let gte x y = if x >= y then -1 else 0
