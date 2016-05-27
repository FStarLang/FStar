let n = 32
type uint32 = int
type native_int = uint32

let (zero:uint32) = 0
let (one:uint32) = 1
let (ones:uint32) = -1

let bits = 32
let mask = (1 lsl 32) - 1
             
(* Standard operators *)
let add a b = (a + b) land mask  
let add_mod a b = (a + b) land mask
let sub a b = a - b
let sub_mod a b = a - b
let mul a b = a * b
let mul_mod a b = a * b
let div a b = a / b
let rem a b = a mod b

let logand a b = a land b 
let logxor a b = a lxor b
let logor a b = a lor b
let lognot a = lnot a

let shift_left a s = a lsl s
let shift_right a s = a lsr s

let rotate_left a s = ((a lsl s) land mask) + ((a lsr (32-s)) land mask)
let rotate_right a s = ((a lsl (32-s)) land mask) + ((a lsr s) land mask)

let of_int s = s                                          
let of_uint32 s = s
let of_string s = int_of_string s
                                
(* TODO *)
let eq x y = if x = y then -1 else 0
let gte x y = if x >= y then -1 else 0

let op_Less_Less_Less : uint32  ->  Prims.nat  ->  uint32 = rotate_left
let op_Hat_Less_Less : uint32  ->  Prims.nat  ->  uint32 = shift_left
let op_Hat_Plus = add
let op_Hat_Subtraction = sub
let op_Hat_Star = mul
let op_Hat_Slash = div
let op_Hat_Less_Less = shift_left
let op_Hat_Greater_Greater = shift_right
let op_Hat_Amp = logand
let op_Hat_Bar = logor
let op_Hat_Hat = logxor

let of_string s = let x = int_of_string s in if x >= 4294967296 || x < 0 then failwith "Wrong constant"
                  else x 
let of_int s = s land mask
                                                             
let to_string s = string_of_int s
let to_int s = s
