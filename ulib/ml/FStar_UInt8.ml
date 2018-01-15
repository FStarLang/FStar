type uint8 = int
type byte = uint8
type t = uint8
type t' = t
              
let (%) x y = if x < 0 then (x mod y) + y else x mod y

let n = Prims.parse_int "8"
let v (x:uint8) : Prims.int = Prims.parse_int (string_of_int x)

let zero = 0
let one = 1
let ones = 255
                                              
let add (a:uint8) (b:uint8) : uint8 = a + b
let add_underspec a b = add a b
let add_mod a b = (add a b) land 255

let sub (a:uint8) (b:uint8) : uint8 = a - b
let sub_underspec a b = sub a b
let sub_mod a b = (sub a b) land 255

let mul (a:uint8) (b:uint8) : uint8 = a * b
let mul_underspec a b = mul a b
let mul_mod a b = (mul a b) land 255

let div (a:uint8) (b:uint8) : uint8 = a / b

let rem (a:uint8) (b:uint8) : uint8 = a mod b

let logand (a:uint8) (b:uint8) : uint8 = a land b
let logxor (a:uint8) (b:uint8) : uint8 = a lxor b
let logor  (a:uint8) (b:uint8) : uint8 = a lor b
let lognot (a:uint8) : uint8 = lnot a
       
let int_to_uint8 (x:Prims.int) : uint8 = int_of_string (Prims.to_string x) % 256

let shift_right (a:uint8) (b:uint8) : uint8 = a lsr b
let shift_left  (a:uint8) (b:uint8) : uint8 = (a lsl b) land 255

(* Comparison operators *)
let eq (a:uint8) (b:uint8) : bool = a = b
let gt (a:uint8) (b:uint8) : bool = a > b
let gte (a:uint8) (b:uint8) : bool = a >= b
let lt (a:uint8) (b:uint8) : bool = a < b
let lte (a:uint8) (b:uint8) : bool =  a <= b

(* Constant time comparison operators, TODO: check and implement efficiently *)
let gte_mask (a:uint8) (b:uint8) : uint8 = lnot((a-b) asr 62) land 255
let eq_mask (a:uint8) (b:uint8) : uint8 = gte_mask a b land gte_mask b a
                                             
(* Infix notations *)
let op_Plus_Hat = add
let op_Plus_Question_Hat = add_underspec
let op_Plus_Percent_Hat = add_mod
let op_Subtraction_Hat = sub
let op_Subtraction_Question_Hat = sub_underspec
let op_Subtraction_Percent_Hat = sub_mod
let op_Star_Hat = mul
let op_Star_Question_Hat = mul_underspec
let op_Star_Percent_Hat = mul_mod
let op_Slash_Hat = div
let op_Percent_Hat = rem
let op_Hat_Hat = logxor  
let op_Amp_Hat = logand
let op_Bar_Hat = logor
let op_Less_Less_Hat = shift_left
let op_Greater_Greater_Hat = shift_right
let op_Equals_Hat = eq
let op_Greater_Hat = gt
let op_Greater_Equals_Hat = gte
let op_Less_Hat = lt
let op_Less_Equals_Hat = lte

let of_string s = int_of_string s
let to_string s = string_of_int s
let to_string_hex s = Printf.sprintf "%02x" s
let uint_to_t s = int_to_uint8 s
let to_int s = s
let __uint_to_t = uint_to_t
