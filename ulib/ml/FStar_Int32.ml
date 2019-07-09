type int32 = int
type uint32 = int
type t = int32
type t' = t

let v (x:int32) : Prims.int = Prims.parse_int (string_of_int x)

let zero = 0
let one = 1
let ones = -1                                             

let add (a:int32) (b:int32) : int32 = a + b
let add_underspec a b = add a b
let add_mod a b = (add a b) land 4294967295

let sub (a:int32) (b:int32) : int32 = a - b
let sub_underspec a b = sub a b
let sub_mod a b = (sub a b) land 4294967295

let mul (a:int32) (b:int32) : int32 = a * b
let mul_underspec a b = mul a b
let mul_mod a b = (mul a b) land 4294967295

let div (a:int32) (b:int32) : int32 = a / b

let rem (a:int32) (b:int32) : int32 = a mod b

let logand (a:int32) (b:int32) : int32 = a land b
let logxor (a:int32) (b:int32) : int32 = a lxor b
let logor  (a:int32) (b:int32) : int32 = a lor b
let lognot (a:int32) : int32 = lnot a
       
let int_to_int32 (x:Prims.int) = int_of_string (Prims.to_string x) land 4294967295

let shift_right (a:int32) (b:uint32) : int32 = a lsr b
let shift_left  (a:int32) (b:uint32) : int32 = (a lsl b) land 4294967295
let shift_arithmetic_right (a:int32) (b:uint32) : int32 = a asr b

(* Comparison operators *)
let eq (a:int32) (b:int32) : bool = a = b
let gt (a:int32) (b:int32) : bool = a > b
let gte (a:int32) (b:int32) : bool = a >= b
let lt (a:int32) (b:int32) : bool = a < b
let lte (a:int32) (b:int32) : bool =  a <= b

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

let cmod x =
  if x > 2147483647 then x - 4294967296 else x

let to_string s = string_of_int (cmod s)
let int_to_t s = int_to_int32 s
let __int_to_t = int_to_t
