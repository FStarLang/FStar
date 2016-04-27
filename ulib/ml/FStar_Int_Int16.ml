type int16 = int

let v (x:int16) : Prims.int = Prims.parse_int (string_of_int x)

let zero = 0
let one = 1
let ones = -1                                             

let add (a:int16) (b:int16) : int16 = a + b
let add_underspec a b = add a b
let add_mod a b = (add a b) land 65535

let sub (a:int16) (b:int16) : int16 = a - b
let sub_underspec a b = sub a b
let sub_mod a b = (sub a b) land 65535

let mul (a:int16) (b:int16) : int16 = a * b
let mul_underspec a b = mul a b
let mul_mod a b = (mul a b) land 65535

let div (a:int16) (b:int16) : int16 = a / b

let rem (a:int16) (b:int16) : int16 = a mod b

let logand (a:int16) (b:int16) : int16 = a land b
let logxor (a:int16) (b:int16) : int16 = a lxor b
let logor  (a:int16) (b:int16) : int16 = a lor b
let lognot (a:int16) : int16 = lnot a
       
let int_to_int16 (x:Prims.int) = int_of_string (Prims.to_string x) land 65535

let shift_right (a:int16) (b:int16) : int16 = a asr b
let shift_left  (a:int16) (b:int16) : int16 = (a lsl b) land 65535

(* Comparison operators *)
let eq (a:int16) (b:int16) : bool = a = b
let gt (a:int16) (b:int16) : bool = a > b
let gte (a:int16) (b:int16) : bool = a >= b
let lt (a:int16) (b:int16) : bool = a < b
let lte (a:int16) (b:int16) : bool =  a <= b

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
let op_Hat_Percent = rem
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

let cmod x =
  if x > 32767 then x - 65536 else x

let to_string s = string_of_int (cmod s)
