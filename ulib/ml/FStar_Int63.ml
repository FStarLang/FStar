type int63 = int

let v (x:int63) : Prims.int = Prims.parse_int (string_of_int x)

let zero = 0
let one = 1
let ones = -1                                             

let add (a:int63) (b:int63) : int63 = a + b
let add_underspec a b = add a b
let add_mod a b = add a b 

let sub (a:int63) (b:int63) : int63 = a - b
let sub_underspec a b = sub a b
let sub_mod a b = (sub a b) 

let mul (a:int63) (b:int63) : int63 = a * b
let mul_underspec a b = mul a b
let mul_mod a b = (mul a b) 

let div (a:int63) (b:int63) : int63 = a / b

let rem (a:int63) (b:int63) : int63 = a mod b

let logand (a:int63) (b:int63) : int63 = a land b
let logxor (a:int63) (b:int63) : int63 = a lxor b
let logor  (a:int63) (b:int63) : int63 = a lor b
let lognot (a:int63) : int63 = lnot a
       
let int_to_int63 (x:Prims.int) : int63 = int_of_string (Prims.to_string x)

let shift_right (a:int63) (b:int63) : int63 = a asr b
let shift_left  (a:int63) (b:int63) : int63 = a lsl b

(* Comparison operators *)
let eq (a:int63) (b:int63) : bool = a = b
let gt (a:int63) (b:int63) : bool = a > b
let gte (a:int63) (b:int63) : bool = a >= b
let lt (a:int63) (b:int63) : bool = a < b
let lte (a:int63) (b:int63) : bool =  a <= b

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

let to_string = string_of_int
