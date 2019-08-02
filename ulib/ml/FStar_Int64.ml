type int64 = Int64.t
type uint32 = int
type t = int64
type t' = t
               
let v (x:int64) : Prims.int = Prims.parse_int (Int64.to_string x)

let zero = Int64.zero
let one = Int64.one
let ones = Int64.pred Int64.zero                                       

let add (a:int64) (b:int64) : int64 = Int64.add a b
let add_underspec a b = add a b
let add_mod a b = add a b

let sub (a:int64) (b:int64) : int64 = Int64.sub a b
let sub_underspec a b = sub a b
let sub_mod a b = sub a b

let mul (a:int64) (b:int64) : int64 = Int64.mul a b
let mul_underspec a b = mul a b
let mul_mod a b = mul a b

let div (a:int64) (b:int64) : int64 = Int64.div a b

let rem (a:int64) (b:int64) : int64 = Int64.rem a b

let logand (a:int64) (b:int64) : int64 = Int64.logand a b
let logxor (a:int64) (b:int64) : int64 = Int64.logxor a b
let logor  (a:int64) (b:int64) : int64 = Int64.logor a b
let lognot (a:int64) : int64 = Int64.lognot a
       
let int_to_int64 (x:Prims.int) : int64 = Int64.of_string (Prims.to_string x) 

let shift_right (a:int64) (b:uint32) : int64 = Int64.shift_right_logical a b
let shift_left  (a:int64) (b:uint32) : int64 = Int64.shift_left a b
let shift_arithmetic_right (a:int64) (b:uint32) : int64 = Int64.shift_right a b

(* Comparison operators *)
let eq (a:int64) (b:int64) : bool = a = b
let gt (a:int64) (b:int64) : bool = a > b
let gte (a:int64) (b:int64) : bool = a >= b
let lt (a:int64) (b:int64) : bool = a < b
let lte (a:int64) (b:int64) : bool =  a <= b

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

let to_string = Int64.to_string                     
let int_to_t s = int_to_int64 s
let __int_to_t = int_to_t
