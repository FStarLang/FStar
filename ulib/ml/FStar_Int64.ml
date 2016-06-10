type int64 = Int64.t
type uint8 = int
               
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

let shift_right (a:int64) (b:uint8) : int64 = Int64.shift_right a b
let shift_left  (a:int64) (b:uint8) : int64 = Int64.shift_left a b 

(* Comparison operators *)
let eq (a:int64) (b:int64) : bool = a = b
let gt (a:int64) (b:int64) : bool = a > b
let gte (a:int64) (b:int64) : bool = a >= b
let lt (a:int64) (b:int64) : bool = a < b
let lte (a:int64) (b:int64) : bool =  a <= b

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

let to_string = Int64.to_string                     
