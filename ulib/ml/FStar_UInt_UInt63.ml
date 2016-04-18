type uint63 = int
type uint8 = int
                
let (%) x y = if x < 0 then (x mod y) + y else x mod y

let v (x:uint63) : Prims.int = Prims.parse_int (string_of_int x)

let add (a:uint63) (b:uint63) : uint63 = a + b
let add_underspec a b = add a b
let add_mod a b = add a b

let sub (a:uint63) (b:uint63) : uint63 = a - b
let sub_underspec a b = sub a b
let sub_mod a b = sub a b

let mul (a:uint63) (b:uint63) : uint63 = a * b
let mul_underspec a b = mul a b
let mul_mod a b = mul a b

let div (a:uint63) (b:uint63) : uint63 = failwith "Not implemented"

let rem (a:uint63) (b:uint63) : uint63 = failwith "Not implemented"

let logand (a:uint63) (b:uint63) : uint63 = a land b
let logxor (a:uint63) (b:uint63) : uint63 = a lxor b
let logor  (a:uint63) (b:uint63) : uint63 = a lor b
let lognot (a:uint63) : uint63 = lnot a
       
let int_to_uint63 (x:Prims.int) : uint63 = int_of_string (Prims.to_string x) 

let shift_right (a:uint63) (b:uint8) : uint63 = a lsr b
let shift_left  (a:uint63) (b:uint8) : uint63 = (a lsl b)

(* Comparison operators *)
let eq (a:uint63) (b:uint63) : bool = a = b
let gt (a:uint63) (b:uint63) : bool = a > b
let gte (a:uint63) (b:uint63) : bool = a >= b
let lt (a:uint63) (b:uint63) : bool = a < b
let lte (a:uint63) (b:uint63) : bool =  a <= b

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
