type uint64 = Int64.t
type uint8 = int
type t = uint64
           
let (%) x y = if x < 0 then (x mod y) + y else x mod y

let v (x:uint64) : Prims.int = Prims.parse_int (Int64.to_string x)

let zero = Int64.zero
let one = Int64.one
let ones = Int64.pred Int64.zero

let add (a:uint64) (b:uint64) : uint64 = Int64.add a b
let add_underspec a b = add a b
let add_mod a b = add a b

let sub (a:uint64) (b:uint64) : uint64 = Int64.sub a b
let sub_underspec a b = sub a b
let sub_mod a b = sub a b

let mul (a:uint64) (b:uint64) : uint64 = Int64.mul a b
let mul_underspec a b = mul a b
let mul_mod a b = mul a b

let div (a:uint64) (b:uint64) : uint64 = failwith "Not implemented"

let rem (a:uint64) (b:uint64) : uint64 = failwith "Not implemneted"

let logand (a:uint64) (b:uint64) : uint64 = Int64.logand a b
let logxor (a:uint64) (b:uint64) : uint64 = Int64.logxor a b
let logor  (a:uint64) (b:uint64) : uint64 = Int64.logor a b
let lognot (a:uint64) : uint64 = Int64.lognot a

let cmod (x:Prims.int) : Prims.int =
  if Prims.op_GreaterThan x (Prims.parse_int "9223372036854775807")
  then Prims.op_Subtraction x (Prims.parse_int "18446744073709551616")
  else x
                                              
let int_to_uint64 (x:Prims.int) : uint64= Int64.of_string
                                            (Prims.to_string (cmod x)) 

let shift_right (a:uint64) (b:uint8) : uint64 = Int64.shift_right_logical a b
let shift_left  (a:uint64) (b:uint8) : uint64 = Int64.shift_left a b

(* Comparison operators *)
let eq (a:uint64) (b:uint64) : bool = a = b
let gt (a:uint64) (b:uint64) : bool = a > b
let gte (a:uint64) (b:uint64) : bool = a >= b
let lt (a:uint64) (b:uint64) : bool = a < b
let lte (a:uint64) (b:uint64) : bool =  a <= b

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
let op_Greater_Equal_Hat = gte
let op_Less_Hat = gt
let op_Less_Equal_Hat = gte

let to_string s = Big_int_Z.string_of_big_int (Big_int_Z.and_big_int (Big_int_Z.big_int_of_int64 s) (Big_int_Z.big_int_of_string "0xffffffffffffffff"))

let uint_to_t s = s
