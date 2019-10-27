type uint63 = int
type uint8 = int
type t = uint63
type t' = t

let (%) x y = if x < 0 then (x mod y) + y else x mod y

let v (x:uint63) : Prims.int = Prims.parse_int (string_of_int x)

let zero = 0
let one = 1
let ones = -1

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

let int_to_uint63 (x:Prims.int) : uint63 = Int64.to_int (Int64.of_string (Prims.to_string x))

let shift_right (a:uint63) (b:uint8) : uint63 = a lsr b
let shift_left  (a:uint63) (b:uint8) : uint63 = (a lsl b)

(* Comparison operators *)
let eq (a:uint63) (b:uint63) : bool = a = b
let gt (a:uint63) (b:uint63) : bool = a > b
let gte (a:uint63) (b:uint63) : bool = a >= b
let lt (a:uint63) (b:uint63) : bool = a < b
let lte (a:uint63) (b:uint63) : bool =  a <= b

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

let to_string s = Int64.to_string (Int64.logand (Int64.of_int s) (Int64.of_string "0x7fffffffffffffff"))
let of_string s = int_of_string s
let uint_to_t s = int_to_uint63 s
let __uint_to_t = uint_to_t
