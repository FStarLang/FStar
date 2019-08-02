type uint32 = int
type t = uint32
type t' = t
                
let (%) x y = if x < 0 then (x mod y) + y else x mod y

let n = Prims.parse_int "32"
let v (x:uint32) : Prims.int = Prims.parse_int (string_of_int x)

let zero = 0
let one = 1
let ones = 4294967295
                                               
let add (a:uint32) (b:uint32) : uint32 = a + b
let add_underspec a b = add a b
let add_mod a b = (add a b) land 4294967295

let sub (a:uint32) (b:uint32) : uint32 = a - b
let sub_underspec a b = sub a b
let sub_mod a b = (sub a b) land 4294967295

let mul (a:uint32) (b:uint32) : uint32 = a * b
let mul_underspec a b = mul a b
let mul_mod a b = (mul a b) land 4294967295

let div (a:uint32) (b:uint32) : uint32 = a / b

let rem (a:uint32) (b:uint32) : uint32 = a mod b

let logand (a:uint32) (b:uint32) : uint32 = a land b
let logxor (a:uint32) (b:uint32) : uint32 = a lxor b
let logor  (a:uint32) (b:uint32) : uint32 = a lor b
let lognot (a:uint32) : uint32 = lnot a
       
let int_to_uint32 (x:Prims.int) = int_of_string (Prims.to_string x) % 4294967296

let shift_right (a:uint32) (b:uint32) : uint32 = a lsr b
let shift_left  (a:uint32) (b:uint32) : uint32 = (a lsl b) land 4294967295

(* Comparison operators *)
let eq (a:uint32) (b:uint32) : bool = a = b
let gt (a:uint32) (b:uint32) : bool = a > b
let gte (a:uint32) (b:uint32) : bool = a >= b
let lt (a:uint32) (b:uint32) : bool = a < b
let lte (a:uint32) (b:uint32) : bool =  a <= b

(* NOT Constant time comparison operators *)
let eq_mask (a:uint32) (b:uint32) : uint32 =
  if a = b then -1 else 0
let gte_mask (a:uint32) (b:uint32) : uint32 =
  if a >= b then -1 else 0

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
let to_int s = s
let uint_to_t s = int_to_uint32 s
let __uint_to_t = uint_to_t
