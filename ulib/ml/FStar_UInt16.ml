type uint16 = int[@@deriving yojson,show]
type t = uint16[@@deriving yojson,show]
type t' = t[@@deriving yojson,show]
           
let (%) x y = if x < 0 then (x mod y) + y else x mod y

let n = Prims.parse_int "16"
let v (x:uint16) : Prims.int = Prims.parse_int (string_of_int x)

let zero = 0
let one = 1
let ones = 65535
                                               
let add (a:uint16) (b:uint16) : uint16 = a + b
let add_underspec a b = add a b
let add_mod a b = (add a b) land 65535

let sub (a:uint16) (b:uint16) : uint16 = a - b
let sub_underspec a b = sub a b
let sub_mod a b = (sub a b) land 65535

let mul (a:uint16) (b:uint16) : uint16 = a * b
let mul_underspec a b = mul a b
let mul_mod a b = (mul a b) land 65535

let div (a:uint16) (b:uint16) : uint16 = a / b

let rem (a:uint16) (b:uint16) : uint16 = a mod b

let logand (a:uint16) (b:uint16) : uint16 = a land b
let logxor (a:uint16) (b:uint16) : uint16 = a lxor b
let logor  (a:uint16) (b:uint16) : uint16 = a lor b
let lognot (a:uint16) : uint16 = lnot a
       
let int_to_uint16 (x:Prims.int) = int_of_string (Prims.to_string x) % 65536

let shift_right (a:uint16) (b:uint16) : uint16 = a lsr b
let shift_left  (a:uint16) (b:uint16) : uint16 = (a lsl b) land 65535

(* Comparison operators *)
let eq (a:uint16) (b:uint16) : bool = a = b
let gt (a:uint16) (b:uint16) : bool = a > b
let gte (a:uint16) (b:uint16) : bool = a >= b
let lt (a:uint16) (b:uint16) : bool = a < b
let lte (a:uint16) (b:uint16) : bool =  a <= b

(* NOT Constant time comparison operators *)
let gte_mask (a:uint16) (b:uint16) : uint16 = if a >= b then 0xFFFF else 0
let eq_mask (a:uint16) (b:uint16) : uint16 = if a = b then 0xFFFF else 0

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

let to_string s = string_of_int s
let uint_to_t s = int_to_uint16 s
let __uint_to_t = uint_to_t
