type uint128 = Stdint.Uint128.t
type uint8 = int
type t = uint128
           
let (%) x y = if x < 0 then (x mod y) + y else x mod y

let n = Prims.parse_int "128"
let v (x:uint128) : Prims.int = Prims.parse_int (Stdint.Uint128.to_string x)

let zero = Stdint.Uint128.zero
let one = Stdint.Uint128.one
let ones = Stdint.Uint128.pred Stdint.Uint128.zero

let add (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.add a b
let add_underspec a b = add a b
let add_mod a b = add a b

let sub (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.sub a b
let sub_underspec a b = sub a b
let sub_mod a b = sub a b

let mul (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.mul a b
let mul_underspec a b = mul a b
let mul_mod a b = mul a b
let mul_wide (a:Stdint.Uint64.t) (b:Stdint.Uint64.t) = Stdint.Uint128.mul (Stdint.Uint128.of_uint64 a)
                                                                          (Stdint.Uint128.of_uint64 b)
                                                          
let div (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.div a b

let rem (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.rem a b

let logand (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.logand a b
let logxor (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.logxor a b
let logor  (a:uint128) (b:uint128) : uint128 = Stdint.Uint128.logor a b
let lognot (a:uint128) : uint128 = Stdint.Uint128.lognot a

(* let cmod (x:Prims.int) : Prims.int = *)
(*   if Prims.op_GreaterThan x (Prims.parse_int "9223372036854775807") *)
(*   then Prims.op_Subtraction x (Prims.parse_int "18446744073709551616") *)
(*   else x *)
                                              
let int_to_uint128 (x:Prims.int) : uint128= Stdint.Uint128.of_string (Prims.to_string x) 

let shift_right (a:uint128) (b:uint8) : uint128 = Stdint.Uint128.shift_right_logical a b
let shift_left  (a:uint128) (b:uint8) : uint128 = Stdint.Uint128.shift_left a b

(* Comparison operators *)
let eq (a:uint128) (b:uint128) : bool = a = b
let gt (a:uint128) (b:uint128) : bool = a > b
let gte (a:uint128) (b:uint128) : bool = a >= b
let lt (a:uint128) (b:uint128) : bool = a < b
let lte (a:uint128) (b:uint128) : bool =  a <= b

let eq_mask (a:uint128) (b:uint128) : uint128 =
  if a = b then Stdint.Uint128.pred Stdint.Uint128.zero
  else Stdint.Uint128.zero
let gte_mask (a:uint128) (b:uint128) : uint128 =
  if a >= b then Stdint.Uint128.pred Stdint.Uint128.zero
  else Stdint.Uint128.zero

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

let of_string s = Stdint.Uint128.of_string s
let to_string s = Stdint.Uint128.to_string s
let uint_to_t s = Stdint.Uint128.of_string (Z.to_string s)
