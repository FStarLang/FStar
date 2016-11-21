open Int64

type t = Int64.t
type uint32 = t

let v (x:uint32) : Prims.int = Prims.parse_int (to_string x)

let zero = zero
let one = one
let ones = of_string "4294967295"
let red x = logand x ones

let add = add
let add_underspec = add
let add_mod x y = red (add x y)

let sub = sub
let sub_underspec = sub
let sub_mod x y = red (sub x y)

let mul = mul
let mul_underspec = mul
let mul_mod x y = red (mul x y)

let div = div
let rem = rem

let logand = logand
let logxor = logxor
let logor = logor
let lognot x = red (lognot x)

let eq x y = 0 = compare x y
let gt x y = 1 = compare x y
let lt x y = -1 = compare x y
let gte x y = 0 <= compare x y
let lte x y = 0 >= compare x y

let of_string = Int64.of_string
let to_string = Int64.to_string

let int_to_uint32 x = red (Int64.of_string (Prims.to_string x))
let shift_right x y = red (shift_right x (to_int y))
let shift_left x y = red (shift_left x (to_int y))

let to_int = Int64.to_int
let to_string = Int64.to_string
let uint_to_t = int_to_uint32

(*

type int32 = int
type t = int32

let v (x:int32) : Prims.int = Prims.parse_int (string_of_int x)

let zero = 0
let one = 1
let ones = -1                                             

let add (a:int32) (b:int32) : int32 = a + b
let add_underspec a b = add a b
let add_mod a b = (add a b) land 4294967295

let sub (a:int32) (b:int32) : int32 = a - b
let sub_underspec a b = sub a b
let sub_mod a b = (sub a b) land 4294967295

let mul (a:int32) (b:int32) : int32 = a * b
let mul_underspec a b = mul a b
let mul_mod a b = (mul a b) land 4294967295

let div (a:int32) (b:int32) : int32 = a / b

let rem (a:int32) (b:int32) : int32 = a mod b

let logand (a:int32) (b:int32) : int32 = a land b
let logxor (a:int32) (b:int32) : int32 = a lxor b
let logor  (a:int32) (b:int32) : int32 = a lor b
let lognot (a:int32) : int32 = lnot a
       
let int_to_int32 (x:Prims.int) = int_of_string (Prims.to_string x) land 4294967295

let shift_right (a:int32) (b:int32) : int32 = a asr b
let shift_left  (a:int32) (b:int32) : int32 = (a lsl b) land 4294967295

(* Comparison operators *)
let eq (a:int32) (b:int32) : bool = a = b
let gt (a:int32) (b:int32) : bool = a > b
let gte (a:int32) (b:int32) : bool = a >= b
let lt (a:int32) (b:int32) : bool = a < b
let lte (a:int32) (b:int32) : bool =  a <= b
*)

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

(*
let cmod x =
  if x > 2147483647 then x - 4294967296 else x

let to_string s = string_of_int (cmod s)
let int_to_t s = s
*)
