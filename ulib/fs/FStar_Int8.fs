module FStar_Int8
(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
(* THIS FILE IS BASED ON AUTOGENERATED ml/FStar_Int8.ml FILE! *)
(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)

type int8 = System.SByte
type t = System.SByte
let n = Prims.of_int 8

let int_to_t x = System.SByte.Parse((string x))
let __int_to_t = int_to_t

let v (x:t) : Prims.int = Prims.parse_int (string x)

let zero = 0y
let one  = 1y
let ones = System.SByte.MaxValue

(* Reexport add, plus aliases *)
let add           : t -> t -> t = (+)
let add_underspec : t -> t -> t = (+)
let add_mod       : t -> t -> t = (+)

(* Reexport sub, plus aliases *)
let sub           : t -> t -> t = (-)
let sub_underspec : t -> t -> t = (-)
let sub_mod       : t -> t -> t = (-)

(* Reexport mul, plus aliases *)
let mul           : t -> t -> t = (*)
let mul_underspec : t -> t -> t = (*)
let mul_mod       : t -> t -> t = (*)

(* Just reexport these *)
let div       : t -> t -> t = (/)
let rem       : t -> t -> t = (%)
let logand    : t -> t -> t = (&&&)
let logxor    : t -> t -> t = (^^^)
let logor     : t -> t -> t = (|||)
let lognot    :      t -> t = (~~~)
let to_string : t -> string = string
let of_string : string -> t = System.SByte.Parse

let to_string_hex (x : t) = "0x" + (x.ToString("X"))

let to_string_hex_pad (i : t) = i.ToString("X2")

(* The shifts take a uint32 argument, so we need to convert *)
let shift_right (n : t) (i : System.UInt32) : t = n >>> (int32 i)
let shift_left  (n : t) (i : System.UInt32) : t = n <<< (int32 i)
let shift_arithmetic_right = shift_right

(* Comparison operators *)
let eq  (a:t) (b:t) : bool = a = b
let gt  (a:t) (b:t) : bool = a > b
let gte (a:t) (b:t) : bool = a >= b
let lt  (a:t) (b:t) : bool = a < b
let lte (a:t) (b:t) : bool = a <= b

(* NOT Constant time operators *)
let eq_mask  (a:t) (b:t) : t = if a  = b then ones else zero
let gte_mask (a:t) (b:t) : t = if a >= b then ones else zero

(* Infix notations *)
let op_Plus_Hat                 = add
let op_Plus_Question_Hat        = add_underspec
let op_Plus_Percent_Hat         = add_mod
let op_Subtraction_Hat          = sub
let op_Subtraction_Question_Hat = sub_underspec
let op_Subtraction_Percent_Hat  = sub_mod
let op_Star_Hat                 = mul
let op_Star_Question_Hat        = mul_underspec
let op_Star_Percent_Hat         = mul_mod
let op_Slash_Hat                = div
let op_Percent_Hat              = rem
let op_Hat_Hat                  = logxor
let op_Amp_Hat                  = logand
let op_Bar_Hat                  = logor
let op_Less_Less_Hat            = shift_left
let op_Greater_Greater_Hat      = shift_right
let op_Equals_Hat               = eq
let op_Greater_Hat              = gt
let op_Greater_Equals_Hat       = gte
let op_Less_Hat                 = lt
let op_Less_Equals_Hat          = lte
