(* GM: This file is manual due to the derivings,
   and that sucks. *)

type uint8 = int[@@deriving yojson,show]
type byte = uint8[@@deriving yojson,show]
type t = uint8[@@deriving yojson,show]
type t' = t[@@deriving yojson,show]
              
let (%) x y = if x < 0 then (x mod y) + y else x mod y

let n = Prims.parse_int "8"
let v (x:uint8) : Prims.int = Prims.parse_int (string_of_int x)

let zero = 0
let one = 1
let ones = 255
                                              
let add (a:uint8) (b:uint8) : uint8 = a + b
let add_underspec a b = (add a b) land 255
let add_mod = add_underspec

let sub (a:uint8) (b:uint8) : uint8 = a - b
let sub_underspec a b = (sub a b) land 255
let sub_mod = sub_underspec

let mul (a:uint8) (b:uint8) : uint8 = a * b
let mul_underspec a b = (mul a b) land 255
let mul_mod = mul_underspec

let div (a:uint8) (b:uint8) : uint8 = a / b

let rem (a:uint8) (b:uint8) : uint8 = a mod b

let logand (a:uint8) (b:uint8) : uint8 = a land b
let logxor (a:uint8) (b:uint8) : uint8 = a lxor b
let logor  (a:uint8) (b:uint8) : uint8 = a lor b
let lognot (a:uint8) : uint8 = lnot a
       
let int_to_uint8 (x:Prims.int) : uint8 = Z.to_int x % 256

let shift_right (a:uint8) (b:Stdint.Uint32.t) : uint8 = a lsr (Stdint.Uint32.to_int b)
let shift_left  (a:uint8) (b:Stdint.Uint32.t) : uint8 = (a lsl (Stdint.Uint32.to_int b)) land 255

(* Comparison operators *)
let eq (a:uint8) (b:uint8) : bool = a = b
let gt (a:uint8) (b:uint8) : bool = a > b
let gte (a:uint8) (b:uint8) : bool = a >= b
let lt (a:uint8) (b:uint8) : bool = a < b
let lte (a:uint8) (b:uint8) : bool =  a <= b

(* NOT Constant time comparison operators *)
let gte_mask (a:uint8) (b:uint8) : uint8 = if a >= b then 255 else 0
let eq_mask (a:uint8) (b:uint8) : uint8 = if a = b then 255 else 0
                                             
let of_string s = int_of_string s
let to_string s = string_of_int s
let to_string_hex s = Printf.sprintf "0x%x" s
let to_string_hex_pad s = Printf.sprintf "%02x" s
let uint_to_t s = int_to_uint8 s
let to_int s = s
let __uint_to_t = uint_to_t
