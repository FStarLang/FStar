module FStar_UInt8

// TODO: Would it make sense to use .net byte here?
type uint8 = Prims.int
type byte = uint8
type t = uint8
type t' = t

let n = Prims.parse_int "8"
let v (x:uint8) : Prims.int = Prims.parse_int (string x)

let zero = 0
let one = 1
let ones = 255
                                              
let add (a:uint8) (b:uint8) : uint8 = a + b
let add_underspec a b = (add a b) &&& 255I
let add_mod = add_underspec

let sub (a:uint8) (b:uint8) : uint8 = a - b
let sub_underspec a b = (sub a b) &&& 255I
let sub_mod = sub_underspec

let mul (a:uint8) (b:uint8) : uint8 = a * b
let mul_underspec a b = (mul a b) &&& 255I
let mul_mod = mul_underspec

let div (a:uint8) (b:uint8) : uint8 = Prims.(/) a b

let rem (a:uint8) (b:uint8) : uint8 = Prims.(mod) a b

let logand (a:uint8) (b:uint8) : uint8 = a &&& b
let logxor (a:uint8) (b:uint8) : uint8 = a ^^^ b
let logor  (a:uint8) (b:uint8) : uint8 = a ||| b
let lognot (a:uint8) : uint8 = bigint.op_OnesComplement a
       
let int_to_uint8 (x:Prims.int) : uint8 = x % 256I

let shift_right (a:uint8) (b:System.UInt32) : uint8 = a >>> (int32 b)
let shift_left  (a:uint8) (b:System.UInt32) : uint8 = (a <<< (int32 b)) &&& 255I

(* Comparison operators *)
let eq (a:uint8) (b:uint8) : bool = a = b
let gt (a:uint8) (b:uint8) : bool = a > b
let gte (a:uint8) (b:uint8) : bool = a >= b
let lt (a:uint8) (b:uint8) : bool = a < b
let lte (a:uint8) (b:uint8) : bool =  a <= b

(* NOT Constant time comparison operators *)
let gte_mask (a:uint8) (b:uint8) : uint8 = if a >= b then 255I else 0I
let eq_mask (a:uint8) (b:uint8) : uint8 = if a = b then 255I else 0I

let of_string s = Prims.parse_int s
let to_string s = Prims.to_string s
// The hex printing for BigInteger in .NET is a bit non-standard as it 
// prints an extra leading '0' for positive numbers
let to_string_hex (s : t) = "0x" + (s.ToString("X").TrimStart([| '0' |]))
let to_string_hex_pad (s : t) = s.ToString("X").TrimStart([| '0' |]).PadLeft(2, '0')
let uint_to_t s = int_to_uint8 s
let to_int s = s
let __uint_to_t = uint_to_t
