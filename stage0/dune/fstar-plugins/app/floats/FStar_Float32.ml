(* OCaml has no native single-precision float, so we model binary32 as a
   double that always holds a value representable in single precision. We
   round the result of every operation back to single precision using a
   round-trip through the 32-bit IEEE bit representation, which rounds to
   nearest (ties to even). This matches hardware single-precision arithmetic. *)
type t = float

let to_f32 (x:float) : t = Int32.float_of_bits (Int32.bits_of_float x)

let of_int (x:Stdint.Int64.t) : t = to_f32 (Stdint.Int64.to_float x)

let zero = of_int (Stdint.Int64.of_int 0)
let one  = of_int (Stdint.Int64.of_int 1)

let add x y = to_f32 (x +. y)
let sub x y = to_f32 (x -. y)
let mul x y = to_f32 (x *. y)
let div x y = to_f32 (x /. y)

let lt x y = x < y
let lte x y = x <= y

let ieee_eq x y = x = y

let bit_eq x y = Int32.bits_of_float x = Int32.bits_of_float y

let of_literal (s:string) : t = to_f32 (float_of_string s)

let to_string = string_of_float
