type t = float

let of_int (x:Stdint.Int64.t) : float = Stdint.Int64.to_float x

let zero = of_int (Stdint.Int64.of_int 0)
let one  = of_int (Stdint.Int64.of_int 1)

let add x y = x +. y
let sub x y = x -. y
let mul x y = x *. y
let div x y = x /. y

let lt x y = x < y
let lte x y = x <= y

let ieee_eq x y = x = y

let bit_eq x y = Int64.bits_of_float x = Int64.bits_of_float y

let of_literal (s:string) : t = float_of_string s

let to_string = string_of_float
