module Uint32 = struct
  
let zero = Stdint.Uint32.zero
let one = Stdint.Uint32.one
let max_int = Stdint.Uint32.max_int
let min_int = Stdint.Uint32.min_int
let bits = Stdint.Uint32.bits

let add x y = Stdint.Uint32.add x y
let sub x y = Stdint.Uint32.sub x y
let mul x y = Stdint.Uint32.mul x y
let div x y = Stdint.Uint32.div x y
let rem x y = Stdint.Uint32.rem x y
let succ x = Stdint.Uint32.succ x
let pred x = Stdint.Uint32.pred x
let abs x = Stdint.Uint32.abs x
let neg x = Stdint.Uint32.neg x
let logand x y = Stdint.Uint32.logand x y
let logor x y = Stdint.Uint32.logor x y
let logxor x y = Stdint.Uint32.logxor x y
let lognot x = Stdint.Uint32.lognot x
let shift_left x n = Stdint.Uint32.shift_left x n
let shift_right x n = Stdint.Uint32.shift_right x n
let shift_right_logical x n = Stdint.Uint32.shift_right_logical x n
let of_int n = Stdint.Uint32.of_int n
let to_int n = Stdint.Uint32.to_int n
let of_string s = Stdint.Uint32.of_string s
let to_string x = Stdint.Uint32.to_string x
let compare x y = Stdint.Uint32.compare x y

end
