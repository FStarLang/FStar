let zero = Stdint.Uint64.zero
let one = Stdint.Uint64.one
let max_int = Stdint.Uint64.max_int
let min_int = Stdint.Uint64.min_int
let bits = Stdint.Uint64.bits

let add x y = Stdint.Uint64.add x y
let sub x y = Stdint.Uint64.sub x y
let mul x y = Stdint.Uint64.mul x y
let div x y = Stdint.Uint64.div x y
let rem x y = Stdint.Uint64.rem x y
let succ x = Stdint.Uint64.succ x
let pred x = Stdint.Uint64.pred x
let abs x = Stdint.Uint64.abs x
let neg x = Stdint.Uint64.neg x
let logand x y = Stdint.Uint64.logand x y
let logor x y = Stdint.Uint64.logor x y
let logxor x y = Stdint.Uint64.logxor x y
let lognot x = Stdint.Uint64.lognot x
let shift_left x n = Stdint.Uint64.shift_left x n
let shift_right x n = Stdint.Uint64.shift_right x n
let shift_right_logical x n = Stdint.Uint64.shift_right_logical x n
let of_int n = Stdint.Uint64.of_int n
let to_int n = Stdint.Uint64.to_int n
let of_string s = Stdint.Uint64.of_string s
let to_string x = Stdint.Uint64.to_string x
let compare x y = Stdint.Uint64.compare x y

let rotate_left x n =
  logor (shift_left x n)
        (shift_right_logical x (64 - n))
let rotate_right x n =
  logor (shift_right_logical x n)
        (shift_left x (64 - n))
