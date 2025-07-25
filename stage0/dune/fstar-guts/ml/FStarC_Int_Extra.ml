let logand      = Z.logand
let logor       = Z.logor
let logxor      = Z.logxor
let lognot      = Z.lognot

(* zarith expects an OCaml int for the shift amount *)
let shift_left  x y = Z.shift_left  x (Z.to_int y)
let shift_right x y = Z.shift_right x (Z.to_int y)
