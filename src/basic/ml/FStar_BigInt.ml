type bigint = Z.t
type t = bigint

let zero = Z.zero
let one = Z.one
let two = Z.of_string "2"

let succ_big_int = Z.succ
let pred_big_int = Z.pred
let minus_big_int = Z.neg
let abs_big_int = Z.abs

let add_big_int = Z.add
let mult_big_int = Z.mul
let sub_big_int = Z.sub
let div_big_int = Z.ediv
let mod_big_int = Z.erem

let eq_big_int = Z.equal
let le_big_int = Z.leq
let lt_big_int = Z.lt
let ge_big_int = Z.geq
let gt_big_int = Z.gt

let logand_big_int = Z.logand
let logor_big_int = Z.logor
let logxor_big_int = Z.logxor
let lognot_big_int = Z.lognot

let shift_left_big_int x y = Z.shift_left x (Z.to_int y)
let shift_right_big_int x y = Z.shift_right x (Z.to_int y)

let sqrt_big_int = Z.sqrt

let string_of_big_int = Z.to_string
let big_int_of_string = Z.of_string

let of_int = Z.of_int
let to_int = Z.to_int

let of_int_fs x = x
let to_int_fs x = x

let of_hex x = Z.of_string ("0x" ^ x)
