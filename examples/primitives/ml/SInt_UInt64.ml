let n = 8
type uint64 = Stdint.uint64
type uint128 = Stdint.uint128
type native_int = uint64
type limb = uint64
type wide = uint128
                    
let (zero:uint64) = Stdint.Uint64.zero
let (one:uint64) = Stdint.Uint64.one
let (ones:uint64) = Stdint.Uint64.pred zero
let (zero_wide:uint128) = Stdint.Uint128.zero
let (one_wide:uint128) = Stdint.Uint128.one
let (ones_wide:uint128) = Stdint.Uint128.pred zero_wide

let bits = 64

(* Standard operators *)
let add a b = Stdint.Uint64.add a b
let add_mod a b = add a b
let sub a b = Stdint.Uint64.sub a b
let sub_mod a b = sub a b
let mul a b = Stdint.Uint64.mul a b
let mul_wide a b = Stdint.Uint128.mul (Stdint.Uint128.of_uint64 a) (Stdint.Uint128.of_uint64 b)
let mul_mod a b = mul a b
let div a b = Stdint.Uint64.div a b
let rem a b = Stdint.Uint64.rem a b

let logand a b = Stdint.Uint64.logand a b
let logxor a b = Stdint.Uint64.logxor a b
let logor a b = Stdint.Uint64.logor a b
let lognot a = Stdint.Uint64.lognot a

let shift_left a s = Stdint.Uint64.shift_left a s
let shift_right a s = Stdint.Uint64.shift_right a s
let shift_right_logical a s = Stdint.Uint64.shift_right_logical a s

let rotate_left a s =
  logor (shift_left a s)
        (shift_right_logical a (64 - s))
let rotate_right a s =
  logor (shift_right_logical a s)
        (shift_left a (64 - s))
(*
val to_uint64: sint -> Tot uint64
let to_uint64 s = to_usint n s
 *)

let add_wide a b = Stdint.Uint128.add a b
let add_mod_wide a b = Stdint.Uint128.add a b
let sub_wide a b = Stdint.Uint128.sub a b
let sub_mod_wide a b = Stdint.Uint128.sub a b
let mul_wide_wide a b = Stdint.Uint128.mul a b
let mul_mod_wide a b = Stdint.Uint128.mul a b
let div_wide a b = Stdint.Uint128.div a b
let rem_wide a b = Stdint.Uint128.rem a b

let logand_wide a b = Stdint.Uint128.logand a b
let logxor_wide a b = Stdint.Uint128.logxor a b
let logor_wide a b = Stdint.Uint128.logor a b
let lognot_wide a = Stdint.Uint128.lognot a

let shift_left_wide a s = Stdint.Uint128.shift_left a s
let shift_right_wide a s = Stdint.Uint128.shift_right a s
let shift_right_logical_wide a s = Stdint.Uint128.shift_right_logical a s

let rotate_left_wide a s =
  logor (shift_left a s)
        (shift_right_logical a (128 - s))
let rotate_right_wide a s =
  logor (shift_right_logical a s)
        (shift_left a (128 - s))
        
let op_Hat_Plus = add
let op_Hat_Subtraction = sub
let op_Hat_Star = mul
let op_Hat_Plus_Percent = add
let op_Hat_Subtraction_Percent = sub
let op_Hat_Star_Percent = mul
let op_Hat_Star_Hat = mul_wide
let op_Hat_Slash = div
let op_Hat_Less_Less = shift_left
let op_Hat_Greater_Greater = shift_right
let op_Hat_Amp = logand
let op_Hat_Bar = logor
let op_Hat_Hat = logxor

let op_Hat_Hat_Less_Less = shift_left_wide
let op_Hat_Hat_Greater_Greater = shift_right_wide
let op_Hat_Hat_Plus = add_wide
let op_Hat_Hat_Plus_Percent = add_mod_wide
let op_Hat_Hat_Subtraction = sub_wide
let op_Hat_Hat_Subtraction_Percent = sub_mod_wide
let op_Hat_Hat_Star = mul_wide_wide
let op_Hat_Hat_Star_Percent = mul_mod_wide
let op_Hat_Hat_Hat = logxor_wide
let op_Hat_Hat_Amp = logand_wide
let op_Hat_Hat_Bar = logor_wide
let op_Hat_Less_Less_Less = rotate_left_wide
let op_Hat_Greater_Greater_Greater = rotate_right_wide
                   
(* let to_uint8 s = Stdint.Uint64.to_int s land 255 *)
(* let of_uint8 s = Stdint.Uint64.of_int s *)
(* let of_uint32 s = of_int s *)

let wide_to_limb s = Stdint.Uint64.of_uint128 s
let limb_to_wide s = Stdint.Uint128.of_uint64 s

let eq x y =
  let a = Stdint.Uint64.lognot (Stdint.Uint64.logxor x y) in
  let a = Stdint.Uint64.logand a (Stdint.Uint64.shift_left a 32) in
  let a = Stdint.Uint64.logand a (Stdint.Uint64.shift_left a 16) in
  let a = Stdint.Uint64.logand a (Stdint.Uint64.shift_left a 8) in
  let a = Stdint.Uint64.logand a (Stdint.Uint64.shift_left a 4) in
  let a = Stdint.Uint64.logand a (Stdint.Uint64.shift_left a 2) in
  let a = Stdint.Uint64.logand a (Stdint.Uint64.shift_left a 1) in
  let r = Stdint.Int64.of_uint64 a in
  let r = Stdint.Int64.shift_right r 63 in
  Stdint.Uint64.of_int64 r

let gte x y =
  let a = Stdint.Int128.of_uint64 x in
  let b = Stdint.Int128.of_uint64 y in
  let a = Stdint.Int128.shift_right (Stdint.Int128.sub a b) 127 in
  Stdint.Uint64.of_int128 a

let of_string s = Stdint.Uint64.of_string s
let of_int s = Stdint.Uint64.of_int s
let uint128_of_int s = Stdint.Uint128.of_int s
let uint128_of_string s = Stdint.Uint128.of_string s
let to_string s = Stdint.Uint64.to_string s
let to_int s = Stdint.Uint64.to_int s
let uint128_to_string s = Stdint.Uint128.to_string s
let uint128_to_int s = Stdint.Uint128.to_int s
