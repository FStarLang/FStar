(*--build-config
  options:--verify_module FStar.UInt64;
  other-files:FStar.Ghost.fst axioms.fst intlib.fst sint.fst;
  --*)

module FStar.UInt64

open FStar.Ghost
open IntLib
open Sint

assume val n: x:pos{x = 64}

type uint64 = usint n
type uint128 = usint (2*n)

let (zero:uint64) = uzero n
let (one:uint64) = uone n
let (ones:uint64) = uones n

let (max_int:erased nat) = eumax_int #n
let (min_int:erased nat) = eumin_int #n

let (bits:pos) = n

(* Standard operators *)
val add: a:uint64 -> b:uint64{v a + v b < reveal max_int} -> Tot uint64
let add a b = uadd #n a b
val add_mod: uint64 -> uint64 -> Tot uint64
let add_mod a b = uadd_mod #n a b
val sub: a:uint64 -> b:uint64{v a - v b >= reveal min_int} -> Tot uint64
let sub a b = usub #n a b
val sub_mod: uint64 -> uint64 -> Tot uint64
let sub_mod a b = usub_mod #n a b
val mul: a:uint64 -> b:uint64{v a * v b < reveal max_int} -> Tot uint64
let mul a b = umul #n a b
val mul_mod: a:uint64 -> b:uint64 -> Tot uint64
let mul_mod a b = umul_mod #n a b
val mul_wide: uint64 -> uint64 -> Tot uint128
let mul_wide a b = umul_large #n a b
val div: uint64 -> b:uint64{v b <> 0} -> Tot uint64
let div a b = udiv #n a b
val rem: uint64 -> b:uint64{v b <> 0} -> Tot uint64
let rem a b = umod #n a b

val logand: uint64 -> uint64 -> Tot uint64
let logand a b = ulogand #n a b
val logxor: uint64 -> uint64 -> Tot uint64
let logxor a b = ulogxor #n a b
val logor: uint64 -> uint64 -> Tot uint64
let logor a b = ulogor #n a b
val lognot: uint64 -> Tot uint64
let lognot a = ulognot #n a

val shift_left: uint64 -> nat -> Tot uint64
let shift_left a s = ushift_left #n a s
val shift_right: uint64 -> nat -> Tot uint64
let shift_right a s = ushift_right #n a s

let rotate_left a s = urotate_left #n a s
let rotate_right a s = urotate_right #n a s

val to_uint64: sint -> Tot uint64
let to_uint64 s = to_usint n s

let op_Less_Less = shift_left
let op_Greater_Greater = shift_right
