module SInt.UInt32

open FStar.Ghost
open Axioms
open IntLib
open SInt

let n = 32

type uint32 = usint n
type uint64 = usint (2*n)

let (zero:uint32) = uzero n
let (one:uint32) = uone n
let (ones:uint32) = uones n

let (max_int:erased nat) = eumax_int #n
let (min_int:erased nat) = eumin_int #n

let (bits:pos) = n

(* Standard operators *)
val add: a:uint32 -> b:uint32{v a + v b < reveal max_int} -> Tot uint32
let add a b = uadd #n a b
val add_mod: uint32 -> uint32 -> Tot uint32
let add_mod a b = uadd_mod #n a b
val sub: a:uint32 -> b:uint32{v a - v b >= reveal min_int} -> Tot uint32
let sub a b = usub #n a b
val sub_mod: uint32 -> uint32 -> Tot uint32
let sub_mod a b = usub_mod #n a b
val mul: a:uint32 -> b:uint32{v a * v b < reveal max_int} -> Tot uint32
let mul a b = umul #n a b
val mul_mod: a:uint32 -> b:uint32 -> Tot uint32
let mul_mod a b = umul_mod #n a b
val mul_wide: uint32 -> uint32 -> Tot uint64
let mul_wide a b = umul_large #n a b
val div: uint32 -> b:uint32{v b <> 0} -> Tot uint32
let div a b = udiv #n a b
val rem: uint32 -> b:uint32{v b <> 0} -> Tot uint32
let rem a b = umod #n a b

val logand: uint32 -> uint32 -> Tot uint32
let logand a b = ulogand #n a b
val logxor: uint32 -> uint32 -> Tot uint32
let logxor a b = ulogxor #n a b
val logor: uint32 -> uint32 -> Tot uint32
let logor a b = ulogor #n a b
val lognot: uint32 -> Tot uint32
let lognot a = ulognot #n a

val shift_left: uint32 -> nat -> Tot uint32
let shift_left a s = ushift_left #n a s
val shift_right: uint32 -> nat -> Tot uint32
let shift_right a s = ushift_right #n a s

val rotate_left: uint32 -> s:nat{s<=n} -> Tot uint32
let rotate_left a s = urotate_left #n a s
val rotate_right: uint32 -> s:nat{s<=n} -> Tot uint32
let rotate_right a s = urotate_right #n a s

let to_uint32 s = to_usint n s
let uint32_of_byte s = to_usint n s
let uint32_of_uint16 s = to_usint n s
let uint32_of_uint64 s = to_usint n s
let uint32_of_int16 s = to_usint n s
let uint32_of_int32 s = to_usint n s
let uint32_of_int64 s = to_usint n s

let op_Less_Less = shift_left
let op_Greater_Greater = shift_right
let op_Hat_Plus = add_mod 
let op_Hat_Hat = logxor  
let op_Less_Less_Less = rotate_left 
let op_Hat_Less_Less = shift_left 

assume val of_string: string -> Tot uint32
assume val of_int: x:nat{x >= 0 /\ x < pow2 n} -> Tot (y:uint32{v y = x})
