module SInt.UInt63

open FStar.Ghost
open Axioms
open IntLib
open SInt

let n : pos = 63

type uint63 = usint n
type native_int = uint63

let (zero:uint63) = uzero n
let (one:uint63) = uone n
let (ones:uint63) = uones n

let (max_int:erased nat) = eumax_int #n
let (min_int:erased nat) = eumin_int #n

let (bits:pos) = n

(* Standard operators *)
val add: a:uint63 -> b:uint63{v a + v b < pow2 n} -> Tot uint63
val add_mod: a:uint63 -> b:uint63 -> Tot uint63
val sub: a:uint63 -> b:uint63{v a - v b >= 0} -> Tot uint63
val sub_mod: a:uint63 -> b:uint63 -> Tot uint63
val mul: a:uint63 -> b:uint63{v a * v b < pow2 n} -> Tot uint63
val mul_mod: a:uint63 -> b:uint63 -> Tot uint63
val div: a:uint63 -> b:uint63{v b <> 0} -> Tot uint63
val rem: a:uint63 -> b:uint63{v b <> 0} -> Tot uint63
val logand: uint63 -> uint63 -> Tot uint63
val logxor: uint63 -> uint63 -> Tot uint63
val logor: uint63 -> uint63 -> Tot uint63
val lognot: uint63 -> Tot uint63
val shift_right: a:uint63 -> s:nat -> Tot uint63
val shift_left: a:uint63 -> s:nat -> Tot uint63
val rotate_left: a:uint63 -> s:nat{s <= n} -> Tot uint63
val rotate_right: a:uint63 -> s:nat{s <= n} -> Tot uint63
let add a b = uadd #n a b
let add_mod a b = uadd_mod #n a b
let sub a b = usub #n a b
let sub_mod a b = usub_mod #n a b
let mul a b = umul #n a b
let mul_mod a b = umul_mod #n a b
let div a b = udiv #n a b
let rem a b = umod #n a b
let logand a b = ulogand #n a b
let logxor a b = ulogxor #n a b
let logor a b = ulogor #n a b
let lognot a = ulognot #n a
let shift_left a s = ushift_left #n a s
let shift_right a s = ushift_right #n a s
let rotate_left a s = urotate_left #n a s
let rotate_right a s = urotate_right #n a s

(* val to_uint63: sint -> Tot uint63 *)
(* let to_uint63 s = to_usint n s *)

(* let of_uint32 s = to_uint63 s *)

assume val of_int: x:nat{x >= 0 /\ x < pow2 n} -> Tot (y:uint63{v y = x})
assume val of_string: string -> Tot uint63

let op_Less_Less = shift_left
let op_Greater_Greater = shift_right

let op_Hat_Plus = add
let op_Hat_Star = mul
let op_Hat_Slash = div
let op_Hat_Subtraction = sub 
let op_Hat_Less_Less  = shift_left 
let op_Hat_Greater_Greater  = shift_right 
let op_Hat_Amp = logand
let op_Hat_Hat = logxor
let op_Hat_Bar = logor

(* To be realized in ML/C directly *)
assume val eq: x:uint63 -> y:uint63 -> Tot (z:uint63{(v x = v y <==> v z = pow2 63 - 1)
								  /\ (v x <> v y <==> v z = 0)})
assume val gte: x:uint63 -> y:uint63 -> Tot (z:uint63{(v x >= v y <==> v z = pow2 63 - 1)
								  /\ (v x < v y <==> v z = 0)})
