(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module SInt.UInt8

(* Defines secret bytes *)

open FStar.Ghost
open Axioms
open IntLib
open SInt

let n = 8 

type uint8 = usint n
type sbyte = uint8

let (zero:uint8) = uzero n
let (one:uint8) = uone n
let (ones:uint8) = uones n

let (max_int:erased nat) = eumax_int #n
let (min_int:erased nat) = eumin_int #n

let (bits:pos) = n

(* Standard operators *)
val add: a:uint8 -> b:uint8{v a + v b < pow2 n} -> Tot uint8
val add_mod: a:uint8 -> b:uint8 -> Tot uint8
val sub: a:uint8 -> b:uint8{v a - v b >= 0} -> Tot uint8
val sub_mod: a:uint8 -> b:uint8 -> Tot uint8
val mul: a:uint8 -> b:uint8{v a * v b < pow2 n} -> Tot uint8
val mul_mod: a:uint8 -> b:uint8 -> Tot uint8
val div: a:uint8 -> b:uint8{v b <> 0} -> Tot uint8
val rem: a:uint8 -> b:uint8{v b <> 0} -> Tot uint8
val logand: uint8 -> uint8 -> Tot uint8
val logxor: uint8 -> uint8 -> Tot uint8
val logor: uint8 -> uint8 -> Tot uint8
val lognot: uint8 -> Tot uint8
val shift_right: a:uint8 -> s:nat -> Tot uint8
val shift_left: a:uint8 -> s:nat -> Tot uint8
val rotate_left: a:uint8 -> s:nat{s <= n} -> Tot uint8
val rotate_right: a:uint8 -> s:nat{s <= n} -> Tot uint8
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

let to_uint8 s = to_usint n s
let of_native_int s = to_usint n s

assume val of_string: string -> Tot uint8
assume val of_int: x:nat{x >= 0 /\ x < pow2 n} -> Tot (y:uint8{v y = x})
(* TODO: port to libraries *)
type uint32 = UInt32.t
assume val of_uint32: x:uint32{UInt32.v x < 256} -> Tot uint8

let op_Hat_Plus = add
let op_Hat_Plus_Percent = add_mod
let op_Hat_Star = mul
let op_Hat_Star_Percent = mul_mod
let op_Hat_Slash = div
let op_Hat_Subtraction = sub 
let op_Hat_Subtraction_Percent = sub_mod
let op_Hat_Less_Less  = shift_left 
let op_Hat_Greater_Greater  = shift_right 
let op_Less_Less_Less = rotate_left
let op_Greater_Greater_Greater = rotate_right
let op_Hat_Amp = logand
let op_Hat_Hat = logxor
let op_Hat_Bar = logor

assume val eq: x:uint8 -> y:uint8 -> Tot (z:uint8{(v x = v y <==> v z = pow2 8 - 1)
								  /\ (v x <> v y <==> v z = 0)})
assume val gte: x:uint8 -> y:uint8 -> Tot (z:uint8{(v x >= v y <==> v z = pow2 8 - 1)
								  /\ (v x < v y <==> v z = 0)})
