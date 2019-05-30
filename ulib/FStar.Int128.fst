(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.Int128
(* This module generated automatically using [mk_int.sh] *)

unfold let n = 128

open FStar.Int
open FStar.Mul

#set-options "--max_fuel 0 --max_ifuel 0"

(* NOTE: anything that you fix/update here should be reflected in [FStar.UIntN.fstp], which is mostly
 * a copy-paste of this module. *)

abstract type t :Type0 =
  | Mk: v:int_t n -> t

abstract
let v (x:t) : Tot (int_t n) = x.v

abstract
val int_to_t: x:int_t n -> Pure t
  (requires True)
  (ensures (fun y -> v y = x))
let int_to_t x = Mk x

let uv_inv (x : t) : Lemma
  (ensures (int_to_t (v x) == x))
  [SMTPat (v x)] = ()

let vu_inv (x : int_t n) : Lemma
  (ensures (v (int_to_t x) == x))
  [SMTPat (int_to_t x)] = ()

let v_inj (x1 x2: t): Lemma
  (requires (v x1 == v x2))
  (ensures (x1 == x2))
  = ()

abstract
let add (a:t) (b:t) : Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))
  = Mk (add (v a) (v b))

(* Subtraction primitives *)
abstract
let sub (a:t) (b:t) : Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))
  = Mk (sub (v a) (v b))

(* Multiplication primitives *)
abstract
let mul (a:t) (b:t) : Pure t
  (requires (size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))
  = Mk (mul (v a) (v b))

(* Division primitives *)
abstract
let div (a:t) (b:t{v b <> 0}) : Pure t
  // division overflows on INT_MIN / -1
  (requires (size (v a / v b) n))
  (ensures (fun c -> v a / v b = v c))
  = Mk (div (v a) (v b))

(* Modulo primitives *)
(* If a/b is not representable the result of a%b is undefind *)
abstract
let rem (a:t) (b:t{v b <> 0}) : Pure t
  (requires (size (v a / v b) n))
  (ensures (fun c -> FStar.Int.mod (v a) (v b) = v c))
  = Mk (mod (v a) (v b))

(* Bitwise operators *)
abstract
let logand (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logand` v y = v z))
  = Mk (logand (v x) (v y))

abstract
let logxor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logxor` v y == v z))
  = Mk (logxor (v x) (v y))

abstract
let logor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logor` v y == v z))
  = Mk (logor (v x) (v y))

abstract
let lognot (x:t) : Pure t
  (requires True)
  (ensures (fun z -> lognot (v x) == v z))
  = Mk (lognot (v x))

(* Shift operators *)

(** If a is negative the result is implementation defined *)
abstract
let shift_right (a:t) (s:UInt32.t) : Pure t
  (requires (0 <= v a /\ UInt32.v s < n))
  (ensures (fun c -> FStar.Int.shift_right (v a) (UInt32.v s) = v c))
  = Mk (shift_right (v a) (UInt32.v s))

(** If a is negative the result is undefined behaviour *)
abstract
let shift_left (a:t) (s:UInt32.t) : Pure t
  (requires (0 <= v a /\ UInt32.v s < n))
  (ensures (fun c -> FStar.Int.shift_left (v a) (UInt32.v s) = v c))
  = Mk (shift_left (v a) (UInt32.v s))

abstract
let shift_arithmetic_right (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.Int.shift_arithmetic_right (v a) (UInt32.v s) = v c))
  = Mk (shift_arithmetic_right (v a) (UInt32.v s))

(* Comparison operators *)
let eq (a:t) (b:t) : Tot bool = eq #n (v a) (v b)
let gt (a:t) (b:t) : Tot bool = gt #n (v a) (v b)
let gte (a:t) (b:t) : Tot bool = gte #n (v a) (v b)
let lt (a:t) (b:t) : Tot bool = lt #n (v a) (v b)
let lte (a:t) (b:t) : Tot bool = lte #n (v a) (v b)

(* Infix notations *)
unfold let op_Plus_Hat = add
unfold let op_Subtraction_Hat = sub
unfold let op_Star_Hat = mul
unfold let op_Slash_Hat = div
unfold let op_Percent_Hat = rem
unfold let op_Hat_Hat = logxor
unfold let op_Amp_Hat = logand
unfold let op_Bar_Hat = logor
unfold let op_Less_Less_Hat = shift_left
unfold let op_Greater_Greater_Hat = shift_right
unfold let op_Greater_Greater_Greater_Hat = shift_arithmetic_right
unfold let op_Equals_Hat = eq
unfold let op_Greater_Hat = gt
unfold let op_Greater_Equals_Hat = gte
unfold let op_Less_Hat = lt
unfold let op_Less_Equals_Hat = lte

abstract inline_for_extraction
let ct_abs (a:t{min_int n < v a}) : Tot (b:t{v b = abs (v a)}) =
  let mask = a >>>^ UInt32.uint_to_t (n - 1) in
  if 0 <= v a then
    begin
    sign_bit_positive (v a);
    nth_lemma (v mask) (zero _);
    logxor_lemma_1 (v a)
    end
  else
    begin
    sign_bit_negative (v a);
    nth_lemma (v mask) (ones _);
    logxor_lemma_2 (v a);
    lognot_negative (v a);
    UInt.lemma_lognot_value #n (to_uint (v a))
    end;
  (a ^^ mask) -^ mask

(* To input / output constants *)
assume val to_string: t -> Tot string
assume val of_string: string -> Tot t

#set-options "--lax"
//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verification check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
private
unfold
let __int_to_t (x:int) : Tot t
    = int_to_t x
#reset-options

abstract
val mul_wide: a:Int64.t -> b:Int64.t -> Pure t
  (requires True)
  (ensures (fun c -> v c = Int64.v a * Int64.v b))
let mul_wide a b = 
  assume (size (Int64.v a * Int64.v b) n);
  Mk ((Int64.v a) * (Int64.v b))
