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

(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_int.sh], DO NOT EDIT DIRECTLY ****)

unfold let n = 128

open FStar.Int
open FStar.Mul

(* NOTE: anything that you fix/update here should be reflected in [FStar.UIntN.fstp], which is mostly
 * a copy-paste of this module. *)

new val t : eqtype

val v (x:t) : Tot (int_t n)

let fits (x:int) : prop = Int.fits x n

val int_to_t: x:int_t n -> Pure t
  (requires True)
  (ensures (fun y -> v y = x))

val uv_inv (x : t) : Lemma
  (ensures (int_to_t (v x) == x))
  [SMTPat (v x)]

val vu_inv (x : int_t n) : Lemma
  (ensures (v (int_to_t x) == x))
  [SMTPat (int_to_t x)]

val v_inj (x1 x2: t): Lemma
  (requires (v x1 == v x2))
  (ensures (x1 == x2))

val zero : x:t{v x = 0}

val one : x:t{v x = 1}

val add (a:t) (b:t) : Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))

(* Subtraction primitives *)
val sub (a:t) (b:t) : Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))

(* Multiplication primitives *)
val mul (a:t) (b:t) : Pure t
  (requires (size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))

(* Division primitives *)
val div (a:t) (b:t{v b <> 0}) : Pure t
  // division overflows on INT_MIN / -1
  (requires (size (v a / v b) n))
  (ensures (fun c -> v a / v b = v c))

(* Modulo primitives *)
(* If a/b is not representable the result of a%b is undefind *)
val rem (a:t) (b:t{v b <> 0}) : Pure t
  (requires (size (v a / v b) n))
  (ensures (fun c -> FStar.Int.mod (v a) (v b) = v c))

(* Bitwise operators *)
val logand (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logand` v y = v z))

val logxor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logxor` v y == v z))

val logor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logor` v y == v z))

val lognot (x:t) : Pure t
  (requires True)
  (ensures (fun z -> lognot (v x) == v z))

(* Shift operators *)

(** If a is negative the result is implementation-defined *)
val shift_right (a:t) (s:UInt32.t) : Pure t
  (requires (0 <= v a /\ UInt32.v s < n))
  (ensures (fun c -> FStar.Int.shift_right (v a) (UInt32.v s) = v c))

(** If a is negative or a * pow2 s is not representable the result is undefined *)
val shift_left (a:t) (s:UInt32.t) : Pure t
  (requires (0 <= v a /\ v a * pow2 (UInt32.v s) <= max_int n /\ UInt32.v s < n))
  (ensures (fun c -> FStar.Int.shift_left (v a) (UInt32.v s) = v c))

val shift_arithmetic_right (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.Int.shift_arithmetic_right (v a) (UInt32.v s) = v c))

(* Comparison operators *)
let eq  (a:t) (b:t) : Tot bool = eq  #n (v a) (v b)
let ne  (a:t) (b:t) : Tot bool = ne  #n (v a) (v b)
let gt  (a:t) (b:t) : Tot bool = gt  #n (v a) (v b)
let gte (a:t) (b:t) : Tot bool = gte #n (v a) (v b)
let lt ( a:t) (b:t) : Tot bool = lt  #n (v a) (v b)
let lte (a:t) (b:t) : Tot bool = lte #n (v a) (v b)

(* Infix notations *)
inline_for_extraction unfold let ( +^ )  = add
inline_for_extraction unfold let ( -^ )  = sub
inline_for_extraction unfold let ( *^ )  = mul
inline_for_extraction unfold let ( /^ )  = div
inline_for_extraction unfold let ( %^ )  = rem
inline_for_extraction unfold let ( ^^ )  = logxor
inline_for_extraction unfold let ( &^ )  = logand
inline_for_extraction unfold let ( |^ )  = logor
inline_for_extraction unfold let ( <<^ ) = shift_left
inline_for_extraction unfold let ( >>^ ) = shift_right
inline_for_extraction unfold let ( >>>^) = shift_arithmetic_right
inline_for_extraction unfold let ( =^ )  = eq
inline_for_extraction unfold let ( <>^ ) = ne
inline_for_extraction unfold let ( >^ )  = gt
inline_for_extraction unfold let ( >=^ ) = gte
inline_for_extraction unfold let ( <^ )  = lt
inline_for_extraction unfold let ( <=^ ) = lte

#push-options "--fuel 0 --ifuel 0"
inline_for_extraction
let ct_abs (a:t{min_int n < v a}) : Tot (b:t{v b = abs (v a)}) =
  let mask = a >>>^ UInt32.uint_to_t (n - 1) in
  if 0 <= v a then
    begin
    sign_bit_positive (v a);
    nth_lemma (v mask) (FStar.Int.zero _);
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
#pop-options

(* To input / output constants *)
(* .. in decimal representation *)
val to_string: t -> Tot string

val of_string: string -> Tot t

//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verification check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
[@@admitted]
private
unfold
let __int_to_t (x:int) : t =
  int_to_t x

val mul_wide: a:Int64.t -> b:Int64.t -> Pure t
  (requires True)
  (ensures (fun c -> v c = Int64.v a * Int64.v b))
