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
module FStar.UInt128

open FStar.UInt
open FStar.Mul

module U32 = FStar.UInt32
module U64 = FStar.UInt64

noextract
let n = 128

val t: (x:Type0{hasEq x})

[@@ noextract_to "krml"]
val v (x:t) : Tot (uint_t n)

[@@ noextract_to "krml"]
val uint_to_t: x:uint_t n -> Pure t
  (requires True)
  (ensures (fun y -> v y = x))

val v_inj (x1 x2: t): Lemma (requires (v x1 == v x2)) (ensures (x1 == x2))

val add: a:t -> b:t -> Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))

val add_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    size (v a + v b) n ==> v a + v b = v c))

val add_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a + v b) % pow2 n = v c))

(* Subtraction primitives *)
val sub: a:t -> b:t -> Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))

val sub_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    size (v a - v b) n ==> v a - v b = v c))

val sub_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a - v b) % pow2 n = v c))

(* Bitwise operators *)
val logand: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun r -> v r == logand (v a) (v b)))

val logxor: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun r -> v r == logxor (v a) (v b)))

val logor: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun r -> v r == logor (v a) (v b)))

val lognot: a:t -> Pure t
  (requires True)
  (ensures (fun r -> v r == lognot (v a)))

//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verifiation check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
private
unfold
let __uint_to_t (x:int) : Tot t =
      assume (fits x 128);
      uint_to_t x


(* Shift operators *)
val shift_left: a:t -> s:UInt32.t -> Pure t
  (requires (U32.v s < n))
  (ensures (fun c -> v c = ((v a * pow2 (UInt32.v s)) % pow2 n)))

val shift_right: a:t -> s:UInt32.t -> Pure t
  (requires (U32.v s < n))
  (ensures (fun c -> v c = (v a / (pow2 (UInt32.v s)))))

(* Comparison operators *)

val eq (a:t) (b:t) : Pure bool
  (requires True)
  (ensures (fun r -> r == eq #n (v a) (v b)))

val gt (a:t) (b:t) : Pure bool
  (requires True)
  (ensures (fun r -> r == gt #n (v a) (v b)))

val lt (a:t) (b:t) : Pure bool
  (requires True)
  (ensures (fun r -> r == lt #n (v a) (v b)))

val gte (a:t) (b:t) : Pure bool
  (requires True)
  (ensures (fun r -> r == gte #n (v a) (v b)))

val lte (a:t) (b:t) : Pure bool
  (requires True)
  (ensures (fun r -> r == lte #n (v a) (v b)))

val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})

val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})

(* Casts *)
val uint64_to_uint128: a:U64.t -> b:t{v b == U64.v a}
val uint128_to_uint64: a:t -> b:U64.t{U64.v b == v a % pow2 64}

(* To input / output constants *)
(* TODO: assume these without implementations *)
//val to_string: t -> Tot string
//val of_string: string -> Tot t

(* Infix notations *)
inline_for_extraction noextract let op_Plus_Hat = add
inline_for_extraction noextract let op_Plus_Question_Hat = add_underspec
inline_for_extraction noextract let op_Plus_Percent_Hat = add_mod
inline_for_extraction noextract let op_Subtraction_Hat = sub
inline_for_extraction noextract let op_Subtraction_Question_Hat = sub_underspec
inline_for_extraction noextract let op_Subtraction_Percent_Hat = sub_mod
inline_for_extraction noextract let op_Amp_Hat = logand
inline_for_extraction noextract let op_Hat_Hat = logxor
inline_for_extraction noextract let op_Bar_Hat = logor
inline_for_extraction noextract let op_Less_Less_Hat = shift_left
inline_for_extraction noextract let op_Greater_Greater_Hat = shift_right
inline_for_extraction noextract let op_Equals_Hat = eq
inline_for_extraction noextract let op_Greater_Hat = gt
inline_for_extraction noextract let op_Less_Hat = lt
inline_for_extraction noextract let op_Greater_Equals_Hat = gte
inline_for_extraction noextract let op_Less_Equals_Hat = lte

(* Multiplication primitives *)
(* Note that unlike UIntN, we do not provide uint128 * uint128 primitives (mul,
  mul_underspec, mul_mod, and mul_div) *)
val mul32: x:U64.t -> y:U32.t -> Pure t
  (requires True)
  (ensures (fun r -> v r == U64.v x * U32.v y))

val mul_wide: x:U64.t -> y:U64.t -> Pure t
  (requires True)
  (ensures (fun r -> v r == U64.v x * U64.v y))
