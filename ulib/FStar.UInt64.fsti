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
module FStar.UInt64

(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_int.sh], DO NOT EDIT DIRECTLY ****)

unfold let n = 64

/// For FStar.UIntN.fstp: anything that you fix/update here should be
/// reflected in [FStar.IntN.fstp], which is mostly a copy-paste of
/// this module.
///
/// Except, as compared to [FStar.IntN.fstp], here:
///  - every occurrence of [int_t] has been replaced with [uint_t]
///  - every occurrence of [@%] has been replaced with [%].
///  - some functions (e.g., add_underspec, etc.) are only defined here, not on signed integers

/// This module provides an abstract type for machine integers of a
/// given signedness and width. The interface is designed to be safe
/// with respect to arithmetic underflow and overflow.

/// Note, we have attempted several times to re-design this module to
/// make it more amenable to normalization and to impose less overhead
/// on the SMT solver when reasoning about machine integer
/// arithmetic. The following github issue reports on the current
/// status of that work.
///
/// https://github.com/FStarLang/FStar/issues/1757

open FStar.UInt
open FStar.Mul

#set-options "--max_fuel 0 --max_ifuel 0"

(** Abstract type of machine integers, with an underlying
    representation using a bounded mathematical integer *)
new val t : eqtype

(** A coercion that projects a bounded mathematical integer from a
    machine integer *)
val v (x:t) : Tot (uint_t n)

(** A coercion that injects a bounded mathematical integers into a
    machine integer *)
val uint_to_t (x:uint_t n) : Pure t
  (requires True)
  (ensures (fun y -> v y = x))

(** Injection/projection inverse *)
val uv_inv (x : t) : Lemma
  (ensures (uint_to_t (v x) == x))
  [SMTPat (v x)]

(** Projection/injection inverse *)
val vu_inv (x : uint_t n) : Lemma
  (ensures (v (uint_to_t x) == x))
  [SMTPat (uint_to_t x)]

(** An alternate form of the injectivity of the [v] projection *)
val v_inj (x1 x2: t): Lemma
  (requires (v x1 == v x2))
  (ensures (x1 == x2))

(** Constants 0 and 1 *)
val zero : x:t{v x = 0}

val one : x:t{v x = 1}

(**** Addition primitives *)

(** Bounds-respecting addition

    The precondition enforces that the sum does not overflow,
    expressing the bound as an addition on mathematical integers *)
val add (a:t) (b:t) : Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))

(** Underspecified, possibly overflowing addition:

    The postcondition only enures that the result is the sum of the
    arguments in case there is no overflow *)
val add_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a + v b) n ==> v a + v b = v c))

(** Addition modulo [2^n]

    Machine integers can always be added, but the postcondition is now
    in terms of addition modulo [2^n] on mathematical integers *)
val add_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.add_mod (v a) (v b) = v c))

(**** Subtraction primitives *)


(** Bounds-respecting subtraction

    The precondition enforces that the difference does not underflow,
    expressing the bound as a difference on mathematical integers *)
val sub (a:t) (b:t) : Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))

(** Underspecified, possibly overflowing subtraction:

    The postcondition only enures that the result is the difference of
    the arguments in case there is no underflow *)
val sub_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a - v b) n ==> v a - v b = v c))

(** Subtraction modulo [2^n]

    Machine integers can always be subtractd, but the postcondition is
    now in terms of subtraction modulo [2^n] on mathematical integers *)
val sub_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.sub_mod (v a) (v b) = v c))

(**** Multiplication primitives *)


(** Bounds-respecting multiplication

    The precondition enforces that the product does not overflow,
    expressing the bound as a product on mathematical integers *)
val mul (a:t) (b:t) : Pure t
  (requires (size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))

(** Underspecified, possibly overflowing product

    The postcondition only enures that the result is the product of
    the arguments in case there is no overflow *)
val mul_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a * v b) n ==> v a * v b = v c))

(** Multiplication modulo [2^n]

    Machine integers can always be multiplied, but the postcondition
    is now in terms of product modulo [2^n] on mathematical integers *)
val mul_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mul_mod (v a) (v b) = v c))

(**** Division primitives *)

(** Euclidean division of [a] and [b], with [b] non-zero *)
val div (a:t) (b:t{v b <> 0}) : Pure t
  (requires (True))
  (ensures (fun c -> v a / v b = v c))

(**** Modulo primitives *)

(** Euclidean remainder

    The result is the modulus of [a] with respect to a non-zero [b] *)
val rem (a:t) (b:t{v b <> 0}) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mod (v a) (v b) = v c))

(**** Bitwise operators *)

/// Also see FStar.BV

(** Bitwise logical conjunction *)
val logand (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logand` v y = v z))

(** Bitwise logical exclusive-or *)
val logxor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logxor` v y == v z))

(** Bitwise logical disjunction *)
val logor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logor` v y == v z))

(** Bitwise logical negation *)
val lognot (x:t) : Pure t
  (requires True)
  (ensures (fun z -> lognot (v x) == v z))

(**** Shift operators *)

(** Shift right with zero fill, shifting at most the integer width *)
val shift_right (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.shift_right (v a) (UInt32.v s) = v c))

(** Shift left with zero fill, shifting at most the integer width *)
val shift_left (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.shift_left (v a) (UInt32.v s) = v c))

(**** Comparison operators *)

(** Equality

    Note, it is safe to also use the polymorphic decidable equality
    operator [=] *)
let eq (a:t) (b:t) : Tot bool = eq #n (v a) (v b)

(** Greater than *)
let gt (a:t) (b:t) : Tot bool = gt #n (v a) (v b)

(** Greater than or equal *)
let gte (a:t) (b:t) : Tot bool = gte #n (v a) (v b)

(** Less than *)
let lt (a:t) (b:t) : Tot bool = lt #n (v a) (v b)

(** Less than or equal *)
let lte (a:t) (b:t) : Tot bool = lte #n (v a) (v b)

(** Unary negation *)
inline_for_extraction
let minus (a:t) = add_mod (lognot a) (uint_to_t 1)

(** The maximum shift value for this type, i.e. its width minus one,
    as an UInt32. *)
inline_for_extraction
let n_minus_one = UInt32.uint_to_t (n - 1)

#set-options "--z3rlimit 80 --initial_fuel 1 --max_fuel 1"

(** A constant-time way to compute the equality of
    two machine integers.

    With inspiration from https://git.zx2c4.com/WireGuard/commit/src/crypto/curve25519-hacl64.h?id=2e60bb395c1f589a398ec606d611132ef9ef764b

    Note, the branching on [a=b] is just for proof-purposes.
  *)
[@ CNoInline ]
let eq_mask (a:t) (b:t)
  : Pure t
    (requires True)
    (ensures (fun c -> (v a = v b ==> v c = pow2 n - 1) /\
                       (v a <> v b ==> v c = 0)))
  = let x = logxor a b in
    let minus_x = minus x in
    let x_or_minus_x = logor x minus_x in
    let xnx = shift_right x_or_minus_x n_minus_one in
    let c = sub_mod xnx (uint_to_t 1) in
    if a = b then
    begin
      logxor_self (v a);
      lognot_lemma_1 #n;
      logor_lemma_1 (v x);
      assert (v x = 0 /\ v minus_x = 0 /\
              v x_or_minus_x = 0 /\ v xnx = 0);
      assert (v c = ones n)
    end
    else
    begin
      logxor_neq_nonzero (v a) (v b);
      lemma_msb_pow2 #n (v (lognot x));
      lemma_msb_pow2 #n (v minus_x);
      lemma_minus_zero #n (v x);
      assert (v c = FStar.UInt.zero n)
    end;
    c

private
val lemma_sub_msbs (a:t) (b:t)
    : Lemma ((msb (v a) = msb (v b)) ==> (v a < v b <==> msb (v (sub_mod a b))))

(** A constant-time way to compute the [>=] inequality of
    two machine integers.

    With inspiration from https://git.zx2c4.com/WireGuard/commit/src/crypto/curve25519-hacl64.h?id=0a483a9b431d87eca1b275463c632f8d5551978a
  *)
[@ CNoInline ]
let gte_mask (a:t) (b:t)
  : Pure t
    (requires True)
    (ensures (fun c -> (v a >= v b ==> v c = pow2 n - 1) /\
                       (v a < v b ==> v c = 0)))
  = let x = a in
    let y = b in
    let x_xor_y = logxor x y in
    let x_sub_y = sub_mod x y in
    let x_sub_y_xor_y = logxor x_sub_y y in
    let q = logor x_xor_y x_sub_y_xor_y in
    let x_xor_q = logxor x q in
    let x_xor_q_ = shift_right x_xor_q n_minus_one in
    let c = sub_mod x_xor_q_ (uint_to_t 1) in
    lemma_sub_msbs x y;
    lemma_msb_gte (v x) (v y);
    lemma_msb_gte (v y) (v x);
    c
#reset-options

(*** Infix notations *)
unfold let op_Plus_Hat = add
unfold let op_Plus_Question_Hat = add_underspec
unfold let op_Plus_Percent_Hat = add_mod
unfold let op_Subtraction_Hat = sub
unfold let op_Subtraction_Question_Hat = sub_underspec
unfold let op_Subtraction_Percent_Hat = sub_mod
unfold let op_Star_Hat = mul
unfold let op_Star_Question_Hat = mul_underspec
unfold let op_Star_Percent_Hat = mul_mod
unfold let op_Slash_Hat = div
unfold let op_Percent_Hat = rem
unfold let op_Hat_Hat = logxor
unfold let op_Amp_Hat = logand
unfold let op_Bar_Hat = logor
unfold let op_Less_Less_Hat = shift_left
unfold let op_Greater_Greater_Hat = shift_right
unfold let op_Equals_Hat = eq
unfold let op_Greater_Hat = gt
unfold let op_Greater_Equals_Hat = gte
unfold let op_Less_Hat = lt
unfold let op_Less_Equals_Hat = lte

(**** To input / output constants *)
(** In decimal representation *)
val to_string: t -> Tot string

(** In hex representation (with leading 0x) *)
val to_string_hex: t -> Tot string

(** In fixed-width hex representation (left-padded with zeroes, no leading 0x) *)
val to_string_hex_pad: t -> Tot string

val of_string: string -> Tot t

#set-options "--admit_smt_queries true"
//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verification check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
private
unfold
let __uint_to_t (x:int) : Tot t
    = uint_to_t x
#reset-options
