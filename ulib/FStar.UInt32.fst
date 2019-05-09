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
module FStar.UInt32
(* This module generated automatically using [mk_int.sh] *)

unfold let n = 32

open FStar.UInt
open FStar.Mul

(* NOTE: anything that you fix/update here should be reflected in [FStar.IntN.fstp], which is mostly
 * a copy-paste of this module. *)

(* Except, as compared to [FStar.IntN.fstp], here:
 * - every occurrence of [int_t] has been replaced with [uint_t]
 * - every occurrence of [@%] has been replaced with [%].
 * - some functions (e.g., add_underspec, etc.) are only defined here, not on signed integers
 *)

[@unfold_for_smt]
private
type t' =
  | Mk: v:uint_t n -> t'

let t : eqtype = t'

unfold
let tt (_:t) = True

[@unfold_for_smt]
let v (a:t)
  : Tot (uint_t n)
  = a.v

[@unfold_for_smt]
let uint_to_t (a:uint_t n)
  : Tot t
  = Mk a

[@unfold_for_smt]
let add (a b:t)
  : Pure t
    (requires size (v a + v b) n)
    (ensures tt)
  = Mk (add (v a) (v b))

abstract
let add_underspec (a b:t)
  : Pure t
    (requires True)
    (ensures fun c ->
      size (v a + v b) n ==>
      v a + v b = v c)
 = Mk (add_underspec (v a) (v b))

[@unfold_for_smt]
let add_mod (a b:t)
  : Tot t
  = Mk (add_mod (v a) (v b))

(* Subtraction primitives *)
[@unfold_for_smt]
let sub (a b:t)
  : Pure t
    (requires size (v a - v b) n)
    (ensures tt)
  = Mk (sub (v a) (v b))

abstract
let sub_underspec (a b:t)
  : Pure t
    (requires True)
    (ensures fun c ->
      size (v a - v b) n ==>
      v a - v b = v c)
  = Mk (sub_underspec (v a) (v b))

[@unfold_for_smt]
let sub_mod (a b:t)
  : Tot t
  = Mk (sub_mod (v a) (v b))

(* Multiplication primitives *)
[@unfold_for_smt]
let mul (a b:t)
  : Pure t
    (requires size (v a * v b) n)
    (ensures tt)
  = Mk (mul (v a) (v b))

abstract
let mul_underspec (a b:t)
  : Pure t
    (requires True)
    (ensures fun c ->
      size (v a * v b) n ==>
      v a * v b = v c)
  = Mk (mul_underspec (v a) (v b))

[@unfold_for_smt]
let mul_mod (a b:t)
  : Tot t
  = Mk (mul_mod (v a) (v b))

[@unfold_for_smt]
let mul_div (a b:t)
  : Tot t
  = Mk (mul_div (v a) (v b))

(* Division primitives *)
[@unfold_for_smt]
let div (a b:t)
  : Pure t
    (requires v b <> 0)
    (ensures tt)
  = Mk (div (v a) (v b))

(* Modulo primitives *)
[@unfold_for_smt]
let rem (a b:t)
  : Pure t
    (requires v b <> 0)
    (ensures tt)
  = Mk (mod (v a) (v b))

(* Bitwise operators *)

[@unfold_for_smt]
let logand (a b:t)
  : Tot t
  = Mk (logand (v a) (v b))

[@unfold_for_smt]
let logxor (a b:t)
  : Tot t
  = Mk (logxor (v a) (v b))

[@unfold_for_smt]
let logor (a b:t)
  : Tot t
  = Mk (logor (v a) (v b))

[@unfold_for_smt]
let lognot (a:t)
  : Tot t
  = Mk (lognot (v a))

(* Shift operators *)
[@unfold_for_smt]
let shift_right (a:t) (s:t)
  : Pure t
    (requires v s < n)
    (ensures tt)
  = Mk (shift_right (v a) (v s))

[@unfold_for_smt]
let shift_left (a:t) (s:t)
  : Pure t
    (requires v s < n)
    (ensures tt)
  = Mk (shift_left (v a) (v s))

(* Comparison operators *)
[@unfold_for_smt]
let eq (a b:t)
  : Tot bool
  = a = b

[@unfold_for_smt]
let gt (a b:t)
  : Tot bool
  = gt #n (v a) (v b)

[@unfold_for_smt]
let gte (a b:t)
  : Tot bool
  = gte #n (v a) (v b)

[@unfold_for_smt]
let lt (a b:t)
  : Tot bool
  = lt #n (v a) (v b)

[@unfold_for_smt]
let lte (a b:t)
  : Tot bool
  = lte #n (v a) (v b)

[@unfold_for_smt]
inline_for_extraction
let minus (a:t)
  : Tot t
  = add_mod (lognot a) (uint_to_t 1)

[@unfold_for_smt]
unfold
let n_minus_one
  : t
  = uint_to_t (n - 1)

#push-options "--z3rlimit_factor 10 --initial_fuel 1 --max_fuel 1"
// With inspiration from https://git.zx2c4.com/WireGuard/commit/src/crypto/curve25519-hacl64.h?id=2e60bb395c1f589a398ec606d611132ef9ef764b
let eq_mask (a b:t)
  : Pure t
    (requires True)
    (ensures fun c ->
      (v a = v b ==> v c = pow2 n - 1) /\
      (v a <> v b ==> v c = 0))
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
      assert (v c = zero n)
    end;
    c

private
let lemma_sub_msbs (a b:t)
  : Lemma (msb (v a) = msb (v b) ==>
          (v a < v b <==> msb (v (sub_mod a b))))
  = from_vec_propriety (to_vec (v a)) 1;
    from_vec_propriety (to_vec (v b)) 1;
    from_vec_propriety (to_vec (v (sub_mod a b))) 1

// With inspiration from https://git.zx2c4.com/WireGuard/commit/src/crypto/curve25519-hacl64.h?id=0a483a9b431d87eca1b275463c632f8d5551978a
let gte_mask (a b:t)
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

(* Infix notations *)
unfold let (  +^ ) = add
unfold let ( +?^ ) = add_underspec
unfold let ( +%^ ) = add_mod
unfold let (  -^ ) = sub
unfold let ( -?^ ) = sub_underspec
unfold let ( -%^ ) = sub_mod
unfold let (  *^ ) = mul
unfold let ( *?^ ) = mul_underspec
unfold let ( *%^ ) = mul_mod
unfold let ( */^ ) = mul_div
unfold let (  /^ ) = div
unfold let (  %^ ) = rem
unfold let (  ^^ ) = logxor
unfold let (  &^ ) = logand
unfold let (  |^ ) = logor
unfold let ( <<^ ) = shift_left
unfold let ( >>^ ) = shift_right
unfold let (  =^ ) = op_Equality #t
unfold let (  >^ ) = gt
unfold let ( >=^ ) = gte
unfold let (  <^ ) = lt
unfold let ( <=^ ) = lte

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
let __uint_to_t (a:int)
  : Tot t
  = uint_to_t a
#reset-options
