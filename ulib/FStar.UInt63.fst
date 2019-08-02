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
module FStar.UInt63
(* This module generated automatically using [mk_int.sh] *)

unfold let n = 63

open FStar.UInt
open FStar.Mul

#set-options "--max_fuel 0 --max_ifuel 0"

(* NOTE: anything that you fix/update here should be reflected in [FStar.UIntN.fstp], which is mostly
 * a copy-paste of this module. *)

(* Except, as compared to [FStar.IntN.fstp], here:
 * - every occurrence of [int_t] has been replaced with [uint_t]
 * - every occurrence of [@%] has been replaced with [%].
 * - some functions (e.g., add_underspec, etc.) are only defined here, not on signed integers
 *)

abstract type t :Type0 =
  | Mk: v:uint_t n -> t

abstract
let v (x:t) : Tot (uint_t n) = x.v

abstract
let uint_to_t (x:uint_t n) : Pure t
  (requires True)
  (ensures (fun y -> v y = x)) = Mk x

let uv_inv (x : t) : Lemma
  (ensures (uint_to_t (v x) == x))
  [SMTPat (v x)] = ()

let vu_inv (x : uint_t n) : Lemma
  (ensures (v (uint_to_t x) == x))
  [SMTPat (uint_to_t x)] = ()

let v_inj (x1 x2: t): Lemma
  (requires (v x1 == v x2))
  (ensures (x1 == x2))
  = ()

abstract
let add (a:t) (b:t) : Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))
  = Mk (add (v a) (v b))

abstract
let add_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a + v b) n ==> v a + v b = v c))
 = Mk (add_underspec (v a) (v b))

abstract
let add_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.add_mod (v a) (v b) = v c))
  = Mk (add_mod (v a) (v b))

(* Subtraction primitives *)
abstract
let sub (a:t) (b:t) : Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))
  = Mk (sub (v a) (v b))

abstract
let sub_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a - v b) n ==> v a - v b = v c))
  = Mk (sub_underspec (v a) (v b))

abstract
let sub_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.sub_mod (v a) (v b) = v c))
  = Mk (sub_mod (v a) (v b))

(* Multiplication primitives *)
abstract
let mul (a:t) (b:t) : Pure t
  (requires (size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))
  = Mk (mul (v a) (v b))

abstract
let mul_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a * v b) n ==> v a * v b = v c))
   = Mk (mul_underspec (v a) (v b))

abstract
let mul_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mul_mod (v a) (v b) = v c))
  = Mk (mul_mod (v a) (v b))

abstract
let mul_div (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mul_div (v a) (v b) = v c))
  = Mk (mul_div (v a) (v b))

(* Division primitives *)
abstract
let div (a:t) (b:t{v b <> 0}) : Pure t
  (requires (True))
  (ensures (fun c -> v a / v b = v c))
  = Mk (div (v a) (v b))

(* Modulo primitives *)
abstract
let rem (a:t) (b:t{v b <> 0}) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mod (v a) (v b) = v c))
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
abstract
let shift_right (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.shift_right (v a) (UInt32.v s) = v c))
  = Mk (shift_right (v a) (UInt32.v s))

abstract
let shift_left (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.shift_left (v a) (UInt32.v s) = v c))
  = Mk (shift_left (v a) (UInt32.v s))

(* Comparison operators *)
let eq (a:t) (b:t) : Tot bool = eq #n (v a) (v b)
let gt (a:t) (b:t) : Tot bool = gt #n (v a) (v b)
let gte (a:t) (b:t) : Tot bool = gte #n (v a) (v b)
let lt (a:t) (b:t) : Tot bool = lt #n (v a) (v b)
let lte (a:t) (b:t) : Tot bool = lte #n (v a) (v b)

inline_for_extraction
let minus (a:t) = add_mod (lognot a) (uint_to_t 1)

inline_for_extraction
let n_minus_one = UInt32.uint_to_t (n - 1)

#set-options "--z3rlimit 80 --initial_fuel 1 --max_fuel 1"
// With inspiration from https://git.zx2c4.com/WireGuard/commit/src/crypto/curve25519-hacl64.h?id=2e60bb395c1f589a398ec606d611132ef9ef764b
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
      assert (v c = zero n)
    end;
    c

private
let lemma_sub_msbs (a:t) (b:t)
  : Lemma ((msb (v a) = msb (v b)) ==> (v a < v b <==> msb (v (sub_mod a b))))
  = from_vec_propriety (to_vec (v a)) 1;
    from_vec_propriety (to_vec (v b)) 1;
    from_vec_propriety (to_vec (v (sub_mod a b))) 1

// With inspiration from https://git.zx2c4.com/WireGuard/commit/src/crypto/curve25519-hacl64.h?id=0a483a9b431d87eca1b275463c632f8d5551978a
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

(* Infix notations *)
unfold let op_Plus_Hat = add
unfold let op_Plus_Question_Hat = add_underspec
unfold let op_Plus_Percent_Hat = add_mod
unfold let op_Subtraction_Hat = sub
unfold let op_Subtraction_Question_Hat = sub_underspec
unfold let op_Subtraction_Percent_Hat = sub_mod
unfold let op_Star_Hat = mul
unfold let op_Star_Question_Hat = mul_underspec
unfold let op_Star_Percent_Hat = mul_mod
unfold let op_Star_Slash_Hat = mul_div
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
let __uint_to_t (x:int) : Tot t
    = uint_to_t x
#reset-options
