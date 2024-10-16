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
module FStar.Int

(* NOTE: anything that you fix/update here should be reflected in [FStar.UInt.fsti], which is mostly
 * a copy-paste of this module. *)

open FStar.Mul
open FStar.BitVector
open FStar.Math.Lemmas

val pow2_values: x:nat -> Lemma
  (let p = pow2 x in
   match x with
   | 0  -> p=1
   | 1  -> p=2
   | 8  -> p=256
   | 16 -> p=65536
   | 31 -> p=2147483648
   | 32 -> p=4294967296
   | 63 -> p=9223372036854775808
   | 64 -> p=18446744073709551616
   | _  -> True)
  [SMTPat (pow2 x)]

/// Specs

let max_int (n:pos) : Tot int = pow2 (n-1) - 1
let min_int (n:pos) : Tot int = - (pow2 (n-1))

let fits (x:int) (n:pos) : Tot bool = min_int n <= x && x <= max_int n
let size (x:int) (n:pos) : Tot Type0 = b2t(fits x n)

(* Machine integer type *)
type int_t (n:pos) = x:int{size x n}

/// Multiplicative operator semantics, see C11 6.5.5

(* Truncation towards zero division *)
let op_Slash (a:int) (b:int{b <> 0}) : Tot int = 
  if (a >= 0 && b < 0) || (a < 0 && b >= 0) then - (abs a / abs b)
  else abs a / abs b

(* Wrap-around modulo: wraps into [-p/2; p/2[ *)
let op_At_Percent (v:int) (p:int{p>0/\ p%2=0}) : Tot int =
  let m = v % p in if m >= p/2 then m - p else m

/// Constants

let zero (n:pos) : Tot (int_t n) = 0

#push-options "--initial_fuel 1 --max_fuel 1"

let pow2_n (#n:pos) (p:nat{p < n-1}) : Tot (int_t n) =
  pow2_le_compat (n - 2) p; pow2 p

let pow2_minus_one (#n:pos{1 < n}) (m:nat{m < n}) : Tot (int_t n) =
  pow2_le_compat (n - 1) m;
  pow2 m - 1 

let one (n:pos{1 < n}) : Tot (int_t n) = 1

#pop-options

let ones (n:pos) : Tot (int_t n) = -1

(* Increment and decrement *)
let incr (#n:pos) (a:int_t n)
    : Pure (int_t n)
      (requires (b2t (a < max_int n))) (ensures (fun _ -> True))
  = a + 1

let decr (#n:pos) (a:int_t n)
    : Pure (int_t n)
      (requires (b2t (a > min_int n))) (ensures (fun _ -> True))
  = a - 1

val incr_underspec: #n:pos -> a:int_t n -> Pure (int_t n)
  (requires (b2t (a < max_int n)))
  (ensures (fun b -> a + 1 = b))

val decr_underspec: #n:pos -> a:int_t n -> Pure (int_t n)
  (requires (b2t (a > min_int n)))
  (ensures (fun b -> a - 1 = b))

let incr_mod (#n:pos) (a:int_t n) : Tot (int_t n) =
  (a + 1) % (pow2 (n-1))

let decr_mod (#n:pos) (a:int_t n) : Tot (int_t n) =
  (a - 1) % (pow2 (n-1))

(* Addition primitives *)
let add (#n:pos) (a:int_t n) (b:int_t n)
    : Pure (int_t n)
      (requires (size (a + b) n))
      (ensures (fun _ -> True))
  = a + b

val add_underspec: #n:pos -> a:int_t n -> b:int_t n -> Pure (int_t n)
  (requires True)
  (ensures (fun c ->
    size (a + b) n ==> a + b = c))

#push-options "--initial_fuel 1 --max_fuel 1"

let add_mod (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  (a + b) @% (pow2 n)

(* Subtraction primitives *)
let sub (#n:pos) (a:int_t n) (b:int_t n)
    : Pure (int_t n)
      (requires (size (a - b) n))
      (ensures (fun _ -> True))    
  = a - b

val sub_underspec: #n:pos -> a:int_t n -> b:int_t n -> Pure (int_t n)
  (requires True)
  (ensures (fun c ->
    size (a - b) n ==> a - b = c))

let sub_mod (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  (a - b) @% (pow2 n)

(* Multiplication primitives *)
let mul (#n:pos) (a:int_t n) (b:int_t n)
    : Pure (int_t n)
      (requires (size (a * b) n))
      (ensures (fun _ -> True))
  = a * b

val mul_underspec: #n:pos -> a:int_t n -> b:int_t n -> Pure (int_t n)
  (requires True)
  (ensures (fun c ->
    size (a * b) n ==> a * b = c))

let mul_mod (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  (a * b) @% (pow2 n)

#pop-options

(* Division primitives *)
let div (#n:pos) (a:int_t n) (b:int_t n{b <> 0})
    : Pure (int_t n)
      (requires (size (a / b) n))
      (ensures (fun c -> b <> 0 ==> a / b = c))
= a / b

val div_underspec: #n:pos -> a:int_t n -> b:int_t n{b <> 0} -> Pure (int_t n)
  (requires True)
  (ensures (fun c ->
    (b <> 0 /\ size (a / b) n) ==> a / b = c))

val div_size: #n:pos -> a:int_t n{min_int n < a} -> b:int_t n{b <> 0} ->
  Lemma (requires (size a n)) (ensures (size (a / b) n))

let udiv (#n:pos) (a:int_t n{min_int n < a}) (b:int_t n{b <> 0})
    : Tot (c:int_t n{b <> 0 ==> a / b = c})
  = div_size #n a b;
    a / b


(* Modulo primitives *)
let mod (#n:pos) (a:int_t n) (b:int_t n{b <> 0}) : Tot (int_t n) =
  a - ((a/b) * b)

(* Comparison operators *)
let eq #n (a:int_t n) (b:int_t n) : Tot bool = a = b
let gt #n (a:int_t n) (b:int_t n) : Tot bool = a > b
let gte #n (a:int_t n) (b:int_t n) : Tot bool = a >= b
let lt #n (a:int_t n) (b:int_t n) : Tot bool = a < b
let lte #n (a:int_t n) (b:int_t n) : Tot bool = a <= b

/// Casts

let to_uint (#n:pos) (x:int_t n) : Tot (UInt.uint_t n) = 
  if 0 <= x then x else x + pow2 n 

let from_uint (#n:pos) (x:UInt.uint_t n) : Tot (int_t n) = 
  if x <= max_int n then x else x - pow2 n 

val to_uint_injective: #n:pos -> x:int_t n
  -> Lemma (ensures from_uint (to_uint x) == x) [SMTPat (to_uint x)]

let to_int_t (m:pos) (a:int) : Tot (int_t m) = a @% pow2 m

open FStar.Seq

(* WARNING: Mind the big endian vs little endian definition *)

let to_vec (#n:pos) (num:int_t n) : Tot (bv_t n) =
  UInt.to_vec (to_uint num)

let from_vec (#n:pos) (vec:bv_t n) : Tot (int_t n) =
  let x = UInt.from_vec vec in
  if max_int n < x then x - pow2 n else x

val to_vec_lemma_1: #n:pos -> a:int_t n -> b:int_t n ->
  Lemma (requires a = b) (ensures equal (to_vec a) (to_vec b))

val to_vec_lemma_2: #n:pos -> a:int_t n -> b:int_t n ->
  Lemma (requires equal (to_vec a) (to_vec b)) (ensures a = b)

val inverse_aux: #n:nat -> vec:bv_t n -> i:nat{i < n} ->
  Lemma (requires True) (ensures index vec i = index (to_vec (from_vec vec)) i)
        [SMTPat (index (to_vec (from_vec vec)) i)]

val inverse_vec_lemma: #n:pos -> vec:bv_t n ->
  Lemma (requires True) (ensures equal vec (to_vec (from_vec vec)))
        [SMTPat (to_vec (from_vec vec))]

val inverse_num_lemma: #n:pos -> num:int_t n ->
  Lemma (requires True) (ensures num = from_vec (to_vec num))
        [SMTPat (from_vec (to_vec num))]

val from_vec_lemma_1: #n:pos -> a:bv_t n -> b:bv_t n ->
  Lemma (requires equal a b) (ensures from_vec a = from_vec b)

val from_vec_lemma_2: #n:pos -> a:bv_t n -> b:bv_t n ->
  Lemma (requires from_vec a = from_vec b) (ensures equal a b)

(* Relations between constants in BitVector and in UInt. *)
val zero_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures index (to_vec (zero n)) i = index (zero_vec #n) i)
        [SMTPat (index (to_vec (zero n)) i)]

val zero_from_vec_lemma: #n:pos ->
  Lemma (requires True) (ensures from_vec (zero_vec #n) = zero n)
        [SMTPat (from_vec (zero_vec #n))]

val one_to_vec_lemma: #n:pos{1 < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (one n)) i = index (elem_vec #n (n - 1)) i)
	[SMTPat (index (to_vec (one n)) i)]

val pow2_to_vec_lemma: #n:pos -> p:nat{p < n-1} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (pow2_n #n p)) i = index (elem_vec #n (n - p - 1)) i)
	[SMTPat (index (to_vec (pow2_n #n p)) i)]

val pow2_from_vec_lemma: #n:pos -> p:pos{p < n-1} ->
  Lemma (requires True) (ensures from_vec (elem_vec #n p) = pow2_n #n (n - p - 1))
        [SMTPat (from_vec (elem_vec #n p))]

val ones_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (ones n)) i = index (ones_vec #n) i)
	[SMTPat (index (to_vec (ones n)) i)]

val ones_from_vec_lemma: #n:pos ->
  Lemma (requires True) (ensures from_vec (ones_vec #n) = ones n)
        [SMTPat (from_vec (ones_vec #n))]


(* (nth a i) returns a boolean indicating the i-th bit of a. *)
let nth (#n:pos) (a:int_t n) (i:nat{i < n}) : Tot bool = index (to_vec #n a) i

val nth_lemma: #n:pos -> a:int_t n -> b:int_t n ->
  Lemma (requires forall (i:nat{i < n}). nth a i = nth b i)
        (ensures a = b)

(* Lemmas for constants *)
val zero_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures nth (zero n) i = false)
        [SMTPat (nth (zero n) i)]

val one_nth_lemma: #n:pos{1 < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = n - 1 ==> nth (one n) i = true) /\
	         (i < n - 1 ==> nth (one n) i = false))
        [SMTPat (nth (one n) i)]

val ones_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures (nth (ones n) i) = true)
        [SMTPat (nth (ones n) i)]

(* Bitwise operators *)
let logand (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  from_vec #n (logand_vec #n (to_vec #n a) (to_vec #n b))

let logxor (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  from_vec #n (logxor_vec #n (to_vec #n a) (to_vec #n b))

let logor (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  from_vec #n (logor_vec #n (to_vec #n a) (to_vec #n b))

let lognot (#n:pos) (a:int_t n) : Tot (int_t n)=
  from_vec #n (lognot_vec #n (to_vec #n a))

(* Bitwise operators definitions *)
val logand_definition: #n:pos -> a:int_t n -> b:int_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logand a b) i = (nth a i && nth b i)))
	[SMTPat (nth (logand a b) i)]

val logxor_definition: #n:pos -> a:int_t n -> b:int_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logxor a b) i = (nth a i <> nth b i)))
	[SMTPat (nth (logxor a b) i)]

val logor_definition: #n:pos -> a:int_t n -> b:int_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logor a b) i = (nth a i || nth b i)))
	[SMTPat (nth (logor a b) i)]

val lognot_definition: #n:pos -> a:int_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (lognot a) i = not(nth a i)))
	[SMTPat (nth (lognot a) i)]

(* Two's complement unary minus *)
inline_for_extraction
let minus (#n:pos{1 < n}) (a:int_t n) : Tot (int_t n) =
  add_mod (lognot a) 1

(* Bitwise operators lemmas *)
(* TODO: lemmas about the relations between different operators *)
(* Bitwise AND operator *)
val logand_commutative: #n:pos -> a:int_t n -> b:int_t n ->
  Lemma (requires True) (ensures (logand #n a b = logand #n b a))

val logand_associative: #n:pos -> a:int_t n -> b:int_t n -> c:int_t n ->
  Lemma (logand #n (logand #n a b) c = logand #n a (logand #n b c))

val logand_self: #n:pos -> a:int_t n ->
  Lemma (logand #n a a = a)

val logand_lemma_1: #n:pos -> a:int_t n ->
  Lemma (requires True) (ensures (logand #n a (zero n) = zero n))

val logand_lemma_2: #n:pos -> a:int_t n ->
  Lemma (logand #n a (ones n) = a)

val sign_bit_negative: #n:pos{1 < n} -> a:int_t n -> 
  Lemma (nth a 0 = true <==> a < 0)

val sign_bit_positive: #n:pos{1 < n} -> a:int_t n -> 
  Lemma (nth a 0 = false <==> 0 <= a)

val logand_pos_le: #n:pos{1 < n} -> a:int_t n{0 <= a} -> b:int_t n{0 <= b} ->
  Lemma (0 <= logand a b /\ logand a b <= a /\ logand a b <= b)

val logand_pow2_minus_one: #n:pos{1 < n} -> a:int_t n -> m:pos{m < n} ->
  Lemma (0 <= logand a (pow2_minus_one m) /\ 
    logand a (pow2_minus_one m) <= pow2_minus_one #n m)

val logand_max: #n:pos{1 < n} -> a:int_t n{0 <= a} ->
  Lemma (0 <= logand a (max_int n) /\ a = logand a (max_int n))

(* Bitwise XOR operator *)
val logxor_commutative: #n:pos -> a:int_t n -> b:int_t n ->
  Lemma (requires True) (ensures (logxor #n a b = logxor #n b a))

val logxor_associative: #n:pos -> a:int_t n -> b:int_t n -> c:int_t n ->
  Lemma (requires True) (ensures (logxor #n (logxor #n a b) c = logxor #n a (logxor #n b c)))

val logxor_self: #n:pos -> a:int_t n ->
  Lemma (requires True) (ensures (logxor #n a a = zero n))

val logxor_lemma_1: #n:pos -> a:int_t n ->
  Lemma (requires True) (ensures (logxor #n a (zero n) = a))

val logxor_lemma_2: #n:pos -> a:int_t n ->
  Lemma (requires True) (ensures (logxor #n a (ones n) = lognot #n a))

val logxor_inv: #n:pos -> a:int_t n -> b:int_t n -> Lemma
  (a = logxor #n (logxor #n a b) b)

val logxor_neq_nonzero: #n:pos -> a:int_t n -> b:int_t n -> Lemma
   (a <> b ==> logxor a b <> 0)

val lognot_negative: #n:pos -> a:int_t n -> Lemma
  (requires a < 0)
  (ensures  lognot a == UInt.lognot #n (a + pow2 n))

(* Shift operators *)

(** If a is negative the result is undefined behaviour *)
let shift_left (#n:pos) (a:int_t n{0 <= a}) (s:nat) : Tot (int_t n) =
  from_vec (shift_left_vec #n (to_vec #n a) s)

(** If a is negative the result is implementation defined *)
let shift_right (#n:pos) (a:int_t n{0 <= a}) (s:nat) : Tot (int_t n) =
  from_vec (shift_right_vec #n (to_vec #n a) s)

let shift_arithmetic_right (#n:pos) (a:int_t n) (s:nat) : Tot (int_t n) =
  from_vec (shift_arithmetic_right_vec #n (to_vec #n a) s)

(* Shift operators lemmas *)
val shift_left_lemma_1: #n:pos -> a:int_t n{0 <= a} -> s:nat -> i:nat{i < n && i >= n - s} ->
  Lemma (requires True)
	(ensures (nth (shift_left #n a s) i = false))
	[SMTPat (nth (shift_left #n a s) i)]

val shift_left_lemma_2: #n:pos -> a:int_t n{0 <= a} -> s:nat -> i:nat{i < n && i < n - s} ->
  Lemma (requires True)
        (ensures (nth (shift_left #n a s) i = nth #n a (i + s)))
	[SMTPat (nth (shift_left #n a s) i)]

val shift_left_value_lemma: #n:pos -> a:int_t n{0 <= a} -> s:nat ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) @% pow2 n)
	[SMTPat (shift_left #n a s)]

val shift_right_lemma_1: #n:pos -> a:int_t n{0 <= a} -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (requires True)
	(ensures (nth (shift_right #n a s) i = false))
	[SMTPat (nth (shift_right #n a s) i)]

val shift_right_lemma_2: #n:pos -> a:int_t n{0 <= a} -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma (requires True)
        (ensures (nth (shift_right #n a s) i = nth #n a (i - s)))
	[SMTPat (nth (shift_right #n a s) i)]

val shift_arithmetic_right_lemma_1: #n:pos -> a:int_t n -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (requires True)
	(ensures (nth (shift_arithmetic_right #n a s) i = nth a 0))
	[SMTPat (nth (shift_arithmetic_right #n a s) i)]

val shift_arithmetic_right_lemma_2: #n:pos -> a:int_t n -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma (requires True)
        (ensures (nth (shift_arithmetic_right #n a s) i = nth #n a (i - s)))
	[SMTPat (nth (shift_arithmetic_right #n a s) i)]
