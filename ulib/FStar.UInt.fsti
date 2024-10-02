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
module FStar.UInt

(* NOTE: anything that you fix/update here should be reflected in [FStar.Int.fsti], which is mostly
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
   | 128 -> p=0x100000000000000000000000000000000
   | _  -> True)
  [SMTPat (pow2 x)]

/// Specs
///
/// Note: lacking any type of functors for F*, this is a copy/paste of [FStar.Int.fst], where the relevant bits that changed are:
///  - definition of max and min
///  - use of regular integer modulus instead of wrap-around modulus

let max_int (n:nat) : Tot int = pow2 n - 1
let min_int (n:nat) : Tot int = 0

let fits (x:int) (n:nat) : Tot bool = min_int n <= x && x <= max_int n
let size (x:int) (n:nat) : Tot Type0 = b2t(fits x n)

(* Machine integer type *)
[@@do_not_unrefine]
type uint_t (n:nat) = x:int{size x n}

/// Constants

let zero (n:nat) : Tot (uint_t n) = 0

let pow2_n (#n:pos) (p:nat{p < n}) : Tot (uint_t n) =
  pow2_le_compat (n - 1) p; pow2 p

let one (n:pos) : Tot (uint_t n) = 1

let ones (n:nat) : Tot (uint_t n) = max_int n

(* Increment and decrement *)
let incr (#n:nat) (a:uint_t n) : Pure (uint_t n)
  (requires (b2t (a < max_int n))) (ensures (fun _ -> True))
  = a + 1

let decr (#n:nat) (a:uint_t n) : Pure (uint_t n)
  (requires (b2t (a > min_int n))) (ensures (fun _ -> True))
  = a - 1

val incr_underspec: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a < max_int n)))
  (ensures (fun b -> a + 1 = b))

val decr_underspec: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a > min_int n)))
  (ensures (fun b -> a - 1 = b))

let incr_mod (#n:nat) (a:uint_t n) : Tot (uint_t n) = (a + 1) % (pow2 n)

let decr_mod (#n:nat) (a:uint_t n) : Tot (uint_t n) = (a - 1) % (pow2 n)

(* Addition primitives *)
let add (#n:nat) (a:uint_t n) (b:uint_t n) : Pure (uint_t n)
  (requires (size (a + b) n))
  (ensures (fun _ -> True))
  =  a + b

val add_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a + b) n ==> a + b = c))

let add_mod (#n:nat) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  (a + b) % (pow2 n)

(* Subtraction primitives *)
let sub (#n:nat) (a:uint_t n) (b:uint_t n) : Pure (uint_t n)
  (requires (size (a - b) n))
  (ensures (fun _ -> True))
  = a - b

val sub_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a - b) n ==> a - b = c))

let sub_mod (#n:nat) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  (a - b) % (pow2 n)

(* Multiplication primitives *)
let mul (#n:nat) (a:uint_t n) (b:uint_t n) : Pure (uint_t n)
  (requires (size (a * b) n))
  (ensures (fun _ -> True))
  = a * b

val mul_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a * b) n ==> a * b = c))

let mul_mod (#n:nat) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  (a * b) % (pow2 n)

private
val lt_square_div_lt (a:nat) (b:pos) : Lemma
  (requires (a < b * b))
  (ensures (a / b < b))

#push-options "--fuel 0 --ifuel 0"
let mul_div (#n:nat) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  FStar.Math.Lemmas.lemma_mult_lt_sqr a b (pow2 n);
  lt_square_div_lt (a * b) (pow2 n);
  (a * b) / (pow2 n)
#pop-options

(* Division primitives *)
let div (#n:nat) (a:uint_t n) (b:uint_t n{b <> 0}) : Pure (uint_t n)
  (requires (size (a / b) n))
  (ensures (fun c -> b <> 0 ==> a / b = c))
  = a / b

val div_underspec: #n:nat -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    (b <> 0 /\ size (a / b) n) ==> a / b = c))

val div_size: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} ->
  Lemma (requires (size a n)) (ensures (size (a / b) n))

let udiv (#n:pos) (a:uint_t n) (b:uint_t n{b <> 0}) : Tot (c:uint_t n{b <> 0 ==> a / b = c}) =
  div_size #n a b;
  a / b


(* Modulo primitives *)
let mod (#n:nat) (a:uint_t n) (b:uint_t n{b <> 0}) : Tot (uint_t n) =
  a - ((a/b) * b)

(* Comparison operators *)
let eq #n (a:uint_t n) (b:uint_t n) : Tot bool = (a = b)
let gt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a > b)
let gte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a >= b)
let lt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a < b)
let lte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a <= b)

/// Casts

let to_uint_t (m:nat) (a:int) : Tot (uint_t m) = a % pow2 m

open FStar.Seq.Base

(* WARNING: Mind the big endian vs little endian definition *)

(* Casts *)
let rec to_vec (#n:nat) (num:uint_t n) : Tot (bv_t n) =
  if n = 0 then empty #bool
  else append (to_vec #(n - 1) (num / 2)) (create 1 (num % 2 = 1))

let rec from_vec (#n:nat) (vec:bv_t n) : Tot (uint_t n) =
  if n = 0 then 0
  else 2 * from_vec #(n - 1) (slice vec 0 (n - 1)) + (if index vec (n - 1) then 1 else 0)

val to_vec_lemma_1: #n:nat -> a:uint_t n -> b:uint_t n ->
  Lemma (requires a = b) (ensures equal (to_vec a) (to_vec b))

val to_vec_lemma_2: #n:nat -> a:uint_t n -> b:uint_t n ->
  Lemma (requires equal (to_vec a) (to_vec b)) (ensures a = b)

val inverse_aux: #n:nat -> vec:bv_t n -> i:nat{i < n} ->
  Lemma (requires True) (ensures index vec i = index (to_vec (from_vec vec)) i)
        [SMTPat (index (to_vec (from_vec vec)) i)]

val inverse_vec_lemma: #n:nat -> vec:bv_t n ->
  Lemma (requires True) (ensures equal vec (to_vec (from_vec vec)))
        [SMTPat (to_vec (from_vec vec))]

val inverse_num_lemma: #n:nat -> num:uint_t n ->
  Lemma (requires True) (ensures num = from_vec (to_vec num))
        [SMTPat (from_vec (to_vec num))]

val from_vec_lemma_1: #n:nat -> a:bv_t n -> b:bv_t n ->
  Lemma (requires equal a b) (ensures from_vec a = from_vec b)

val from_vec_lemma_2: #n:nat -> a:bv_t n -> b:bv_t n ->
  Lemma (requires from_vec a = from_vec b) (ensures equal a b)

val from_vec_aux: #n:nat -> a:bv_t n -> s1:nat{s1 < n} -> s2:nat{s2 < s1} ->
  Lemma (requires True)
        (ensures (from_vec #s2 (slice a 0 s2)) * pow2 (n - s2) + (from_vec #(s1 - s2) (slice a s2 s1)) * pow2 (n - s1) + (from_vec #(n - s1) (slice a s1 n)) = ((from_vec #s2 (slice a 0 s2)) * pow2 (s1 - s2) + (from_vec #(s1 - s2) (slice a s2 s1))) * pow2 (n - s1) + (from_vec #(n - s1) (slice a s1 n)))

val seq_slice_lemma: #n:nat -> a:bv_t n -> s1:nat{s1 < n} -> t1:nat{t1 >= s1 && t1 <= n} -> s2:nat{s2 < t1 - s1} -> t2:nat{t2 >= s2 && t2 <= t1 - s1} ->
  Lemma (equal (slice (slice a s1 t1) s2 t2) (slice a (s1 + s2) (s1 + t2)))

val from_vec_propriety: #n:pos -> a:bv_t n -> s:nat{s < n} ->
  Lemma (requires True)
        (ensures from_vec a = (from_vec #s (slice a 0 s)) * pow2 (n - s) + from_vec #(n - s) (slice a s n))
        (decreases (n - s))

val append_lemma: #n:pos -> #m:pos -> a:bv_t n -> b:bv_t m ->
  Lemma (from_vec #(n + m) (append a b) = (from_vec #n a) * pow2 m + (from_vec #m b))

val slice_left_lemma: #n:pos -> a:bv_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures from_vec #s (slice a 0 s) = (from_vec #n a) / (pow2 (n - s)))

val slice_right_lemma: #n:pos -> a:bv_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures from_vec #s (slice a (n - s) n) = (from_vec #n a) % (pow2 s))

(* Relations between constants in BitVector and in UInt. *)
val zero_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures index (to_vec (zero n)) i = index (zero_vec #n) i)
        [SMTPat (index (to_vec (zero n)) i)]

val zero_from_vec_lemma: #n:pos ->
  Lemma (requires True) (ensures from_vec (zero_vec #n) = zero n)
        [SMTPat (from_vec (zero_vec #n))]

val one_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (one n)) i = index (elem_vec #n (n - 1)) i)
        [SMTPat (index (to_vec (one n)) i)]

val pow2_to_vec_lemma: #n:pos -> p:nat{p < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (pow2_n #n p)) i = index (elem_vec #n (n - p - 1)) i)
        [SMTPat (index (to_vec (pow2_n #n p)) i)]

val pow2_from_vec_lemma: #n:pos -> p:nat{p < n} ->
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
let nth (#n:pos) (a:uint_t n) (i:nat{i < n}) : Tot bool =
  index (to_vec #n a) i

val nth_lemma: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires forall (i:nat{i < n}). nth a i = nth b i)
        (ensures a = b)

(* Lemmas for constants *)
val zero_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures nth (zero n) i = false)
        [SMTPat (nth (zero n) i)]

val pow2_nth_lemma: #n:pos -> p:nat{p < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = n - p - 1 ==> nth (pow2_n #n p) i = true) /\
                 (i <> n - p - 1 ==> nth (pow2_n #n p) i = false))
        [SMTPat (nth (pow2_n #n p) i)]

val one_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = n - 1 ==> nth (one n) i = true) /\
                 (i < n - 1 ==> nth (one n) i = false))
        [SMTPat (nth (one n) i)]

val ones_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures (nth (ones n) i) = true)
        [SMTPat (nth (ones n) i)]

(* Bitwise operators *)
let logand (#n:pos) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  from_vec #n (logand_vec #n (to_vec #n a) (to_vec #n b))

let logxor (#n:pos) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  from_vec #n (logxor_vec #n (to_vec #n a) (to_vec #n b))

let logor (#n:pos) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  from_vec #n (logor_vec #n (to_vec #n a) (to_vec #n b))

let lognot (#n:pos) (a:uint_t n) : Tot (uint_t n) =
  from_vec #n (lognot_vec #n (to_vec #n a))

(* Bitwise operators definitions *)
val logand_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (logand a b) i = (nth a i && nth b i)))
        [SMTPat (nth (logand a b) i)]

val logxor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (logxor a b) i = (nth a i <> nth b i)))
        [SMTPat (nth (logxor a b) i)]

val logor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (logor a b) i = (nth a i || nth b i)))
        [SMTPat (nth (logor a b) i)]

val lognot_definition: #n:pos -> a:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (lognot a) i = not(nth a i)))
        [SMTPat (nth (lognot a) i)]

(* Two's complement unary minus *)
inline_for_extraction
let minus (#n:pos) (a:uint_t n) : Tot (uint_t n) =
  add_mod (lognot a) 1

(* Bitwise operators lemmas *)
(* TODO: lemmas about the relations between different operators *)
(* Bitwise AND operator *)
val logand_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logand #n a b = logand #n b a))

val logand_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True)
        (ensures (logand #n (logand #n a b) c = logand #n a (logand #n b c)))

val logand_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logand #n a a = a))

val logand_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logand #n a (zero n) = zero n))

val logand_lemma_2: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logand #n a (ones n) = a))

(* subset_vec_le_lemma proves that a subset of bits is numerically smaller or equal. *)
val subset_vec_le_lemma: #n:pos -> a:bv_t n -> b:bv_t n ->
  Lemma (requires is_subset_vec #n a b) (ensures (from_vec a) <= (from_vec b))

(* logand_le proves the the result of AND is less than or equal to both arguments. *)
val logand_le: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True)
        (ensures (logand a b) <= a /\ (logand a b) <= b)

(* Bitwise XOR operator *)
val logxor_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a b = logxor #n b a))

val logxor_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True) (ensures (logxor #n (logxor #n a b) c = logxor #n a (logxor #n b c)))

val logxor_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a a = zero n))

val logxor_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a (zero n) = a))

val logxor_lemma_2: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a (ones n) = lognot #n a))

private let xor (b:bool) (b':bool) : Tot bool = b <> b'

private val xor_lemma (a:bool) (b:bool) : Lemma
  (requires (True))
  (ensures  (xor (xor a b) b = a))
  [SMTPat (xor (xor a b) b)]

val logxor_inv: #n:pos -> a:uint_t n -> b:uint_t n -> Lemma
  (a = logxor #n (logxor #n a b) b)

val logxor_neq_nonzero: #n:pos -> a:uint_t n -> b:uint_t n -> Lemma
   (a <> b ==> logxor a b <> 0)

(* Bitwise OR operators *)
val logor_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logor #n a b = logor #n b a))

val logor_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True)
        (ensures (logor #n (logor #n a b) c = logor #n a (logor #n b c)))

val logor_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logor #n a a = a))

val logor_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logor #n a (zero n) = a))

val logor_lemma_2: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logor #n a (ones n) = ones n))


(* superset_vec_le_lemma proves that a superset of bits is numerically greater than or equal. *)
val superset_vec_ge_lemma: #n:pos -> a:bv_t n -> b:bv_t n ->
  Lemma (requires is_superset_vec #n a b)
        (ensures (from_vec a) >= (from_vec b))

(* logor_ge proves that the result of an OR is greater than or equal to both arguments. *)
val logor_ge: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True)
        (ensures (logor a b) >= a /\ (logor a b) >= b)

(* Bitwise NOT operator *)
val lognot_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (lognot #n (lognot #n a) = a))

val lognot_lemma_1: #n:pos ->
  Lemma (requires True) (ensures (lognot #n (zero n) = ones n))

(** Used in the next two lemmas *)
private val index_to_vec_ones: #n:pos -> m:nat{m <= n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (pow2 m <= pow2 n /\
          (i < n - m ==> index (to_vec #n (pow2 m - 1)) i == false) /\
          (n - m <= i ==> index (to_vec #n (pow2 m - 1)) i == true)))
        [SMTPat (index (to_vec #n (pow2 m - 1)) i)]


val logor_disjoint: #n:pos -> a:uint_t n -> b:uint_t n -> m:pos{m < n} ->
  Lemma (requires (a % pow2 m == 0 /\ b < pow2 m))
        (ensures  (logor #n a b == a + b))

val logand_mask: #n:pos -> a:uint_t n -> m:pos{m < n} ->
  Lemma (pow2 m < pow2 n /\ logand #n a (pow2 m - 1) == a % pow2 m)


(* Shift operators *)

let shift_left (#n:pos) (a:uint_t n) (s:nat) : Tot (uint_t n) =
  from_vec (shift_left_vec #n (to_vec #n a) s)

let shift_right (#n:pos) (a:uint_t n) (s:nat) : Tot (uint_t n) =
  from_vec (shift_right_vec #n (to_vec #n a) s)

(* Shift operators lemmas *)
val shift_left_lemma_1: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i >= n - s} ->
  Lemma (requires True)
        (ensures (nth (shift_left #n a s) i = false))
        [SMTPat (nth (shift_left #n a s) i)]

val shift_left_lemma_2: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i < n - s} ->
  Lemma (requires True)
        (ensures (nth (shift_left #n a s) i = nth #n a (i + s)))
        [SMTPat (nth (shift_left #n a s) i)]

val shift_right_lemma_1: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (requires True)
        (ensures (nth (shift_right #n a s) i = false))
        [SMTPat (nth (shift_right #n a s) i)]

val shift_right_lemma_2: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma (requires True)
        (ensures (nth (shift_right #n a s) i = nth #n a (i - s)))
        [SMTPat (nth (shift_right #n a s) i)]

(* Lemmas with shift operators and bitwise operators *)
val shift_left_logand_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logand #n a b) s = logand #n (shift_left #n a s) (shift_left #n b s)))

val shift_right_logand_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logand #n a b) s = logand #n (shift_right #n a s) (shift_right #n b s)))

val shift_left_logxor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logxor #n a b) s = logxor #n (shift_left #n a s) (shift_left #n b s)))

val shift_right_logxor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logxor #n a b) s = logxor #n (shift_right #n a s) (shift_right #n b s)))

val shift_left_logor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logor #n a b) s = logor #n (shift_left #n a s) (shift_left #n b s)))

val shift_right_logor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logor #n a b) s = logor #n (shift_right #n a s) (shift_right #n b s)))


(* Lemmas about value after shift operations *)
val shift_left_value_aux_1: #n:pos -> a:uint_t n -> s:nat{s >= n} ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)

val shift_left_value_aux_2: #n:pos -> a:uint_t n ->
  Lemma (requires True)
        (ensures shift_left #n a 0 = (a * pow2 0) % pow2 n)

val shift_left_value_aux_3: #n:pos -> a:uint_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)

val shift_left_value_lemma: #n:pos -> a:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)
        [SMTPat (shift_left #n a s)]

val shift_right_value_aux_1: #n:pos -> a:uint_t n -> s:nat{s >= n} ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)

val shift_right_value_aux_2: #n:pos -> a:uint_t n ->
  Lemma (requires True)
        (ensures shift_right #n a 0 = a / pow2 0)

val shift_right_value_aux_3: #n:pos -> a:uint_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)

val shift_right_value_lemma: #n:pos -> a:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)
        [SMTPat (shift_right #n a s)]

(* Lemmas about the most significant bit in various situations *)

let msb (#n:pos) (a:uint_t n) : Tot bool = nth a 0

val lemma_msb_pow2: #n:pos -> a:uint_t n ->
  Lemma (msb a <==> a >= pow2 (n-1))

val lemma_minus_zero: #n:pos -> a:uint_t n ->
  Lemma (minus a = 0 ==> a = 0)

val lemma_msb_gte: #n:pos{n > 1} -> a:uint_t n -> b:uint_t n ->
  Lemma ((a >= b && not (msb a)) ==> not (msb b))


(* Lemmas toward showing ~n + 1 = -a *)

val lemma_uint_mod: #n:pos -> a:uint_t n ->
  Lemma (a = a % pow2 n)

val lemma_add_sub_cancel: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (add_mod (sub_mod a b) b = a)

val lemma_mod_sub_distr_l: a:int -> b:int -> p:pos ->
  Lemma ((a - b) % p = ((a % p) - b) % p)

val lemma_sub_add_cancel: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (sub_mod (add_mod a b) b = a)

let zero_extend_vec (#n:pos) (a:BitVector.bv_t n): Tot (BitVector.bv_t (n+1)) = append (create 1 false) a
let one_extend_vec (#n:pos) (a:BitVector.bv_t n): Tot (BitVector.bv_t (n+1)) = append (create 1 true) a

let zero_extend (#n:pos) (a:uint_t n): Tot (uint_t (n+1)) = from_vec (zero_extend_vec (to_vec a))
let one_extend (#n:pos) (a:uint_t n): Tot (uint_t (n+1)) = from_vec (one_extend_vec (to_vec a))

val lemma_zero_extend: #n:pos -> a:uint_t n ->
  Lemma (zero_extend a = a)
  [SMTPat (zero_extend a)]

val lemma_one_extend: #n:pos -> a:uint_t n ->
  Lemma (one_extend a = pow2 n + a)
  [SMTPat (one_extend a)]

val lemma_lognot_zero_ext: #n:pos -> a:uint_t n ->
  Lemma (lognot #(n+1) (zero_extend a) = pow2 n + (lognot #n a))

val lemma_lognot_one_ext: #n:pos -> a:uint_t n ->
  Lemma (lognot #(n+1) (one_extend a) = lognot #n a)

val lemma_lognot_value_mod: #n:pos -> a:uint_t n ->
  Lemma
  (requires True)
  (ensures (lognot a = pow2 n - a - 1))
  (decreases n)

val lemma_lognot_value_zero: #n:pos -> a:uint_t n{a = 0} ->
  Lemma (lognot a = sub_mod (sub_mod 0 a) 1)

val lemma_one_mod_pow2: #n:pos ->
  Lemma (1 = 1 % (pow2 n))

val lemma_lognot_value_nonzero: #n:pos -> a:uint_t n{a <> 0} ->
  Lemma (lognot a = sub_mod (sub_mod 0 a) 1)

val lemma_lognot_value: #n:pos -> a:uint_t n ->
  Lemma (lognot #n a = sub_mod (sub_mod 0 a) 1)

val lemma_minus_eq_zero_sub: #n:pos -> a:uint_t n ->
  Lemma (minus #n a = sub_mod #n 0 a)
