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

(* NOTE: anything that you fix/update here should be reflected in [FStar.Int.fst], which is mostly
 * a copy-paste of this module. *)

open FStar.Mul
open FStar.BitVector
open FStar.Math.Lemmas

#push-options "--max_fuel 0 --max_ifuel 0"

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
let pow2_values x =
   match x with
   | 0  -> assert_norm (pow2 0 == 1)
   | 1  -> assert_norm (pow2 1 == 2)
   | 8  -> assert_norm (pow2 8 == 256)
   | 16 -> assert_norm (pow2 16 == 65536)
   | 31 -> assert_norm (pow2 31 == 2147483648)
   | 32 -> assert_norm (pow2 32 == 4294967296)
   | 63 -> assert_norm (pow2 63 == 9223372036854775808)
   | 64 -> assert_norm (pow2 64 == 18446744073709551616)
   | 128 -> assert_norm (pow2 128 = 0x100000000000000000000000000000000)
   | _  -> ()

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
type uint_t (n:nat) = x:int{size x n}

/// Constants

val zero: n:nat -> Tot (uint_t n)
let zero n = 0

#push-options "--initial_fuel 1 --max_fuel 1"

val pow2_n: #n:pos -> p:nat{p < n} -> Tot (uint_t n)
let pow2_n #n p = pow2_le_compat (n - 1) p; pow2 p

val one: n:pos -> Tot (uint_t n)
let one n = 1

#pop-options

val ones: n:nat -> Tot (uint_t n)
let ones n = max_int n

(* Increment and decrement *)
val incr: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a < max_int n))) (ensures (fun _ -> True))
let incr #n a = a + 1

val decr: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a > min_int n))) (ensures (fun _ -> True))
let decr #n a = a - 1

abstract
val incr_underspec: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a < max_int n)))
  (ensures (fun b -> a + 1 = b))
let incr_underspec #n a =
  if a < max_int n then a + 1 else 0

abstract
val decr_underspec: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a > min_int n)))
  (ensures (fun b -> a - 1 = b))
let decr_underspec #n a =
  if a > min_int n then a - 1 else 0

val incr_mod: #n:nat -> a:uint_t n -> Tot (uint_t n)
let incr_mod #n a = (a + 1) % (pow2 n)

val decr_mod: #n:nat -> a:uint_t n -> Tot (uint_t n)
let decr_mod #n a = (a - 1) % (pow2 n)

(* Addition primitives *)
val add: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a + b) n))
  (ensures (fun _ -> True))
let add #n a b = a + b

abstract
val add_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a + b) n ==> a + b = c))
let add_underspec #n a b =
  if fits (a+b) n then a + b else 0

val add_mod: #n:nat -> uint_t n -> uint_t n -> Tot (uint_t n)
let add_mod #n a b =
  (a + b) % (pow2 n)

(* Subtraction primitives *)
val sub: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a - b) n))
  (ensures (fun _ -> True))
let sub #n a b = a - b

abstract val sub_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a - b) n ==> a - b = c))
let sub_underspec #n a b =
  if fits (a-b) n then a - b else 0

val sub_mod: #n:nat -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let sub_mod #n a b =
  (a - b) % (pow2 n)

(* Multiplication primitives *)
val mul: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires (size (a * b) n))
  (ensures (fun _ -> True))
let mul #n a b = a * b

abstract
val mul_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a * b) n ==> a * b = c))
let mul_underspec #n a b =
  if fits (a*b) n then a * b else 0

val mul_mod: #n:nat -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let mul_mod #n a b =
  (a * b) % (pow2 n)

private
let lt_square_div_lt (a:nat) (b:pos) : Lemma
  (requires (a < b * b))
  (ensures (a / b < b))
  = ()

val mul_div: #n:nat -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let mul_div #n a b =
  FStar.Math.Lemmas.lemma_mult_lt_sqr a b (pow2 n);
  lt_square_div_lt (a * b) (pow2 n);
  (a * b) / (pow2 n)

(* Division primitives *)
val div: #n:nat -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires (size (a / b) n))
  (ensures (fun c -> b <> 0 ==> a / b = c))
let div #n a b = a / b

abstract
val div_underspec: #n:nat -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    (b <> 0 /\ size (a / b) n) ==> a / b = c))
let div_underspec #n a b =
  if fits (a / b) n then a / b else 0

val div_size: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} ->
  Lemma (requires (size a n)) (ensures (size (a / b) n))
let div_size #n a b =
  FStar.Math.Lib.slash_decr_axiom a b; ()

val udiv: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} ->
  Tot (c:uint_t n{b <> 0 ==> a / b = c})
let udiv #n a b =
  div_size #n a b;
  a / b


(* Modulo primitives *)
val mod: #n:nat -> a:uint_t n -> b:uint_t n{b <> 0} -> Tot (uint_t n)
let mod #n a b = a - ((a/b) * b)

(* Comparison operators *)
let eq #n (a:uint_t n) (b:uint_t n) : Tot bool = (a = b)
let gt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a > b)
let gte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a >= b)
let lt #n (a:uint_t n) (b:uint_t n) : Tot bool = (a < b)
let lte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a <= b)

/// Casts

#push-options "--initial_fuel 1 --max_fuel 1"

val to_uint_t: m:nat -> a:int -> Tot (uint_t m)
let to_uint_t m a = a % pow2 m

open FStar.Seq

(* WARNING: Mind the big endian vs little endian definition *)

(* Casts *)
val to_vec: #n:nat -> num:uint_t n -> Tot (bv_t n)
let rec to_vec #n num =
  if n = 0 then Seq.empty #bool
  else Seq.append (to_vec #(n - 1) (num / 2)) (Seq.create 1 (num % 2 = 1))

val from_vec: #n:nat -> vec:bv_t n -> Tot (uint_t n)
let rec from_vec #n vec =
  if n = 0 then 0
  else 2 * from_vec #(n - 1) (slice vec 0 (n - 1)) + (if index vec (n - 1) then 1 else 0)

val to_vec_lemma_1: #n:nat -> a:uint_t n -> b:uint_t n ->
  Lemma (requires a = b) (ensures equal (to_vec a) (to_vec b))
let to_vec_lemma_1 #n a b = ()

val to_vec_lemma_2: #n:nat -> a:uint_t n -> b:uint_t n ->
  Lemma (requires equal (to_vec a) (to_vec b)) (ensures a = b)
let rec to_vec_lemma_2 #n a b =
  if n = 0 then () else begin
    assert(equal (slice (to_vec b) 0 (n - 1)) (to_vec #(n - 1) (b / 2)));
    assert(equal (slice (to_vec a) 0 (n - 1)) (to_vec #(n - 1) (a / 2)));
    to_vec_lemma_2 #(n - 1) (a / 2) (b / 2);
    assert(a % 2 = (if index (to_vec a) (n - 1) then 1 else 0));
    assert(b % 2 = (if index (to_vec b) (n - 1) then 1 else 0));
    assert(a % 2 = b % 2)
  end

val inverse_aux: #n:nat -> vec:bv_t n -> i:nat{i < n} ->
  Lemma (requires True) (ensures index vec i = index (to_vec (from_vec vec)) i)
        [SMTPat (index (to_vec (from_vec vec)) i)]
let rec inverse_aux #n vec i =
  if i = n - 1 then
    assert((from_vec vec) % 2 = (if index vec (n - 1) then 1 else 0))
  else inverse_aux #(n - 1) (slice vec 0 (n - 1)) i

val inverse_vec_lemma: #n:nat -> vec:bv_t n ->
  Lemma (requires True) (ensures equal vec (to_vec (from_vec vec)))
        [SMTPat (to_vec (from_vec vec))]
let inverse_vec_lemma #n vec = ()

val inverse_num_lemma: #n:nat -> num:uint_t n ->
  Lemma (requires True) (ensures num = from_vec (to_vec num))
        [SMTPat (from_vec (to_vec num))]
let inverse_num_lemma #n num = to_vec_lemma_2 #n num (from_vec (to_vec num))

val from_vec_lemma_1: #n:nat -> a:bv_t n -> b:bv_t n ->
  Lemma (requires equal a b) (ensures from_vec a = from_vec b)
let from_vec_lemma_1 #n a b = ()

val from_vec_lemma_2: #n:nat -> a:bv_t n -> b:bv_t n ->
  Lemma (requires from_vec a = from_vec b) (ensures equal a b)
let from_vec_lemma_2 #n a b = inverse_vec_lemma a; inverse_vec_lemma b


open FStar.Math.Lemmas

#pop-options

val from_vec_aux: #n:nat -> a:bv_t n -> s1:nat{s1 < n} -> s2:nat{s2 < s1} ->
  Lemma (requires True)
        (ensures (from_vec #s2 (slice a 0 s2)) * pow2 (n - s2) + (from_vec #(s1 - s2) (slice a s2 s1)) * pow2 (n - s1) + (from_vec #(n - s1) (slice a s1 n)) = ((from_vec #s2 (slice a 0 s2)) * pow2 (s1 - s2) + (from_vec #(s1 - s2) (slice a s2 s1))) * pow2 (n - s1) + (from_vec #(n - s1) (slice a s1 n)))
let from_vec_aux #n a s1 s2 =
  paren_mul_left (from_vec #s2 (slice a 0 s2)) (pow2 (s1 - s2)) (pow2 (n - s1));
  paren_mul_right (from_vec #s2 (slice a 0 s2)) (pow2 (s1 - s2)) (pow2 (n - s1));
  pow2_plus (s1 - s2) (n - s1)

val seq_slice_lemma: #n:nat -> a:bv_t n -> s1:nat{s1 < n} -> t1:nat{t1 >= s1 && t1 <= n} -> s2:nat{s2 < t1 - s1} -> t2:nat{t2 >= s2 && t2 <= t1 - s1} ->
  Lemma (equal (slice (slice a s1 t1) s2 t2) (slice a (s1 + s2) (s1 + t2)))
let seq_slice_lemma #n a s1 t1 s2 t2 = ()

#push-options "--initial_fuel 1 --max_fuel 1"

val from_vec_propriety: #n:pos -> a:bv_t n -> s:nat{s < n} ->
  Lemma (requires True)
        (ensures from_vec a = (from_vec #s (slice a 0 s)) * pow2 (n - s) + from_vec #(n - s) (slice a s n))
        (decreases (n - s))
let rec from_vec_propriety #n a s =
  if s = n - 1 then () else begin
    from_vec_propriety #n a (s + 1);
    from_vec_propriety #(s + 1) (slice a 0 (s + 1)) s;
    seq_slice_lemma #n a 0 (s + 1) 0 s;
    seq_slice_lemma #n a 0 (s + 1) s (s + 1);
    from_vec_aux #n a (s + 1) s;
    from_vec_propriety #(n - s) (slice a s n) 1;
    seq_slice_lemma #n a s n 0 1;
    seq_slice_lemma #n a s n 1 (n - s)
  end

#pop-options

val append_lemma: #n:pos -> #m:pos -> a:bv_t n -> b:bv_t m ->
  Lemma (from_vec #(n + m) (append a b) = (from_vec #n a) * pow2 m + (from_vec #m b))
let append_lemma #n #m a b =
  assert(equal a (slice (append a b) 0 n));
  assert(equal b (slice (append a b) n (n + m)));
  from_vec_propriety #(n + m) (append a b) n

val slice_left_lemma: #n:pos -> a:bv_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures from_vec #s (slice a 0 s) = (from_vec #n a) / (pow2 (n - s)))
let slice_left_lemma #n a s =
  from_vec_propriety #n a s;
  division_addition_lemma (from_vec #(n - s) (slice a s n)) (pow2 (n - s)) (from_vec #s (slice a 0 s));
  small_division_lemma_1 (from_vec #(n - s) (slice a s n)) (pow2 (n - s))

val slice_right_lemma: #n:pos -> a:bv_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures from_vec #s (slice a (n - s) n) = (from_vec #n a) % (pow2 s))
let slice_right_lemma #n a s =
  from_vec_propriety #n a (n - s);
  modulo_addition_lemma (from_vec #s (slice a (n - s) n)) (pow2 s) (from_vec #(n - s) (slice a 0 (n - s)));
  small_modulo_lemma_1 (from_vec #s (slice a (n - s) n)) (pow2 s)

#push-options "--initial_fuel 1 --max_fuel 1"

(* Relations between constants in BitVector and in UInt. *)
val zero_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures index (to_vec (zero n)) i = index (zero_vec #n) i)
        [SMTPat (index (to_vec (zero n)) i)]
let rec zero_to_vec_lemma #n i =
  if i = n - 1 then () else zero_to_vec_lemma #(n - 1) i

val zero_from_vec_lemma: #n:pos ->
  Lemma (requires True) (ensures from_vec (zero_vec #n) = zero n)
        [SMTPat (from_vec (zero_vec #n))]
let zero_from_vec_lemma #n = to_vec_lemma_2 (from_vec (zero_vec #n)) (zero n)

val one_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (one n)) i = index (elem_vec #n (n - 1)) i)
        [SMTPat (index (to_vec (one n)) i)]
let one_to_vec_lemma #n i =
  if i = n - 1 then () else zero_to_vec_lemma #n i

val pow2_to_vec_lemma: #n:pos -> p:nat{p < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (pow2_n #n p)) i = index (elem_vec #n (n - p - 1)) i)
        [SMTPat (index (to_vec (pow2_n #n p)) i)]
let rec pow2_to_vec_lemma #n p i =
  if i = n - 1 then ()
  else if p = 0 then one_to_vec_lemma #n i
  else pow2_to_vec_lemma #(n - 1) (p - 1) i

val pow2_from_vec_lemma: #n:pos -> p:nat{p < n} ->
  Lemma (requires True) (ensures from_vec (elem_vec #n p) = pow2_n #n (n - p - 1))
        [SMTPat (from_vec (elem_vec #n p))]
let pow2_from_vec_lemma #n p =
  to_vec_lemma_2 (from_vec (elem_vec #n p)) (pow2_n #n (n - p - 1))

val ones_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (ones n)) i = index (ones_vec #n) i)
        [SMTPat (index (to_vec (ones n)) i)]
let rec ones_to_vec_lemma #n i =
  if i = n - 1 then () else ones_to_vec_lemma #(n - 1) i

val ones_from_vec_lemma: #n:pos ->
  Lemma (requires True) (ensures from_vec (ones_vec #n) = ones n)
        [SMTPat (from_vec (ones_vec #n))]
let ones_from_vec_lemma #n =
  to_vec_lemma_2 (from_vec (ones_vec #n)) (ones n)


(* (nth a i) returns a boolean indicating the i-th bit of a. *)
val nth: #n:pos -> a:uint_t n -> i:nat{i < n} -> Tot bool
let nth #n a i = index (to_vec #n a) i

val nth_lemma: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires forall (i:nat{i < n}). nth a i = nth b i)
        (ensures a = b)
let nth_lemma #n a b =
  assert(forall (i:nat{i < n}). index (to_vec #n a) i = index (to_vec #n b) i);
  to_vec_lemma_2 a b

(* Lemmas for constants *)
val zero_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures nth (zero n) i = false)
        [SMTPat (nth (zero n) i)]
let rec zero_nth_lemma #n i = ()

val pow2_nth_lemma: #n:pos -> p:nat{p < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = n - p - 1 ==> nth (pow2_n #n p) i = true) /\
                 (i <> n - p - 1 ==> nth (pow2_n #n p) i = false))
        [SMTPat (nth (pow2_n #n p) i)]
let pow2_nth_lemma #n p i = ()

val one_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = n - 1 ==> nth (one n) i = true) /\
                 (i < n - 1 ==> nth (one n) i = false))
        [SMTPat (nth (one n) i)]
let one_nth_lemma #n i = ()

val ones_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures (nth (ones n) i) = true)
        [SMTPat (nth (ones n) i)]
let rec ones_nth_lemma #n i = ()

(* Bitwise operators *)
val logand: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let logand #n a b = from_vec #n (logand_vec #n (to_vec #n a) (to_vec #n b))

val logxor: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let logxor #n a b = from_vec #n (logxor_vec #n (to_vec #n a) (to_vec #n b))

val logor: #n:pos -> a:uint_t n -> b:uint_t n -> Tot (uint_t n)
let logor #n a b = from_vec #n (logor_vec #n (to_vec #n a) (to_vec #n b))

val lognot: #n:pos -> a:uint_t n  -> Tot (uint_t n)
let lognot #n a = from_vec #n (lognot_vec #n (to_vec #n a))

(* Bitwise operators definitions *)
val logand_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (logand a b) i = (nth a i && nth b i)))
        [SMTPat (nth (logand a b) i)]
let logand_definition #n a b i = ()

val logxor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (logxor a b) i = (nth a i <> nth b i)))
        [SMTPat (nth (logxor a b) i)]
let logxor_definition #n a b i = ()

val logor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (logor a b) i = (nth a i || nth b i)))
        [SMTPat (nth (logor a b) i)]
let logor_definition #n a b i = ()

val lognot_definition: #n:pos -> a:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (lognot a) i = not(nth a i)))
        [SMTPat (nth (lognot a) i)]
let lognot_definition #n a i = ()

(* Two's complement unary minus *)
inline_for_extraction
val minus: #n:pos -> a:uint_t n -> Tot (uint_t n)
let minus #n a = add_mod (lognot a) 1

(* Bitwise operators lemmas *)
(* TODO: lemmas about the relations between different operators *)
(* Bitwise AND operator *)
val logand_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logand #n a b = logand #n b a))
let logand_commutative #n a b = nth_lemma #n (logand #n a b) (logand #n b a)

val logand_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True)
        (ensures (logand #n (logand #n a b) c = logand #n a (logand #n b c)))
let logand_associative #n a b c = nth_lemma #n (logand #n (logand #n a b) c) (logand #n a (logand #n b c))

val logand_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logand #n a a = a))
let logand_self #n a = nth_lemma #n (logand #n a a) a

val logand_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logand #n a (zero n) = zero n))
let logand_lemma_1 #n a = nth_lemma #n (logand #n a (zero n)) (zero n)

val logand_lemma_2: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logand #n a (ones n) = a))
let logand_lemma_2 #n a = nth_lemma #n (logand #n a (ones n)) a

(* subset_vec_le_lemma proves that a subset of bits is numerically smaller or equal. *)
val subset_vec_le_lemma: #n:pos -> a:bv_t n -> b:bv_t n ->
  Lemma (requires is_subset_vec #n a b) (ensures (from_vec a) <= (from_vec b))
let rec subset_vec_le_lemma #n a b = match n with
  | 1 -> ()
  | _ -> lemma_slice_subset_vec #n a b 0 (n-1);
        subset_vec_le_lemma #(n-1) (slice a 0 (n-1)) (slice b 0 (n-1))

(* logand_le proves the the result of AND is less than or equal to both arguments. *)
val logand_le: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True)
        (ensures (logand a b) <= a /\ (logand a b) <= b)
let logand_le #n a b =
  let va = to_vec a in
  let vb = to_vec b in
  let vand = to_vec (logand a b) in
  subset_vec_le_lemma #n vand va;
  subset_vec_le_lemma #n vand vb

(* Bitwise XOR operator *)
val logxor_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a b = logxor #n b a))
let logxor_commutative #n a b = nth_lemma #n (logxor #n a b) (logxor #n b a)

val logxor_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True) (ensures (logxor #n (logxor #n a b) c = logxor #n a (logxor #n b c)))
let logxor_associative #n a b c = nth_lemma #n (logxor #n (logxor #n a b) c) (logxor #n a (logxor #n b c))

val logxor_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a a = zero n))
let logxor_self #n a = nth_lemma #n (logxor #n a a) (zero n)

val logxor_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a (zero n) = a))
let logxor_lemma_1 #n a = nth_lemma #n (logxor #n a (zero n)) a

val logxor_lemma_2: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a (ones n) = lognot #n a))
let logxor_lemma_2 #n a = nth_lemma #n (logxor #n a (ones n)) (lognot #n a)

#reset-options "--initial_fuel 0 --max_fuel 0"

private let xor (b:bool) (b':bool) : Tot bool = b <> b'
private let xor_lemma (a:bool) (b:bool) : Lemma
  (requires (True))
  (ensures  (xor (xor a b) b = a))
  [SMTPat (xor (xor a b) b)]
  = ()

val logxor_inv: #n:pos -> a:uint_t n -> b:uint_t n -> Lemma
  (a = logxor #n (logxor #n a b) b)
let logxor_inv #n a b =
  let open FStar.BitVector in
  let open FStar.Seq in
  let va = to_vec a in
  let vb = to_vec b in
  cut(forall (i:nat). i < n ==> index (logxor_vec #n va vb) i = (index va i <> index vb i));
  cut (forall (i:nat). {:pattern (index (logxor_vec (logxor_vec va vb) vb) i)}
    i < n ==> index (logxor_vec (logxor_vec va vb) vb) i = (xor (xor (index va i)
                                                                    (index vb i))
                                                               (index vb i)));
  cut (forall (i:nat). i < n ==> index (logxor_vec (logxor_vec va vb) vb) i = index va i);
  Seq.lemma_eq_intro (logxor_vec (logxor_vec va vb) vb) va;
  inverse_num_lemma a; inverse_num_lemma b

val logxor_neq_nonzero: #n:pos -> a:uint_t n -> b:uint_t n -> Lemma
   (a <> b ==> logxor a b <> 0)
let logxor_neq_nonzero #n a b =
  let va = to_vec a in
  let vb = to_vec b in
  if logxor a b = 0 then
  begin
    let open FStar.Seq in
    let f (i:nat{i < n}) : Lemma (not (nth #n 0 i)) = zero_nth_lemma #n i in
    Classical.forall_intro f;
    assert (forall (i:nat{i < n}). index va i = index vb i);
    lemma_eq_intro va vb;
    assert (from_vec va = from_vec vb)
  end

(* Bitwise OR operators *)
val logor_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logor #n a b = logor #n b a))
let logor_commutative #n a b = nth_lemma #n (logor #n a b) (logor #n b a)

val logor_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True)
        (ensures (logor #n (logor #n a b) c = logor #n a (logor #n b c)))
let logor_associative #n a b c = nth_lemma #n (logor #n (logor #n a b) c) (logor #n a (logor #n b c))

val logor_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logor #n a a = a))
let logor_self #n a = nth_lemma #n (logor #n a a) a

val logor_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logor #n a (zero n) = a))
let logor_lemma_1 #n a = nth_lemma (logor #n a (zero n)) a

val logor_lemma_2: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logor #n a (ones n) = ones n))
let logor_lemma_2 #n a = nth_lemma (logor #n a (ones n)) (ones n)

#set-options "--initial_fuel 1 --max_fuel 1"

(* superset_vec_le_lemma proves that a superset of bits is numerically greater than or equal. *)
val superset_vec_ge_lemma: #n:pos -> a:bv_t n -> b:bv_t n ->
  Lemma (requires is_superset_vec #n a b)
        (ensures (from_vec a) >= (from_vec b))
let rec superset_vec_ge_lemma #n a b = match n with
  | 1 -> ()
  | _ -> lemma_slice_superset_vec #n a b 0 (n-1);
        superset_vec_ge_lemma #(n-1) (slice a 0 (n-1)) (slice b 0 (n-1))

(* logor_ge proves that the result of an OR is greater than or equal to both arguments. *)
val logor_ge: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True)
        (ensures (logor a b) >= a /\ (logor a b) >= b)
let logor_ge #n a b =
  let va = to_vec a in
  let vb = to_vec b in
  let vor = to_vec (logor a b) in
  superset_vec_ge_lemma #n vor va;
  superset_vec_ge_lemma #n vor vb

(* Bitwise NOT operator *)
val lognot_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (lognot #n (lognot #n a) = a))
let lognot_self #n a = nth_lemma (lognot #n (lognot #n a)) a

val lognot_lemma_1: #n:pos ->
  Lemma (requires True) (ensures (lognot #n (zero n) = ones n))
let lognot_lemma_1 #n = nth_lemma (lognot #n (zero n)) (ones n)

(** Used in the next two lemmas *)
private val to_vec_mod_pow2: #n:nat -> a:uint_t n -> m:pos -> i:nat{n - m <= i /\ i < n} ->
  Lemma (requires (a % pow2 m == 0))
        (ensures  (index (to_vec a) i == false))
        [SMTPat (index (to_vec #n a) i); SMTPat (a % pow2 m == 0)]
let rec to_vec_mod_pow2 #n a m i =
  if i = n - 1 then
    begin
    lemma_index_app2 (to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i;
    mod_mult_exact a 2 (pow2 (m - 1))
    end
  else
    begin
    lemma_index_app1 (to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i;
    assert (index (to_vec a) i == index (to_vec #(n - 1) (a / 2)) i);
    mod_pow2_div2 a m;
    to_vec_mod_pow2 #(n - 1) (a / 2) (m - 1) i
    end

(** Used in the next two lemmas *)
private val to_vec_lt_pow2: #n:nat -> a:uint_t n -> m:nat -> i:nat{i < n - m} ->
  Lemma (requires (a < pow2 m))
        (ensures  (index (to_vec a) i == false))
        [SMTPat (index (to_vec #n a) i); SMTPat (a < pow2 m)]
let rec to_vec_lt_pow2 #n a m i =
  if n = 0 then ()
  else
    if m = 0 then
      assert (a == zero n)
    else
      begin
      lemma_index_app1 (to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i;
      assert (index (to_vec a) i == index (to_vec #(n - 1) (a / 2)) i);
      to_vec_lt_pow2 #(n - 1) (a / 2) (m - 1) i
      end

(** Used in the next two lemmas *)
#reset-options "--initial_fuel 0 --max_fuel 1 --z3rlimit 40"
private val index_to_vec_ones: #n:pos -> m:nat{m <= n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (pow2 m <= pow2 n /\
          (i < n - m ==> index (to_vec #n (pow2 m - 1)) i == false) /\
          (n - m <= i ==> index (to_vec #n (pow2 m - 1)) i == true)))
        [SMTPat (index (to_vec #n (pow2 m - 1)) i)]
let rec index_to_vec_ones #n m i =
   let a = pow2 m - 1 in
   pow2_le_compat n m;
   if m = 0 then one_to_vec_lemma #n i
   else if m = n then ones_to_vec_lemma #n i
   else if i = n - 1 then ()
   else index_to_vec_ones #(n - 1) (m - 1) i

#reset-options "--initial_fuel 0 --max_fuel 0"

val logor_disjoint: #n:pos -> a:uint_t n -> b:uint_t n -> m:pos{m < n} ->
  Lemma (requires (a % pow2 m == 0 /\ b < pow2 m))
        (ensures  (logor #n a b == a + b))
let logor_disjoint #n a b m =
  assert (a % pow2 m == 0); // To trigger pattern above
  assert (forall (i:nat{n - m <= i /\ i < n}).{:pattern (index (to_vec a) i)}
    index (to_vec a) i == false);
  assert (b < pow2 m); // To trigger pattern above
  assert (forall (i:nat{i < n - m}).{:pattern (index (to_vec b) i)}
    index (to_vec b) i == false);
  Seq.lemma_split (logor_vec (to_vec a) (to_vec b)) (n - m);
  Seq.lemma_eq_intro
    (logor_vec (to_vec a) (to_vec b))
    (append (slice (to_vec a) 0 (n - m)) (slice (to_vec b) (n - m) n));
  append_lemma #(n - m) #m (slice (to_vec a) 0 (n - m)) (slice (to_vec b) (n - m) n);
  slice_left_lemma #n (to_vec a) (n - m);
  div_exact_r a (pow2 m);
  assert (from_vec #(n - m) (slice (to_vec a) 0 (n - m)) * pow2 m == a);
  slice_right_lemma #n (to_vec b) m;
  small_modulo_lemma_1 b (pow2 m);
  assert (from_vec #m (slice (to_vec b) (n - m) n) == b)

val logand_mask: #n:pos -> a:uint_t n -> m:pos{m < n} ->
  Lemma (pow2 m < pow2 n /\ logand #n a (pow2 m - 1) == a % pow2 m)
let logand_mask #n a m =
  pow2_lt_compat n m;
  Seq.lemma_split (logand_vec (to_vec a) (to_vec (pow2 m - 1))) (n - m);
  Seq.lemma_eq_intro
    (logand_vec (to_vec a) (to_vec (pow2 m - 1)))
    (append (zero_vec #(n - m)) (slice (to_vec a) (n - m) n));
  append_lemma #(n - m) #m (zero_vec #(n - m)) (slice (to_vec a) (n - m) n);
  assert (0 * pow2 m + a % pow2 m == a % pow2 m);
  assert (from_vec #(n - m) (zero_vec #(n - m)) == 0);
  slice_right_lemma #n (to_vec a) m;
  assert (from_vec #m (slice (to_vec a) (n - m) n) == a % pow2 m)


(* Shift operators *)

val shift_left: #n:pos -> a:uint_t n -> s:nat -> Tot (uint_t n)
let shift_left #n a s = from_vec (shift_left_vec #n (to_vec #n a) s)

val shift_right: #n:pos -> a:uint_t n -> s:nat -> Tot (uint_t n)
let shift_right #n a s = from_vec (shift_right_vec #n (to_vec #n a) s)

(* Shift operators lemmas *)
val shift_left_lemma_1: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i >= n - s} ->
  Lemma (requires True)
        (ensures (nth (shift_left #n a s) i = false))
        [SMTPat (nth (shift_left #n a s) i)]
let shift_left_lemma_1 #n a s i = ()

val shift_left_lemma_2: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i < n - s} ->
  Lemma (requires True)
        (ensures (nth (shift_left #n a s) i = nth #n a (i + s)))
        [SMTPat (nth (shift_left #n a s) i)]
let shift_left_lemma_2 #n a s i = ()

val shift_right_lemma_1: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (requires True)
        (ensures (nth (shift_right #n a s) i = false))
        [SMTPat (nth (shift_right #n a s) i)]
let shift_right_lemma_1 #n a s i = ()

val shift_right_lemma_2: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma (requires True)
        (ensures (nth (shift_right #n a s) i = nth #n a (i - s)))
        [SMTPat (nth (shift_right #n a s) i)]
let shift_right_lemma_2 #n a s i = ()

(* Lemmas with shift operators and bitwise operators *)
val shift_left_logand_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logand #n a b) s = logand #n (shift_left #n a s) (shift_left #n b s)))
let shift_left_logand_lemma #n a b s = nth_lemma (shift_left #n (logand #n a b) s) (logand #n (shift_left #n a s) (shift_left #n b s))

val shift_right_logand_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logand #n a b) s = logand #n (shift_right #n a s) (shift_right #n b s)))
let shift_right_logand_lemma #n a b s = nth_lemma (shift_right #n (logand #n a b) s) (logand #n (shift_right #n a s) (shift_right #n b s))

val shift_left_logxor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logxor #n a b) s = logxor #n (shift_left #n a s) (shift_left #n b s)))
let shift_left_logxor_lemma #n a b s = nth_lemma (shift_left #n (logxor #n a b) s) (logxor #n (shift_left #n a s) (shift_left #n b s))

val shift_right_logxor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logxor #n a b) s = logxor #n (shift_right #n a s) (shift_right #n b s)))
let shift_right_logxor_lemma #n a b s = nth_lemma (shift_right #n (logxor #n a b) s) (logxor #n (shift_right #n a s) (shift_right #n b s))

val shift_left_logor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logor #n a b) s = logor #n (shift_left #n a s) (shift_left #n b s)))
let shift_left_logor_lemma #n a b s = nth_lemma (shift_left #n (logor #n a b) s) (logor #n (shift_left #n a s) (shift_left #n b s))

val shift_right_logor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logor #n a b) s = logor #n (shift_right #n a s) (shift_right #n b s)))
let shift_right_logor_lemma #n a b s = nth_lemma (shift_right #n (logor #n a b) s) (logor #n (shift_right #n a s) (shift_right #n b s))


(* Lemmas about value after shift operations *)
val shift_left_value_aux_1: #n:pos -> a:uint_t n -> s:nat{s >= n} ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)
let shift_left_value_aux_1 #n a s = pow2_multiplication_modulo_lemma_1 a n s

val shift_left_value_aux_2: #n:pos -> a:uint_t n ->
  Lemma (requires True)
        (ensures shift_left #n a 0 = (a * pow2 0) % pow2 n)
let shift_left_value_aux_2 #n a =
  assert_norm(a * pow2 0 = a);
  small_modulo_lemma_1 a (pow2 n)

val shift_left_value_aux_3: #n:pos -> a:uint_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)
let shift_left_value_aux_3 #n a s =
  append_lemma #(n - s) #s (slice (to_vec a) s n) (zero_vec #s);
  slice_right_lemma #n (to_vec a) (n - s);
  pow2_multiplication_modulo_lemma_2 a n s

val shift_left_value_lemma: #n:pos -> a:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)
        [SMTPat (shift_left #n a s)]
let shift_left_value_lemma #n a s =
  if s >= n then shift_left_value_aux_1 #n a s
  else if s = 0 then shift_left_value_aux_2 #n a
  else shift_left_value_aux_3 #n a s

val shift_right_value_aux_1: #n:pos -> a:uint_t n -> s:nat{s >= n} ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)
let shift_right_value_aux_1 #n a s =
  pow2_le_compat s n;
  small_division_lemma_1 a (pow2 s)

val shift_right_value_aux_2: #n:pos -> a:uint_t n ->
  Lemma (requires True)
        (ensures shift_right #n a 0 = a / pow2 0)
let shift_right_value_aux_2 #n a = assert_norm (pow2 0 == 1)

val shift_right_value_aux_3: #n:pos -> a:uint_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)
let shift_right_value_aux_3 #n a s =
  append_lemma #s #(n - s) (zero_vec #s) (slice (to_vec a) 0 (n - s));
  slice_left_lemma #n (to_vec a) (n - s)

val shift_right_value_lemma: #n:pos -> a:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)
        [SMTPat (shift_right #n a s)]
let shift_right_value_lemma #n a s =
  if s >= n then shift_right_value_aux_1 #n a s
  else if s = 0 then shift_right_value_aux_2 #n a
  else shift_right_value_aux_3 #n a s


(* Lemmas about the most significant bit in various situations *)

val msb: #n:pos -> a:uint_t n -> Tot bool
let msb #n a = nth a 0

#set-options "--initial_fuel 1 --max_fuel 1"
val lemma_msb_pow2: #n:pos -> a:uint_t n ->
  Lemma (msb a <==> a >= pow2 (n-1))
let lemma_msb_pow2 #n a = if n = 1 then () else from_vec_propriety (to_vec a) 1

private val plus_one_mod : p:pos -> a:nat ->
    Lemma (requires (a < p /\ ((a + 1) % p == 0))) (ensures (a == p - 1))
private let plus_one_mod p a = ()

val lemma_minus_zero: #n:pos -> a:uint_t n ->
  Lemma (minus a = 0 ==> a = 0)
let lemma_minus_zero #n a =
  if minus a = 0 then
  begin
    plus_one_mod (pow2 n) (lognot a);
    lognot_self a;
    logxor_self (ones n);
    logxor_lemma_2 #n (ones n)
  end

val lemma_msb_gte: #n:pos{n > 1} -> a:uint_t n -> b:uint_t n ->
  Lemma ((a >= b && not (msb a)) ==> not (msb b))
let lemma_msb_gte #n a b =
  from_vec_propriety (to_vec a) 1;
  from_vec_propriety (to_vec b) 1


(* Lemmas toward showing ~n + 1 = -a *)

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

#set-options "--z3rlimit 80"
val lemma_uint_mod: #n:pos -> a:uint_t n ->
  Lemma (a = a % pow2 n)
let lemma_uint_mod #n a = ()
#set-options "--z3rlimit 5"

val lemma_add_sub_cancel: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (add_mod (sub_mod a b) b = a)
let lemma_add_sub_cancel #n a b =
  let ab = (a-b) % pow2 n in
  let abb = (ab + b) % pow2 n in
  let ab_mod = sub_mod a b in
  let abb_mod = add_mod ab b in
  let p = pow2 n in
  lemma_uint_mod a;
  assert (add_mod (sub_mod a b) b = add_mod ab_mod b);
  assert (add_mod ab_mod b = (ab_mod + b) % p);
  assert (add_mod ab_mod b = ((a-b) % p + b) % p);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (a-b) b p;
  assert (((a-b) + b) % p = (((a-b) % p) + b) % p);
  assert (a % p = (((a-b) % p) + b) % p)

val lemma_mod_sub_distr_l: a:int -> b:int -> p:pos ->
  Lemma ((a - b) % p = ((a % p) - b) % p)
let lemma_mod_sub_distr_l a b p =
  let q = (a - (a % p)) / p in
  FStar.Math.Lemmas.lemma_mod_spec2 a p;
  FStar.Math.Lemmas.lemma_mod_plus (a % p - b) q p

val lemma_sub_add_cancel: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (sub_mod (add_mod a b) b = a)
let lemma_sub_add_cancel #n a b =
  let ab = (a+b) % pow2 n in
  let abb = (ab - b) % pow2 n in
  let ab_mod = add_mod a b in
  let abb_mod = sub_mod ab b in
  let p = pow2 n in
  lemma_uint_mod a;
  lemma_mod_sub_distr_l (a+b) b p

let zero_extend_vec (#n:pos) (a:BitVector.bv_t n): Tot (BitVector.bv_t (n+1)) = Seq.append (Seq.create 1 false) a
let one_extend_vec (#n:pos) (a:BitVector.bv_t n): Tot (BitVector.bv_t (n+1)) = Seq.append (Seq.create 1 true) a

let zero_extend (#n:pos) (a:uint_t n): Tot (uint_t (n+1)) = from_vec (zero_extend_vec (to_vec a))
let one_extend (#n:pos) (a:uint_t n): Tot (uint_t (n+1)) = from_vec (one_extend_vec (to_vec a))

val lemma_zero_extend: #n:pos -> a:uint_t n ->
  Lemma (zero_extend a = a)
  [SMTPat (zero_extend a)]
let lemma_zero_extend #n a =
  let hd0 = Seq.create 1 false in
  let av = to_vec a in
  let eav = Seq.append hd0 av in
  let r = zero_extend a in
  append_lemma #1 #n hd0 av;
  assert (r = from_vec eav);
  from_vec_propriety #(n+1) eav 1;
  assert (r = a)

val lemma_one_extend: #n:pos -> a:uint_t n ->
  Lemma (one_extend a = pow2 n + a)
  [SMTPat (one_extend a)]
let lemma_one_extend #n a =
  let hd1 = Seq.create 1 true in
  let av = to_vec a in
  let eav = Seq.append hd1 av in
  let r = one_extend a in
  append_lemma #1 #n hd1 av;
  assert (r = from_vec eav);
  from_vec_propriety #(n+1) eav 1;
  assert (r = pow2 n + a)

val lemma_lognot_zero_ext: #n:pos -> a:uint_t n ->
  Lemma (lognot #(n+1) (zero_extend a) = pow2 n + (lognot #n a))
let lemma_lognot_zero_ext #n a =
  let lhs = lognot #(n+1) a in
  let rhs = pow2 n + (lognot #n a) in

  let av = to_vec a in
  assert (Seq.length av = n);
  let hd0 = Seq.create 1 false in
  let hd1 = Seq.create 1 true in
  let nav = to_vec (lognot a) in
  let eav = Seq.append hd0 av in

  append_lemma #1 #n hd0 av;
  assert (from_vec #(n+1) eav = op_Multiply (from_vec #1 hd0) (pow2 n) + from_vec av);
  assert (op_Multiply (from_vec #1 hd0) (pow2 n) = 0);
  assert (from_vec #(n+1) eav = from_vec #n av);
  assert (from_vec #(n+1) eav < pow2 n);

  let nav = BitVector.lognot_vec #n av in
  let neav_r = BitVector.lognot_vec #(n+1) eav in
  let neav_l = Seq.append hd1 nav in
  append_lemma #1 #n hd1 nav;
  assert (from_vec #(n+1) neav_l = (op_Multiply (from_vec #1 hd1) (pow2 n)) + (from_vec #n nav));
  assert (op_Multiply (from_vec #1 hd1) (pow2 n) = pow2 n);
  assert (from_vec #(n+1) neav_l = pow2 n + from_vec #n nav);
  assert (pow2 n + from_vec #n nav = rhs);

  assert (forall (i:pos{i < n+1}). Seq.index neav_r i = Seq.index neav_l i);
  Seq.Base.lemma_eq_intro neav_l neav_r;
  assert (neav_l = neav_r);
  assert (from_vec neav_r = lhs)

val lemma_lognot_one_ext: #n:pos -> a:uint_t n ->
  Lemma (lognot #(n+1) (one_extend a) = lognot #n a)
let lemma_lognot_one_ext #n a =
  let lhs = lognot #(n+1) (one_extend a) in
  let rhs = lognot #n a in
  let av = to_vec a in
  assert (Seq.length av = n);
  let hd0 = Seq.create 1 false in
  let hd1 = Seq.create 1 true in
  let nav = to_vec (lognot #n a) in
  let eav = Seq.append hd1 av in
  append_lemma #1 #n hd1 av;
  append_lemma #1 #n hd0 nav;
  let nav = BitVector.lognot_vec #n av in
  let neav_r = BitVector.lognot_vec #(n+1) eav in
  let neav_l = Seq.append hd0 nav in
  Seq.Base.lemma_eq_elim neav_l neav_r

#set-options "--z3rlimit 10"
val lemma_lognot_value_mod: #n:pos -> a:uint_t n ->
  Lemma
  (requires True)
  (ensures (lognot a = pow2 n - a - 1))
  (decreases n)
let rec lemma_lognot_value_mod #n a =
    if n = 1 then () else
    begin
      assert (-pow2 n <= (-(a+1)) && -(a+1) < 0);

      let av = to_vec a in
      let hd = from_vec #1 (Seq.slice (to_vec a) 0 1) in
      let tl = from_vec #(n-1) (Seq.slice (to_vec a) 1 n) in

      assert (hd = 0 || hd = 1);
      let hdpow = op_Multiply hd (pow2 (n-1)) in

      from_vec_propriety (to_vec a) 1;
      assert (from_vec av = (op_Multiply
                              (from_vec #1     (Seq.slice av 0 1)) (pow2 (n-1))) +
                              (from_vec #(n-1) (Seq.slice av 1 n)));

      let ntl = lognot tl in
      lemma_lognot_value_mod #(n-1) tl;
      assert (ntl = pow2 (n-1) - tl - 1);

      assert (a = hdpow + tl);
      assert (lognot a = lognot #n (hdpow + tl));
      assert (tl < pow2 (n-1));
      if hdpow = 0 then
      begin
        assert (lognot a = lognot #n tl);
        lemma_lognot_zero_ext #(n-1) tl;
        lemma_zero_extend tl
      end
      else
      begin
        lemma_lognot_one_ext #(n-1) tl;
        lemma_one_extend tl
      end
    end

val lemma_lognot_value_zero: #n:pos -> a:uint_t n{a = 0} ->
  Lemma (lognot a = sub_mod (sub_mod 0 a) 1)
let lemma_lognot_value_zero #n a =
  let p = pow2 n in
  calc (==) {
    sub_mod (sub_mod 0 a) 1;
    == { }
    sub_mod ((0 - a) % p) 1;
    == { }
    ((0 - a) % p - 1) % p;
    == { }
    (0 % p - 1) % p;
    == { modulo_lemma 0 p }
    (0 - 1) % p;
    == { lemma_mod_sub_0 p }
    p - 1;
    == { }
    p - 0 - 1;
    == { lemma_lognot_value_mod a }
    lognot a;
  }

#set-options "--z3rlimit 100"
private
val lemma_mod_variation: #n:pos -> a:uint_t n ->
  Lemma (a <> 0 ==> ((-a) % pow2 n) - 1 % pow2 n = (((-a) % pow2 n) - 1) % pow2 n)
let lemma_mod_variation #n a = ()

#set-options "--z3rlimit 5"
val lemma_one_mod_pow2: #n:pos ->
  Lemma (1 = 1 % (pow2 n))
let lemma_one_mod_pow2 #n = ()

#set-options "--z3rlimit 50"
private
val lemma_lognot_value_variation: #n:pos -> a:uint_t n{a <> 0} ->
  Lemma (lognot a = (-a) % pow2 n - 1 % pow2 n)
let lemma_lognot_value_variation #n a =
  let p = pow2 n in
  calc (==) {
    lognot a <: int;
    == { lemma_lognot_value_mod a }
    p - a - 1;
    == { FStar.Math.Lemmas.modulo_lemma a p }
    p - (a % p) - 1;
    == { FStar.Math.Lemmas.modulo_lemma 1 p }
    (p - (a % p)) - (1 % p);
    == { FStar.Math.Lemmas.lemma_mod_sub_1 a p }
    (-a) % p - 1 % p;
  }

val lemma_lognot_value_nonzero: #n:pos -> a:uint_t n{a <> 0} ->
  Lemma (lognot a = sub_mod (sub_mod 0 a) 1)
let lemma_lognot_value_nonzero #n a =
  let p = pow2 n in
  lemma_lognot_value_variation #n a;
  assert (lognot a = (-a) % (pow2 n) - 1 % (pow2 n));
  assert (sub_mod (sub_mod 0 a) 1 = (((0 - a) % p) - 1) % p);
  lemma_mod_variation #n a;
  assert (((-a) % p) - 1 % p = (((-a) % p) - 1) % p);
  assert ((-a) % p - 1 % p = (((0 - a) % p) - 1) % p)

val lemma_lognot_value: #n:pos -> a:uint_t n ->
  Lemma (lognot #n a = sub_mod (sub_mod 0 a) 1)
let lemma_lognot_value #n a =
  if a = 0 then lemma_lognot_value_zero a
  else lemma_lognot_value_nonzero a

val lemma_minus_eq_zero_sub: #n:pos -> a:uint_t n ->
  Lemma (minus #n a = sub_mod #n 0 a)
let lemma_minus_eq_zero_sub #n a =
  let na = lognot a in
  let ma = minus a in
  assert (sub_mod ma 1 = sub_mod (add_mod na 1) 1);
  lemma_sub_add_cancel na 1;
  assert (sub_mod ma 1 = na);
  lemma_lognot_value #n a;
  assert (na = sub_mod (sub_mod 0 a) 1);
  assert (ma = add_mod (sub_mod (sub_mod 0 a) 1) 1);
  lemma_add_sub_cancel (sub_mod 0 a) 1
