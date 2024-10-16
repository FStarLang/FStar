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
module FStar.Math.Lemmas

open FStar.Mul

(* Lemma: definition of Euclidean division *)
val euclidean_div_axiom: a:int -> b:pos -> Lemma
  (a - b * (a / b) >= 0 /\ a - b * (a / b) < b)

val lemma_eucl_div_bound: a:int -> b:int -> q:int -> Lemma
  (requires (a < q))
  (ensures  (a + q * b < q * (b+1)))

val lemma_mult_le_left: a:nat -> b:int -> c:int -> Lemma
  (requires (b <= c))
  (ensures  (a * b <= a * c))

val lemma_mult_le_right: a:nat -> b:int -> c:int -> Lemma
  (requires (b <= c))
  (ensures  (b * a <= c * a))

val lemma_mult_lt_left: a:pos -> b:int -> c:int -> Lemma
  (requires (b < c))
  (ensures  (a * b < a * c))

val lemma_mult_lt_right: a:pos -> b:int -> c:int -> Lemma
  (requires (b < c))
  (ensures  (b * a < c * a))

val lemma_mult_lt_sqr (n:nat) (m:nat) (k:nat{n < k && m < k})
  : Lemma (n * m < k * k)

(* Lemma: multiplication on integers is commutative *)
val swap_mul: a:int -> b:int -> Lemma (a * b = b * a)

val lemma_cancel_mul (a b : int) (n : pos) : Lemma (requires (a * n = b * n)) (ensures (a = b))

(* Lemma: multiplication is right distributive over addition *)
val distributivity_add_left: a:int -> b:int -> c:int -> Lemma
  ((a + b) * c = a * c + b * c)

(* Lemma: multiplication is left distributive over addition *)
val distributivity_add_right: a:int -> b:int -> c:int -> Lemma
  (a * (b + c) = a * b + a * c)

(* Lemma: multiplication is associative, hence parenthesizing is meaningless *)
(* GM: This is really just an identity since the LHS is associated to the left *)
val paren_mul_left: a:int -> b:int -> c:int -> Lemma
  (a * b * c = (a * b) * c)

(* Lemma: multiplication is associative, hence parenthesizing is meaningless *)
val paren_mul_right: a:int -> b:int -> c:int -> Lemma
  (a * b * c = a * (b * c))

(* Lemma: addition is associative, hence parenthesizing is meaningless *)
val paren_add_left: a:int -> b:int -> c:int -> Lemma
  (a + b + c = (a + b) + c)

(* Lemma: addition is associative, hence parenthesizing is meaningless *)
val paren_add_right: a:int -> b:int -> c:int -> Lemma
  (a + b + c = a + (b + c))

val addition_is_associative: a:int -> b:int -> c:int -> Lemma
  (a + b + c = (a + b) + c /\ a + b + c = a + (b + c))

val subtraction_is_distributive: a:int -> b:int -> c:int -> Lemma
  (a - b + c = (a - b) + c /\
   a - b - c = a - (b + c) /\
   a - b - c = (a - b) - c /\
   a + (-b - c) = a - b - c /\
   a - (b - c) = a - b + c)

val swap_add_plus_minus: a:int -> b:int -> c:int -> Lemma
  (a + b - c = (a - c) + b)

(* Lemma: minus applies to the whole term *)
val neg_mul_left: a:int -> b:int -> Lemma (-(a * b) = (-a) * b)

(* Lemma: minus applies to the whole term *)
val neg_mul_right: a:int -> b:int -> Lemma (-(a * b) = a * (-b))

val swap_neg_mul: a:int -> b:int -> Lemma ((-a) * b = a * (-b))

(* Lemma: multiplication is left distributive over subtraction *)
val distributivity_sub_left: a:int -> b:int -> c:int ->
  Lemma ((a - b) * c = a * c - b * c)

(* Lemma: multiplication is right distributive over subtraction *)
val distributivity_sub_right: a:int -> b:int -> c:int ->
  Lemma ((a * (b - c) = a * b - a * c))

(* Lemma: multiplication precedence on addition *)
val mul_binds_tighter: a:int -> b:int -> c:int -> Lemma (a + (b * c) = a + b * c)

val lemma_abs_mul : a:int -> b:int -> Lemma (abs a * abs b = abs (a * b))

val lemma_abs_bound : a:int -> b:nat -> Lemma (abs a < b <==> -b < a /\ a < b)

(* Lemma: multiplication keeps symmetric bounds :
    b > 0 && d > 0 && -b < a < b && -d < c < d ==> - b * d < a * c < b * d *)
val mul_ineq1: a:int -> b:nat -> c:int -> d:nat -> Lemma
    (requires (-b < a /\ a < b /\
               -d < c /\ c < d))
    (ensures  (-(b * d) < a * c /\ a * c < b * d))

(* Zero is neutral for addition *)
val add_zero_left_is_same (n : int) : Lemma(0 + n = n)
val add_zero_right_is_same (n : int) : Lemma(n + 0 = n)

(* One is neutral for multiplication *)
val mul_one_left_is_same (n : int) : Lemma(1 * n = n)
val mul_one_right_is_same (n : int) : Lemma(n * 1 = n)

(* Multiplying by zero gives zero *)
val mul_zero_left_is_zero (n : int) : Lemma(0 * n = 0)
val mul_zero_right_is_zero (n : int) : Lemma(n * 0 = 0)

val nat_times_nat_is_nat: a:nat -> b:nat -> Lemma (a * b >= 0)

val pos_times_pos_is_pos: a:pos -> b:pos -> Lemma (a * b > 0)

val nat_over_pos_is_nat: a:nat -> b:pos -> Lemma (a / b >= 0)

val nat_plus_nat_equal_zero_lemma: a:nat -> b:nat{a + b = 0} -> Lemma(a = 0 /\ b = 0)

val int_times_int_equal_zero_lemma: a:int -> b:int{a * b = 0} -> Lemma(a = 0 \/ b = 0)

val pow2_double_sum: n:nat -> Lemma (pow2 n + pow2 n = pow2 (n + 1))

val pow2_double_mult: n:nat -> Lemma (2 * pow2 n = pow2 (n + 1))

val pow2_lt_compat: n:nat -> m:nat -> Lemma
  (requires (m < n))
  (ensures  (pow2 m < pow2 n))
  (decreases m)

val pow2_le_compat: n:nat -> m:nat -> Lemma
  (requires (m <= n))
  (ensures  (pow2 m <= pow2 n))

val pow2_plus: n:nat -> m:nat -> Lemma
  (ensures (pow2 n * pow2 m = pow2 (n + m)))
  (decreases n)

(* Lemma : definition of the exponential property of pow2 *)
val pow2_minus: n:nat -> m:nat{ n >= m } -> Lemma
  ((pow2 n) / (pow2 m) = pow2 (n - m))

(* Lemma: loss of precision in euclidean division *)
val multiply_fractions (a:int) (n:nonzero) : Lemma (n * ( a / n ) <= a)

(** Same as `small_mod` *)
val modulo_lemma: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))

(** Same as `lemma_div_def` in Math.Lib *)
val lemma_div_mod: a:int -> p:nonzero -> Lemma (a = p * (a / p) + a % p)

val lemma_mod_lt: a:int -> p:pos -> Lemma (0 <= a % p /\ a % p < p /\ (a >= 0 ==> a % p <= a))

val lemma_div_lt_nat: a:int -> n:nat -> m:nat{m <= n} ->
  Lemma (requires (a < pow2 n))
        (ensures  (a / pow2 m < pow2 (n-m)))

val lemma_div_lt (a:int) (n:nat) (m:nat) : Lemma
  (requires m <= n /\ a < pow2 n)
  (ensures a / pow2 m < pow2 (n-m))

val bounded_multiple_is_zero (x:int) (n:pos) : Lemma
  (requires -n < x * n /\ x * n < n)
  (ensures x == 0)

val small_div (a:nat) (n:pos) : Lemma (requires a < n) (ensures a / n == 0)

val small_mod (a:nat) (n:pos) : Lemma (requires a < n) (ensures a % n == a)

val lt_multiple_is_equal (a:nat) (b:nat) (x:int) (n:nonzero) : Lemma
  (requires a < n /\ b < n /\ a == b + x * n)
  (ensures a == b /\ x == 0)

val lemma_mod_plus (a:int) (k:int) (n:pos) : Lemma ((a + k * n) % n = a % n)

val lemma_div_plus (a:int) (k:int) (n:pos) : Lemma ((a + k * n) / n = a / n + k)

val lemma_div_mod_plus (a:int) (k:int) (n:pos)
  : Lemma ((a + k * n) / n = a / n + k /\
           (a + k * n) % n = a % n)

val add_div_mod_1 (a:int) (n:pos)
  : Lemma ((a + n) % n == a % n /\
           (a + n) / n == a / n + 1)

val sub_div_mod_1 (a:int) (n:pos)
  : Lemma ((a - n) % n == a % n /\
           (a - n) / n == a / n - 1)

val cancel_mul_div (a:int) (n:nonzero) : Lemma ((a * n) / n == a)

val cancel_mul_mod (a:int) (n:pos) : Lemma ((a * n) % n == 0)

val lemma_mod_add_distr (a:int) (b:int) (n:pos) : Lemma ((a + b % n) % n = (a + b) % n)

val lemma_mod_sub_distr (a:int) (b:int) (n:pos) : Lemma ((a - b % n) % n = (a - b) % n)

val lemma_mod_sub_0: a:pos -> Lemma ((-1) % a = a - 1)

val lemma_mod_sub_1: a:pos -> b:pos{a < b} -> Lemma ((-a) % b = b - (a%b))

val lemma_mod_mul_distr_l (a:int) (b:int) (n:pos) : Lemma
  (requires True)
  (ensures (a * b) % n = ((a % n) * b) % n)


val lemma_mod_mul_distr_r (a:int) (b:int) (n:pos) : Lemma ((a * b) % n = (a * (b % n)) % n)

val lemma_mod_injective: p:pos -> a:nat -> b:nat -> Lemma
  (requires (a < p /\ b < p /\ a % p = b % p))
  (ensures  (a = b))

val lemma_mul_sub_distr: a:int -> b:int -> c:int -> Lemma
  (a * b - a * c = a * (b - c))

val lemma_div_exact: a:int -> p:pos -> Lemma
  (requires (a % p = 0))
  (ensures  (a = p * (a / p)))

val div_exact_r (a:int) (n:pos) : Lemma
  (requires (a % n = 0))
  (ensures  (a = (a / n) * n))

val lemma_mod_spec: a:int -> p:pos -> Lemma
  (a / p = (a - (a % p)) / p)

val lemma_mod_spec2: a:int -> p:pos -> Lemma
  (let q:int = (a - (a % p)) / p in a = (a % p) + q * p)

val lemma_mod_plus_distr_l: a:int -> b:int -> p:pos -> Lemma
  ((a + b) % p = ((a % p) + b) % p)

val lemma_mod_plus_distr_r: a:int -> b:int -> p:pos -> Lemma
  ((a + b) % p = (a + (b % p)) % p)

val lemma_mod_mod: a:int -> b:int -> p:pos -> Lemma
  (requires (a = b % p))
  (ensures  (a % p = b % p))

(* * Lemmas about multiplication, division and modulo. **)
(* * This part focuses on the situation where          **)
(* * dividend: nat    divisor: pos                     **)
(* * TODO: add triggers for certain lemmas.            **)

(* Lemma: Definition of euclidean division *)
val euclidean_division_definition: a:int -> b:nonzero ->
  Lemma (a = (a / b) * b + a % b)

(* Lemma: Propriety about modulo *)
val modulo_range_lemma: a:int -> b:pos ->
  Lemma (a % b >= 0 && a % b < b)

val small_modulo_lemma_1: a:nat -> b:nonzero ->
  Lemma (requires a < b) (ensures a % b = a)

val small_modulo_lemma_2: a:int -> b:pos ->
  Lemma (requires a % b = a) (ensures a < b)

val small_division_lemma_1: a:nat -> b:nonzero ->
  Lemma (requires a < b) (ensures a / b = 0)

val small_division_lemma_2 (a:int) (n:pos) : Lemma
  (requires a / n = 0)
  (ensures 0 <= a /\ a < n)

(* Lemma: Multiplication by a positive integer preserves order *)
val multiplication_order_lemma: a:int -> b:int -> p:pos ->
  Lemma (a >= b <==> a * p >= b * p)

(* Lemma: Propriety about multiplication after division *)
val division_propriety: a:int -> b:pos ->
  Lemma (a - b < (a / b) * b && (a / b) * b <= a)

(* Internal lemmas for proving the definition of division *)
val division_definition_lemma_1: a:int -> b:pos -> m:int{a - b < m * b} ->
  Lemma (m > a / b - 1)

val division_definition_lemma_2: a:int -> b:pos -> m:int{m * b <= a} ->
  Lemma (m < a / b + 1)

(* Lemma: Definition of division *)
val division_definition: a:int -> b:pos -> m:int{a - b < m * b && m * b <= a} ->
  Lemma (m = a / b)

(* Lemma: (a * b) / b = a; identical to `cancel_mul_div` above *)
val multiple_division_lemma (a:int) (n:nonzero) : Lemma ((a * n) / n = a)

(* Lemma: (a * b) % b = 0 *)
val multiple_modulo_lemma (a:int) (n:pos) : Lemma ((a * n) % n = 0)

(* Lemma: Division distributivity under special condition *)
val division_addition_lemma: a:int -> b:pos -> n:int ->
  Lemma ( (a + n * b) / b = a / b + n )

(* Lemma: Modulo distributivity *)
val modulo_distributivity: a:int -> b:int -> c:pos -> Lemma ((a + b) % c == (a % c + b % c) % c)

val lemma_div_le: a:int -> b:int -> d:pos ->
  Lemma (requires (a <= b))
        (ensures  (a / d <= b / d))

(* Lemma: Division distributivity under special condition *)
val division_sub_lemma (a:int) (n:pos) (b:nat) : Lemma ((a - b * n) / n = a / n - b)

val lemma_mod_plus_mul_distr: a:int -> b:int -> c:int -> p:pos -> Lemma
  (((a + b) * c) % p = ((((a % p) + (b % p)) % p) * (c % p)) % p)

(* Lemma: Modulo distributivity under special condition *)
val modulo_addition_lemma (a:int) (n:pos) (b:int) : Lemma ((a + b * n) % n = a % n)

(* Lemma: Modulo distributivity under special condition *)
val lemma_mod_sub (a:int) (n:pos) (b:int) : Lemma (ensures (a - b * n) % n = a % n)

val mod_mult_exact (a:int) (n:pos) (q:pos) : Lemma
  (requires (a % (n * q) == 0))
  (ensures a % n == 0)

val mod_mul_div_exact (a:int) (b:pos) (n:pos) : Lemma
  (requires (a % (b * n) == 0))
  (ensures (a / b) % n == 0)

val mod_pow2_div2 (a:int) (m:pos) : Lemma
  (requires a % pow2 m == 0)
  (ensures (a / 2) % pow2 (m - 1) == 0)

(* Lemma: Divided by a product is equivalent to being divided one by one *)
val division_multiplication_lemma (a:int) (b:pos) (c:pos) : Lemma
  (a / (b * c) = (a / b) / c)

val modulo_scale_lemma : a:int -> b:pos -> c:pos -> Lemma ((a * b) % (b * c) == (a % c) * b)

val lemma_mul_pos_pos_is_pos (x:pos) (y:pos) : Lemma (x*y > 0)
val lemma_mul_nat_pos_is_nat (x:nat) (y:pos) : Lemma (x*y >= 0)

val modulo_division_lemma: a:nat -> b:pos -> c:pos ->
    Lemma ((a % (b * c)) / b = (a / b) % c)

val modulo_modulo_lemma (a:int) (b:pos) (c:pos) : Lemma
  ((a % (b * c)) % b = a % b)

val pow2_multiplication_division_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
  Lemma ( (a * pow2 c) / pow2 b = a * pow2 (c - b))

val pow2_multiplication_division_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
  Lemma ( (a * pow2 c) / pow2 b = a / pow2 (b - c))

val pow2_multiplication_modulo_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
  Lemma ( (a * pow2 c) % pow2 b = 0 )

val pow2_multiplication_modulo_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
  Lemma ( (a * pow2 c) % pow2 b = (a % pow2 (b - c)) * pow2 c )

val pow2_modulo_division_lemma_1: a:nat -> b:nat -> c:nat{c >= b} ->
  Lemma ( (a % pow2 c) / pow2 b = (a / pow2 b) % (pow2 (c - b)) )

val pow2_modulo_division_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
  Lemma ( (a % pow2 c) / pow2 b = 0 )

val pow2_modulo_modulo_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
  Lemma ( (a % pow2 c) % pow2 b = a % pow2 b )

val pow2_modulo_modulo_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
  Lemma ( (a % pow2 c) % pow2 b = a % pow2 c )

val modulo_add : p:pos -> a:int -> b:int -> c:int -> Lemma
  (requires (b % p = c % p))
  (ensures  ((a + b) % p = (a + c) % p))

val lemma_mod_twice : a:int -> p:pos -> Lemma ((a % p) % p == a % p)

val modulo_sub : p:pos -> a:int -> b:int -> c:int -> Lemma
  (requires ((a + b) % p = (a + c) % p))
  (ensures (b % p = c % p))

val mod_add_both (a:int) (b:int) (x:int) (n:pos) : Lemma
  (requires a % n == b % n)
  (ensures (a + x) % n == (b + x) % n)

val lemma_mod_plus_injective (n:pos) (a:int) (b:nat) (c:nat) : Lemma
  (requires b < n /\ c < n /\ (a + b) % n = (a + c) % n)
  (ensures  b = c)

(* Another characterization of the modulo *)
val modulo_sub_lemma (a : int) (b : nat) (c : pos) :
  Lemma
  (requires (b < c /\ (a - b) % c = 0))
  (ensures (b = a % c))