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
open FStar.Math.Lib

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Lemma: definition of Euclidean division for nats *)
val euclidean_div_axiom: a:nat -> b:pos -> Lemma
  ((a - b * (a / b) >= 0 /\ a - b * (a / b) < b))
let euclidean_div_axiom a b = ()

val lemma_eucl_div_bound: a:nat -> b:nat -> q:pos -> Lemma
  (requires (a < q))
  (ensures  (a + q * b < q * (b+1)))
let lemma_eucl_div_bound a b q = ()

val lemma_mult_le_left: a:pos -> b:pos -> c:pos -> Lemma
  (requires (b <= c))
  (ensures  (a * b <= a * c))
let lemma_mult_le_left a b c = ()

val lemma_mult_le_right: a:nat -> b:int -> c:int -> Lemma
  (requires (b <= c))
  (ensures  (b * a <= c * a))
let lemma_mult_le_right a b c = ()

val lemma_mult_lt_left: a:pos -> b:pos -> c:pos -> Lemma
  (requires (b < c))
  (ensures  (a * b < a * c))
let lemma_mult_lt_left a b c = ()

val lemma_mult_lt_right: a:nat -> b:int -> c:int -> Lemma
  (requires (b < c))
  (ensures  (b * a <= c * a))
let lemma_mult_lt_right a b c = ()

let lemma_mult_lt_sqr (n:nat) (m:nat) (k:nat{n < k && m < k})
  : Lemma (FStar.Mul.(n * m < k * k))
  = ()

(* Lemma: multiplication is right distributive over addition *)
val distributivity_add_left: a:int -> b:int -> c:int -> Lemma
  ((a + b) * c = a * c + b * c)
let distributivity_add_left a b c = ()

(* Lemma: multiplication is left distributive over addition *)
val distributivity_add_right: a:int -> b:int -> c:int -> Lemma
  ((a * (b + c) = a * b + a * c))
let distributivity_add_right a b c = ()

(* Lemma: multiplication is left distributive over substraction *)
val distributivity_sub_left:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( (a - b) * c = a * c - b * c ))
let distributivity_sub_left a b c = ()

(* Lemma: multiplication is left distributive over substraction *)
val distributivity_sub_right: a:int -> b:int -> c:int -> Lemma
  ((a * (b - c) = a * b - a * c))
let distributivity_sub_right a b c = ()

(* Lemma: multiplication is associative, hence parenthesizing is meaningless *)
val paren_mul_left: a:int -> b:int -> c:int -> Lemma
  (a * b * c = (a * b) * c)
let paren_mul_left a b c = ()

(* Lemma: multiplication is associative, hence parenthesizing is meaningless *)
val paren_mul_right: a:int -> b:int -> c:int -> Lemma
  (a * b * c = a * (b * c))
let paren_mul_right a b c = ()

(* Lemma: addition is associative, hence parenthesizing is meaningless *)
val paren_add_left: a:int -> b:int -> c:int -> Lemma
  (a + b + c = (a + b) + c)
let paren_add_left a b c = ()

(* Lemma: addition is associative, hence parenthesizing is meaningless *)
val paren_add_right: a:int -> b:int -> c:int -> Lemma
  (a + b + c = a + (b + c))
let paren_add_right a b c = ()

val addition_is_associative: a:int -> b:int -> c:int -> Lemma
  (a + b + c = (a + b) + c /\ a + b + c = a + (b + c))
let addition_is_associative a b c = ()

val subtraction_is_distributive: a:int -> b:int -> c:int -> Lemma
  (a - b + c = (a - b) + c /\
   a - b - c = a - (b + c) /\
   a - b - c = (a - b) - c /\
   a + (-b - c) = a - b - c /\
   a - (b - c) = a - b + c)
let subtraction_is_distributive a b c = ()

val swap_add_plus_minus: a:int -> b:int -> c:int -> Lemma
 (a + b - c = (a - c) + b)
let swap_add_plus_minus a b c = ()

(* Lemma: multiplication on integers is commutative *)
val swap_mul: a:int -> b:int -> Lemma (a * b = b * a)
let swap_mul a b = ()

(* Lemma: minus applies to the whole term *)
val neg_mul_left: a:int -> b:int -> Lemma (-(a * b) = (-a) * b)
let neg_mul_left a b = ()

(* Lemma: minus applies to the whole term *)
val neg_mul_right: a:int -> b:int -> Lemma (-(a * b) = a * (-b))
let neg_mul_right a b = ()

val swap_neg_mul: a:int -> b:int -> Lemma ((-a) * b = a * (-b))
let swap_neg_mul a b =
  neg_mul_left a b;
  neg_mul_right a b

(* Lemma: multiplication precedence on addition *)
val mul_binds_tighter: a:int -> b:int -> c:int -> Lemma (a + (b * c) = a + b * c)
let mul_binds_tighter a b c = ()

(* Lemma: multiplication keeps symetric bounds :
    b > 0 && d > 0 && -b < a < b && -d < c < d ==> - b * d < a * c < b * d *)
#reset-options "--initial_fuel 0 --max_fuel 0 --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped"
val mul_ineq1: a:int -> b:nat -> c:int -> d:nat -> Lemma
    (requires (-b < a /\ a < b /\
               -d < c /\ c < d))
    (ensures  (-(b * d) < a * c /\ a * c < b * d))
let mul_ineq1 a b c d = ()

#reset-options "--initial_fuel 0 --max_fuel 0"
val nat_times_nat_is_nat: a:nat -> b:nat -> Lemma (a * b >= 0)
let nat_times_nat_is_nat a b = ()

val pos_times_pos_is_pos: a:pos -> b:pos -> Lemma (a * b > 0)
let pos_times_pos_is_pos a b = ()

val nat_over_pos_is_nat: a:nat -> b:pos -> Lemma (a / b >= 0)
let nat_over_pos_is_nat a b = ()

#reset-options "--initial_fuel 1 --max_fuel 1"

val pow2_double_sum: n:nat -> Lemma (pow2 n + pow2 n = pow2 (n + 1))
let pow2_double_sum n = ()

val pow2_double_mult: n:nat -> Lemma (2 * pow2 n = pow2 (n + 1))
let pow2_double_mult n = ()

val pow2_lt_compat: n:nat -> m:nat -> Lemma
  (requires (m < n))
  (ensures  (pow2 m < pow2 n))
  (decreases (n - m))
let rec pow2_lt_compat n m =
  match n-m with
  | 1 -> ()
  | _ -> pow2_lt_compat (n-1) m; pow2_lt_compat n (n-1)

val pow2_le_compat: n:nat -> m:nat -> Lemma
  (requires (m <= n))
  (ensures  (pow2 m <= pow2 n))
  (decreases (n - m))
let pow2_le_compat n m =
  match n-m with
  | 0 -> ()
  | _ -> pow2_lt_compat n m

val pow2_plus: n:nat -> m:nat -> Lemma
  (ensures (pow2 n * pow2 m = pow2 (n + m)))
  (decreases n)
let rec pow2_plus n m =
  match n with
  | 0 -> ()
  | _ -> pow2_plus (n - 1) m

(* Lemma : definition of the exponential property of pow2 *)
val pow2_minus: n:nat -> m:nat{ n >= m } -> Lemma
  ((pow2 n) / (pow2 m) = pow2 (n - m))
let pow2_minus n m =
  if n = m then ()
  else
    begin
    pow2_lt_compat n m;
    pow2_plus (n - m) m;
    slash_star_axiom (pow2 (n - m)) (pow2 m) (pow2 n)
    end

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Lemma: loss of precision in euclidean division *)
val multiply_fractions (a:int) (n:pos) : Lemma (n * ( a / n ) <= a)
let multiply_fractions (a:int) (n:pos) = ()

val modulo_lemma: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))
let modulo_lemma a b = ()

(** Same as `lemma_div_def` in Math.Lib *)
val lemma_div_mod: a:int -> p:pos -> Lemma (a = p * (a / p) + a % p)
let lemma_div_mod a p = ()

val lemma_mod_lt: a:int -> p:pos -> Lemma (0 <= a % p /\ a % p < p)
let lemma_mod_lt a p = ()


val lemma_div_lt_nat: a:nat -> n:nat -> m:nat{m <= n} ->
  Lemma (requires (a < pow2 n))
        (ensures  (a / pow2 m < pow2 (n-m)))
let lemma_div_lt_nat a n m =
  lemma_div_mod a (pow2 m);
  assert(a = pow2 m * (a / pow2 m) + a % pow2 m);
  pow2_plus m (n-m);
  assert(pow2 n = pow2 m * pow2 (n - m))

val lemma_div_lt (a:int) (n:nat) (m:nat) : Lemma
  (requires m <= n /\ a < pow2 n)
  (ensures a / pow2 m < pow2 (n-m))
let lemma_div_lt a n m =
  if a >= 0 then lemma_div_lt_nat a n m
  else ()


val bounded_multiple_is_zero (x:int) (n:pos) : Lemma
  (requires -n < x * n /\ x * n < n)
  (ensures x == 0)
let bounded_multiple_is_zero (x:int) (n:pos) = ()


val small_div (a:nat) (n:pos) : Lemma (requires a < n) (ensures a / n == 0)
let small_div (a:nat) (n:pos) : Lemma (requires a < n) (ensures a / n == 0) = ()


val small_mod (a:nat) (n:pos) : Lemma (requires a < n) (ensures a % n == a)
let small_mod (a:nat) (n:pos) : Lemma (requires a < n) (ensures a % n == a) = ()


val lt_multiple_is_equal (a:nat) (b:nat) (x:int) (n:pos) : Lemma
  (requires a < n /\ b < n /\ a == b + x * n)
  (ensures a == b /\ x == 0)
let lt_multiple_is_equal (a:nat) (b:nat) (x:int) (n:pos) =
  assert (0 * n == 0);
  bounded_multiple_is_zero x n

#reset-options "--z3rlimit 100 --initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 1 --z3seed 1"

 let lemma_mod_plus_0 (a:int) (b:int) (p:pos) : Lemma
  ((a + b * p) % p - a % p = p * (b + a / p - (a + b * p) / p))
  =
  let z: int = a + b * p in
  lemma_div_mod a p;
  lemma_div_mod z p

#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

 let lemma_mod_plus_1 (a:int) (b:int) (p:pos) : Lemma
  ((a + b * p) % p = a + b * p - p * ((a + b * p) / p))
  = lemma_div_mod (a+b*p) p;
    lemma_mod_lt a p;
    lemma_mod_lt (a + b * p) p

val lemma_eq_trans_2: w:int -> x:int -> y:int -> z:int -> Lemma
  (requires (w = x /\ x = y /\ y = z))
  (ensures  (w = z))
let lemma_eq_trans_2 w x y z = ()

val lemma_mod_plus: a:int -> b:int -> p:pos -> Lemma
  ((a + b * p) % p = a % p)
let lemma_mod_plus a b p =
  lemma_div_mod a p;
  lemma_div_mod (a + b * p) p;
  lemma_mod_lt a p;
  lemma_mod_lt (a + b * p) p;
  lemma_mod_plus_0 a b p;
  lemma_mod_plus_1 a b p;
  cut (a + b * p - p * ((a + b * p) / p) = a - p * (a / p));
  let w = (a + b * p) % p in
  let x = a + b * p - p * ((a + b * p) / p) in
  let z = a % p in
  let y = a - p * (a / p) in
  lemma_eq_trans_2 w x y z


let add_div_mod_1 (a:int) (n:pos) : Lemma ((a + n) % n == a % n /\ (a + n) / n == a / n + 1) =
  lemma_div_mod a n;
  lemma_div_mod (a + n) n;
  // ((a + n) % n) == a % n + (a / n) * n + n - ((a + n) / n) * n
  distributivity_add_left (a / n) 1 n;
  distributivity_sub_left (a / n + 1) ((a + n) / n) n;
  // (((a + n) % n) == a % n + (a / n + 1 - (a + n) / n) * n
  lt_multiple_is_equal ((a + n) % n) (a % n) (a / n + 1 - (a + n) / n) n;
  ()

#push-options "--z3rlimit_factor 4"
let sub_div_mod_1 (a:int) (n:pos) : Lemma ((a - n) % n == a % n /\ (a - n) / n == a / n - 1) =
  lemma_div_mod a n;
  lemma_div_mod (a - n) n;
  // ((a - n) % n) == a % n - n + (a / n) * n - ((a - n) / n) * n
  distributivity_add_left (a / n) 1 n;
  distributivity_sub_left (a / n - 1) ((a - n) / n) n;
  // ((a - n) % n) == a % n + (a / n - 1 - (a - n) / n) * n
  lt_multiple_is_equal ((a - n) % n) (a % n) (a / n - 1 - (a - n) / n) n;
  ()
#pop-options

#reset-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=true --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native --z3rlimit 30"

let rec lemma_div_mod_plus (a:int) (b:int) (n:pos) : Lemma
  (requires True)
  (ensures
    (a + b * n) / n = a / n + b /\
    (a + b * n) % n = a % n
  )
  (decreases (if b > 0 then b else -b))
  =
  if b = 0 then ()
  else if b > 0 then
  (
    lemma_div_mod_plus a (b - 1) n;
    sub_div_mod_1 (a + b * n) n
  )
  else // b < 0
  (
    lemma_div_mod_plus a (b + 1) n;
    add_div_mod_1 (a + b * n) n
  )
#reset-options


val lemma_div_plus (a:int) (b:int) (n:pos) : Lemma ((a + b * n) / n = a / n + b)
let lemma_div_plus (a:int) (b:int) (n:pos) = lemma_div_mod_plus a b n


val cancel_mul_div (a:int) (n:pos) : Lemma ((a * n) / n == a)
let cancel_mul_div (a:int) (n:pos) =
  small_div 0 n;
  lemma_div_plus 0 a n


val cancel_mul_mod (a:int) (n:pos) : Lemma ((a * n) % n == 0)
let cancel_mul_mod (a:int) (n:pos) =
  small_mod 0 n;
  lemma_mod_plus 0 a n


val mod_add_both (a:int) (b:int) (x:int) (n:pos) : Lemma
  (requires a % n == b % n)
  (ensures (a + x) % n == (b + x) % n)
let mod_add_both (a:int) (b:int) (x:int) (n:pos) =
  lemma_div_mod a n;
  lemma_div_mod b n;
  lemma_div_mod (a + x) n;
  lemma_div_mod (b + x) n;
  assert ((a + x) % n == a + x - n * ((a + x) / n));
  assert ((b + x) % n == b + x - n * ((b + x) / n));
  assert ((a + x) % n - (b + x) % n == a - b + n * ((b + x) / n - (a + x) / n));
  lemma_div_plus (b%n + x) (b/n) n;
  lemma_div_plus (a%n + x) (a/n) n;
  swap_mul n (b/n); swap_mul n (a/n); (* ugh *)
  assert ((a + x) % n - (b + x) % n == a - b + n * (b/n + (b%n + x)/n - a/n - (a%n + x)/n));
  assert ((a + x) % n - (b + x) % n == a - b + n * (b/n - a/n));
  distributivity_sub_right n (b/n) (a/n);
  assert ((a + x) % n - (b + x) % n == 0);
  ()


val lemma_mod_add_distr (a:int) (b:int) (n:pos) : Lemma ((a + b % n) % n = (a + b) % n)
let lemma_mod_add_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  // (a + b) % n == (a + (b % n) + (b / n) * n) % n
  lemma_mod_plus (a + (b % n)) (b / n) n

val lemma_mod_sub_distr (a:int) (b:int) (n:pos) : Lemma ((a - b % n) % n = (a - b) % n)
let lemma_mod_sub_distr (a:int) (b:int) (n:pos) =
  lemma_div_mod b n;
  distributivity_sub_left 0 (b / n) n;
  // (a - b) % n == (a - (b % n) - (b / n) * n) % n
  lemma_mod_plus (a - (b % n)) (-(b / n)) n


val lemma_mod_sub_0: a:pos -> Lemma ((-1) % a = a - 1)
let lemma_mod_sub_0 a = ()
val lemma_mod_sub_1: a:pos -> b:pos{a < b} -> Lemma ((-a) % b = b - (a%b))
#push-options "--z3rlimit_factor 20 --max_fuel 0 --max_ifuel 0"
let lemma_mod_sub_1 a b = ()
#pop-options

//NS: not sure why this requires 4 unfoldings
//    it fails initially, and then succeeds on a retry with less fuel; strange
#reset-options "--z3rlimit 20 --initial_ifuel 0 --initial_fuel 0 --z3seed 1"
let lemma_mod_mul_distr_l_0 (a:nat) (b:nat) (p:pos) : Lemma
  ((((a % p) + (a / p) * p) * b) % p = ((a % p) * b + ((a / p) * b) * p) % p)
  = ()

#reset-options "--initial_ifuel 1 --z3rlimit 5"
val lemma_mod_mul_distr_l (a:int) (b:int) (n:pos) : Lemma
  (requires True)
  (ensures (a * b) % n = ((a % n) * b) % n)
  (decreases (if b >= 0 then b else -b))
let rec lemma_mod_mul_distr_l (a:int) (b:int) (n:pos) =
  if b = 0 then
  (
    assert (a * 0 == 0 /\ ((a % n) * 0) == 0);
    small_mod 0 n
  )
  else if b > 0 then
  (
    lemma_mod_mul_distr_l a (b - 1) n;
    distributivity_sub_right a b 1;
    distributivity_sub_right (a % n) b 1;
    // (a * b - a) % n == ((a % n) * b - (a % n)) % n
    lemma_mod_sub_distr ((a % n) * b) a n;
    // (a * b - a) % n = ((a % n) * b - a) % n
    mod_add_both (a * b - a) ((a % n) * b - a) a n
  )
  else
  (
    lemma_mod_mul_distr_l a (b + 1) n;
    distributivity_add_right a b 1;
    distributivity_add_right (a % n) b 1;
    // (a * b + a) % n == ((a % n) * b + (a % n)) % n
    lemma_mod_add_distr ((a % n) * b) a n;
    // (a * b + a) % n = ((a % n) * b + a) % n
    mod_add_both (a * b + a) ((a % n) * b + a) (-a) n
  )

val lemma_mod_mul_distr_r (a:int) (b:int) (n:pos) : Lemma ((a * b) % n = (a * (b % n)) % n)
let lemma_mod_mul_distr_r (a:int) (b:int) (n:pos) = lemma_mod_mul_distr_l b a n

val lemma_mod_injective: p:pos -> a:nat -> b:nat -> Lemma
  (requires (a < p /\ b < p /\ a % p = b % p))
  (ensures  (a = b))
let lemma_mod_injective p a b = ()

val lemma_mul_sub_distr: a:int -> b:int -> c:int -> Lemma
  (a * b - a * c = a * (b - c))
let lemma_mul_sub_distr a b c = ()

val lemma_div_exact: a:int -> p:pos -> Lemma
  (requires (a % p = 0))
  (ensures  (a = p * (a / p)))
let lemma_div_exact a p = ()

val div_exact_r (a:int) (n:pos) : Lemma
  (requires (a % n = 0))
  (ensures  (a = (a / n) * n))
let div_exact_r (a:int) (n:pos) = lemma_div_exact a n

#set-options "--z3rlimit 20"

val lemma_mod_spec: a:int -> p:pos -> Lemma
  (a / p = (a - (a % p)) / p)
let lemma_mod_spec a p =
  lemma_div_mod a p;
  assert (a = p * (a / p) + a % p);
  assert (a % p = a - p * (a / p));
  assert (a - (a % p) = p * (a / p));
  lemma_mod_plus 0 (a / p) p;
  assert ((p * (a / p)) % p = 0);
  lemma_div_exact (p * (a / p)) p

val lemma_mod_spec2: a:int -> p:pos -> Lemma
  (let q:int = (a - (a % p)) / p in a = (a % p) + q * p)
let lemma_mod_spec2 a p =
  lemma_mod_spec a p

val lemma_mod_plus_distr_l: a:int -> b:int -> p:pos -> Lemma
  ((a + b) % p = ((a % p) + b) % p)
let lemma_mod_plus_distr_l a b p =
  let q = (a - (a % p)) / p in
  lemma_mod_spec2 a p;
  lemma_mod_plus (a % p + b) q p

val lemma_mod_plus_distr_r: a:int -> b:int -> p:pos -> Lemma
  ((a + b) % p = (a + (b % p)) % p)
let lemma_mod_plus_distr_r a b p =
  lemma_mod_plus_distr_l b a p

#reset-options "--z3rlimit 50"

val lemma_mod_plus_mul_distr: a:nat -> b:nat -> c:nat -> p:pos -> Lemma
  (((a + b) * c) % p = ((((a % p) + (b % p)) % p) * (c % p)) % p)
let lemma_mod_plus_mul_distr a b c p =
  let init = ((a + b) * c) % p in
                                     //  ((a + b) * c) % p
  lemma_mod_mul_distr_l (a + b) c p; //= (((a + b) % p) * c) % p
  swap_mul ((a + b) % p) c;          //= (c * ((a + b) % p)) % p
  lemma_mod_mul_distr_l c ((a + b) % p) p; //= (c % p * ((a + b) % p)) % p
  let reached = (c % p * ((a + b) % p)) % p in
  assert (init = reached);
  lemma_mod_plus_distr_l a b p;
  lemma_mod_plus_distr_l b (a % p) p

#reset-options "--initial_fuel 0 --max_fuel 0 --max_ifuel 0"

val lemma_mod_mod: a:int -> b:int -> p:pos -> Lemma
  (requires (a = b % p))
  (ensures  (a % p = b % p))
let lemma_mod_mod a b p =
  lemma_mod_lt b p;
  modulo_lemma (b % p) p


(* * Lemmas about multiplication, division and modulo. **)
(* * This part focuses on the situation where          **)
(* * dividend: nat    divisor: pos                     **)
(* * TODO: add triggers for certain lemmas.            **)

(* Lemma: Definition of euclidean division *)
val euclidean_division_definition: a:int -> b:pos ->
    Lemma (a = (a / b) * b + a % b)
let euclidean_division_definition a b = ()

(* Lemma: Propriety about modulo *)
val modulo_range_lemma: a:int -> b:pos ->
    Lemma (a % b >= 0 && a % b < b)
let modulo_range_lemma a b = ()

val small_modulo_lemma_1: a:nat -> b:pos ->
    Lemma (requires a < b) (ensures a % b = a)
let small_modulo_lemma_1 a b = ()
val small_modulo_lemma_2: a:nat -> b:pos ->
    Lemma (requires a % b = a) (ensures a < b)
let small_modulo_lemma_2 a b = ()

val small_division_lemma_1: a:nat -> b:pos ->
    Lemma (requires a < b) (ensures a / b = 0)
let small_division_lemma_1 a b = ()
val small_division_lemma_2 (a:int) (n:pos) : Lemma
  (requires a / n = 0)
  (ensures 0 <= a /\ a < n)
let small_division_lemma_2 (a:int) (n:pos) = lemma_div_mod a n

(* Lemma: Multiplication by a positive integer preserves order *)
val multiplication_order_lemma: a:int -> b:int -> p:pos ->
    Lemma (a >= b <==> a * p >= b * p)
let multiplication_order_lemma a b p = ()

(* Lemma: Propriety about multiplication after division *)
val division_propriety: a:int -> b:pos ->
    Lemma (a - b < (a / b) * b && (a / b) * b <= a)
let division_propriety a b = ()

(* Internal lemmas for proving the definition of division *)
val division_definition_lemma_1: a:int -> b:pos -> m:int{a - b < m * b} ->
    Lemma (m > a / b - 1)
let division_definition_lemma_1 a b m =
  if a / b - 1 < 0 then () else begin
    division_propriety a b;
    multiplication_order_lemma m (a / b - 1) b
  end
val division_definition_lemma_2: a:int -> b:pos -> m:int{m * b <= a} ->
    Lemma (m < a / b + 1)
let division_definition_lemma_2 a b m =
  division_propriety a b;
  multiplication_order_lemma (a / b + 1) m b

(* Lemma: Definition of division *)
val division_definition: a:int -> b:pos -> m:int{a - b < m * b && m * b <= a} ->
    Lemma (m = a / b)
let division_definition a b m =
  division_definition_lemma_1 a b m;
  division_definition_lemma_2 a b m

(* Lemma: (a * b) / b = a *)
val multiple_division_lemma (a:int) (n:pos) : Lemma ((a * n) / n = a)
let multiple_division_lemma (a:int) (n:pos) = cancel_mul_div a n

(* Lemma: (a * b) % b = 0 *)
val multiple_modulo_lemma (a:int) (n:pos) : Lemma ((a * n) % n = 0)
let multiple_modulo_lemma (a:int) (n:pos) = cancel_mul_mod a n

(* Lemma: Division distributivity under special condition *)
val division_addition_lemma: a:int -> b:pos -> n:int ->
    Lemma ( (a + n * b) / b = a / b + n )
let division_addition_lemma a b n = division_definition (a + n * b) b (a / b + n)

let lemma_div_le_ (a:nat) (b:nat) (d:pos) : Lemma
  (requires (a <= b /\ a / d > b / d))
  (ensures  (False))
  = lemma_div_mod a d;
    lemma_div_mod b d;
    cut (d * (a / d) + a % d <= d * (b / d) + b % d);
    cut (d * (a / d) - d * (b / d) <= b % d - a % d);
    distributivity_sub_right d (a/d) (b/d);
    cut (b % d < d /\ a % d < d);
    cut (d * (a/d - b/d) <= d)

val lemma_div_le: a:nat -> b:nat -> d:pos ->
  Lemma (requires (a <= b))
        (ensures  (a / d <= b / d))
let lemma_div_le a b d =
  if a / d > b / d then lemma_div_le_ a b d

(* Lemma: Division distributivity under special condition *)
#reset-options "--initial_fuel 0 --max_fuel 0 --z3cliopt smt.arith.nl=true --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native --z3rlimit 30"
val division_sub_lemma (a:nat) (n:pos) (b:nat) : Lemma ((a - b * n) / n = a / n - b)
let division_sub_lemma (a:nat) (n:pos) (b:nat) = lemma_div_plus a (-b) n
#reset-options

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped"
(* Lemma: Modulo distributivity *)
val modulo_distributivity: a:int -> b:int -> c:pos ->
    Lemma ( (a + b) % c = (a % c + b % c) % c )
let modulo_distributivity a b c =
  euclidean_division_definition a c;
  euclidean_division_definition b c;
  euclidean_division_definition (a % c + b % c) c;
  division_addition_lemma (a - (a / c) * c + b - (b / c) * c) c (a / c + b / c)

(* Lemma: Modulo distributivity under special condition *)
val modulo_addition_lemma (a:int) (n:pos) (b:int) : Lemma ((a + b * n) % n = a % n)
let modulo_addition_lemma (a:int) (n:pos) (b:int) = lemma_mod_plus a b n

(* Lemma: Modulo distributivity under special condition *)
val lemma_mod_sub (a:int) (n:pos) (b:nat) : Lemma (ensures (a - b * n) % n = a % n)
let lemma_mod_sub (a:int) (n:pos) (b:nat) = lemma_mod_plus a (-b) n

val mod_mult_exact (a:int) (n:pos) (q:pos) : Lemma
  (requires (pos_times_pos_is_pos n q; a % (n * q) == 0))
  (ensures a % n == 0)
let mod_mult_exact (a:int) (n:pos) (q:pos) =
  pos_times_pos_is_pos n q;
  lemma_div_mod a (n * q);
  let k = a / (n * q) in
  paren_mul_right k q n;
  // a == (k * q) * n
  cancel_mul_mod (k * q) n

val mod_mul_div_exact (a:int) (b:pos) (n:pos) : Lemma
  (requires (pos_times_pos_is_pos b n; a % (b * n) == 0))
  (ensures (a / b) % n == 0)
let mod_mul_div_exact (a:int) (b:pos) (n:pos) =
  pos_times_pos_is_pos b n;
  lemma_div_mod a (b * n);
  let k = a / (b * n) in
  paren_mul_right k n b;
  // a == (k * n) * b
  cancel_mul_div (k * n) b;
  // a / b = k * n
  cancel_mul_mod k n

#reset-options "--initial_fuel 1 --max_fuel 1"

val mod_pow2_div2 (a:int) (m:pos) : Lemma
  (requires a % pow2 m == 0)
  (ensures (a / 2) % pow2 (m - 1) == 0)
let mod_pow2_div2 (a:int) (m:pos) : Lemma
  (requires a % pow2 m == 0)
  (ensures (a / 2) % pow2 (m - 1) == 0)
  =
  mod_mul_div_exact a 2 (pow2 (m - 1))

// JP: there seems to be a discrepancy in z3 behavior across platforms. This
// goes fine on Windows / CI with rlimit=40, but on Linux systems rlimit=400 is
// needed. Leaving the high rlimit because it doesn't seem to deteriorate the
// total verification time too much (I see ~40 seconds on my machine).
// GM: Noticed the same, set it to 200
#reset-options "--max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr boxwrap --z3rlimit 200"

(* Lemma: Divided by a product is equivalent to being divided one by one *)
val division_multiplication_lemma (a:int) (b:pos) (c:pos) : Lemma
  (pos_times_pos_is_pos b c; a / (b * c) = (a / b) / c)
let division_multiplication_lemma (a:int) (b:pos) (c:pos) =
  pos_times_pos_is_pos b c;
  lemma_div_mod a b;
  lemma_div_mod (a / b) c;
  lemma_div_mod a (b * c);
  let k1 = a / b - ((a / b) / c) * c in // k1 = (a / b) % c
  let k2 = a - (a / (b * c)) * (b * c) in // k2 = a % (b * c)
  distributivity_sub_left (a / b) (((a / b) / c) * c) b;
  paren_mul_right ((a / b) / c) c b;
  swap_mul b c;
  // k1 * b == (a / b) * b - ((a / b) / c) * (b * c)
  // k1 * b - k2 == (a / (b * c) - (a / b) / c) * (b * c) - a % b
  lemma_mult_le_right b 0 k1;
  lemma_mult_le_right b k1 (c - 1);
  distributivity_sub_left c 1 b;
  // 0 <= k1 <= (c - 1)
  // 0 <= k1 * b <= (c - 1) * b
  // 0 <= k2 < b * c
  // 1 - b * c <= k1 * b - k2 <= b * c - b
  distributivity_sub_left (a / (b * c)) ((a / b) / c) (b * c);
  bounded_multiple_is_zero (a / (b * c) - (a / b) / c) (b * c)


let lemma_mul_pos_pos_is_pos (x:pos) (y:pos) : Lemma (x*y > 0) = ()
let lemma_mul_nat_pos_is_nat (x:nat) (y:pos) : Lemma (x*y >= 0) = ()

#set-options "--z3rlimit 50"

let modulo_division_lemma_0 (a:nat) (b:pos) (c:pos) : Lemma
  (a / (b*c) <= a /\ (a - (a / (b * c)) * (b * c)) / b = a / b - ((a / (b * c)) * c))
  = slash_decr_axiom a (b*c);
    cut ( (a / (b*c)) * (b * c) = ((a / (b * c)) * c) * b);
    lemma_div_mod a (b*c);
    division_sub_lemma a b ((a / (b*c)) * c)

val modulo_division_lemma: a:nat -> b:pos -> c:pos ->
    Lemma ( (a % (b * c)) / b = (a / b) % c )
let modulo_division_lemma a b c =
  division_addition_lemma (a - (a / (b * c)) * (b * c)) b ((a / (b * c)) * c);
  let x = (a - (a / (b * c)) * (b * c)) in
  let y = ((a / (b * c)) * c) in
  cut ((x + y * b) % b = x % b);
  lemma_mul_pos_pos_is_pos b c;
  let bc:pos = b * c in
  let a_bc = a/bc in
  distributivity_sub_left a a_bc bc;
  paren_mul_right (a / (b * c)) c b;
  paren_mul_left (a / (b * c)) c b;
  modulo_division_lemma_0 a b c;
  euclidean_division_definition a (b * c);
  division_multiplication_lemma a b c;
  euclidean_division_definition (a / b) c

#set-options "--z3rlimit 150"

val modulo_modulo_lemma (a:int) (b:pos) (c:pos) : Lemma
  (pos_times_pos_is_pos b c; (a % (b * c)) % b = a % b)
let modulo_modulo_lemma (a:int) (b:pos) (c:pos) =
  pos_times_pos_is_pos b c;
  lemma_div_mod a (b * c);
  paren_mul_right (a / (b * c)) c b;
  swap_mul b c;
  lemma_mod_plus (a % (b * c)) ((a / (b * c)) * c) b

#set-options "--z3rlimit 10"

val pow2_multiplication_division_lemma_1: a:nat -> b:nat -> c:nat{c >= b} ->
    Lemma ( (a * pow2 c) / pow2 b = a * pow2 (c - b))
let pow2_multiplication_division_lemma_1 a b c =
  pow2_plus (c - b) b;
  paren_mul_right a (pow2 (c - b)) (pow2 b);
  paren_mul_left a (pow2 (c - b)) (pow2 b);
  multiple_division_lemma (a * pow2 (c - b)) (pow2 b)

val pow2_multiplication_division_lemma_2: a:nat -> b:nat -> c:nat{c <= b} ->
    Lemma ( (a * pow2 c) / pow2 b = a / pow2 (b - c))
let pow2_multiplication_division_lemma_2 a b c =
  pow2_plus c (b - c);
  division_multiplication_lemma (a * pow2 c) (pow2 c) (pow2 (b - c));
  multiple_division_lemma a (pow2 c)

val pow2_multiplication_modulo_lemma_1: a:nat -> b:nat -> c:nat{c >= b} ->
    Lemma ( (a * pow2 c) % pow2 b = 0 )
let pow2_multiplication_modulo_lemma_1 a b c =
  pow2_plus (c - b) b;
  paren_mul_right a (pow2 (c - b)) (pow2 b);
  paren_mul_left a (pow2 (c - b)) (pow2 b);
  multiple_modulo_lemma (a * pow2 (c - b)) (pow2 b)

#set-options "--z3rlimit 350"
val pow2_multiplication_modulo_lemma_2: a:nat -> b:nat -> c:nat{c <= b} ->
    Lemma ( (a * pow2 c) % pow2 b = (a % pow2 (b - c)) * pow2 c )
let pow2_multiplication_modulo_lemma_2 a b c =
  euclidean_division_definition a (pow2 (b - c));
  let q = pow2 (b - c) in
  let r = a % pow2 (b - c) in
  assert(a = q * (a / q) + a % q);
  pow2_plus (b - c) c;
  paren_mul_right (a / pow2 (b - c)) (pow2 (b - c)) (pow2 c);
  paren_mul_left (a / pow2 (b - c)) (pow2 (b - c)) (pow2 c);
  nat_over_pos_is_nat a (pow2 (b - c));
  modulo_addition_lemma ((a % pow2 (b - c)) * pow2 c) (pow2 b) (a / pow2 (b - c));
  multiplication_order_lemma (pow2 (b - c)) (a % pow2 (b - c)) (pow2 c);
  small_modulo_lemma_1 ((a % pow2 (b - c)) * pow2 c) (pow2 b)

#set-options "--z3rlimit 5"

val pow2_modulo_division_lemma_1: a:nat -> b:nat -> c:nat{c >= b} ->
    Lemma ( (a % pow2 c) / pow2 b = (a / pow2 b) % (pow2 (c - b)) )
let pow2_modulo_division_lemma_1 a b c =
  pow2_plus (c - b) b;
  modulo_division_lemma a (pow2 b) (pow2 (c - b))

val pow2_modulo_division_lemma_2: a:nat -> b:nat -> c:nat{c <= b} ->
    Lemma ( (a % pow2 c) / pow2 b = 0 )
let pow2_modulo_division_lemma_2 a b c =
  pow2_le_compat b c;
  small_division_lemma_1 (a % pow2 c) (pow2 b)

val pow2_modulo_modulo_lemma_1: a:nat -> b:nat -> c:nat{c >= b} ->
    Lemma ( (a % pow2 c) % pow2 b = a % pow2 b )
let pow2_modulo_modulo_lemma_1 a b c =
  pow2_plus (c - b) b;
  modulo_modulo_lemma a (pow2 b) (pow2 (c - b))

val pow2_modulo_modulo_lemma_2: a:nat -> b:nat -> c:nat{c <= b} ->
    Lemma ( (a % pow2 c) % pow2 b = a % pow2 c )
let pow2_modulo_modulo_lemma_2 a b c =
  pow2_le_compat b c;
  small_modulo_lemma_1 (a % pow2 c) (pow2 b)

val modulo_add : p:pos -> a:int -> b:int -> c:int -> Lemma
  (requires (b % p = c % p))
  (ensures  ((a + b) % p = (a + c) % p))
let modulo_add p a b c =
  modulo_distributivity a b p;
  modulo_distributivity a c p

val lemma_mod_twice : a:int -> p:pos -> Lemma ((a % p) % p == a % p)
let lemma_mod_twice a p = lemma_mod_mod (a % p) a p

val modulo_sub : p:pos -> a:int -> b:int -> c:int -> Lemma
  (requires ((a + b) % p = (a + c) % p))
  (ensures (b % p = c % p))

let modulo_sub p a b c =
  modulo_distributivity a b p;
  modulo_distributivity a c p;
  // have : (a % p + b % p) % p = (a % p + c % p) % p
  assert ((a % p + b % p) % p = (a % p + c % p) % p);
  euclidean_division_definition a p;
  let q = a / p in
  let r = a % p in
  assert ((r + b % p) % p = (r + c % p) % p);
  if r = 0 then (
    lemma_mod_twice b p;
    lemma_mod_twice c p
  ) else (
    assert (r > 0);
    lemma_mod_twice a p;

    lemma_mod_sub_1 r p; // gives ((-r) % p) = p - (r % p)
                         // ; and so r = r % p = p - ((-r) % p) = p - h

    let h = (-r) % p in

    // add h to both sides, that is (p-r)
    modulo_add p h (r + b % p) (r + c % p);

    // cancel the extra p
    lemma_mod_plus (b % p) 1 p;
    lemma_mod_plus (c % p) 1 p;
    lemma_mod_twice b p;
    lemma_mod_twice c p
  )

val lemma_mod_plus_injective (n:pos) (a:int) (b:nat) (c:nat) : Lemma
  (requires b < n /\ c < n /\ (a + b) % n = (a + c) % n)
  (ensures  b = c)
let lemma_mod_plus_injective (n:pos) (a:int) (b:nat) (c:nat) =
  small_mod b n;
  small_mod c n;
  mod_add_both (a + b) (a + c) (-a) n
