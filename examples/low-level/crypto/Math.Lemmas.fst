module Math.Lemmas

open FStar.Mul
open Math.Axioms

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

(* Lemma: multiplication is right distributive over addition *)
val distributivity_add_left: a:int -> b:int -> c:int -> Lemma
  ((a + b) * c = a * c + b * c)
let distributivity_add_left a b c = ()

(* Lemma: multiplication is left distributive over addition *)
val distributivity_add_right: a:int -> b:int -> c:int -> Lemma
  ((a * (b + c) = a * b + a * c))
let distributivity_add_right a b c = ()

(* Lemma: multiplication is left distributive over substraction *)
val distributivity_sub_right: a:int -> b:int -> c:int -> Lemma
  ((a * (b - c) = a * b - a * c))
let distributivity_sub_right a b c = ()

(* Lemma: multiplication is commutative, hence parenthesizing is meaningless *)
val paren_mul_left: a:int -> b:int -> c:int -> Lemma
  (a * b * c = (a * b) * c)
let paren_mul_left a b c = ()

(* Lemma: multiplication is commutative, hence parenthesizing is meaningless *)
val paren_mul_right: a:int -> b:int -> c:int -> Lemma
  (a * b * c = a * (b * c))
let paren_mul_right a b c = ()

(* Lemma: addition is commutative, hence parenthesizing is meaningless *)
val paren_add_left: a:int -> b:int -> c:int -> Lemma
  (a + b + c = (a + b) + c)
let paren_add_left a b c = ()

(* Lemma: addition is commutative, hence parenthesizing is meaningless *)
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
val mul_ineq1: a:int -> b:nat -> c:int -> d:nat -> Lemma
    (requires (a < b /\ a > -b /\ c < d /\ c > -d))
    (ensures  (a * c < b * d /\ a * c > - (b * d)))
let mul_ineq1 a b c d = ()

val nat_times_nat_is_nat: a:nat -> b:nat -> Lemma (a * b >= 0)
let nat_times_nat_is_nat a b = ()

val pos_times_pos_is_pos: a:pos -> b:pos -> Lemma (a * b > 0)
let pos_times_pos_is_pos a b = ()

val nat_over_pos_is_nat: a:nat -> b:pos -> Lemma (a / b >= 0)
let nat_over_pos_is_nat a b = ()

#set-options "--initial_fuel 1 --max_fuel 1"

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

(* Lemma: loss of precision in euclidean division *)
val multiply_fractions: a:nat -> n:pos -> Lemma (n * ( a / n ) <= a)
let multiply_fractions a n = euclidean_div_axiom a n

#set-options "--z3timeout 30 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val modulo_lemma: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))
let modulo_lemma a b = ()

val lemma_div_mod: a:nat -> p:pos -> Lemma (a = p * (a / p) + a % p)
let lemma_div_mod a p = ()

val lemma_mod_lt: a:int -> p:pos -> Lemma (0 <= a % p /\ a % p < p)
let lemma_mod_lt a p = ()

val lemma_eq_trans_2: w:int -> x:int -> y:int -> z:int -> Lemma
  (requires (w = x /\ x = y /\ y = z))
  (ensures  (x = z))
let lemma_eq_trans_2 w x y z = ()

val lemma_mod_plus: a:nat -> b:nat -> p:pos -> Lemma
  ((a + b * p) % p = a % p)
let lemma_mod_plus a b p =
  lemma_div_mod a p;
  lemma_div_mod (a + b * p) p;
  lemma_mod_lt a p;
  lemma_mod_lt (a + b * p) p;
  assert ((a + b * p) % p - a % p = p * (b + a / p - (a + b * p) / p));
  assert ((a + b * p) % p = a + b * p - p * ((a + b * p) / p));
  assert (a % p = a - p * (a / p));
  assert (a + b * p - p * ((a + b * p) / p) = a - p * (a / p));
  let w = (a + b * p) % p in
  let x = a + b * p - p * ((a + b * p) / p) in
  let z = a % p in
  let y = a - p * (a / p) in
  lemma_eq_trans_2 w x y z

val lemma_mod_injective: p:pos -> a:nat -> b:nat -> Lemma
  (requires (a < p /\ b < p /\ a % p = b % p))
  (ensures  (a = b))
let lemma_mod_injective p a b = ()

val lemma_mul_sub_distr: a:int -> b:int -> c:int -> Lemma
  (a * b - a * c = a * (b - c))
let lemma_mul_sub_distr a b c = ()

val lemma_div_exact: a:nat -> p:pos -> Lemma
  (requires (a % p = 0))
  (ensures  (a = p * (a / p)))
let lemma_div_exact a p = ()

val lemma_mod_spec: a:nat -> p:pos -> Lemma
  (a / p = (a - (a % p)) / p)
let lemma_mod_spec a p =
  lemma_div_mod a p;
  assert (a = p * (a / p) + a % p);
  assert (a % p = a - p * (a / p));
  assert (a - (a % p) = p * (a / p));
  lemma_mod_plus 0 (a / p) p;
  assert ((p * (a / p)) % p = 0);
  lemma_div_exact (p * (a / p)) p

val lemma_mod_spec2: a:nat -> p:pos -> Lemma
  (let q:nat = (a - (a % p)) / p in a = (a % p) + q * p)
let lemma_mod_spec2 a p =
  lemma_mod_spec a p

val lemma_mod_plus_injective: p:pos -> a:nat -> b:nat -> c:nat -> Lemma
  (requires (b < p /\ c < p /\ (a + b) % p = (a + c) % p))
  (ensures  (b = c))
let lemma_mod_plus_injective p a b c =
  lemma_mod_spec2 (a + b) p;
  lemma_mod_spec2 (a + c) p;
  let r = (a + b) % p in
  let qb = ((a + b) - r) / p in
  let qc = ((a + c) - r) / p in
  assert (a + b = (a + c) + p * qb - p * qc);
  lemma_mul_sub_distr p qb qc;
  assert (b = c + p * (qb - qc));
  assert (qb - qc = 0)

val lemma_mod_plus_distr_l: a:nat -> b:nat -> p:pos -> Lemma
  ((a + b) % p = ((a % p) + b) % p)
let lemma_mod_plus_distr_l a b p =
  let q = (a - (a % p)) / p in
  lemma_mod_spec2 a p;
  lemma_mod_plus (a % p + b) q p

#reset-options

val lemma_mod_mul_distr_l: a:nat -> b:nat -> p:pos -> Lemma
  ((a * b) % p = ((a % p) * b) % p)
let lemma_mod_mul_distr_l a b p =
  lemma_div_mod a p;
  assert ((a * b) % p = (((a % p) + (a / p) * p) * b) % p);
  assert ((a * b) % p = ((a % p) * b + ((a / p) * b) * p) % p);
  lemma_mod_plus ((a % p) * b) ((a / p) * b) p

val lemma_mod_plus_mul_distr: a:nat -> b:nat -> c:nat -> p:pos -> Lemma
  (((a + b) * c) % p = ((((a % p) + (b % p)) % p) * (c % p)) % p)
let lemma_mod_plus_mul_distr a b c p =
  lemma_mod_mul_distr_l (a + b) c p;
  lemma_mod_mul_distr_l c ((a + b) % p) p;
  lemma_mod_plus_distr_l a b p;
  lemma_mod_plus_distr_l b (a % p) p

val lemma_mod_mod: a:int -> b:int -> p:pos -> Lemma
  (requires (a = b % p))
  (ensures  (a % p = b % p))
let lemma_mod_mod a b p =
  lemma_mod_lt b p;
  modulo_lemma (b % p) p
