module Math.Lemmas

open FStar.Mul
open Math.Axioms

(* Lemma: definition of the euclidean division for nats *)
val euclidean_div_axiom:
  a:nat -> b:pos ->
  Lemma
    (requires (True))
    (ensures ( a - b * (a / b) >= 0 /\ a - b * (a / b) < b ))
let euclidean_div_axiom a b = ()

(* Lemma: multiplication is right distributive over addition *)
val distributivity_add_left:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( (a + b) * c = a * c + b * c ))
let distributivity_add_left a b c = ()

(* Lemma: multiplication is left distributive over addition *)
val distributivity_add_right:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( a * (b + c) = a * b + a * c ))
let distributivity_add_right a b c = ()

(* Lemma: multiplication is left distributive over substraction *)
val distributivity_sub_right:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( a * (b - c) = a * b - a * c ))
let distributivity_sub_right a b c = ()

(* Lemma: multiplication is commutative, hence parenthesizing is meaningless *)
val paren_mul_left:
  a:int -> b:int -> c:int ->
  Lemma 
    (requires (True))
    (ensures ( a * b * c = ( a * b ) * c))
let paren_mul_left a b c = ()

(* Lemma: multiplication is commutative, hence parenthesizing is meaningless *)
val paren_mul_right:
  a:int -> b:int -> c:int ->
  Lemma
    (requires (True))
    (ensures ( a * b * c = a * (b * c) ))
let paren_mul_right a b c = ()

(* Lemma: addition is commutative, hence parenthesizing is meaningless *)
val paren_add_left:
  a:int -> b:int -> c:int ->
  Lemma 
    (requires (True))
    (ensures ( a + b + c = ( a + b ) + c))
let paren_add_left a b c = ()

(* Lemma: addition is commutative, hence parenthesizing is meaningless *)
val paren_add_right:
  a:int -> b:int -> c:int ->
  Lemma
    (requires (True))
    (ensures ( a + b + c = a + (b + c) ))
let paren_add_right a b c = ()

val addition_is_associative: a:int -> b:int -> c:int -> 
  Lemma (a + b + c = (a + b) + c /\ a + b + c = a + (b + c))
let addition_is_associative a b c = ()

val subtraction_is_distributive: a:int -> b:int -> c:int -> 
  Lemma (a - b + c = (a - b) + c /\ a - b - c = a - (b + c) /\ a - b - c = (a - b) - c
	/\ a + (-b-c) = a - b - c)
let subtraction_is_distributive a b c = ()

val swap_add_plus_minus:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
    (ensures ( a + b - c = (a - c) + b ))
let swap_add_plus_minus a b c = ()

(* Lemma: multiplication on integers is commutative *)
val swap_mul:
  a:int -> b:int ->
  Lemma (requires (True))
 (ensures ( a * b = b * a ))
let swap_mul a b = ()

(* Lemma: minus applies to the whole term *)
val neg_mul_left:
  a:int -> b:int ->
  Lemma
    (requires (True))
    (ensures ( -(a*b) = (-a) * b ))
let neg_mul_left a b = ()

(* Lemma: minus applies to the whole term *)
val neg_mul_right:
  a:int -> b:int ->
  Lemma
    (requires (True))
    (ensures ( -(a*b) = a * (-b)))
let neg_mul_right a b = ()

val swap_neg_mul:
   a:int -> b:int ->
   Lemma
     (requires (True))
     (ensures ( (-a) * b = a * (-b)))
let swap_neg_mul a b =
  neg_mul_left a b;
  neg_mul_right a b
  
(* Lemma: multiplication precedence on addition *)
val mul_binds_tighter:
  a:int -> b:int -> c:int ->
  Lemma
    (requires (True))
    (ensures (
  a + (b * c) = a + b * c
       ))
let mul_binds_tighter a b c = ()

(* Lemma: multiplication keeps symetric bounds :
    b > 0 && d > 0 && -b < a < b && -d < c < d ==> - b * d < a * c < b * d *)
val mul_ineq1:
  a:int -> b:nat -> c:int -> d:nat ->
  Lemma
    (requires ( a < b /\ a > -b /\ c < d /\ c > -d))
    (ensures (a * c < b * d /\ a * c > - (b * d)))
let mul_ineq1 a b c d = ()

val nat_times_nat_is_nat:
  a:nat -> b:nat -> 
  Lemma (requires (True))
	(ensures (a * b >= 0))
let nat_times_nat_is_nat a b = ()

val pos_times_pos_is_pos:
  a:pos -> b:pos -> 
  Lemma (requires (True))
	(ensures (a * b > 0))
let pos_times_pos_is_pos a b = ()

val nat_over_pos_is_nat: a:nat -> b:pos -> Lemma (a / b >= 0)
let nat_over_pos_is_nat a b = ()

val pow2_double_sum:
  n:nat -> Lemma (requires (True)) (ensures (pow2 n + pow2 n = pow2 (n+1))) 
let pow2_double_sum n =
  assert(n = ((n+1)-1));
  assert(pow2 n + pow2 n = 2 * pow2 n)

val pow2_double_mult:
  n:nat -> Lemma (requires (True)) (ensures (2 * pow2 n = pow2 (n+1)))
let pow2_double_mult n =
  assert(2 * pow2 n = pow2 n + pow2 n)

val pow2_increases_1:
  n:nat -> m:nat ->
  Lemma
    (requires (m < n))
    (ensures (pow2 m < pow2 n))
    (decreases (n-m))
let rec pow2_increases_1 n m =
  match n-m with
  | 1 -> ()
  | _ -> pow2_increases_1 (n-1) m; pow2_increases_1 n (n-1)

val pow2_increases_2:
  n:nat -> m:nat ->
  Lemma
    (requires (m <= n))
    (ensures (pow2 m <= pow2 n))
    (decreases (n-m))
let pow2_increases_2 n m =
  match n-m with
  | 0 -> ()
  | _ -> pow2_increases_1 n m

val aux_lemma_0: n:nat -> m:nat -> Lemma ((n-1)+m+1 = n+m)
let aux_lemma_0 n m = ()

val aux_lemma_1: n:nat -> Lemma (0+n = n)
let aux_lemma_1 n = ()

val aux_lemma_2: n:nat -> Lemma (1 * n = n)
let aux_lemma_2 n = ()

val pow2_exp_1:
  n:nat -> m:nat -> 
  Lemma 
    (requires (True))
    (ensures (pow2 n * pow2 m = pow2 (n+m)))
    (decreases n)
let rec pow2_exp_1 n m =
  match n with
  | 0 -> 
    assert(b2t(pow2 n = 1));
    aux_lemma_1 m;
    aux_lemma_2 (pow2 m)
  | i -> 
    cut(i >= 0 /\ i <> 0); 
    cut(b2t(i >= 1)); 
    cut(b2t(n - 1 >= 0)); 
    pow2_exp_1 (n-1) (m); 
    cut(b2t(pow2 (n-1) * pow2 m = pow2 ((n-1)+m)));
    pow2_double_mult ((n-1)+m);
    cut(b2t(2 * pow2 ((n-1)+m) = pow2 ((n-1)+m+1)));
    aux_lemma_0 n m;
    cut(b2t( 2 * (pow2 (n-1) * pow2 m) = pow2 (n+m))); 
    paren_mul_left 2 (pow2 (n-1)) (pow2 m);
    paren_mul_right 2 (pow2 (n-1)) (pow2 m);
    pow2_double_mult (n-1)
    
val nat_mul_1: a:nat -> b:nat -> Lemma (requires True) (ensures (a*b >= 0))
let nat_mul_1 a b = ()

(* Lemma : multiplying by a strictly positive value preserves strict inequalities *)
val mul_pos_strict_incr: a:pos -> b:int -> c:pos -> Lemma (requires (b < c)) (ensures (a * b < a * c /\ b * a < c * a ))
let mul_pos_strict_incr a b c = ()

(* Lemma : multiplying by a positive value preserves inequalities *)
val mul_incr : a:nat -> b:nat -> c:nat -> 
		     Lemma 
		       (requires ( b <= c))
		       (ensures ( a * b <= a * c /\ b * a <= c * a))
let mul_incr a b c = ()

(* Lemma : loss of precision in euclidean division *)
val multiply_fractions:
  a:nat -> n:pos ->
  Lemma
    (requires (True))
    (ensures ( n * ( a / n ) <= a ))
let multiply_fractions a n =
  (euclidean_div_axiom a n)

(* Lemma : distributivity of minus over parenthesized sum *)
val paren_sub: a:int -> b:int -> c:int -> Lemma ((a - (b + c) = a - b - c /\ a - (b - c) = a - b + c))
let paren_sub a b c = ()

val non_zero_nat_is_pos: i:nat -> Lemma (requires (i <> 0)) (ensures (i >= 1))
let non_zero_nat_is_pos i = ()

val non_zero_nat_is_pos_2: n:nat -> Lemma (requires (n<>0)) (ensures (n-1>=0))
let non_zero_nat_is_pos_2 n = ()

val nat_plus_nat_is_nat: n:nat -> m:nat -> Lemma (n+m>=0)
let nat_plus_nat_is_nat n m = ()

val modulo_lemma: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))
let modulo_lemma a b = ()

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val lemma_div_mod: a:nat -> p:pos -> Lemma (a = p * (a / p) + a % p)
let lemma_div_mod a p = ()

val lemma_mod_lt: a:int -> p:pos -> Lemma (0 <= a % p /\ a % p < p)
let lemma_mod_lt a p = ()

val lemma_eq_trans_2: w:int -> x:int -> y:int -> z:int ->
  Lemma
  (requires (w = x /\ x = y /\ y = z))
  (ensures  (x = z))
let lemma_eq_trans_2 w x y z = ()

val lemma_mod_plus: a:nat -> b:nat -> p:pos ->
  Lemma ((a + b * p) % p = a % p)
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

val lemma_mod_injective: p:pos -> a:nat -> b:nat ->
  Lemma
  (requires (a < p /\ b < p /\ a % p = b % p))
  (ensures  (a = b))
let lemma_mod_injective p a b = ()

val lemma_mul_sub_distr: a:int -> b:int -> c:int ->
  Lemma (a * b - a * c = a * (b - c))
let lemma_mul_sub_distr a b c = ()

val lemma_div_exact: a:nat -> p:pos ->
  Lemma
  (requires (a % p = 0))
  (ensures  (a = p * (a / p)))
let lemma_div_exact a p = ()

val lemma_mod_spec: a:nat -> p:pos ->
  Lemma (a / p = (a - (a % p)) / p)
let lemma_mod_spec a p =
  lemma_div_mod a p;
  assert (a = p * (a / p) + a % p);
  assert (a % p = a - p * (a / p));
  assert (a - (a % p) = p * (a / p));
  lemma_mod_plus 0 (a / p) p;
  assert ((p * (a / p)) % p = 0);
  lemma_div_exact (p * (a / p)) p

val lemma_mod_spec2: a:nat -> p:pos ->
  Lemma (let q:nat = (a - (a % p)) / p in a = (a % p) + q * p)
let lemma_mod_spec2 a p =
  lemma_mod_spec a p

val lemma_mod_plus_injective: p:pos -> a:nat -> b:nat -> c:nat ->
  Lemma
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
