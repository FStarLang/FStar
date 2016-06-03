module IntLibLemmas

open Axioms
open IntLib

val pow2_increases: n:nat -> m:nat -> Lemma 
  (requires (n > m)) (ensures (pow2 n > pow2 m)) (decreases (n-m))
let rec pow2_increases n m = match n - m with | 1 -> () | _ -> pow2_increases (n-1) m; pow2_increases n (n-1)

val pow2_exp: n:nat -> m:nat -> Lemma (pow2 n * pow2 m = pow2 (n+m))
let rec pow2_exp n m =  match n with | 0 -> () | _ -> pow2_exp (n-1) (m)

val pow2_doubles: n:nat -> Lemma (pow2 n + pow2 n = pow2 (n+1))
let pow2_doubles n = ()

assume val pow2_div: n:nat -> m:nat -> Lemma (div (pow2 n) (pow2 m) = pow2 (max (n-m) 0))
assume val div_inequality: a:nat -> b:nat -> c:pos -> 
  Lemma ( (a < b ==> div a c <= div b c) /\ (a <= b ==> div a c <= div b c))
assume val div_pow2_inequality: a:nat -> n:nat{a < pow2 n} -> Lemma (forall (m:nat). m <= n ==> div a (pow2 m) < pow2 (n-m))
assume val pow2_disjoint_ranges: x:nat -> y:nat -> n1:nat -> n2:nat ->
  Lemma (requires (x < pow2 n1 /\ y < pow2 n1 /\ x < pow2 n2 /\ y % pow2 n2 = 0))
	(ensures (x + y < pow2 n1))

val div_positive: a:nat -> b:pos -> Lemma (a / b >= 0)
let div_positive a b = ()

assume val modulo_lemma: a:nat -> b:pos -> Lemma ((a * b) % b = 0)
