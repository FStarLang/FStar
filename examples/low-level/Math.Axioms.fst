module Math.Axioms

open FStar.Mul

(** Necessary axioms **)
(* Axiom: euclidian division on nats yield a smaller output than its input *)
assume val slash_decr_axiom: a:nat -> b:pos -> Lemma (a / b <= a)
(* Axiom: definition of the "b divides c" relation *)
assume val slash_star_axiom: a:int -> b:pos -> c:nat -> Lemma (requires (a * b = c)) (ensures (a = c / b))
(* Axiom: the opposite of a multiple of b is also a multiple of b and vice-versa *)
assume val neg_of_multiple_is_multiple: a:int -> b:pos -> Lemma 
  (requires (a % b = 0)) 
  (ensures ((-a) % b = 0))
assume val neg_of_non_multiple_is_non_multiple: a:int -> b:pos -> Lemma
    (requires (a % b <> 0))
    (ensures ((-a) % b <> 0))

(** Usefull lemmas for future proofs **)
val modulo_lemma_0: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))
let modulo_lemma_0 a b = ()

(* Lemma: definition of the euclidian division for nats *)
val euclidian_div_axiom:
  a:nat -> b:pos ->
  Lemma
    (requires (True))
    (ensures ( a - b * (a / b) >= 0 /\ a - b * (a / b) < b ))
let euclidian_div_axiom a b = ()

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
