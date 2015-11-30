(*--build-config 
  --*)

(* STATUS :
   Useful axioms to handle integer mathematical formulas.
   TODO : Merge together close axioms, and prove those that
          are actually lemmas relying on preceding axioms.
 *)
module Axiomatic
(* Axiom : euclidian division on nats yield a smaller output than its input *)
assume val slash_decr_axiom:
  a:nat -> b:pos ->
  Lemma
    (requires (True))
    (ensures (a / b <= a))

(* Axiom : definition of the "b divides c" relation *)
assume val slash_star_axiom:
  a:int -> b:pos -> c:nat ->
  Lemma
    (requires ( a * b = c ))
    (ensures ( a = c / b ))

(* Axiom : definition of the euclidian division for nats *)
assume val euclidian_div_axiom:
  a:nat -> b:pos ->
  Lemma
    (requires (True))
    (ensures ( a - b * (a / b) >= 0 /\ a - b * (a / b) < b ))

(* Axiom : multiplication is right distributive over addition *)
assume val distributivity_add_left:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( (a + b) * c = a * c + b * c ))

(* Axiom : multiplication is left distributive over addition *)
assume val distributivity_add_right:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( a * (b + c) = a * b + a * c ))

(* Axiom : multiplication is left distributive over substraction *)
assume val distributivity_sub_right:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( a * (b - c) = a * b - a * c ))

(* Axiom : multiplication is commutative, hence parenthesizing is meaningless *)
assume val paren_mul_left:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( a * b * c = ( a * b ) * c))

(* Axiom : multiplication is commutative, hence parenthesizing is meaningless *)
assume val paren_mul_right:
  a:int -> b:int -> c:int ->
  Lemma
    (requires (True))
    (ensures ( a * b * c = a * (b * c) ))

(*
assume val swap_add_plus_minus:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
 (ensures ( a + b - c = (a - c) + b ))

 *)
(* Axiom : multiplication on integers is commutative *)
assume val swap_mul:
  a:int -> b:int ->
  Lemma (requires (True))
 (ensures ( a * b = b * a ))

(* Axiom : minus applies to the whole term *)
assume val neg_mul_left:
  a:int -> b:int ->
  Lemma
    (requires (True))
    (ensures ( -(a*b) = (-a) * b ))

(* Axiom : minus applies to the whole term *)
assume val neg_mul_right:
  a:int -> b:int ->
  Lemma
    (requires (True))
    (ensures ( -(a*b) = a * (-b)))

val swap_neg_mul:
   a:int -> b:int ->
   Lemma
     (requires (True))
     (ensures ( (-a) * b = a * (-b)))
let swap_neg_mul a b =
  neg_mul_left a b;
  neg_mul_right a b
(* Axiom : a being multiple of b implies that (-a) is a multiple of b *)
assume val neg_of_multiple_is_multiple:
  a:int -> b:pos ->
  Lemma
    (requires (True))
    (ensures ( ( a % b = 0 ==> (-a) % b = 0 ) /\ ( a % b <> 0 ==> (-a) % b <> 0 ) ))

(* Axiom : definition of the modulo of the inverse *)
assume val neg_modulo:
  a:int -> b:pos ->
  Lemma
    (requires (True))
    (ensures ( b - (a%b) = (-a)%b ))

(* Axiom : multiplication precedence on addition *)
assume val mul_binds_tighter:
  a:int -> b:int -> c:int ->
  Lemma
    (requires (True))
    (ensures (
  a + (b * c) = a + b * c
       ))

(* Axiom : multiplication keeps symetric bounds :
    b > 0 && d > 0 && -b < a < b && -d < c < d ==> - b * d < a * c < b * d *)
assume val mul_ineq1:
  a:int -> b:nat -> c:int -> d:nat ->
  Lemma
    (requires ( a < b /\ a > -b /\ c < d /\ c > -d))
    (ensures (a * c < b * d /\ a * c > - (b * d)))

assume val ineq_axiom:
  unit ->
  Lemma
    (requires (True))
    (ensures (forall (a:nat) (b:nat) (c:nat). a * c <= b * c <==> a <= b))

