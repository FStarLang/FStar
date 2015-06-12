#define VERIFY

(* STATUS : 
   Useful axioms to handle integer mathematical formulas.
   TODO : Merge together close axioms, and prove those that
          are actually lemmas relying on preceding axioms.
 *) 

module Axiomatic

(* Axiom : euclidian division on nats yield a smaller output than its input *)
#ifndef COMPILE
assume
#endif
val slash_decr_axiom:
  a:nat -> b:pos ->
  Lemma
    (requires (True))
    (ensures (a / b <= a))
#ifdef COMPILE
let slash_decr_axiom a b = ()
#endif

(* Axiom : definition of the "b divides c" relation *)
#ifndef COMPILE
assume
#endif
val slash_star_axiom:
  a:int -> b:pos -> c:nat ->
  Lemma
    (requires ( a * b = c ))
    (ensures ( a = c / b ))
#ifdef COMPILE
let slash_star_axiom a b c = ()
#endif

(* Axiom : definition of the euclidian division for nats *)
#ifndef COMPILE
assume
#endif
val euclidian_div_axiom:
  a:nat -> b:pos -> 
  Lemma
    (requires (True))
    (ensures ( a - b * (a / b) >= 0 /\ a - b * (a / b) < b ))
#ifdef COMPILE
let euclidian_div_axiom a b = ()
#endif

(* Axiom : multiplication is right distributive over addition *)
#ifndef COMPILE
assume
#endif
val distributivity_add_left:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
	(ensures ( (a + b) * c = a * c + b * c ))
#ifdef COMPILE
let distributivity_add_left a b c = ()
#endif

(* Axiom : multiplication is left distributive over addition *)
#ifndef COMPILE
assume
#endif
val distributivity_add_right:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
	(ensures ( a * (b + c) = a * b + a * c ))
#ifdef COMPILE
let distributivity_add_right a b c = ()
#endif

(* Axiom : multiplication is left distributive over substraction *)
#ifndef COMPILE
assume
#endif
val distributivity_sub_right:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
	(ensures ( a * (b - c) = a * b - a * c ))
#ifdef COMPILE
let distributivity_sub_right a b c = ()
#endif

(* Axiom : multiplication is commutative, hence parenthesizing is meaningless *)
#ifndef COMPILE
assume
#endif
val paren_mul_left:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
	(ensures ( a * b * c = ( a * b ) * c))
#ifdef COMPILE
let paren_mul_left a b c = ()
#endif

(* Axiom : multiplication is commutative, hence parenthesizing is meaningless *)
#ifndef COMPILE
assume
#endif
val paren_mul_right:
  a:int -> b:int -> c:int ->
  Lemma 
    (requires (True))
    (ensures ( a * b * c = a * (b * c) ))
#ifdef COMPILE
let paren_mul_right a b c = ()
#endif

(*
#ifndef COMPILE
assume
#endif
val swap_add_plus_minus:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
	(ensures ( a + b - c = (a - c) + b ))
#ifdef COMPILE
let swap_add_plus_minus a b c = ()
#endif
 *)

(* Axiom : multiplication on integers is commutative *)
#ifndef COMPILE
assume
#endif
val swap_mul:
  a:int -> b:int ->
  Lemma (requires (True))
	(ensures ( a * b = b * a ))
#ifdef COMPILE
let swap_mul a b = ()
#endif

(* Axiom : minus applies to the whole term *)
#ifndef COMPILE
assume
#endif
val neg_mul_left:
  a:int -> b:int ->
  Lemma 
    (requires (True))
    (ensures ( -(a*b) = (-a) * b ))
#ifdef COMPILE
let neg_mul_left a b = ()
#endif

(* Axiom : minus applies to the whole term *)
#ifndef COMPILE
assume
#endif
val neg_mul_right:
  a:int -> b:int ->
  Lemma
    (requires (True))
    (ensures ( -(a*b) = a * (-b)))
#ifdef COMPILE
let neg_mul_right a b = ()
#endif

val swap_neg_mul:
   a:int -> b:int ->
   Lemma
     (requires (True))
     (ensures ( (-a) * b = a * (-b)))
let swap_neg_mul a b = 
  neg_mul_left a b;
  neg_mul_right a b		 

(* Axiom : a being multiple of b implies that (-a) is a multiple of b *)
#ifndef COMPILE
assume
#endif
val neg_of_multiple_is_multiple:
  a:int -> b:pos ->
  Lemma
    (requires (True))
    (ensures ( ( a % b = 0 ==> (-a) % b = 0 ) /\ ( a %  b <> 0 ==> (-a) % b <> 0 ) ))
#ifdef COMPILE
let neg_of_multiple_is_multiple a b = ()
#endif

(* Axiom : definition of the modulo of the inverse *)
#ifndef COMPILE
assume
#endif
val neg_modulo:
  a:int -> b:pos ->
  Lemma
    (requires (True))
    (ensures ( b - (a%b) = (-a)%b ))
#ifdef COMPILE
let neg_modulo a b = ()
#endif

(* Axiom : multiplication precedence on addition *)
#ifndef COMPILE
assume
#endif
val mul_binds_tighter:
  a:int -> b:int -> c:int ->
  Lemma
    (requires (True))
    (ensures (
	 a + (b * c) = a + b * c
       ))
#ifdef COMPILE
let mul_binds_tighter a b c = ()
#endif

(* Axiom : multiplication keeps symetric bounds : 
    b > 0 && d > 0 && -b < a < b && -d < c < d ==> - b * d < a * c < b * d *)
#ifndef COMPILE
assume
#endif
val mul_ineq1:
  a:int -> b:nat -> c:int -> d:nat ->
  Lemma
    (requires ( a < b /\ a > -b /\ c < d /\ c > -d))
    (ensures (a * c < b * d /\ a * c > - (b * d)))
#ifdef COMPILE
let mul_ineq1 a b c d = ()
#endif
