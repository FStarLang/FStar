module Math.Axioms

open FStar.Mul

(** Necessary axioms **)

(* Axiom: euclidean division on nats yield a smaller output than its input *)
assume val slash_decr_axiom: a:nat -> b:pos -> Lemma (a / b <= a)

(* Axiom: definition of the "b divides c" relation *)
assume val slash_star_axiom: a:nat -> b:pos -> c:nat -> Lemma
  (requires (a * b = c))
  (ensures  (a = c / b))

(* TODO: these last two axioms are currently not used *)

(* Axiom: the opposite of a multiple of b is also a multiple of b and vice-versa *)
assume val neg_of_multiple_is_multiple: a:int -> b:pos -> Lemma
  (requires (a % b = 0)) 
  (ensures  ((-a) % b = 0))

assume val neg_of_non_multiple_is_non_multiple: a:int -> b:pos -> Lemma
  (requires (a % b <> 0))
  (ensures  ((-a) % b <> 0))
