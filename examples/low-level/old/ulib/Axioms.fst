module Axioms

(** Axioms **)
let op_Star = op_Multiply
assume val modulo_lemma: a:int -> b:pos -> Lemma ( (b*a) % b = 0 )
assume val slash_decr_axiom: a:nat -> b:pos -> Lemma (a / b <= a) 
assume val neg_modulo: a:int -> b:pos -> Lemma ((-a) % b = (b - (a%b)) % b)
// TODO: prove those two based on the one above  
assume val neg_of_multiple_is_multiple: a:int -> b:pos -> 
  Lemma (requires (a % b = 0)) (ensures ((-a) % b = 0))
assume val neg_of_non_multiple_is_non_multiple: a:int -> b:pos -> 
  Lemma (requires (a % b <> 0)) (ensures ((-a) % b <> 0))

(** Lemmas **)
val euclidian_division_definition:  a:nat -> b:pos -> Lemma (a = (a/b)*b + (a%b))
let euclidian_division_definition a b = ()

val division_lemma: a:nat -> b:pos -> Lemma ( (a*b)/b = a )
let division_lemma a b = 
  euclidian_division_definition (a*b) b;
  modulo_lemma a b

val slash_star_axiom:
  a:int -> b:pos -> c:nat ->
  Lemma (requires ( a * b = c )) (ensures ( a = c / b ))
let slash_star_axiom a b c = 
  if a >= 0 then division_lemma a b
  else division_lemma (-a) b
