module FStar.PredicateExtensionality
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let predicate (a: Type) = a -> Tot prop

let peq (#a: Type) (p1: predicate a) (p2: predicate a) = forall x. p1 x <==> p2 x

val predicateExtensionality: a: Type -> p1: predicate a -> p2: predicate a ->
  Lemma (requires (peq #a p1 p2)) (ensures (p1 == p2))
let predicateExtensionality a p1 p2 =
  PropositionalExtensionality.axiom ();
  assert (FunctionalExtensionality.feq p1 p2)

