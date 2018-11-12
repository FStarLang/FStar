module FStar.PredicateExtensionality
module F = FStar.FunctionalExtensionality
module P = FStar.PropositionalExtensionality

let predicate (a:Type) = a -> Tot prop

let peq (#a:Type) (p1:predicate a) (p2:predicate a) =
  forall x. (p1 x <==> p2 x)

let predicateExtensionality (a:Type) (p1 p2:predicate a)
  : Lemma (requires (peq #a p1 p2))
  	  (ensures (F.on_domain a p1==F.on_domain a p2))
  = P.axiom();
    assert (F.feq p1 p2)

