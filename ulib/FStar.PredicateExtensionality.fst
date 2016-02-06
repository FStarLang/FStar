
(* CH: because of the stratified nature of F* this variant of
   extensionality doesn't seem to follow from functional and
   propositional extensionality; does it? *)

module FStar.PredicateExtensionality
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let predicate (a:Type) = a -> Type

let peq (#a:Type) (p1:predicate a) (p2:predicate a) = forall x. p1 x <==> p2 x

assume val predicateExtensionality : a:Type -> p1:predicate a -> p2:predicate a ->
  Lemma (requires True)
	(ensures (peq #a p1 p2 <==> p1==p2))
	[SMTPat (peq #a p1 p2)]
