
(* CH: because of the stratified nature of F* this variant of
   extensionality doesn't seem to follow from functional and
   propositional extensionality; does it? *)

module FStar.PredicateExtensionality
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

kind Pred (a:Type) = a -> Type

opaque logic type PEq : #a:Type -> (Pred a) -> (Pred a) -> Type =
  (fun (a:Type) (p1:Pred a) (p2:Pred a) -> (forall x. p1 x <==> p2 x))

assume PredicateExtensionality :
    (forall (a:Type) (p1:Pred a) (p2:Pred a).
       {:pattern PEq #a p1 p2} PEq #a p1 p2 <==> p1==p2)
