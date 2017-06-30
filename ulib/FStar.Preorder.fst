module FStar.Preorder

(* Preordered relations and stable predicates *)

type relation (a:Type) = a -> a -> Type0

type predicate (a:Type) = a -> Type0

let preorder_rel (#a:Type) (rel:relation a) =
  (forall (x:a). rel x x) /\ (forall (x:a) (y:a) (z:a). (rel x y /\ rel y z) ==> rel x z)

type preorder (a:Type) = rel:relation a{preorder_rel rel}

let stable (#a:Type) (p:predicate a) (rel:relation a{preorder_rel rel}) =
  forall (x:a) (y:a). (p x /\ rel x y) ==> p y
