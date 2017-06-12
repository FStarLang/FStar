module FStar.Preorder

(* Preordered relations and stable predicates *)

let relation (a:Type) = a -> a -> Type0

let predicate (a:Type) = a -> Type0

let preorder_rel (#a:Type) (rel:relation a) = 
  (forall x. rel x x) /\ (forall x y z. (rel x y /\ rel y z) ==> rel x z)

let preorder (a:Type) = rel:relation a{preorder_rel rel}

let stable (#a:Type) (p:predicate a) (rel:relation a{preorder_rel rel}) =
  forall x y. (p x /\ rel x y) ==> p y
