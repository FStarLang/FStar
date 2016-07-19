module Preorder

(* Preordered relations and stable predicates *)

let relation (a:Type) = a -> a -> Type0

let predicate (a:Type) = a -> Type0

type preorder (#a:Type) (rel:relation a) = 
  (forall x . rel x x) /\ (forall x y z . rel x y /\ rel y z ==> rel x z)

type stable (#a:Type) (rel:relation a{preorder rel}) (p:predicate a) =
  forall x y . p x /\ rel x y ==> p y
