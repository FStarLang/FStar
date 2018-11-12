module Preorder

(* Preordered relations and stable predicates *)

let relation (a:Type) = a -> a -> Type0

let predicate (a:Type) = a -> Type0

(* NB: It may be better to tag both of the next two definitions
       with the "inline" qualifier.

   This will cause the F* normalizer to produce Z3 proofs obligations
   that have fewer higher-order quantifiers, which is typically better for Z3.
*)
type preorder (#a:Type) (rel:relation a) = 
  (forall x . rel x x) /\ (forall x y z . rel x y /\ rel y z ==> rel x z)

type stable (#a:Type) (rel:relation a{preorder rel}) (p:predicate a) =
  forall x y . p x /\ rel x y ==> p y

(* NB: consider using this instead for readability ...? *)
let preorder_t (a:Type) = rel:relation a{preorder rel}
