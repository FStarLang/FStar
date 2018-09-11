module FStar.Algebra.CommMonoid

open FStar.Mul

unopteq
type cm (a:Type) =
  | CM :
    unit:a ->
    mult:(a -> a -> a) ->
    identity : (x:a -> Lemma (unit `mult` x == x)) ->
    associativity : (x:a -> y:a -> z:a ->
                      Lemma (x `mult` y `mult` z == x `mult` (y `mult` z))) ->
    commutativity:(x:a -> y:a -> Lemma (x `mult` y == y `mult` x)) ->
    cm a

let right_identity (#a:Type) (m:cm a) (x:a) :
    Lemma (CM?.mult m x (CM?.unit m) == x) =
  CM?.commutativity m x (CM?.unit m); CM?.identity m x

let int_plus_cm : cm int =
  CM 0 (+) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())

let int_multiply_cm : cm int =
  CM 1 ( * ) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())
