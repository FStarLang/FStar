module FStar.Algebra.CommMonoid

open FStar.Mul

unopteq
type cm (a: Type) =
  | CM : 
    unit: a ->
    mult: (a -> a -> a) ->
    identity: (x: a -> Lemma (mult unit x == x)) ->
    associativity: (x: a -> y: a -> z: a -> Lemma (mult (mult x y) z == mult x (mult y z))) ->
    commutativity: (x: a -> y: a -> Lemma (mult x y == mult y x)) ->
    cm a

let right_identity (#a: Type) (m: cm a) (x: a) : Lemma (CM?.mult m x (CM?.unit m) == x) =
  CM?.commutativity m x (CM?.unit m);
  CM?.identity m x

let int_plus_cm: cm int = CM 0 ( + ) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())

let int_multiply_cm: cm int = CM 1 ( * ) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())

