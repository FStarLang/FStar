module FStar.Algebra.CommMonoid

unopteq
type cm (a:Type) =
  | CM :
    unit:a ->
    mult:(a -> a -> a) ->
    right_unitality : (x:a -> Lemma (x `mult` unit == x)) ->
    left_unitality : (x:a -> Lemma (unit `mult` x == x)) ->
    associativity : (x:a -> y:a -> z:a ->
                      Lemma (x `mult` y `mult` z == x `mult` (y `mult` z))) ->
    commutativity:(x:a -> y:a -> Lemma (x `mult` y == y `mult` x)) ->
    cm a

let int_plus_cm : cm int =
  CM 0 (+) (fun x -> ()) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())

let int_multiply_cm : cm int =
  CM 1 op_Multiply (fun x -> ()) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())
