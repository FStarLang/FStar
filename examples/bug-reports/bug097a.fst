module Test

assume val f : list 'a -> Tot nat

type Equivalence (a:Type) = forall x. f x = f x
