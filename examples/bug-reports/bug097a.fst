module Bug097a

assume val f : list 'a -> Tot nat

type equivalence (a:Type) = forall x. f x = f x
