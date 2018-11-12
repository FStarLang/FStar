module Bug1523

assume val f : #a:Type -> list a -> list a

[@(expect_failure [66])]
let _ =  assert (l_Forall (fun i -> f i == f i)) // just what (forall i. f i == f i) desugars to
