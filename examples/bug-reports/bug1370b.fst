module Bug1370b

[@(expect_failure [316])]
effect Ouch1 (a:Type) = Tot False

[@(expect_failure [316])]
effect Ouch2 (x:int) (a:Type) = Tot a

effect Good3 (a:Type) (x:int) = Tot a

effect Good4 (a:Type) (x:int) = PURE a (fun p -> x > 0 /\ (forall y. p y))

effect Good5 (a:Type) (wp:((a -> Type0) -> Type0)) = PURE a wp
