module Bug1802

[@(expect_failure [67])]
noeq type test (a:Type u#a) : Type0 =
  | Cons: b:Type u#b -> x:a -> test a
