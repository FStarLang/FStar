module Bug1802

[@(expect_failure [67])]
noeq type test2 (a:Type) : Type0 =
  | Cons2: a -> test2 a

[@(expect_failure [67])]
noeq type test1 (a:Type u#a) : Type0 =
  | Cons1: b:Type u#b -> x:a -> test1 a

noeq type test3 (a:Type u#a) =
  | Cons3: x:a -> test3 a

noeq type test4 (a:Type u#a) : Type0 =
  | Cons4: nat -> test4 a

noeq type test5 (a:Type u#a) (b:Type u#b) =
  | Cons5 : a -> b -> test5 a b
