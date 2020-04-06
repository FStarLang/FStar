module Bug1121b

[@(expect_failure [138])]
let foo () : Tot int =
  match (1,2) with
  | (x,x) -> x

[@(expect_failure [138])]
let foo2 x = match x with (x,x) -> 1

[@(expect_failure [138])]
let foo3 x x = 42

[@(expect_failure [138])]
let foo4 (x:int) =
    let inner_foo x x = x + x in
    inner_foo x x
