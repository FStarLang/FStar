module Bug3771

[@@expect_failure [132]]
let f (x:int) = 1
and g (x:int) = 2

[@@expect_failure [132]]
let foo () =
  let f (x:int) = 1
  and g (x:int) = 2
  in
  ()
