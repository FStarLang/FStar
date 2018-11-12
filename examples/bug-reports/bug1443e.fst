module Bug1443e

type test (a : unit) =
  | Test : test a

val f : #x:unit -> test x
let f #x = (Test #x)

[@(expect_failure [66])]
let g () : unit = match f with
  | Test -> ()
