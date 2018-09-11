module Bug1535a

exception E1 of int

[@expect_failure]
let f (e:exn) : Tot int =
  match e with
  | E1 f -> f
