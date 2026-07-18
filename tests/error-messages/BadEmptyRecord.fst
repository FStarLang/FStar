module BadEmptyRecord

type t =
  | A of int

[@@expect_failure [360]]
let test (x:t) =
  match x with
  | A {} -> ()
