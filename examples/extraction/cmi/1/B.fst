module B
type t =
  | T
let test_function = A.id (C.id T)
