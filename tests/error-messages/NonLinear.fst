module NonLinear

[@@expect_failure [138]]
let test (l : list int) =
  match l with
  | x :: x :: [] -> 1
  | _ -> 0
