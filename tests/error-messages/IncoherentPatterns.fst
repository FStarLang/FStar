module IncoherentPatterns

[@@expect_failure [297]]
let test (l : list int) =
  match l with
  | Cons x Nil
  | Cons _ (Cons _ Nil) -> ()
  | _ -> ()
