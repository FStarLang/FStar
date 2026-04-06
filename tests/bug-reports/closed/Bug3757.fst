module Bug3757

#set-options "--print_expected_failures"

[@@expect_failure [360]]
let match_test (x : int & int) =
  match x with
  | { x = 1 } -> true
  | _ -> false

[@@expect_failure [360]]
let foo () : int & bool = { x=1 }

[@@expect_failure [360]]
let foo () = { _1=1; _2=2 }

type t =
  | X : f1:int -> f2:int -> t

[@@expect_failure [360]]
let _ = {f1=1; f2=2}
