module MutualRecPositivity

[@@expect_failure [3]]
noeq
type t =
  | T : s -> t
and s =
  | S : (t -> t) -> s
