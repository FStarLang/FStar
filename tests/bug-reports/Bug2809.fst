module Bug2809

[@@expect_failure]
noeq
type t : eqtype =
  | B of (int -> int)

(* let test (x y : t) = if x = y then 1 else 0 *)
