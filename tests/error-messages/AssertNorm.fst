module AssertNorm

(* The failure is in the assert_norm that's what should be highlighted. *)

[@@expect_failure [19]]
let f (x y z : int) =
  assert_norm (x + x == y + y);
  assert (x + y == y + x);
  42
