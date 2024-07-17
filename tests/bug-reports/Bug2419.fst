module Bug2419

[@@expect_failure [185]]
type t0 =
 | T0 : squash t0

[@@expect_failure [185]]
type t1 (x : nat) =
 | T1 : squash (t1 x)

[@@expect_failure [185]]
type t2 (x y : nat) =
 | T2 : squash (t2 x y)
