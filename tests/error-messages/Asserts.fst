module Asserts

[@@expect_failure [19]]
let test (x y : int) =
  let x = y + 1 in
  assert (x == y)

[@@expect_failure [19]]
let test2 (x y : int) =
  let x = y + 1 in
  assert (x == y);
  123

[@@expect_failure [19]]
let test3 (x y : int) =
  assert False;
  let x = y + 1 in
  123
