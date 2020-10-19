module IfThen

[@@expect_failure]
let test (b:bool) : int =
  if b then
    42
