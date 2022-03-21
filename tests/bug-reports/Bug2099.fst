module Bug2099

[@@expect_failure [19]]
let x = 1 / 0

[@@expect_failure [19]]
let _ = assert_norm (1 / 0 == 42)
