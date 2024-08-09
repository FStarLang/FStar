module Bug2245

assume val a: int*int*int

[@@expect_failure]
let b: (int*int)*int = a
