module Bug2245

assume val a: int&int&int

[@@expect_failure [189]]
let b: (int&int)&int = a
