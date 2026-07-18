module AQualMismatch

val f : x:int -> int

[@@expect_failure]
let f #x = 1
