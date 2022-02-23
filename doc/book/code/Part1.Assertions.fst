module Part1.Assertions
open FStar.Mul
let sqr_is_nat (x:int) : unit = assert (x * x >= 0)

[@@expect_failure[19]]
let sqr_is_pos (x:int) : unit = assert (x * x > 0)


//SNIPPET_START: max
let max x y = if x > y then x else y
let _ = assert (max 0 1 = 1)
let _ = assert (forall x y. max x y >= x /\
                            max x y >= y /\
                            (max x y = x \/ max x y = y))
//SNIPPET_END: max
