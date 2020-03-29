module Bug1913

[@expect_failure]
let _ = assert (False /\ True)

[@expect_failure]
let _ = assert ((/\) False True)

let _ = assert (False \/ True)

let _ = assert ((\/) False True)
