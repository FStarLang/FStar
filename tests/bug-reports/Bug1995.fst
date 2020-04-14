module Bug1995

[@(expect_failure [200])]
let _ = _ u#0

[@(expect_failure [200])]
let _ = () u#0

[@(expect_failure [200])]
let f x = x u#0
