module MustEraseForExtraction
[@(expect_failure [318])]
let t1 = unit

let t2 = unit

[@(expect_failure [318])]
let t3 = bool
