module Bug829

type r = { x : int }

[@(expect_failure [114])]
let true = 2

[@(expect_failure [114])]
let { x = true } = { x = 2 }

[@(expect_failure [19])]
let (x, true) = (2, false)

let (x, true)  = (2, true)

[@(expect_failure [19])]
let (false, false, xx) = (true, true, 9)

[@(expect_failure [114])]
let (true, true) = (2, false)
