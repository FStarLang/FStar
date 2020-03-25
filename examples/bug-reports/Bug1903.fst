module Bug1903

[@(expect_failure [178])] (* bad ascription *)
let None : option unit = Some ()

[@(expect_failure [19])] (* incomplete match *)
let None = Some ()

[@(expect_failure [72])] (* X unbound *)
let X = 42

[@(expect_failure [114])] (* type doesn't match *)
let None = 42

[@(expect_failure [19])] (* incomplete match *)
let 0 = 1

let 0 = 0 (* OK *)
