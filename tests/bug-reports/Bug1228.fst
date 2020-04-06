module Bug1228

[@(expect_failure [19])]
let 2 = 4  // Incomplete pattern (ok in OCaml)

[@(expect_failure [19])]
let [] = [1]  // idem

[@(expect_failure [178])]
let 2: int = 4  // Incomplete pattern (ok in OCaml)

[@(expect_failure [178])]
let []: list int = [1]  // idem

[@(expect_failure [178])]
let (): int = 4  // int to unit?

let foo (x: int): int = x

[@(expect_failure [114])]
let () = foo  // function to unit?

[@(expect_failure [114])]
let 3 = foo  // function to int?

[@(expect_failure [114])]
let 4 = [1; 2; 3]  // list int to int?

[@(expect_failure [178])]
let (): int -> int = foo  // function to unit?

[@(expect_failure [178])]
let 3: int -> int = foo  // function to int?

[@(expect_failure [178])]
let 4: list int = [1; 2; 3]  // list int to int?
