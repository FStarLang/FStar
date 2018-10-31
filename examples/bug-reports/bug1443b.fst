module Bug1443b

[@(expect_failure [66])]
let test =
   let rec blah i = () in ()
