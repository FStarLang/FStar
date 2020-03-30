module Bug1614e

(* Query should not succeed! Second command should remove all facts *)
#set-options "--using_facts_from 'Prims'"
#set-options "--using_facts_from '-*'"

[@(expect_failure [19])]
let test x = assert (x + 1 == 1 + x)
