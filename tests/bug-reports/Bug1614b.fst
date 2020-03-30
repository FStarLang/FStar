module Bug1614b

assume val x : (y:int{y==1})

#reset-options "--using_facts_from '* -*'"

(* This query used to succeed since -* was badly interpreted as removing a module named `*` *)

[@expect_failure]
let _ = assert (x + 1 == 2)
