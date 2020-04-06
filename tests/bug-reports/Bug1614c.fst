module Bug1614c

(* Funnily enough, the double space below used to be interpreted as `*` *)
#set-options "--using_facts_from '-* Fake1  Fake2'"

(* This should fail if Prims is not in the set of facts *)
[@expect_failure]
let test x = assert (x + 1 == 1 + x)
