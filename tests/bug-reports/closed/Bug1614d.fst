module Bug1614d

(* Should work, we first remove all, then we readd what's necessary *)
#set-options "--using_facts_from '-*'"
#set-options "--using_facts_from 'Prims'"

let test x = assert (x + 1 == 1 + x)
