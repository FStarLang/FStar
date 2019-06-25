module Bug1614a

assume val x : (y:int{y==1})

(* An abbreviation for triggering the query *)
let f () : Pure unit (requires (x + 1 == 2)) (ensures (fun () -> True)) = ()

let _ = f ()

#push-options "--using_facts_from '-*'"

 [@(expect_failure [19])] let _ = f ()

 #push-options "--using_facts_from '*'"
  let _ = f ()

  #set-options "--using_facts_from '-*'"
  [@(expect_failure [19])] let _ = f ()

  #reset-options ""
  let _ = f ()

 #pop-options

 [@(expect_failure [19])] let _ = f ()

 #reset-options

 let _ = f ()

#pop-options

let _ = f ()

#set-options "--using_facts_from '-*'"

[@(expect_failure [19])] let _ = f ()

#set-options "--using_facts_from '*'"

let _ = f ()

#set-options "--using_facts_from '-*'"

[@(expect_failure [19])] let _ = f ()

#reset-options

let _ = f ()
