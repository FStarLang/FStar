module Bug1614f

abstract let w (p:Type) : Type = p

[@expect_failure]
let test1 (p:Type) : Pure unit (requires (w (squash p))) (ensures (fun _ -> p)) = ()

#push-options "--smtencoding.valid_intro true --smtencoding.valid_elim true"
 let test2 (p:Type) : Pure unit (requires (w (squash p))) (ensures (fun _ -> p)) = ()

 #restart-solver
 
 let test3 (p:Type) : Pure unit (requires (w (squash p))) (ensures (fun _ -> p)) = ()
#pop-options

[@expect_failure]
let test4 (p:Type) : Pure unit (requires (w (squash p))) (ensures (fun _ -> p)) = ()

#restart-solver
 
[@expect_failure]
let test5 (p:Type) : Pure unit (requires (w (squash p))) (ensures (fun _ -> p)) = ()
