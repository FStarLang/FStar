module Bug1614f

// With prop refactoring, squash p : Type0 (not prop),
// so it can't be used directly where prop is expected.
// Test that p (which is prop) works directly in requires/ensures.

let test1 (p:prop) : Pure unit (requires p) (ensures (fun _ -> p)) = ()

#push-options "--smtencoding.valid_intro true --smtencoding.valid_elim true"
 let test2 (p:prop) : Pure unit (requires p) (ensures (fun _ -> p)) = ()

 #restart-solver
 
 let test3 (p:prop) : Pure unit (requires p) (ensures (fun _ -> p)) = ()
#pop-options

let test4 (p:prop) : Pure unit (requires p) (ensures (fun _ -> p)) = ()

#restart-solver
 
let test5 (p:prop) : Pure unit (requires p) (ensures (fun _ -> p)) = ()
