module Bug1614f

abstract let w (p:Type) : Type = p

%Fail
let test1 (p:Type) : Pure unit (requires (w (squash p))) (ensures (fun _ -> p)) = ()

#push-options "--smtencoding.valid_intro true --smtencoding.valid_elim true"
 let test2 (p:Type) : Pure unit (requires (w (squash p))) (ensures (fun _ -> p)) = ()

 #restart-solver
 
 let test3 (p:Type) : Pure unit (requires (w (squash p))) (ensures (fun _ -> p)) = ()
#pop-options

%Fail
let test4 (p:Type) : Pure unit (requires (w (squash p))) (ensures (fun _ -> p)) = ()

#restart-solver
 
%Fail
let test5 (p:Type) : Pure unit (requires (w (squash p))) (ensures (fun _ -> p)) = ()
