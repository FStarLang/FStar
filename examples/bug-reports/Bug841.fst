module Bug841

let f1 (|_, _ |) = ()

%Fail [19]
let f2 (| None, _ |) = ()

let f3 (|(_,_), _ |) = ()
