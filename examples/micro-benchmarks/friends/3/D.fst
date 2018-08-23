module D
friend B
open C
let f1 (s:C.state) : A.t = let y:B.u = s.x in y // SUCCEEDS
let f2 (s:C.state) : A.t = s.x // FAILS
