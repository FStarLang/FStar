module BugUnfoldAbstractEquational
let t0 (b:bool) =
  match b with
  | true -> int
  | false -> string
let f0 #b (x:t0 b) = ()

abstract
let iint (b:bool) = t0 b

let test #b (i:iint b) = f0 i
