module FailwithPath

open FStar.All

let test0 (x:int) : ML nat =
  if x < 0 then failwith "";
  x
