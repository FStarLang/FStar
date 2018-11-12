module Unfold
[@"opaque_to_smt"]
unfold let x = 0
let test1 = assert (x = 0)
let test2 y = y + x
let test3 y = assert (test2 y = y)
