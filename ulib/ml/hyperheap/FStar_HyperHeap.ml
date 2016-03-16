type t = unit
type rid = unit
type ('a, 'b) rref = 'b ref
let root = ()
type ('a, 'b, 'c) fresh_region = unit
let extends a b = true
let as_ref i r = r
