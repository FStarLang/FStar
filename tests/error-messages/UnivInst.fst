module UnivInst

(* errro 200: unexpected number of universe instantiations. *)

let id (#a : Type u#aa) (x : a) : a = x

[@@expect_failure [200]]
let _ = id u#0 u#0 #int 1

let _ = id u#0 #int 1

[@@expect_failure]
let _ = id u#1 #int 1

let foo (#a : Type u#aa) (#b : Type u#bb) (x : a) (y : b) : a & b = (x, y)

[@@expect_failure [200]]
let _ = foo u#0 1 true

let _ = foo u#0 u#0 1 true

[@@expect_failure]
let _ = foo u#0 u#2 1 true

[@@expect_failure [200]]
let _ = foo u#0 u#0 u#0 1 true
