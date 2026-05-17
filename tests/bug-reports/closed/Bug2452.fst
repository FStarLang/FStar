module Bug2452

[@@expect_failure]
let f () : int = (-1) <: nat

[@@expect_failure]
let f x : bool = true <: (b:bool{false})

[@@expect_failure]
let g (x : bool) : bool = x <: (b:bool{false})

(* This works, h is just inferred to have a refined type. *)
let h x : bool = x <: (b:bool{false})

[@@expect_failure]
let q = f true

[@@expect_failure]
let z : bool = true <: (b:bool{false})
