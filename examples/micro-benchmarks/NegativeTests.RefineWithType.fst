module NegativeTests.RefineWithType

let t0 : Type0 = int

let t : Type = x:int{t0}
(* Expected error message for this:
(Error) Subtyping check failed; expected type prop; got type Type0 *)
