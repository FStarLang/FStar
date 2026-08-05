module IfaceExpectFailurePrivate

(* An `[@@expect_failure]` block that mentions no name of the interface must
   leave the to-do list alone: [f] and [h] are still implemented below, and the
   interface's [g] is still copied in between. *)

let f (x:int) : int = x

[@@expect_failure]
let bogus : int = "not an int"

let h (x:int) : int = g x

let _ = assert (h 1 == 2)
