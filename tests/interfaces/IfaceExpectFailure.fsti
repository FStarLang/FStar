module IfaceExpectFailure

(* An `[@@expect_failure]` block defines nothing: its declarations are checked
   with errors trapped and then discarded. So it must not tick `one` off the
   interface's to-do list --- otherwise `one` would be silently admitted, never
   checked, never reported as unimplemented, and exported as an axiom in
   IfaceExpectFailure.fst.checked. *)

val one : False
