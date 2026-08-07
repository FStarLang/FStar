module IfaceCircularScope

val one : int

(* Justified by [val one] above, so it must not be in scope in the
   implementation until [one] has been implemented. *)
let two : int = one + 1

val three : int
