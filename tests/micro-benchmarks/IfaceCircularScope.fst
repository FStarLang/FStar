module IfaceCircularScope

(* Issue #4390, benign variant: defining [one] in terms of [two] would be
   circular, since the interface derives [two] from [one]. *)
[@@expect_failure [133]]
let one : int = two - 1

let one : int = 0

(* Now that [one] is implemented, the interface's [two] is revealed. *)
let three : int = two

let _ = assert (three == 1)
