module IfaceLetInterleaved

let f (x:int) : int = x

(* [g] is copied over from the interface just before this declaration, so both
   its name and its definition are available here. *)
let h (x:int) : int = g x

let _ = assert (h 1 == 2)
