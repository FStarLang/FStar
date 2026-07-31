module IfaceNoOpenLeak

(* The [open FStar.List.Tot] of the interface does not scope over the
   implementation, so [length] is not in scope here. *)
let f (l : list int) : nat = length l
