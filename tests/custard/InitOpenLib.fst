module InitOpenLib

let x = 1

(* Nothing refers to this module except through an [open], as
   [FStarC.Hooks] is opened by the compiler's drivers; its initializer
   still has to run. *)
let _ = FStar.IO.print_string "initializer\n"
