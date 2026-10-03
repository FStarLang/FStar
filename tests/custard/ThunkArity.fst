module ThunkArity
open FStar.All
module G = FStar.Ghost

(* Section 127.  [ext] takes a thunk -- [fork_core] in miniature -- and runs
   it after announcing that it is about to.  [spawn] hands it a *partial*
   application: [f1] has two binders and the call supplies one.  Erasing the
   second, which carries nothing, must not make that call saturated, or the
   thunk is run where it is built and "work" is printed first. *)

let ext (f : G.erased int -> ML unit) : ML unit =
  FStar.IO.print_string "before\n";
  f (G.hide 0)

let work (p:int) : ML unit =
  FStar.IO.print_string "work\n"

let spawn (p:int) : ML unit =
  let f1 (u:unit) (e:G.erased int) : ML unit = work p in
  ext (f1 ())

let main () : ML unit = spawn 1
