module InitOrder

open FStar.All

(* Section 4.4.  Computed at start-up, after InitOrderLib is initialized, as
   in OCaml: InitOrderLib's initializer has to come first although nothing
   refers to it. *)
let v : int = !InitOrderLib.r

let main () : ML unit =
  FStar.IO.print_string (string_of_int v ^ "\n")
