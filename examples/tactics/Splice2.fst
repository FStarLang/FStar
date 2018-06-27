module Splice2

open Splice

(* Checking that the spliced definitions are properly exported,
 * were they name-annotated or not. *)

let _ = assert (x == 42)
let _ = assert (y == 42)
