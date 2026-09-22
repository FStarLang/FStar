module OcamlEscape
open FStar.All

(* Section 115.  Escaping an OCaml keyword by appending an underscore is only
   an escape if it lands somewhere nothing else does, and [method] and
   [method_] both came out [method_] -- so the second binder captured every
   use of the first, in OCaml that compiles without a warning.  The
   underscores are stripped before the keyword test now, which shifts the
   whole family by one and keeps it injective.

   Called with [method = true] and [method_ = false], so the answer is
   [method], which is [true]; before the fix both names read the second
   parameter and it printed [false]. *)
let select (method:bool) (method_:bool) : bool =
  if method_ then not method else method

let main () : ML unit =
  FStar.IO.print_string (if select true false then "true\n" else "false\n");
  FStar.IO.print_string (if select true true then "true\n" else "false\n")
