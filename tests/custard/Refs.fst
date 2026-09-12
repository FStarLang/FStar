module Refs
open FStar.All
open FStar.IO

(* Section 8.4: [FStar.All]'s references are garbage collected, so they have
   no [free] and the OCaml backend gives them [t ref] rather than a
   one-element array. *)

let bump (r : ref int) : ML unit = r := !r + 1

let main () : ML unit =
  let r = alloc 0 in
  bump r; bump r; bump r;
  print_string (string_of_int !r);
  print_string "\n"
