module Refs
open FStar.All
open FStar.IO

(* Section 8.4: [FStar.All]'s references are garbage collected, so they have
   no [free] and the OCaml backend gives them [t ref] rather than a
   one-element array. *)

let bump (r : ref int) : ML unit = r := !r + 1

(* Section 102.2.1.  A [ref] reached through a pattern binder.  [let (_, r) = p]
   elaborates to [let _letpattern = p in match _letpattern with ...], and
   propagating that copy substitutes into the match -- which renames the
   branch's binders.  A pattern carries no type, so the rename carries none
   either, and taking it whole would leave [r] with no recorded type.  The
   recorded type is what says [ref] rather than array, so [bump2] is the pin:
   it must assign with [:=], not index a one-element array. *)
let bump2 (p : (int & ref int)) : ML unit =
  let (n, r) = p in
  r := !r + n

let main () : ML unit =
  let r = alloc 0 in
  bump r; bump r; bump r;
  bump2 (4, r);
  print_string (string_of_int !r);
  print_string "\n"
