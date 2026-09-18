module KeyNames
open FStar.All
open FStar.IO

(* Section 12.3: a specialization key must be injective on names.  Both
   arguments below print as "tweak" under the pretty-printer, which prints an
   [fv] by its last identifier alone, and neither unfolds -- so with [show] as
   the key printer the two calls shared one specialization and this program
   printed "abab". *)

let apply ([@@@monomorphize] f : string -> string) (s:string) : string = f s

let main () : ML unit =
  print_string (apply KeyNamesA.tweak "Ab");
  print_string (apply KeyNamesB.tweak "Ab");
  print_string "\n"
