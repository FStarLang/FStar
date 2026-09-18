module SuffixCollision
open FStar.All
open FStar.IO

(* Section 115.  A specialization's name suffix is derived from its arguments
   when that spelling is free, and from a counter when it is not.  Only the
   first of those was recorded as taken, so a later request whose *preferred*
   spelling happened to equal an earlier request's *fallback* got a name that
   was already in use, and the two specializations collapsed into one.

   Every suffix handed out is now claimed, whichever branch produced it.  The
   three calls below are three different specializations and have to print
   three different lines. *)
let combine ([@@@monomorphize] a:string) ([@@@monomorphize] b:string)
            (suffix:string) : string =
  a ^ "|" ^ b ^ suffix

let main () : ML unit =
  print_string (combine "x" "y" "\n");
  print_string (combine "x_y" "x_y" "\n");
  print_string (combine "x_y_1" "x_y_1" "\n")
