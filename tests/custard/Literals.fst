module Literals

open FStar.All

(* Section 5.1: reducing a closed arithmetic expression leaves an *embedded*
   integer rather than a constant, so a negative literal reaches the extractor
   as a lazy term.  Unfolding it is what keeps these from being mistaken for
   erased subterms and replaced by [()]. *)

let a : int = 3
let b : int = -1
let c : int = 0 - 1
let d : int = op_Tilde_Minus 1
let e (n:int) : int = 0 - n

let main () : ML unit =
  FStar.IO.print_string (string_of_int (a + b + c + d + e 5));
  FStar.IO.print_string "\n"
