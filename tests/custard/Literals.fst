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

(* Section 5.1: [Prims.int] is [Z.t], so a literal is a call.  [Prims.parse_int]
   is [Z.of_string], which re-parses the string every time the expression is
   evaluated -- once per iteration for a literal inside a loop.  Only a value
   too wide for OCaml's [int] needs it. *)
let z : int = 0
let o : int = 1
let big : int = 4611686018427387904

let main () : ML unit =
  FStar.IO.print_string (string_of_int (a + b + c + d + e 5));
  FStar.IO.print_string "\n";
  FStar.IO.print_string (string_of_int (z + o + big));
  FStar.IO.print_string "\n"
