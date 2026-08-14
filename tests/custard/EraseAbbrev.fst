module EraseAbbrev
open FStar.All
open FStar.IO
module G = FStar.Ghost

inline_for_extraction noextract
let step_t (n:Prims.int) = x:Prims.int -> g:G.erased Prims.int -> y:Prims.int -> Tot Prims.int

let add3 : step_t 0 = fun x g y -> x + y
let add4 (n:Prims.int) : step_t n = fun x g y -> x + y + n

let main () : ML unit =
  print_string (string_of_int (add3 3 (G.hide 7) 4));
  print_string (string_of_int (add4 1 3 (G.hide 7) 4));
  print_string "\n"
