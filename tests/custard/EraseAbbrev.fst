module EraseAbbrev
open FStar.All
open FStar.IO
module G = FStar.Ghost

inline_for_extraction noextract
let step_t (n:Prims.int) = x:Prims.int -> g:G.erased Prims.int -> y:Prims.int -> Tot Prims.int

let add3 : step_t 0 = fun x g y -> x + y
let add4 (n:Prims.int) : step_t n = fun x g y -> x + y + n

(* Section 18.1: the same spine, but the head is a *local variable*.  Whether
   the surplus arguments are filtered was read off the head's type as written,
   and an abbreviation stops that type short, so the erased [g] survived as a
   [()] the callee does not take and every argument after it shifted.  Reached
   through a name this was always right, [classify] having unfolded all along;
   a [fn rec] hands its own recursive call to its body as a closure, which is
   a local of exactly this shape. *)
let twice (f : step_t 0) (x:Prims.int) : Prims.int =
  f (f x (G.hide 1) 1) (G.hide 2) 2

(* The head is a local bound by a [let] rather than by a binder. *)
let via_let (f : step_t 0) (x:Prims.int) : Prims.int =
  let g = f in g x (G.hide 3) 3

let main () : ML unit =
  print_string (string_of_int (add3 3 (G.hide 7) 4));
  print_string (string_of_int (add4 1 3 (G.hide 7) 4));
  print_string (string_of_int (twice add3 5));
  print_string (string_of_int (via_let add3 5));
  print_string "\n"
