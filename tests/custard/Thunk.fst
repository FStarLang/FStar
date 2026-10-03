module Thunk
open FStar.All
open FStar.IO

(* Section 3.2c: [counter] is a *value* whose evaluation allocates a
   reference and then returns a function.  Specialization applies a
   definition to a spine and re-abstracts, which is eta-expansion, and
   eta-expanding this one re-allocates the reference on every call: the
   counter would restart from zero each time and the output would be "111"
   rather than "123".  This is what made the extracted compiler drop every
   primitive step -- FStarC.TypeChecker.Cfg.cached_steps memoizes exactly
   like this. *)

let counter : unit -> ML int =
  let n = alloc 0 in
  fun () -> n := !n + 1; !n

let main () : ML unit =
  print_string (string_of_int (counter ()));
  print_string (string_of_int (counter ()));
  print_string (string_of_int (counter ()));
  print_string "\n"
