module SpecBinderErasure

(* Only the implicit binder that a [requires] clause desugars into is dropped
   by extraction (it is tagged with [Prims.spec_binder]).  A user-written
   implicit binder of type [squash p] is an ordinary argument and must survive,
   consistently in the binder, in the argument and in the function's type.

   Dropping it too used to erase effectful calls altogether: [tick] below has
   no other binder, so the abstraction disappeared and the module extracted to

       let run (uu___ : unit) : unit = ()

   (issue #4650).  And since the test was the *syntax* of the binder's type,
   writing [squash True] through an abbreviation ([proof] below) gave the two
   sides different answers, so [f]'s application lost an argument its
   definition still expected. *)

open FStar.All

let tick (#p : squash True) : ML unit =
  FStar.IO.print_string "tick\n"

type proof = squash True

let a (#p:proof) (x:int) : int = x
let f : (#p:squash True -> int -> int) = a

(* A real [requires], on the other hand, is dropped: [g] and [h] both extract
   to a one-argument function, exactly as they did before preconditions became
   binders.  [t_abbrev] is the same arrow written as a type abbreviation, so
   [use] can only be applied to [g] if both sides agree. *)
val g : x:int -> Pure int (requires x >= 0) (ensures fun y -> y == x)
let g x = x

let h (x:int) : Pure int (requires x >= 0) (ensures fun y -> y == x) = x

type t_abbrev = x:int -> Pure int (requires x >= 0) (ensures fun _ -> True)
let use (fn:t_abbrev) : int = fn 3

let main () : ML unit =
  tick #();
  tick #();
  FStar.IO.print_string (string_of_int (f #() 7));
  FStar.IO.print_string (string_of_int (g 1));
  FStar.IO.print_string (string_of_int (h 2));
  FStar.IO.print_string (string_of_int (use g));
  FStar.IO.print_string (string_of_int (use h));
  FStar.IO.print_newline ()

let _ : unit = main ()
