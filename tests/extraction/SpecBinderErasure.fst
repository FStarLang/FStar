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

(* Dropping the binder must not leave the definition with no binder at all.
   Generalization erases [#a] into a type parameter, so [tock]'s only
   remaining binder is the one [requires q] desugars into, and deleting that
   one too turned [tock] into a value whose effect ran once, at module
   initialization, instead of at each call -- the other half of issue #4650.
   It is kept a function by thunking it, and the thunk's arrow has to stay
   *impure*, or the calls below are dead pure code and are dropped again. *)
assume val q : prop
assume val pf : squash q
let tock (#a:Type) : ML unit (requires q) = FStar.IO.print_string "tock\n"

(* The same shape with a pure, total body needs no thunk: [three] is a value
   either way, so it stays one and its uses pass no argument. *)
let three (#a:Type) : Pure int (requires q) (ensures fun _ -> True) = 3

let main () : ML unit =
  tick #();
  tick #();
  tock #int;
  tock #bool;
  FStar.IO.print_string (string_of_int (three #int));
  FStar.IO.print_string (string_of_int (f #() 7));
  FStar.IO.print_string (string_of_int (g 1));
  FStar.IO.print_string (string_of_int (h 2));
  FStar.IO.print_string (string_of_int (use g));
  FStar.IO.print_string (string_of_int (use h));
  FStar.IO.print_newline ()

let _ : unit = main ()
