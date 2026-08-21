(* A type as an entry point (section 8.2).

   Custard unfolds type abbreviations rather than emitting them: a
   monomorphized abbreviation has no generic form left to emit, and the
   backends need to see the representation behind the name.  So an
   abbreviation that only a hand-written realization mentions is reached by
   nothing and would be dropped as dead.

   '--custard_entry' names it, exactly as it names a realization's callees,
   and a root is a root whichever kind of declaration it is. *)
module TypeEntry

type pair = int & int

(* Reached by nothing below; emitted because it is a root. *)
type t = pair

let mk (x:int) : t = (x, x)

let main () : FStar.All.ML unit =
  let (a, b) = mk 3 in
  FStar.IO.print_string (string_of_int (a + b));
  FStar.IO.print_string "\n"
