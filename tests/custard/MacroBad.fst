module MacroBad

open FStar.Attributes

(* Section 68.  A [#define] is substituted before the program runs, so its
   body has to be something the C compiler can evaluate at translation time.
   A value that only exists at run time is not that, and saying so at the
   attribute is better than emitting a [#define] whose expansion happens to
   be a variable. *)

assume val handle : UInt32.t

[@@ CMacro ]
let g : UInt32.t = handle

let main () : FStar.All.ML Int32.t = let _ = g in 0l
