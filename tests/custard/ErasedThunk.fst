module ErasedThunk
open FStar.All
open FStar.IO

(* Section 116.  The callback's erased binder is the last one, so [keep_thunk]
   kept it as a [unit] parameter when the *type* was translated; the call
   spine has to delete the same binders the type kept. *)
let invoke (f:FStar.Ghost.erased bool -> ML int) : ML int =
  f (FStar.Ghost.hide true)

let main () : ML unit =
  print_string (string_of_int (invoke (fun _ -> 7)));
  print_string "\n"
