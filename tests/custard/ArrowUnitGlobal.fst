module ArrowUnitGlobal
module I32 = FStar.Int32
open FStar.All

(* Section 115.  A parameterless definition of arrow type is lowered to a
   variable of function-pointer type, and the pointer -- like every other
   arrow in the C backend -- drops its [unit] parameters.  Its recorded
   *arity* did not: it was taken from the arrow unfiltered, so a call that
   supplies every argument the source has looked like a partial application
   and was refused with error 368.  Extraction succeeding is half the
   assertion; the other half is that the call goes through. *)
assume val flag : bool

let keep (a:bool) (_:unit) : bool = a
let flip (a:bool) (_:unit) : bool = not a

(* The conditional is what keeps this a pointer rather than a definition that
   would be eta-expanded to full arity. *)
let selected : bool -> unit -> bool = if flag then keep else flip

let call_selected (a:bool) : bool = selected a ()

let main () : ML I32.t =
  if call_selected true && not (call_selected false) then 0l else 1l
