module DebugUnreachable

(* Code F* would have proved unreachable, reached.  It is a whole definition:
   an unreachable branch of a match or a conditional is removed before C is
   printed. *)
open FStar.All

let impossible (x:int) : int = false_elim ()

let pos (x:int) : int = if x > 0 then x else impossible x

let main () : ML FStar.UInt32.t =
  let r = alloc 0 in
  if pos !r = 0 then 0ul else 1ul
