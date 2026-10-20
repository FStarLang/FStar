module DebugUnreachable

(* Code F* would have proved unreachable, reached. *)
open FStar.All

let pos (x:int) : int = if x > 0 then x else false_elim ()

let main () : ML FStar.UInt32.t =
  let r = alloc 0 in
  if pos !r = 0 then 0ul else 1ul
