module NoPrefApp
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

(* The consumer of {!NoPrefLib}, which passes no naming option of its own. *)
let main () : ML I32.t =
  if U32.eq (NoPrefLib.add1 41ul) 42ul then 0l else 1l
