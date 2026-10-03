module TryOk
module U32 = FStar.UInt32
open FStar.All

exception Boom

(* Section 46.3.  Nothing here raises, so the answer is 7.  The krml backend
   used to translate the [try] to a bare abort, discarding the call to [safe]
   along with the handler: exit 255, and karamel reported only that the
   exception "was dropped". *)
let safe (n:U32.t) : FStar.All.ML U32.t =
  if U32.eq n 0ul then raise Boom else n

let attempt () : FStar.All.ML U32.t =
  try safe 7ul with _ -> 99ul

let main () : FStar.All.ML FStar.Int32.t =
  if U32.eq (attempt ()) 7ul then 0l else 1l
