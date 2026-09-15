module Bug2001

(* A universe application on an effect, as in [Tot u#_ unit], says nothing: a
   computation is an effect name applied to its result type, so its universe is
   that of the result type.  It used to be accepted and silently discarded --
   and before that, in the report this test is named for, it made the compiler
   blow up -- so keep it pinned that it is now rejected outright. *)

let x = ()

let blowup (x : int) : Tot u#_ unit = ()
