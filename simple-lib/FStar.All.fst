(*
   A minimal FStar.All for the simplified effect system: the [ALL] effect,
   which may diverge, raise exceptions and perform state.  It is the effect
   the F* compiler's own source code is written in.
*)
module FStar.All

open FStar.Pervasives

assume effect ALL

assume sub_effect PURE  ~> ALL
assume sub_effect GHOST ~> ALL
assume sub_effect DIV   ~> ALL

effect ML (a: Type) = ALL a

assume val failwith : string -> ML 'a
assume val raise : exn -> ML 'a
assume val try_with : (unit -> ML 'a) -> (exn -> ML 'a) -> ML 'a
