module CoerceAdmit

(* silly test, but at some point I broke
coercions whenever admit was on, and that was
not caught by anything in tests/. *)

#push-options "--admit_smt_queries true"
let test1 (x : option int) =
  None? x /\ Some? x
#pop-options
