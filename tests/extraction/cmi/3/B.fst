module B
open A

(* A *type* computed by the looping function. Extraction normalizes types with
   delta, so this is what used to diverge. *)
let t (sq: squash False) : Type0 = absurd ()

let f (sq: squash False) (x: t sq) : nat = 0

(* The same thing with the real FStar.Pervasives.false_elim, which is in this
   exact situation since FStar.Pervasives.fsti gained an inline_for_extraction
   definition. *)
let t' (sq: squash False) : Type0 = false_elim ()

let f' (sq: squash False) (x: t' sq) : nat = 1
