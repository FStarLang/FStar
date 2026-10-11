module UseTac

open FStar.Tactics.V2

(* Tac.prove_it has no common implementation, so this only works when the
   plugin extracted from Tac-ocaml.fst is loaded. *)
let _ = assert (1 + 1 == 2) by (Tac.prove_it ())
