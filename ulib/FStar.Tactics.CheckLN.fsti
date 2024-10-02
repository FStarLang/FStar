module FStar.Tactics.CheckLN

open FStar.Tactics.V2

(* Checks if a term is locally nameless. *)
[@@plugin]
val check_ln (t:term) : Tac bool
