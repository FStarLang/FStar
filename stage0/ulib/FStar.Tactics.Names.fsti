module FStar.Tactics.Names

open FStar.Stubs.Reflection.Types
open FStar.Tactics.Effect

(** Decides whether a top-level name [nm] syntactically
appears in the term [t]. *)
[@@plugin]
val name_appears_in (nm:name) (t:term) : Tac bool
