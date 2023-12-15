module FStar.Tactics.MkProjectors

open FStar.Stubs.Reflection.Types
open FStar.Tactics.Effect

(* To be called by projection generation. *)

[@@plugin]
val mk_one_projector (unf:list string) (np:nat) (i:nat) : Tac unit

[@@plugin]
val mk_projs (is_class:bool) (tyname:string) : Tac (list sigelt)
