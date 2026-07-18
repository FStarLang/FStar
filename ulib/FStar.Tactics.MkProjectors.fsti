module FStar.Tactics.MkProjectors

open FStar.Stubs.Reflection.Types
open FStar.Tactics.Effect

(** Opt-in to the new projector generation by a metaprogram. This also
    affects typeclass method generation. *)
val meta_projectors : unit

[@@plugin]
val mk_one_projector (unf:list string) (np:nat) (i:nat) : Tac unit

[@@plugin]
val mk_one_method (proj:string) (np:nat) : Tac unit

[@@plugin]
val mk_projs (is_class:bool) (tyname:string) : Tac (list sigelt)
