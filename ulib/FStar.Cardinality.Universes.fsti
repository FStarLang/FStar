module FStar.Cardinality.Universes

open FStar.Functions
open FStar.Cardinality.Cantor

(* Prove that there can be no injection from Type (u+1) into Type u *)
val no_inj_universes (f : Type u#(a+1) -> Type u#a)
  : Lemma (~(is_inj f))
