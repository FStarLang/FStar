module FStar.Cardinality.Universes

open FStar.Functions
open FStar.Cardinality.Cantor

(* Prove that there can be no injection from a universe into a strictly smaller
universe. We use `max (a+1) b` to represent an arbitrary universe strictly larger
than `a` as we cannot write sums of universe levels. *)
val no_inj_universes (f : Type u#(max (a+1) b) -> Type u#a)
  : Lemma (~(is_inj f))

(* A simpler version for the +1 case. *)
val no_inj_universes_suc (f : Type u#(a+1) -> Type u#a)
  : Lemma (~(is_inj f))
