module FStar.Cardinality.Cantor

(* Cantor's theorem: there is no surjection from a set to its
powerset, and therefore also no injection from the powerset to the
set. *)

open FStar.Functions

val no_surj_powerset (a : Type) (f : a -> powerset a)
  : Lemma (~(is_surj f))

val no_inj_powerset (a : Type) (f : powerset a -> a)
  : Lemma (~(is_inj f))
