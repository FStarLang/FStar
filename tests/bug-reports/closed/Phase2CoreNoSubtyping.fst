module Phase2CoreNoSubtyping

(* A [no_subtyping] lemma's type is checked with Core, with every subtyping
   check turned into an equality check (see doc/ref/phase2_core.md). TcTerm's
   [use_eq_strict] rejected even these, e.g. because [int : eqtype] where
   [Type] is expected. *)
[@@ FStar.Attributes.no_subtyping]
let lem (x:int) : Lemma (x + 1 > x) = ()

[@@ FStar.Attributes.no_subtyping]
let lem_pre (x:int) (y:int) : Lemma (requires x > 0) (ensures x + y > y) = ()
