module FStar.Tactics.LaxTermEq

open FStar.Tactics.Effect

(* This module exposes a "laxer" term_eq that ignores some bits of the term
representation, such as universe levels and ascriptions, and also resolves uvars
to their solutions (if any).

This is different from FStar.Reflection.TermEq.term_eq, which is a completely
pure function and it can provide a proof of two terms being provably equal.

This version is more useful for a tactic client that just wants to compare terms
heuristically.

This version cannot be TacRO as it requires freshness, but it is essentially
read-only. *)

open FStar.Stubs.Reflection.Types

[@@plugin]
val lax_term_eq (t1 t2 : term) : Tac bool

[@@plugin]
val lax_univ_eq (t1 t2 : universe) : Tac bool
