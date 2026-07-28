module FStar.Reflection.TermEq.Simple

(* This is just a wrapper over FStar.Reflection.TermEq.

For clients who just want to use term_eq, and not term_eq_dec, this
interface brings in less dependencies.

Returning just a boolean and providing the SMTPat lemma makes it a bit
more convenient to use: one can write `if term_eq (foo _) _` for an
effectful foo without running into a variable escaping its scope. *)

open FStar.Stubs.Reflection.Types
open FStar.Reflection.TermSpec

(* A conservative version: works on all terms, returns `true` if they
are guaranteed to have the same denotation. *)
[@@plugin]
val term_eq (t1 t2 : term) : bool

val term_eq_ok (t1 t2 : term)
  : Lemma (requires term_eq t1 t2)
          (ensures denote_term t1 == denote_term t2)
          [SMTPat (term_eq t1 t2)]

(* Idem for universes *)
[@@plugin]
val univ_eq (u1 u2 : universe) : bool

val univ_eq_ok (u1 u2 : universe)
  : Lemma (requires univ_eq u1 u2)
          (ensures u1 == u2)
          [SMTPat (univ_eq u1 u2)]
