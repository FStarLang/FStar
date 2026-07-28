module FStar.Stubs.Tactics.Types.Reflection

open FStar.Stubs.Reflection.Types
include FStar.Stubs.TypeChecker.Core
open FStar.Reflection.TermSpec

(* The compiler typing/subtyping/equivalence judgment tokens are indexed
   over the erasable model type [term_spec], so that the DSL typing
   judgment ([FStar.Reflection.Typing]) can bridge to them without any
   [denote_term] coercion at the token boundary. Their runtime
   representation on the compiler side is [unit], and [term_spec] is
   erasable, so this indexing is extraction-safe. *)
let comp_spec_typ = tot_or_ghost & term_spec

(* Typing reflection *)
val non_informative_token (g:env) (t:term_spec) : prop
val subtyping_token (g:env) (t0 t1:term_spec) : prop
val equiv_token (g:env) (t0 t1:term_spec) : prop
val typing_token (g:env) (e:term_spec) (c:comp_spec_typ) : prop
