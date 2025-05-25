module FStar.Stubs.Tactics.Types.Reflection

open FStar.Stubs.Reflection.Types
include FStar.Stubs.TypeChecker.Core

(* Typing reflection *)
val non_informative_token (g:env) (t:typ) : Type0
val subtyping_token (g:env) (t0 t1:typ) : Type0
val equiv_token (g:env) (t0 t1:typ) : Type0
val typing_token (g:env) (e:term) (c:tot_or_ghost & typ) : Type0
