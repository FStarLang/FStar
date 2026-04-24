module FStar.Stubs.Tactics.Types.Reflection

open FStar.Stubs.Reflection.Types
include FStar.Stubs.TypeChecker.Core

(* Typing reflection *)
val non_informative_token (g:env) (t:typ) : prop
val subtyping_token (g:env) (t0 t1:typ) : prop
val equiv_token (g:env) (t0 t1:typ) : prop
val typing_token (g:env) (e:term) (c:tot_or_ghost & typ) : prop
