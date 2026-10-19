(*
   Copyright Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
(* Checking top-level declarations with FStarC.TypeChecker.Core.

   Every term of a top-level declaration is first elaborated by TcTerm, in an
   environment with [admit] set: TcTerm infers implicits, inserts coercions,
   runs tactics, etc., but proves nothing. Core then checks the elaborated
   term and computes its verification condition: Core is the only source of
   verification conditions, and TcTerm is run once. See
   doc/ref/phase2_core.md. The functions here are the common part of that for
   the declarations other than [let] (whose driver is [Tc.tc_sig_let]): they
   check a fully elaborated term (no unification variables) with Core,
   discharge Core's guard, and report Core's errors. *)
module FStarC.TypeChecker.CoreCheck

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
module Env = FStarC.TypeChecker.Env
module Core = FStarC.TypeChecker.Core

(* Whether terms checked in [env] are checked by Core: [env] does not admit
   its verification conditions (as it does in a lax module, or while
   elaborating). *)
val enabled (env:Env.env) : ML bool

(* [core ()] if Core is [enabled] in [env]; otherwise [elab ()], which only
   elaborates, as there is nothing to prove. *)
val check_or_elaborate (env:Env.env) (core:unit -> ML 'a) (elab:unit -> ML 'a) : ML 'a

(* Elaborate [e] with [tc] (in [env] with [admit] set), solving its
   implicits, and return the elaborated term, without unification variables,
   ready to be checked by Core, along with what else [tc] returned. Core's
   memo table is cleared before and after, since the guards of the
   elaboration are not proven. *)
val elaborate (env:Env.env) (tc:Env.env -> term -> ML (term & 'a & FStarC.TypeChecker.Common.guard_t)) (e:term)
  : ML (term & 'a)

(* Report a structural failure of Core, with the error code TcTerm reports
   it with, if any. *)
val raise_core_error (env:Env.env) (what:string) (err:Core.error) : ML 'a

(* Discharge a guard computed by Core in [env], and commit it. *)
val discharge (env:Env.env) (g:option Core.guard_and_tok_t) : ML unit

(* [check_term env e t must_tot]: [e] has type [t] (Tot, if [must_tot]). *)
val check_term (env:Env.env) (what:string) (e:term) (t:typ) (must_tot:bool) : ML unit

(* The effect and type of [e]. *)
val compute_term_type (env:Env.env) (what:string) (e:term) : ML (Core.tot_or_ghost & typ)

(* The universe of the type [t]: [t] must be a type. *)
val universe_of (env:Env.env) (what:string) (t:typ) : ML universe

(* Whether [t0] is a subtype of [t1]; the guard, if any, is discharged. *)
val check_subtyping (env:Env.env) (t0 t1:typ) : ML bool

(* Check that the sort of each binder is a type, in the environment extended
   with the binders before it; return that environment extended with all of
   them, and the universes of their sorts. The binders must be opened. *)
val check_binders (env:Env.env) (what:string) (bs:binders) : ML (Env.env & universes)

(* Warn about the SMT patterns of the lemma types in [t] (see
   [TcTerm.check_smt_pat]): Core does not report these. *)
val check_smt_patterns (env:Env.env) (t:term) : ML unit
