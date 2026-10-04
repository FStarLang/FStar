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
(* Phase 2 of top-level checking with FStarC.TypeChecker.Core.

   With --ext phase2_core (the default), every term of a top-level
   declaration is elaborated by TcTerm in phase 1 and then checked by Core,
   which is the source of truth for whether it is well-typed: TcTerm's phase 2
   is not run. See doc/ref/phase2_core.md. The functions here are the common
   part of that for the declarations other than [let] (whose driver is
   [Tc.tc_sig_let]): they check a fully elaborated term (no unification
   variables) with Core, discharge Core's guard, and report Core's errors as
   TcTerm would. *)
module FStarC.TypeChecker.CoreCheck

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
module Env = FStarC.TypeChecker.Env
module Core = FStarC.TypeChecker.Core

(* Whether phase 2 of checking a declaration in [env] is done by Core: the
   extension is on, and [env] is neither phase 1 nor lax. *)
val enabled (env:Env.env) : ML bool

(* Run phase 2 of checking (part of) a declaration, [what], with Core if it is
   [enabled], and with TcTerm otherwise. In the diagnostic modes of the
   extension ("warn", "compare"), a failure of [core] is reported as a warning
   and [tcterm] is used instead. *)
val phase2 (env:Env.env) (what:string) (core:unit -> ML 'a) (tcterm:unit -> ML 'a) : ML 'a

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

(* Warn about the SMT patterns of the lemma types in [t], as TcTerm does
   when checking them in phase 2 (see [TcTerm.check_smt_pat]): Core does not
   report these. *)
val check_smt_patterns (env:Env.env) (t:term) : ML unit
