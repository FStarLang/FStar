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
module FStarC.TypeChecker.Core.Base

(* The vocabulary of the core typechecker (see FStarC.TypeChecker.Core):
   its debug toggles, the effects it tracks, its typing environment, the
   facts and relations it computes, and the contexts and errors with which
   it reports failures. *)

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Class.Show
module Env = FStarC.TypeChecker.Env
module I = FStarC.Ident
module R = FStarC.Range

(*** Debug toggles *)

(* --debug Core: trace every check and every cache operation. *)
val dbg : ref bool

(* --debug CoreFacts: trace the facts assumed about witnesses of
   subtyping (see [Core.Guard.witness_guard]). *)
val dbg_facts : ref bool

(* --debug CoreEq: trace entry into the checker and report cache
   statistics. *)
val dbg_Eq : ref bool

(* --debug CoreTop: trace the calls into the public API. *)
val dbg_Top : ref bool

(* --debug CoreExit: show the guard each call into the public API returns,
   before and after simplification. *)
val dbg_Exit : ref bool

(* --debug DisableCoreCache: never reuse the cached typing of a term. *)
val dbg_DisableCoreCache : ref bool

(*** Effects *)

(* The effect of a computation, as tracked internally. [Tot] and [GTot] are
   distinguished because the checker's rules for them (promotion of a ghost
   computation with a non-informative type, erasure) are special; every other
   effect is a *root* effect name (see doc/ref/simplified_effect_system.md),
   ordered by the effect lattice. *)
type eff =
  | ETot
  | EGhost
  | EEff of I.lident

(* The effect name of an [eff]: [Tot] and [GTot] are [PURE] and [GHOST]. *)
val eff_to_lid (e:eff) : I.lident

instance val showable_eff : showable eff

val eff_eq (e0 e1:eff) : ML bool

(*** Environments *)

(* The environment of the checker: TcTerm's [Env.env], extended with
   - [allow_universe_instantiation]: whether a universe-polymorphic name
     may be related to an instance of itself (only at the top level);
   - [should_read_cache]: whether the typing of a term may be read from the
     cache rather than recomputed;
   - [max_binder_index]: the largest index of a variable in scope, above
     which fresh binders are numbered (see [Core.Binders.push_binder]);
   - [at_top]: whether a top-level function is being checked and no binder
     has been pushed yet (see the field). *)
type env = {
   tcenv : Env.env;
   allow_universe_instantiation : bool;
   should_read_cache: bool;
   max_binder_index: int;
   (* Checking a top-level function, and no binder has been pushed yet: the
      binders closed over here are those of the definition, which TcTerm has
      in its environment when it discharges its guard. *)
   at_top: bool
}

(* Run [f] if [--debug Core] is on. *)
val debug (g:env) (f: unit -> ML unit) : ML unit

(*** Facts and relations *)

(* What the typing of a term [e] says about [e] and its subterms, beyond
   [e]'s type: propositions assumed in the VCs that [e] is the witness of
   (see [witness_guard]), or that are in the scope of a [let] binding [e]
   (see [close_let_guard]). They are computed by [do_check] in the same pass
   as [e]'s type, from those of [e]'s subterms, and cached with it; lazily,
   since most are never needed. Only a pure [e] has any.
   * [f_sub]: about the subterms of [e]: the arguments of an application,
     the definitions of its [let]s, the branches of a [match] (under the
     condition that each is taken), ...
   * [f_term]: about [e] itself (what its type says about it, see
     [term_facts]), and [f_sub]; and [f_tail] if [e] was checked against an
     expected type pushed into it, whose type was then not synthesized
     (see [check_against_typ_synth]).
   * [f_tail]: [f_term] of the expression that the [let]s of [e] end with,
     under those [let]s, e.g. [p] for [let x = e1 in lemma x], where
     [lemma x : squash p]. *)
type facts = {
  f_sub : Thunk.t (list term);
  f_term: Thunk.t (list term);
  f_tail: Thunk.t (list term);
}

(* The witness of a subtyping, with the facts about its subterms. *)
type witness = term & Thunk.t (list term)

(* The relations between types that the checker decides, the second being
   that of a witness (if any) to the subtyping, whose type is then related
   to an expected one: the facts about its subterms may be assumed in the
   guard (see [Core.Guard.witness_guard]). *)
type relation =
  | EQUALITY
  | SUBTYPING : option witness -> relation

instance val showable_rel : showable relation

(*** Contexts and errors *)

(* What an error is about: a term being checked, or a relation being
   decided. *)
type context_term =
  | CtxTerm : term -> context_term
  | CtxRel : term -> relation -> term -> context_term

(* The context of a computation in the [Core.Monad.result] monad:
   - [no_guard]: whether it must succeed without a guard;
   - [unfolding_ok]: whether it may unfold definitions;
   - [error_context]: what is being checked, innermost first, for error
     messages (see [Core.Monad.with_context]). *)
type context = {
  no_guard : bool;
  unfolding_ok : bool;
  error_context: list (string & option context_term)
}

(* A brief summary of a context; see [print_error] for the full one. *)
instance val showable_context : showable context

(* An error may carry the code with which TcTerm reports the same failure;
   it is then reported as TcTerm does (see [error_code]). *)
let error = context & Errors.error_message (* = list doc *) & option Errors.error_code

(* The full context of the error, then its message. *)
val print_error (err:error) : ML string

instance val showable_error : showable error

(* The message of the error, without its context. *)
val print_error_short (err:error) : ML string

(* The code with which TcTerm reports the same failure, if any. *)
val error_code (err:error) : ML (option Errors.error_code)

val error_message (err:error) : ML Errors.error_message

(* The position of the innermost term of the error's context that has
   one. *)
val error_range (err:error) : ML (option R.t)

(*** Guards *)

(* The guard of a computation, if any: a proposition that must be proven
   for the computation's result to be valid. *)
let precondition = option typ

(* A result and its guard. *)
let success a = a & precondition
