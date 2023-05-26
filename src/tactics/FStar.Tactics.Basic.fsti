(*
   Copyright 2008-2016 Microsoft Research

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

module FStar.Tactics.Basic

(* This module implements the primitives in
 * ulib/FStar.Tactics.Builtins. It would be named
 * the same, but there needs to be a thin adapter
 * layer since the tac monad representation differs
 * between compiler and userspace (and a few other
 * annoyances too). *)

open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.Reflection.Data
open FStar.Tactics.Types
open FStar.Tactics.Monad

module BU     = FStar.Compiler.Util
module EMB    = FStar.Syntax.Embeddings
module O      = FStar.Options
module Range  = FStar.Compiler.Range
module Z      = FStar.BigInt
module TcComm = FStar.TypeChecker.Common
module Core   = FStar.TypeChecker.Core
module RD     = FStar.Reflection.Data

(* Internal utilities *)
val goal_typedness_deps : goal -> list ctx_uvar

val proofstate_of_goals : Range.range -> env -> list goal -> list implicit -> proofstate
(* Returns proofstate and uvar for main witness *)
val proofstate_of_goal_ty : Range.range -> env -> typ -> proofstate * term

val proofstate_of_all_implicits: Range.range -> env -> implicits -> proofstate * term

(* Helper *)
val focus                  : tac 'a -> tac 'a

(* Metaprogramming primitives (not all of them).
 * Documented in `ulib/FStar.Tactics.Builtins.fst` *)

val top_env                : unit -> tac env
val fresh                  : unit -> tac Z.t
val refine_intro           : unit -> tac unit
val tc                     : env -> term -> tac typ
val tcc                    : env -> term -> tac comp
val unshelve               : term -> tac unit
val unquote                : typ -> term -> tac term
val norm                   : list EMB.norm_step -> tac unit
val norm_term_env          : env -> list EMB.norm_step -> term -> tac term
val norm_binder_type       : list EMB.norm_step -> binder -> tac unit
val intro                  : unit -> tac RD.binding
val intro_rec              : unit -> tac (RD.binding * RD.binding)
val rename_to              : RD.binding -> string -> tac RD.binding
val revert                 : unit -> tac unit
val var_retype             : RD.binding -> tac unit
val clear_top              : unit -> tac unit
val clear                  : RD.binding -> tac unit
val rewrite                : RD.binding -> tac unit
val t_exact                : bool -> bool -> term -> tac unit
val t_apply                : bool -> bool -> bool -> term -> tac unit
val t_apply_lemma          : bool -> bool -> term -> tac unit
val print                  : string -> tac unit
val debugging              : unit -> tac bool
val dump                   : string -> tac unit
val dump_all               : bool -> string -> tac unit
val dump_uvars_of          : goal -> string -> tac unit
val t_trefl                : (*allow_guards:*)bool -> tac unit
val dup                    : unit -> tac unit
val prune                  : string -> tac unit
val addns                  : string -> tac unit
val t_destruct             : term -> tac (list (fv * Z.t))
val gather_explicit_guards_for_resolved_goals : unit -> tac unit
val set_options            : string -> tac unit
val uvar_env               : env -> option typ -> tac term
val ghost_uvar_env         : env -> typ -> tac term
val fresh_universe_uvar    : unit -> tac term
val unify_env              : env -> term -> term -> tac bool
val unify_guard_env        : env -> term -> term -> tac bool
val match_env              : env -> term -> term -> tac bool
val launch_process         : string -> list string -> string -> tac string
val fresh_bv_named         : string -> tac bv
val change                 : typ -> tac unit
val get_guard_policy       : unit -> tac guard_policy
val set_guard_policy       : guard_policy -> tac unit
val lax_on                 : unit -> tac bool
val tadmit_t               : term -> tac unit
val binder_bv              : binder -> tac bv
val join                   : unit -> tac unit
val lget                   : typ -> string -> tac term
val lset                   : typ -> string -> term -> tac unit
val curms                  : unit -> tac Z.t
val set_urgency            : Z.t -> tac unit
val t_commute_applied_match : unit -> tac unit
val goal_with_type : goal -> typ -> goal
val mark_goal_implicit_already_checked : goal -> unit
val string_to_term         : env -> string -> tac term
val push_bv_dsenv          : env -> string -> tac (env * RD.binding)
val term_to_string         : term -> tac string
val comp_to_string         : comp -> tac string
val range_to_string        : Range.range -> tac string

val term_eq_old            : term -> term -> tac bool
val with_compat_pre_core   : Z.t -> tac 'a -> tac 'a

val get_vconfig            : unit -> tac VConfig.vconfig
val set_vconfig            : VConfig.vconfig -> tac unit
val t_smt_sync             : VConfig.vconfig -> tac unit
val free_uvars             : term -> tac (list Z.t)


(***** Callbacks for the meta DSL framework *****)
let issues = list FStar.Errors.issue
val refl_check_subtyping              : env -> typ -> typ -> tac (option unit & issues)
val refl_check_equiv                  : env -> typ -> typ -> tac (option unit & issues)
val refl_core_compute_term_type       : env -> term -> tot_or_ghost -> tac (option typ & issues)
val refl_core_check_term              : env -> term -> typ -> tot_or_ghost -> tac (option unit & issues)
val refl_tc_term                      : env -> term -> tot_or_ghost -> tac (option (term & typ) & issues)
val refl_universe_of                  : env -> term -> tac (option universe & issues)
val refl_check_prop_validity          : env -> term -> tac (option unit & issues)
val refl_instantiate_implicits        : env -> term -> tac (option (term & typ) & issues)
val refl_maybe_relate_after_unfolding : env -> term -> term -> tac (option Core.side & issues)
val refl_maybe_unfold_head            : env -> term -> tac (option term & issues)

val push_open_namespace               : env -> list string -> tac env
val push_module_abbrev                : env -> string -> list string -> tac env
val resolve_name                      : env -> list string -> tac (option (either bv fv))
