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

module FStarC.Tactics.V1.Basic

(* This module implements the primitives in
 * ulib/FStarC.Tactics.Builtins. It would be named
 * the same, but there needs to be a thin adapter
 * layer since the tac monad representation differs
 * between compiler and userspace (and a few other
 * annoyances too). *)

open FStarC
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.Reflection.V1.Data
open FStarC.Tactics.Types
open FStarC.Tactics.Monad

module Range  = FStarC.Range
module Z      = FStarC.BigInt

(* Internal utilities *)
val goal_typedness_deps : goal -> list ctx_uvar

(* Helper *)
val focus                  : tac 'a -> tac 'a

(* Metaprogramming primitives (not all of them).
 * Documented in `ulib/FStarC.Tactics.Builtins.fst` *)

val top_env                : unit -> tac env
val fresh                  : unit -> tac Z.t
val refine_intro           : unit -> tac unit
val tc                     : env -> term -> tac typ
val tcc                    : env -> term -> tac comp
val unshelve               : term -> tac unit
val unquote                : typ -> term -> tac term
val norm                   : list NormSteps.norm_step -> tac unit
val norm_term_env          : env -> list NormSteps.norm_step -> term -> tac term
val norm_binder_type       : list NormSteps.norm_step -> binder -> tac unit
val intro                  : unit -> tac binder
val intro_rec              : unit -> tac (binder & binder)
val rename_to              : binder -> string -> tac binder
val revert                 : unit -> tac unit
val binder_retype          : binder -> tac unit
val clear_top              : unit -> tac unit
val clear                  : binder -> tac unit
val rewrite                : binder -> tac unit
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
val t_destruct             : term -> tac (list (fv & Z.t))
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
val inspect                : term -> tac term_view
val pack                   : term_view -> tac term
val pack_curried           : term_view -> tac term
val join                   : unit -> tac unit
val lget                   : typ -> string -> tac term
val lset                   : typ -> string -> term -> tac unit
val curms                  : unit -> tac Z.t
val set_urgency            : Z.t -> tac unit
val t_commute_applied_match : unit -> tac unit
val goal_with_type : goal -> typ -> goal
val mark_goal_implicit_already_checked : goal -> unit
val string_to_term         : env -> string -> tac term
val push_bv_dsenv          : env -> string -> tac (env & bv)
val term_to_string         : term -> tac string
val comp_to_string         : comp -> tac string
val range_to_string        : Range.range -> tac string

val term_eq_old            : term -> term -> tac bool
val with_compat_pre_core   : Z.t -> tac 'a -> tac 'a

val get_vconfig            : unit -> tac FStarC.VConfig.vconfig
val set_vconfig            : FStarC.VConfig.vconfig -> tac unit
val t_smt_sync             : FStarC.VConfig.vconfig -> tac unit
val free_uvars             : term -> tac (list Z.t)
