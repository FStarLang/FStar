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
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.Reflection.V1.Data
open FStarC.Tactics.Types
open FStarC.Tactics.Monad

module Range  = FStarC.Range

(* Internal utilities *)
val goal_typedness_deps : goal -> ML (list ctx_uvar)
val mark_goal_implicit_already_checked : goal -> ML unit
val goal_with_type : goal -> typ -> ML goal

(* Metaprogramming primitives (not all of them).
 * Documented in `ulib/FStarC.Tactics.Builtins.fst` *)

val print                  : string -> ML (tac unit)
val debugging              : unit -> ML (tac bool)
val dump                   : string -> ML (tac unit)
val dump_all               : bool -> string -> ML (tac unit)
val dump_uvars_of          : goal -> string -> ML (tac unit)
val get_guard_policy       : unit -> ML (tac guard_policy)
val set_guard_policy       : guard_policy -> ML (tac unit)
val tadmit_t               : term -> ML (tac unit)
val fresh                  : unit -> ML (tac int)
val curms                  : unit -> ML (tac int)
val tcc                    : env -> term -> ML (tac comp)
val tc                     : env -> term -> ML (tac typ)

(* Helper *)
val focus                  : tac 'a -> ML (tac 'a)

val intro                  : unit -> ML (tac binder)
val intro_rec              : unit -> ML (tac (binder & binder))
val norm                   : list NormSteps.norm_step -> ML (tac unit)
val norm_term_env          : env -> list NormSteps.norm_step -> term -> ML (tac term)
val refine_intro           : unit -> ML (tac unit)
val t_exact                : bool -> bool -> term -> ML (tac unit)
val t_apply                : bool -> bool -> bool -> term -> ML (tac unit)
val t_apply_lemma          : bool -> bool -> term -> ML (tac unit)
val rewrite                : binder -> ML (tac unit)
val rename_to              : binder -> string -> ML (tac binder)
val binder_retype          : binder -> ML (tac unit)
val norm_binder_type       : list NormSteps.norm_step -> binder -> ML (tac unit)
val revert                 : unit -> ML (tac unit)
val clear                  : binder -> ML (tac unit)
val clear_top              : unit -> ML (tac unit)
val prune                  : string -> ML (tac unit)
val addns                  : string -> ML (tac unit)
val t_trefl                : (*allow_guards:*)bool -> ML (tac unit)
val dup                    : unit -> ML (tac unit)
val join                   : unit -> ML (tac unit)
val set_options            : string -> ML (tac unit)
val top_env                : unit -> ML (tac env)
val lax_on                 : unit -> ML (tac bool)
val unquote                : typ -> term -> ML (tac term)
val uvar_env               : env -> option typ -> ML (tac term)
val ghost_uvar_env         : env -> typ -> ML (tac term)
val fresh_universe_uvar    : unit -> ML (tac term)
val unshelve               : term -> ML (tac unit)
val match_env              : env -> term -> term -> ML (tac bool)
val unify_env              : env -> term -> term -> ML (tac bool)
val unify_guard_env        : env -> term -> term -> ML (tac bool)
val launch_process         : string -> list string -> string -> ML (tac string)
val fresh_bv_named         : string -> ML (tac bv)
val change                 : typ -> ML (tac unit)
val t_destruct             : term -> ML (tac (list (fv & int)))
val gather_explicit_guards_for_resolved_goals : unit -> ML (tac unit)
val inspect                : term -> ML (tac term_view)
val pack                   : term_view -> ML (tac term)
val pack_curried           : term_view -> ML (tac term)
val lget                   : typ -> string -> ML (tac term)
val lset                   : typ -> string -> term -> ML (tac unit)
val set_urgency            : int -> ML (tac unit)
val t_commute_applied_match : unit -> ML (tac unit)
val string_to_term         : env -> string -> ML (tac term)
val push_bv_dsenv          : env -> string -> ML (tac (env & bv))
val term_to_string         : term -> ML (tac string)
val comp_to_string         : comp -> ML (tac string)
val range_to_string        : Range.t -> ML (tac string)

val with_compat_pre_core   : int -> tac 'a -> ML (tac 'a)

val get_vconfig            : unit -> ML (tac FStarC.VConfig.vconfig)
val set_vconfig            : FStarC.VConfig.vconfig -> ML (tac unit)
val t_smt_sync             : FStarC.VConfig.vconfig -> ML (tac unit)
val free_uvars             : term -> ML (tac (list int))
