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

module FStarC.Tactics.V2.Basic

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
open FStarC.Reflection.V2.Data
open FStarC.Tactics.Types
open FStarC.Tactics.Monad

module Range  = FStarC.Range
module Core   = FStarC.TypeChecker.Core
module RD     = FStarC.Reflection.V2.Data

(* Metaprogramming primitives (not all of them).
 * Documented in `ulib/FStarC.Tactics.Builtins.fst` *)

val fixup_range (r : Range.t) : ML (tac (Range.t))
val compress               : term -> ML (tac term)
val compress_univ          : universe -> ML (tac universe)
val print                  : string -> ML (tac unit)
val debugging              : unit -> ML (tac bool)
val ide                    : unit -> ML (tac bool)
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
val intro                  : unit -> ML (tac RD.binding)
val intros                 : (max:int) -> ML (tac (list RD.binding))
val intro_rec              : unit -> ML (tac (RD.binding & RD.binding))
val norm                   : list NormSteps.norm_step -> ML (tac unit)
val norm_term_env          : env -> list NormSteps.norm_step -> term -> ML (tac term)
val refl_norm_well_typed_term : env -> list NormSteps.norm_step -> term -> ML (tac term)
val refine_intro           : unit -> ML (tac unit)
val t_exact                : bool -> bool -> term -> ML (tac unit)
val t_apply                : bool -> bool -> bool -> term -> ML (tac unit)
val t_apply_lemma          : bool -> bool -> term -> ML (tac unit)
val rewrite                : RD.binding -> ML (tac unit)
val grewrite               : term -> term -> ML (tac unit)
val rename_to              : RD.binding -> string -> ML (tac RD.binding)
val var_retype             : RD.binding -> ML (tac unit)
val norm_binding_type      : list NormSteps.norm_step -> RD.binding -> ML (tac unit)
val revert                 : unit -> ML (tac unit)
val clear                  : RD.binding -> ML (tac unit)
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
val lget                   : typ -> string -> ML (tac term)
val lset                   : typ -> string -> term -> ML (tac unit)
val set_urgency            : int -> ML (tac unit)
val set_dump_on_failure    : bool -> ML (tac unit)
val t_commute_applied_match : unit -> ML (tac unit)
val string_to_term         : env -> string -> ML (tac term)
val push_bv_dsenv          : env -> string -> ML (tac (env & RD.binding))
val term_to_string         : term -> ML (tac string)
val comp_to_string         : comp -> ML (tac string)
val term_to_doc            : term -> ML (tac Pprint.document)
val comp_to_doc            : comp -> ML (tac Pprint.document)
val range_to_string        : Range.t -> ML (tac string)
val with_compat_pre_core   : int -> tac 'a -> ML (tac 'a)

val get_vconfig            : unit -> ML (tac FStarC.VConfig.vconfig)
val set_vconfig            : FStarC.VConfig.vconfig -> ML (tac unit)
val t_smt_sync             : FStarC.VConfig.vconfig -> ML (tac unit)
val free_uvars             : term -> ML (tac (list int))

val all_ext_options        : unit -> ML (tac (list (string & string)))
val ext_getv               : string -> ML (tac string)
val ext_enabled            : string -> ML (tac bool)
val ext_getns              : string -> ML (tac (list (string & string)))

val alloc                  : 'a -> ML (tac (tref 'a))
val read                   : tref 'a -> ML (tac 'a)
val write                  : tref 'a -> 'a -> ML (tac unit)

val splice_quals           : unit -> ML (tac (list RD.qualifier))
val splice_attrs           : unit -> ML (tac (list attribute))

(***** Callbacks for the meta DSL framework *****)
let uvar_solution = bv & term
let remaining_uvar_t = bv & typ
let remaining_uvars_t = list remaining_uvar_t
let issues = list FStarC.Errors.issue
let refl_tac (a : Type) = tac (option a & issues)

val refl_is_non_informative           : env -> typ -> ML (refl_tac unit)
val refl_check_subtyping              : env -> typ -> typ -> ML (refl_tac unit)
val t_refl_check_equiv                : smt_ok:bool -> unfolding_ok:bool -> env -> typ -> typ -> ML (refl_tac unit)
val refl_core_compute_term_type       : env -> term -> ML (refl_tac (Core.tot_or_ghost & typ))
val refl_core_check_term              : env -> term -> typ -> Core.tot_or_ghost -> ML (refl_tac unit)
val refl_core_check_term_at_type      : env -> term -> typ -> ML (refl_tac Core.tot_or_ghost)
val refl_tc_term                      : env -> term -> ML (refl_tac (term & (Core.tot_or_ghost & typ)))
val refl_universe_of                  : env -> term -> ML (refl_tac universe)
val refl_check_prop_validity          : env -> term -> ML (refl_tac unit)
val refl_check_match_complete         : env -> term -> term -> list pattern -> ML (refl_tac (list pattern & list (list RD.binding)))
val refl_instantiate_implicits        : env -> term -> expected_typ:option term -> inst_extra:bool -> ML (refl_tac (remaining_uvars_t & term & typ))
val refl_try_unify                    : env -> list (bv & typ) -> term -> term -> ML (refl_tac (list uvar_solution))
val refl_maybe_relate_after_unfolding : env -> term -> term -> ML (refl_tac Core.side)
val refl_maybe_unfold_head            : env -> term -> ML (refl_tac term)

val push_open_namespace               : env -> list string -> ML (tac env)
val push_module_abbrev                : env -> string -> list string -> ML (tac env)
val resolve_name                      : env -> list string -> ML (tac (option (either bv fv)))
val log_issues                        : list Errors.issue -> ML (tac unit)

val proofstate_of_goals : Range.t -> env -> list goal -> list implicit -> ML proofstate
(* Returns proofstate and uvar for main witness *)
val proofstate_of_goal_ty : Range.t -> env -> typ -> ML (proofstate & term)

val proofstate_of_all_implicits: Range.t -> env -> implicits -> ML (proofstate & term)

val call_subtac                       : env -> tac unit -> universe -> typ -> ML (refl_tac term)
val call_subtac_tm                    : env -> term     -> universe -> typ -> ML (refl_tac term)

val stats_record (a:'a) (wp:'b) (s:string) (f : tac 'c) : ML (tac 'c)

val with_error_context (a:'a) (wp:'b) (s:string) (f : tac 'c) : ML (tac 'c)
