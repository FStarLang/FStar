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
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.Reflection.V2.Data
open FStarC.Tactics.Types
open FStarC.Tactics.Monad

module Range  = FStarC.Range
module Core   = FStarC.TypeChecker.Core
module RD     = FStarC.Reflection.V2.Data

val proofstate_of_goals : Range.t -> env -> list goal -> list implicit -> proofstate
(* Returns proofstate and uvar for main witness *)
val proofstate_of_goal_ty : Range.t -> env -> typ -> proofstate & term

val proofstate_of_all_implicits: Range.t -> env -> implicits -> proofstate & term

(* Metaprogramming primitives (not all of them).
 * Documented in `ulib/FStarC.Tactics.Builtins.fst` *)

val fixup_range (r : Range.t) : tac (Range.t)
val compress               : term -> tac term
val compress_univ          : universe -> tac universe
val top_env                : unit -> tac env
val fresh                  : unit -> tac int
val refine_intro           : unit -> tac unit
val tc                     : env -> term -> tac typ
val tcc                    : env -> term -> tac comp
val unshelve               : term -> tac unit
val unquote                : typ -> term -> tac term
val norm                   : list NormSteps.norm_step -> tac unit
val norm_term_env          : env -> list NormSteps.norm_step -> term -> tac term
val norm_binding_type      : list NormSteps.norm_step -> RD.binding -> tac unit
val intro                  : unit -> tac RD.binding
val intros                 : (max:int) -> tac (list RD.binding)
val intro_rec              : unit -> tac (RD.binding & RD.binding)
val rename_to              : RD.binding -> string -> tac RD.binding
val revert                 : unit -> tac unit
val var_retype             : RD.binding -> tac unit
val clear_top              : unit -> tac unit
val clear                  : RD.binding -> tac unit
val rewrite                : RD.binding -> tac unit
val grewrite               : term -> term -> tac unit
val t_exact                : bool -> bool -> term -> tac unit
val t_apply                : bool -> bool -> bool -> term -> tac unit
val t_apply_lemma          : bool -> bool -> term -> tac unit
val print                  : string -> tac unit
val debugging              : unit -> tac bool
val ide                    : unit -> tac bool
val dump                   : string -> tac unit
val dump_all               : bool -> string -> tac unit
val dump_uvars_of          : goal -> string -> tac unit
val t_trefl                : (*allow_guards:*)bool -> tac unit
val dup                    : unit -> tac unit
val prune                  : string -> tac unit
val addns                  : string -> tac unit
val t_destruct             : term -> tac (list (fv & int))
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
val join                   : unit -> tac unit
val lget                   : typ -> string -> tac term
val lset                   : typ -> string -> term -> tac unit
val curms                  : unit -> tac int
val set_urgency            : int -> tac unit
val set_dump_on_failure    : bool -> tac unit
val t_commute_applied_match : unit -> tac unit
val string_to_term         : env -> string -> tac term
val push_bv_dsenv          : env -> string -> tac (env & RD.binding)
val term_to_string         : term -> tac string
val comp_to_string         : comp -> tac string
val term_to_doc            : term -> tac Pprint.document
val comp_to_doc            : comp -> tac Pprint.document
val range_to_string        : Range.t -> tac string
val with_compat_pre_core   : int -> tac 'a -> tac 'a

val get_vconfig            : unit -> tac FStarC.VConfig.vconfig
val set_vconfig            : FStarC.VConfig.vconfig -> tac unit
val t_smt_sync             : FStarC.VConfig.vconfig -> tac unit
val free_uvars             : term -> tac (list int)

val all_ext_options        : unit -> tac (list (string & string))
val ext_getv               : string -> tac string
val ext_enabled            : string -> tac bool
val ext_getns              : string -> tac (list (string & string))

val alloc                  : 'a -> tac (tref 'a)
val read                   : tref 'a -> tac 'a
val write                  : tref 'a -> 'a -> tac unit

val splice_quals           : unit -> tac (list RD.qualifier)
val splice_attrs           : unit -> tac (list attribute)

(***** Callbacks for the meta DSL framework *****)
let uvar_solution = bv & term
let remaining_uvar_t = bv & typ
let remaining_uvars_t = list remaining_uvar_t
let issues = list FStarC.Errors.issue
let refl_tac (a : Type) = tac (option a & issues)

val refl_is_non_informative           : env -> typ -> refl_tac unit
val refl_check_subtyping              : env -> typ -> typ -> refl_tac unit
val t_refl_check_equiv                : smt_ok:bool -> unfolding_ok:bool -> env -> typ -> typ -> refl_tac unit
val refl_core_compute_term_type       : env -> term -> refl_tac (Core.tot_or_ghost & typ)
val refl_core_check_term              : env -> term -> typ -> Core.tot_or_ghost -> refl_tac unit
val refl_core_check_term_at_type      : env -> term -> typ -> refl_tac Core.tot_or_ghost
val refl_tc_term                      : env -> term -> refl_tac (term & (Core.tot_or_ghost & typ))
val refl_universe_of                  : env -> term -> refl_tac universe
val refl_check_prop_validity          : env -> term -> refl_tac unit
val refl_check_match_complete         : env -> term -> term -> list pattern -> refl_tac (list pattern & list (list RD.binding))
val refl_instantiate_implicits        : env -> term -> expected_typ:option term -> inst_extra:bool -> refl_tac (remaining_uvars_t & term & typ)
val refl_try_unify                    : env -> list (bv & typ) -> term -> term -> refl_tac (list uvar_solution)
val refl_maybe_relate_after_unfolding : env -> term -> term -> refl_tac Core.side
val refl_maybe_unfold_head            : env -> term -> refl_tac term
val refl_norm_well_typed_term         : env -> list NormSteps.norm_step -> term -> tac term

val push_open_namespace               : env -> list string -> tac env
val push_module_abbrev                : env -> string -> list string -> tac env
val resolve_name                      : env -> list string -> tac (option (either bv fv))
val log_issues                        : list Errors.issue -> tac unit

val call_subtac                       : env -> tac unit -> universe -> typ -> refl_tac term
val call_subtac_tm                    : env -> term     -> universe -> typ -> refl_tac term

val stats_record (a:'a) (wp:'b) (s:string) (f : tac 'c) : tac 'c

val with_error_context (a:'a) (wp:'b) (s:string) (f : tac 'c) : tac 'c
