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

module FStarC.Tactics.V2.Primops

(* Most of the tactic running logic is here. V1.Interpreter calls
into this module for all of that. *)

open FStarC
open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Range
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.Tactics.Types
open FStarC.Tactics.Printing
open FStarC.Tactics.Monad
open FStarC.Tactics.V2.Basic
open FStarC.Tactics.CtrlRewrite
open FStarC.Tactics.Native
open FStarC.Tactics.Common
open FStarC.Tactics.InterpFuns
open FStarC.Class.Show
open FStarC.Class.Monad

module E       = FStarC.Tactics.Embedding
module NBET    = FStarC.TypeChecker.NBETerm
module NRE     = FStarC.Reflection.V2.NBEEmbeddings
module PC      = FStarC.Parser.Const
module RE      = FStarC.Reflection.V2.Embeddings
module S       = FStarC.Syntax.Syntax
module TI      = FStarC.Tactics.Interpreter

let solve (#a:Type) {| ev : a |} : Tot a = ev

instance _ = RE.e_term (* REMOVE ME *)

(* Takes a `sealed a`, but that's just a userspace abstraction. *)
let unseal (_typ:_) (x:Sealed.sealed 'a) : tac 'a = return (Sealed.unseal x)
let unseal_step =
  (* Unseal is not in builtins. *)
  let s =
    mk_tac_step_2 1 "unseal"
      #e_any      #(e_sealed      e_any)      #e_any
      #NBET.e_any #(NBET.e_sealed NBET.e_any) #NBET.e_any
      unseal unseal
  in
  { s with name = PC.unseal_lid }

let e_ret_t #a (d : embedding a) : embedding (option a & issues) = solve
let nbe_e_ret_t #a (d : NBET.embedding a) : NBET.embedding (option a & issues) = solve

let ops = [
  (* Total steps *)
  mk_tot_step_1_psc 0 "tracepoint" tracepoint_with_psc tracepoint_with_psc;
  mk_tot_step_2 0 "set_proofstate_range" set_proofstate_range set_proofstate_range;
  mk_tot_step_1 0 "incr_depth" incr_depth incr_depth;
  mk_tot_step_1 0 "decr_depth" decr_depth decr_depth;
  mk_tot_step_1 0 "goals_of" goals_of goals_of;
  mk_tot_step_1 0 "smt_goals_of" smt_goals_of smt_goals_of;
  mk_tot_step_1 0 "goal_env" goal_env goal_env;
  mk_tot_step_1 0 "goal_type" goal_type goal_type;
  mk_tot_step_1 0 "goal_witness" goal_witness goal_witness;
  mk_tot_step_1 0 "is_guard" is_guard is_guard;
  mk_tot_step_1 0 "get_label" get_label get_label;
  mk_tot_step_2 0 "set_label" set_label set_label;

  (* Tactic builtin steps *)

  unseal_step;
  
  mk_tac_step_1 0 "get" (fun () -> get) (fun () -> get);

  mk_tac_step_1 0 "fixup_range" fixup_range fixup_range;

  mk_tac_step_1 0 "compress" compress compress;
  mk_tac_step_1 0 "set_goals" set_goals set_goals;
  mk_tac_step_1 0 "set_smt_goals" set_smt_goals set_smt_goals;

  mk_tac_step_2 1 "catch"
    #e_any #(TI.e_tactic_thunk e_any) #(e_either E.e_exn e_any)
    #NBET.e_any #(TI.e_tactic_nbe_thunk NBET.e_any) #(NBET.e_either E.e_exn_nbe NBET.e_any)
    (fun _ -> catch)
    (fun _ -> catch);

  mk_tac_step_1 0 "raise_core" (traise <: exn -> tac unit) (traise <: exn -> tac unit) ;

  mk_tac_step_1 0 "intro" intro intro;
  mk_tac_step_1 0 "intros" intros intros;
  mk_tac_step_1 0 "intro_rec" intro_rec intro_rec;
  mk_tac_step_1 0 "norm" norm norm;
  mk_tac_step_3 0 "norm_term_env" norm_term_env norm_term_env;
  mk_tac_step_2 0 "norm_binding_type" norm_binding_type norm_binding_type;
  mk_tac_step_2 0 "rename_to" rename_to rename_to;
  mk_tac_step_1 0 "var_retype" var_retype var_retype;
  mk_tac_step_1 0 "revert" revert revert;
  mk_tac_step_1 0 "clear_top" clear_top clear_top;
  mk_tac_step_1 0 "clear" clear clear;
  mk_tac_step_1 0 "rewrite" rewrite rewrite;
  mk_tac_step_2 0 "grewrite" grewrite grewrite;
  mk_tac_step_1 0 "refine_intro" refine_intro refine_intro;
  mk_tac_step_3 0 "t_exact"  t_exact t_exact;
  mk_tac_step_4 0 "t_apply"  t_apply t_apply;
  mk_tac_step_3 0 "t_apply_lemma" t_apply_lemma t_apply_lemma;
  mk_tac_step_1 0 "set_options" set_options set_options;
  mk_tac_step_2 0 "tcc" tcc tcc;
  mk_tac_step_2 0 "tc"  tc tc;
  mk_tac_step_1 0 "unshelve" unshelve unshelve;

  mk_tac_step_2 1 "unquote"
    #e_any #RE.e_term #e_any
    #NBET.e_any #NRE.e_term #NBET.e_any
    unquote
    (fun _ _ -> failwith "NBE unquote");

  mk_tac_step_1 0 "prune" prune prune;
  mk_tac_step_1 0 "addns" addns addns;
  mk_tac_step_1 0 "print" print print;
  mk_tac_step_1 0 "debugging" debugging debugging;
  mk_tac_step_1 0 "ide" ide ide;
  mk_tac_step_1 0 "dump" dump dump;
  mk_tac_step_2 0 "dump_all" dump_all dump_all;
  mk_tac_step_2 0 "dump_uvars_of" dump_uvars_of dump_uvars_of;

  mk_tac_step_3 0 "ctrl_rewrite"
    #E.e_direction #(TI.e_tactic_1 RE.e_term (e_tuple2 e_bool E.e_ctrl_flag))
                   #(TI.e_tactic_thunk e_unit)
                   #e_unit
    #E.e_direction_nbe #(TI.e_tactic_nbe_1 NRE.e_term (NBET.e_tuple2 NBET.e_bool E.e_ctrl_flag_nbe))
                       #(TI.e_tactic_nbe_thunk NBET.e_unit)
                       #NBET.e_unit
    ctrl_rewrite
    ctrl_rewrite;

  mk_tac_step_1 0 "t_trefl" t_trefl t_trefl;
  mk_tac_step_1 0 "dup" dup dup;
  mk_tac_step_1 0 "tadmit_t" tadmit_t tadmit_t;
  mk_tac_step_1 0 "join" join join;
  mk_tac_step_1 0 "t_destruct" t_destruct t_destruct;
  mk_tac_step_1 0 "top_env" top_env top_env;
  mk_tac_step_1 0 "fresh" fresh fresh;
  mk_tac_step_1 0 "curms" curms curms;
  mk_tac_step_2 0 "uvar_env" uvar_env uvar_env;
  mk_tac_step_2 0 "ghost_uvar_env" ghost_uvar_env ghost_uvar_env;
  mk_tac_step_1 0 "fresh_universe_uvar" fresh_universe_uvar fresh_universe_uvar;
  mk_tac_step_3 0 "unify_env" unify_env unify_env;
  mk_tac_step_3 0 "unify_guard_env" unify_guard_env unify_guard_env;
  mk_tac_step_3 0 "match_env" match_env match_env;
  mk_tac_step_3 0 "launch_process" launch_process launch_process;
  mk_tac_step_1 0 "change" change change;
  mk_tac_step_1 0 "get_guard_policy" get_guard_policy get_guard_policy;
  mk_tac_step_1 0 "set_guard_policy" set_guard_policy set_guard_policy;
  mk_tac_step_1 0 "lax_on" lax_on lax_on;

  mk_tac_step_2 1 "lget"
    #e_any #e_string #e_any
    #NBET.e_any #NBET.e_string #NBET.e_any
    lget
    (fun _ _ -> fail "sorry, `lget` does not work in NBE");

  mk_tac_step_3 1 "lset"
    #e_any #e_string #e_any #e_unit
    #NBET.e_any #NBET.e_string #NBET.e_any #NBET.e_unit
    lset
    (fun _ _ _ -> fail "sorry, `lset` does not work in NBE");

  mk_tac_step_1 1 "set_urgency" set_urgency set_urgency;
  mk_tac_step_1 1 "set_dump_on_failure" set_dump_on_failure set_dump_on_failure;
  mk_tac_step_1 1 "t_commute_applied_match" t_commute_applied_match t_commute_applied_match;
  mk_tac_step_1 0 "gather_or_solve_explicit_guards_for_resolved_goals"
    gather_explicit_guards_for_resolved_goals
    gather_explicit_guards_for_resolved_goals;
  mk_tac_step_2 0 "string_to_term" string_to_term string_to_term;
  mk_tac_step_2 0 "push_bv_dsenv" push_bv_dsenv push_bv_dsenv;
  mk_tac_step_1 0 "term_to_string"  term_to_string term_to_string;
  mk_tac_step_1 0 "comp_to_string" comp_to_string comp_to_string;
  mk_tac_step_1 0 "term_to_doc"  term_to_doc term_to_doc;
  mk_tac_step_1 0 "comp_to_doc" comp_to_doc comp_to_doc;
  mk_tac_step_1 0 "range_to_string" range_to_string range_to_string;

  mk_tac_step_3 1 "with_compat_pre_core"
    #e_any #e_int #(TI.e_tactic_thunk e_any) #e_any
    #NBET.e_any #NBET.e_int #(TI.e_tactic_nbe_thunk NBET.e_any) #NBET.e_any
    (fun _ -> with_compat_pre_core)
    (fun _ -> with_compat_pre_core);

  mk_tac_step_1 0 "get_vconfig" get_vconfig get_vconfig;
  mk_tac_step_1 0 "set_vconfig" set_vconfig set_vconfig;
  mk_tac_step_1 0 "t_smt_sync" t_smt_sync t_smt_sync;
  mk_tac_step_1 0 "free_uvars"  free_uvars free_uvars;
  mk_tac_step_1 0 "all_ext_options" all_ext_options all_ext_options;
  mk_tac_step_1 0 "ext_getv" ext_getv ext_getv;
  mk_tac_step_1 0 "ext_enabled" ext_enabled ext_enabled;
  mk_tac_step_1 0 "ext_getns" ext_getns ext_getns;

  mk_tac_step_2 1 "alloc"
    #e_any #e_any #(E.e_tref #S.term)
    #NBET.e_any #NBET.e_any #(E.e_tref_nbe #NBET.t)
    (fun _ -> alloc)
    (fun _ -> alloc);

  mk_tac_step_2 1 "read"
    #e_any #(E.e_tref #S.term) #e_any
    #NBET.e_any #(E.e_tref_nbe #NBET.t) #NBET.e_any
    (fun _ -> read)
    (fun _ -> read);

  mk_tac_step_3 1 "write"
    #e_any #(E.e_tref #S.term) #e_any #e_unit
    #NBET.e_any #(E.e_tref_nbe #NBET.t) #NBET.e_any #NBET.e_unit
    (fun _ -> write)
    (fun _ -> write);

  mk_tac_step_1 0 "splice_quals" splice_quals splice_quals;
  mk_tac_step_1 0 "splice_attrs" splice_attrs splice_attrs;

  // reflection typechecker callbacks (part of the DSL framework)

  mk_tac_step_2 0 "is_non_informative"      refl_is_non_informative refl_is_non_informative;
  mk_tac_step_3 0 "check_subtyping"         refl_check_subtyping refl_check_subtyping;
  mk_tac_step_5 0 "t_check_equiv"           t_refl_check_equiv t_refl_check_equiv;
  mk_tac_step_2 0 "core_compute_term_type"  refl_core_compute_term_type refl_core_compute_term_type;
  mk_tac_step_4 0 "core_check_term"         refl_core_check_term refl_core_check_term;
  mk_tac_step_3 0 "core_check_term_at_type" refl_core_check_term_at_type refl_core_check_term_at_type;
  mk_tac_step_2 0 "tc_term"                 refl_tc_term refl_tc_term;
  mk_tac_step_2 0 "universe_of"             refl_universe_of refl_universe_of;
  mk_tac_step_2 0 "check_prop_validity"     refl_check_prop_validity refl_check_prop_validity;
  mk_tac_step_4 0 "check_match_complete"    refl_check_match_complete refl_check_match_complete;
  mk_tac_step_4 0 "instantiate_implicits"
    #_ #_ #_ #_ #(e_ret_t (e_tuple3 (e_list (e_tuple2 RE.e_namedv solve)) solve solve))
    #_ #_ #_ #_ #(nbe_e_ret_t (NBET.e_tuple3 (NBET.e_list (NBET.e_tuple2 NRE.e_namedv solve)) solve solve))
    refl_instantiate_implicits refl_instantiate_implicits;
  mk_tac_step_4 0 "try_unify"
    #_ #(e_list (e_tuple2 RE.e_namedv RE.e_term))             #_ #_ #(e_ret_t (e_list (e_tuple2 RE.e_namedv RE.e_term)))
    #_ #(NBET.e_list (NBET.e_tuple2 NRE.e_namedv NRE.e_term)) #_ #_ #(nbe_e_ret_t (NBET.e_list (NBET.e_tuple2 NRE.e_namedv NRE.e_term)))
    refl_try_unify refl_try_unify;
  mk_tac_step_3 0 "maybe_relate_after_unfolding" refl_maybe_relate_after_unfolding refl_maybe_relate_after_unfolding;
  mk_tac_step_2 0 "maybe_unfold_head" refl_maybe_unfold_head refl_maybe_unfold_head;
  mk_tac_step_3 0 "norm_well_typed_term" refl_norm_well_typed_term refl_norm_well_typed_term;

  mk_tac_step_2 0 "push_open_namespace" push_open_namespace push_open_namespace;
  mk_tac_step_3 0 "push_module_abbrev" push_module_abbrev push_module_abbrev;
  mk_tac_step_2 0 "resolve_name"
    #_ #_ #(e_option (e_either RE.e_bv solve)) // disambiguate bv/namedv
    #_ #_ #(NBET.e_option (NBET.e_either NRE.e_bv solve))
    resolve_name resolve_name;
  mk_tac_step_1 0 "log_issues" log_issues log_issues;
  mk_tac_step_4 0 "call_subtac"
    #_ #(TI.e_tactic_thunk e_unit) #_ #_ #_
    #_ #(TI.e_tactic_nbe_thunk NBET.e_unit) #_ #_ #_
    call_subtac call_subtac;

  mk_tac_step_4 0 "call_subtac_tm"
    call_subtac_tm call_subtac_tm;

  mk_tac_step_4 1 "stats_record"
    #e_any      #e_any      #_ #(TI.e_tactic_thunk e_any)          #e_any
    #NBET.e_any #NBET.e_any #_ #(TI.e_tactic_nbe_thunk NBET.e_any) #NBET.e_any
    stats_record
    stats_record;

  mk_tac_step_4 1 "with_error_context"
    #e_any      #e_any      #_ #(TI.e_tactic_thunk e_any)          #e_any
    #NBET.e_any #NBET.e_any #_ #(TI.e_tactic_nbe_thunk NBET.e_any) #NBET.e_any
    with_error_context
    with_error_context;
]
