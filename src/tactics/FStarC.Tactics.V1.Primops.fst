module FStarC.Tactics.V1.Primops

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Range
open FStarC.Util
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.Tactics.Result
open FStarC.Tactics.Types
open FStarC.Tactics.Printing
open FStarC.Tactics.Monad
open FStarC.Tactics.V1.Basic
open FStarC.Tactics.CtrlRewrite
open FStarC.Tactics.Native
open FStarC.Tactics.Common
open FStarC.Tactics.InterpFuns
open FStarC.Class.Show
open FStarC.Class.Monad
open FStarC.Class.HasRange

module E       = FStarC.Tactics.Embedding
module NBET    = FStarC.TypeChecker.NBETerm
module NRE     = FStarC.Reflection.V1.NBEEmbeddings
module PO      = FStarC.TypeChecker.Primops
module RE      = FStarC.Reflection.V1.Embeddings
module TI      = FStarC.Tactics.Interpreter

(* Bring instances *)
open FStarC.Reflection.V2.Embeddings {}
open FStarC.Reflection.V2.NBEEmbeddings {}

let solve (#a:Type) {| ev : a |} : Tot a = ev

instance _ : embedding term = RE.e_term (* REMOVE ME *)

let fix_module (ps : PO.primitive_step) : PO.primitive_step =
  let p : Path.path string = Ident.path_of_lid ps.name in
  if p `Path.is_under` ["FStar"; "Stubs"; "Tactics"; "V2"; "Builtins"] then
    let p' = ["FStar"; "Stubs"; "Tactics"; "V1"; "Builtins"] @ (p |> List.tl |> List.tl |> List.tl |> List.tl |> List.tl) in
    { ps with name = Ident.lid_of_path p' (pos ps.name) }
  else
    failwith "huh?"

let ops =
  List.map fix_module <|
[
  (* Total steps defined in V2 *)

  mk_tac_step_1 0 "set_goals" set_goals set_goals;
  mk_tac_step_1 0 "set_smt_goals" set_smt_goals set_smt_goals;

  mk_tac_step_2 1 "catch"
    #e_any #(TI.e_tactic_thunk e_any) #(e_either E.e_exn e_any)
    #NBET.e_any #(TI.e_tactic_nbe_thunk NBET.e_any) #(NBET.e_either E.e_exn_nbe NBET.e_any)
    (fun _ -> catch)
    (fun _ -> catch);

  mk_tac_step_2 1 "recover"
    #e_any #(TI.e_tactic_thunk e_any) #(e_either E.e_exn e_any)
    #NBET.e_any #(TI.e_tactic_nbe_thunk NBET.e_any) #(NBET.e_either E.e_exn_nbe NBET.e_any)
    (fun _ -> recover)
    (fun _ -> recover);

  mk_tac_step_1 0 "intro" intro intro ;
  mk_tac_step_1 0 "intro_rec" intro_rec intro_rec ;
  mk_tac_step_1 0 "norm" norm norm ;
  mk_tac_step_3 0 "norm_term_env" norm_term_env norm_term_env ;
  mk_tac_step_2 0 "norm_binder_type" norm_binder_type norm_binder_type;
  mk_tac_step_2 0 "rename_to" rename_to rename_to ;

  mk_tac_step_1 0 "binder_retype" binder_retype binder_retype ;
  mk_tac_step_1 0 "revert" revert revert ;
  mk_tac_step_1 0 "clear_top" clear_top clear_top ;
  mk_tac_step_1 0 "clear" clear clear ;
  mk_tac_step_1 0 "rewrite" rewrite rewrite ;
  mk_tac_step_1 0 "refine_intro" refine_intro refine_intro ;
  mk_tac_step_3 0 "t_exact" t_exact t_exact ;
  mk_tac_step_4 0 "t_apply" t_apply t_apply ;
  mk_tac_step_3 0 "t_apply_lemma" t_apply_lemma t_apply_lemma ;
  mk_tac_step_1 0 "set_options" set_options set_options ;
  mk_tac_step_2 0 "tcc" tcc tcc ;
  mk_tac_step_2 0 "tc" tc tc ;

  mk_tac_step_1 0 "unshelve" unshelve unshelve;

  mk_tac_step_2 1 "unquote"
    #e_any #RE.e_term #e_any
    #NBET.e_any #NRE.e_term #NBET.e_any
    unquote
    (fun _ _ -> failwith "NBE unquote");

  mk_tac_step_1 0 "prune" prune prune ;
  mk_tac_step_1 0 "addns" addns addns ;
  mk_tac_step_1 0 "print" print print ;
  mk_tac_step_1 0 "debugging" debugging debugging ;
  mk_tac_step_1 0 "dump" dump dump ;
  mk_tac_step_2 0 "dump_all" dump_all dump_all ;
  mk_tac_step_2 0 "dump_uvars_of" dump_uvars_of dump_uvars_of ;

  mk_tac_step_3 0 "ctrl_rewrite"
    #E.e_direction #(TI.e_tactic_1 RE.e_term (e_tuple2 e_bool E.e_ctrl_flag)) #(TI.e_tactic_thunk e_unit) #e_unit
    #E.e_direction_nbe #(TI.e_tactic_nbe_1 NRE.e_term (NBET.e_tuple2 NBET.e_bool E.e_ctrl_flag_nbe)) #(TI.e_tactic_nbe_thunk NBET.e_unit) #NBET.e_unit
    ctrl_rewrite
    ctrl_rewrite;

  mk_tac_step_1 0 "t_trefl" t_trefl t_trefl ;
  mk_tac_step_1 0 "dup" dup dup  ;

  mk_tac_step_1 0 "tadmit_t" #RE.e_term #_ #NRE.e_term #_ tadmit_t tadmit_t ;
  mk_tac_step_1 0 "join" join join ;

  mk_tac_step_1 0 "t_destruct"
    #RE.e_term #_
    #NRE.e_term #_
    t_destruct t_destruct;

  mk_tac_step_1 0 "top_env"
    top_env 
    top_env ;

  mk_tac_step_1 0 "inspect"
    #RE.e_term #_
    #NRE.e_term #_
    inspect inspect ;

  mk_tac_step_1 0 "pack"
    #_ #RE.e_term
    #_ #NRE.e_term
    pack pack ;

  mk_tac_step_1 0 "pack_curried"
    #_ #RE.e_term
    #_ #NRE.e_term
    pack_curried pack_curried;

  mk_tac_step_1 0 "fresh" fresh fresh ;
  mk_tac_step_1 0 "curms" curms curms ;
  mk_tac_step_2 0 "uvar_env"
    #_ #(e_option RE.e_term) #RE.e_term
    #_ #(NBET.e_option NRE.e_term) #NRE.e_term
    uvar_env uvar_env ;

  mk_tac_step_2 0 "ghost_uvar_env"
    #_ #RE.e_term #RE.e_term
    #_ #NRE.e_term #NRE.e_term
    ghost_uvar_env ghost_uvar_env ;

  mk_tac_step_1 0 "fresh_universe_uvar"
    #_ #RE.e_term
    #_ #NRE.e_term
    fresh_universe_uvar
    fresh_universe_uvar ;

  mk_tac_step_3 0 "unify_env"
    #RE.e_env #RE.e_term #RE.e_term #e_bool
    #NRE.e_env #NRE.e_term #NRE.e_term #NBET.e_bool
    unify_env unify_env ;

  mk_tac_step_3 0 "unify_guard_env"
    #RE.e_env #RE.e_term #RE.e_term #e_bool
    #NRE.e_env #NRE.e_term #NRE.e_term #NBET.e_bool
    unify_guard_env unify_guard_env ;

  mk_tac_step_3 0 "match_env"
    #RE.e_env #RE.e_term #RE.e_term #e_bool
    #NRE.e_env #NRE.e_term #NRE.e_term #NBET.e_bool
    match_env match_env ;

  mk_tac_step_3 0 "launch_process" launch_process launch_process ;

  mk_tac_step_1 0 "fresh_bv_named"
    #e_string #RE.e_bv
    #NBET.e_string #NRE.e_bv
    fresh_bv_named fresh_bv_named ;

  mk_tac_step_1 0 "change"
    #RE.e_term #e_unit
    #NRE.e_term #NBET.e_unit
    change change ;

  mk_tac_step_1 0 "get_guard_policy" get_guard_policy get_guard_policy ;
  mk_tac_step_1 0 "set_guard_policy" set_guard_policy set_guard_policy ;
  mk_tac_step_1 0 "lax_on" lax_on lax_on ;

  mk_tac_step_2 1 "lget"
    #e_any #e_string #e_any
    #NBET.e_any #NBET.e_string #NBET.e_any
    lget 
    (fun _ _ -> fail "sorry, `lget` does not work in NBE") ;

  mk_tac_step_3 1 "lset"
    #e_any #e_string #e_any #e_unit
    #NBET.e_any #NBET.e_string #NBET.e_any #NBET.e_unit
    lset
    (fun _ _ _ -> fail "sorry, `lset` does not work in NBE") ;

  mk_tac_step_1 0 "set_urgency" set_urgency set_urgency ;

  mk_tac_step_1 0 "t_commute_applied_match"
    t_commute_applied_match
    t_commute_applied_match ;

  mk_tac_step_1 0 "gather_or_solve_explicit_guards_for_resolved_goals"
    gather_explicit_guards_for_resolved_goals 
    gather_explicit_guards_for_resolved_goals ;

  mk_tac_step_2 0 "string_to_term"
    #RE.e_env #e_string #RE.e_term
    #NRE.e_env #NBET.e_string #NRE.e_term
    string_to_term string_to_term ;

  mk_tac_step_2 0 "push_bv_dsenv"
    #RE.e_env #e_string #(e_tuple2 RE.e_env RE.e_bv)
    #NRE.e_env #NBET.e_string #(NBET.e_tuple2 NRE.e_env NRE.e_bv)
    push_bv_dsenv push_bv_dsenv ;

  mk_tac_step_1 0 "term_to_string"
    #RE.e_term #e_string
    #NRE.e_term #NBET.e_string
    term_to_string term_to_string ;

  mk_tac_step_1 0 "comp_to_string"
    comp_to_string
    comp_to_string ;

  mk_tac_step_1 0 "range_to_string" range_to_string range_to_string ;
  mk_tac_step_2 0 "term_eq_old"
    #RE.e_term #RE.e_term #e_bool
    #NRE.e_term #NRE.e_term #NBET.e_bool
    term_eq_old
    term_eq_old ;

  mk_tac_step_3 1 "with_compat_pre_core"
    #e_any #e_int #(TI.e_tactic_thunk e_any) #e_any
    #NBET.e_any #NBET.e_int #(TI.e_tactic_nbe_thunk NBET.e_any) #NBET.e_any
    (fun _ -> with_compat_pre_core) (fun _ -> with_compat_pre_core) ;

  mk_tac_step_1 0 "get_vconfig" get_vconfig get_vconfig ;
  mk_tac_step_1 0 "set_vconfig" set_vconfig set_vconfig ;
  mk_tac_step_1 0 "t_smt_sync" t_smt_sync t_smt_sync ;

  mk_tac_step_1 0 "free_uvars"
    #RE.e_term #_
    #NRE.e_term #_
    free_uvars free_uvars ;

]
