open Prims
open FStar_Pervasives_Native
open FStar_Pervasives
open FStarC_Tactics_Result
open FStarC_Tactics_Types
open FStar_Tactics_Effect

module N    = FStarC_TypeChecker_Normalize
module E    = FStar_Tactics_Effect
module B    = FStarC_Tactics_V2_Basic
module TM   = FStarC_Tactics_Monad
module CTRW = FStarC_Tactics_CtrlRewrite
module RT   = FStarC_Reflection_Types
module RD   = FStarC_Reflection_Data
module EMB  = FStarC_Syntax_Embeddings
module EMB_Base  = FStarC_Syntax_Embeddings_Base
module NBET = FStarC_TypeChecker_NBETerm

type 'a __tac = ('a, unit) E.tac_repr

let interpret_tac (s:string) (t: 'a TM.tac) (ps: proofstate): 'a __result =
  FStarC_Errors.with_ctx
    ("While running primitive " ^ s ^ " (called from within a plugin)")
    (fun () -> TM.run t ps)

let uninterpret_tac (t: 'a __tac) (ps: proofstate): 'a __result =
  t ps

let to_tac_0 (t: 'a __tac): 'a TM.tac =
  (fun (ps: proofstate) ->
    uninterpret_tac t ps) |> TM.mk_tac

let to_tac_1 (t: 'b -> 'a __tac): 'b -> 'a TM.tac = fun x ->
  (fun (ps: proofstate) ->
    uninterpret_tac (t x) ps) |> TM.mk_tac

let from_tac_1 s (t: 'a -> 'r TM.tac): 'a  -> 'r __tac =
  fun (xa: 'a) (ps : proofstate) ->
    let m = t xa in
    interpret_tac s m ps

let from_tac_2 s (t: 'a -> 'b -> 'r TM.tac): 'a  -> 'b -> 'r __tac =
  fun (xa: 'a) (xb: 'b) (ps : proofstate) ->
    let m = t xa xb in
    interpret_tac s m ps

let from_tac_3 s (t: 'a -> 'b -> 'c -> 'r TM.tac): 'a  -> 'b -> 'c -> 'r __tac =
  fun (xa: 'a) (xb: 'b) (xc: 'c) (ps : proofstate) ->
    let m = t xa xb xc in
    interpret_tac s m ps

let from_tac_4 s (t: 'a -> 'b -> 'c -> 'd -> 'r TM.tac): 'a  -> 'b -> 'c -> 'd -> 'r __tac =
  fun (xa: 'a) (xb: 'b) (xc: 'c) (xd: 'd)  (ps : proofstate) ->
    let m = t xa xb xc xd in
    interpret_tac s m ps

let from_tac_5 s (t: 'a -> 'b -> 'c -> 'd -> 'e -> 'r TM.tac): 'a  -> 'b -> 'c -> 'd -> 'e -> 'r __tac =
  fun (xa: 'a) (xb: 'b) (xc: 'c) (xd: 'd) (xe: 'e) (ps : proofstate) ->
    let m = t xa xb xc xd xe in
    interpret_tac s m ps


(* Pointing to the internal primitives *)
let compress                = from_tac_1 "B.compress" B.compress
let set_goals               = from_tac_1 "TM.set_goals" TM.set_goals
let set_smt_goals           = from_tac_1 "TM.set_smt_goals" TM.set_smt_goals
let top_env                 = from_tac_1 "B.top_env" B.top_env
let fresh                   = from_tac_1 "B.fresh" B.fresh
let refine_intro            = from_tac_1 "B.refine_intro" B.refine_intro
let tc                      = from_tac_2 "B.tc" B.tc
let tcc                     = from_tac_2 "B.tcc" B.tcc
let unshelve                = from_tac_1 "B.unshelve" B.unshelve
let unquote                 = fun t -> failwith "Sorry, unquote does not work in compiled tactics"
let norm                    = fun s ->   from_tac_1 "B.norm" B.norm s
let norm_term_env           = fun e s -> from_tac_3 "B.norm_term_env" B.norm_term_env e s
let norm_binding_type       = fun s ->   from_tac_2 "B.norm_binding_type" B.norm_binding_type s
let intro                   = from_tac_1 "B.intro" B.intro
let intros                  = from_tac_1 "B.intros" B.intros
let intro_rec               = from_tac_1 "B.intro_rec" B.intro_rec
let rename_to               = from_tac_2 "B.rename_to" B.rename_to
let revert                  = from_tac_1 "B.revert" B.revert
let var_retype              = from_tac_1 "B.var_retype" B.var_retype
let clear_top               = from_tac_1 "B.clear_top" B.clear_top
let clear                   = from_tac_1 "B.clear" B.clear
let rewrite                 = from_tac_1 "B.rewrite" B.rewrite
let grewrite                = from_tac_2 "B.grewrite" B.grewrite
let t_exact                 = from_tac_3 "B.t_exact" B.t_exact
let t_apply                 = from_tac_4 "B.t_apply" B.t_apply
let t_apply_lemma           = from_tac_3 "B.t_apply_lemma" B.t_apply_lemma
let print                   = from_tac_1 "B.print" B.print
let debugging               = from_tac_1 "B.debugging" B.debugging
let ide                     = from_tac_1 "B.ide" B.ide
let dump                    = from_tac_1 "B.dump" B.dump
let dump_all                = from_tac_2 "B.dump_all" B.dump_all
let dump_uvars_of           = from_tac_2 "B.dump_uvars_of" B.dump_uvars_of
let t_trefl                 = from_tac_1 "B.t_trefl" B.t_trefl
let dup                     = from_tac_1 "B.dup" B.dup
let prune                   = from_tac_1 "B.prune" B.prune
let addns                   = from_tac_1 "B.addns" B.addns
let t_destruct              = from_tac_1 "B.t_destruct" B.t_destruct
let set_options             = from_tac_1 "B.set_options" B.set_options
let uvar_env                = from_tac_2 "B.uvar_env" B.uvar_env
let ghost_uvar_env          = from_tac_2 "B.ghost_uvar_env" B.ghost_uvar_env
let unify_env               = from_tac_3 "B.unify_env" B.unify_env
let unify_guard_env         = from_tac_3 "B.unify_guard_env" B.unify_guard_env
let match_env               = from_tac_3 "B.match_env" B.match_env
let launch_process          = from_tac_3 "B.launch_process" B.launch_process
let fresh_bv_named          = from_tac_1 "B.fresh_bv_named" B.fresh_bv_named
let change                  = from_tac_1 "B.change" B.change
let get_guard_policy        = from_tac_1 "B.get_guard_policy" B.get_guard_policy
let set_guard_policy        = from_tac_1 "B.set_guard_policy" B.set_guard_policy
let lax_on                  = from_tac_1 "B.lax_on" B.lax_on
let tadmit_t                = from_tac_1 "B.tadmit_t" B.tadmit_t
let join                    = from_tac_1 "B.join" B.join
let curms                   = from_tac_1 "B.curms" B.curms
let set_urgency             = from_tac_1 "B.set_urgency" B.set_urgency
let set_dump_on_failure     = from_tac_1 "B.set_dump_on_failure" B.set_dump_on_failure
let t_commute_applied_match = from_tac_1 "B.t_commute_applied_match" B.t_commute_applied_match
let gather_or_solve_explicit_guards_for_resolved_goals = from_tac_1 "B.gather_explicit_guards_for_resolved_goals" B.gather_explicit_guards_for_resolved_goals
let string_to_term          = from_tac_2 "B.string_to_term" B.string_to_term
let push_bv_dsenv           = from_tac_2 "B.push_bv_dsenv" B.push_bv_dsenv
let term_to_string          = from_tac_1 "B.term_to_string" B.term_to_string
let comp_to_string          = from_tac_1 "B.comp_to_string" B.comp_to_string
let term_to_doc             = from_tac_1 "B.term_to_doc" B.term_to_doc
let comp_to_doc             = from_tac_1 "B.comp_to_doc" B.comp_to_doc
let range_to_string         = from_tac_1 "B.range_to_string" B.range_to_string
let term_eq_old             = from_tac_2 "B.term_eq_old" B.term_eq_old

let with_compat_pre_core (n:Prims.int) (f: unit -> 'a __tac) : 'a __tac =
  from_tac_2 "B.with_compat_pre_core" B.with_compat_pre_core n (to_tac_0 (f ()))

let get_vconfig             = from_tac_1 "B.get_vconfig" B.get_vconfig
let set_vconfig             = from_tac_1 "B.set_vconfig" B.set_vconfig
let t_smt_sync              = from_tac_1 "B.t_smt_sync" B.t_smt_sync
let free_uvars              = from_tac_1 "B.free_uvars" B.free_uvars
let all_ext_options         = from_tac_1 "B.all_ext_options" B.all_ext_options
let ext_getv                = from_tac_1 "B.ext_getv" B.ext_getv
let ext_getns               = from_tac_1 "B.ext_getns" B.ext_getns

let alloc x                 = from_tac_1 "B.alloc" B.alloc x
let read  r                 = from_tac_1 "B.read" B.read r
let write r x               = from_tac_2 "B.write" B.write r x

type ('env, 't) prop_validity_token = unit
type ('env, 'sc, 't, 'pats, 'bnds) match_complete_token = unit

let is_non_informative           = from_tac_2 "B.refl_is_non_informative" B.refl_is_non_informative
let check_subtyping              = from_tac_3 "B.refl_check_subtyping" B.refl_check_subtyping
let t_check_equiv                = from_tac_5 "B.t_refl_check_equiv" B.t_refl_check_equiv
let core_compute_term_type       = from_tac_2 "B.refl_core_compute_term_type" B.refl_core_compute_term_type
let core_check_term              = from_tac_4 "B.refl_core_check_term" B.refl_core_check_term
let core_check_term_at_type      = from_tac_3 "B.refl_core_check_term_at_type" B.refl_core_check_term_at_type
let check_match_complete         = from_tac_4 "B.refl_check_match_complete" B.refl_check_match_complete
let tc_term                      = from_tac_2 "B.refl_tc_term" B.refl_tc_term
let universe_of                  = from_tac_2 "B.refl_universe_of" B.refl_universe_of
let check_prop_validity          = from_tac_2 "B.refl_check_prop_validity" B.refl_check_prop_validity
let instantiate_implicits        = from_tac_3 "B.refl_instantiate_implicits" B.refl_instantiate_implicits
let try_unify                    = from_tac_4 "B.refl_try_unify" B.refl_try_unify
let maybe_relate_after_unfolding = from_tac_3 "B.refl_maybe_relate_after_unfolding" B.refl_maybe_relate_after_unfolding
let maybe_unfold_head            = from_tac_2 "B.refl_maybe_unfold_head" B.refl_maybe_unfold_head
let norm_well_typed_term         = from_tac_3 "B.norm_well_typed_term" B.refl_norm_well_typed_term

let push_open_namespace          = from_tac_2 "B.push_open_namespace" B.push_open_namespace
let push_module_abbrev           = from_tac_3 "B.push_module_abbrev" B.push_module_abbrev
let resolve_name                 = from_tac_2 "B.resolve_name" B.resolve_name
let log_issues                   = from_tac_1 "B.log_issues" B.log_issues

(* The handlers need to "embed" their argument. *)
let catch   (t: unit -> 'a __tac): ((exn, 'a) either) __tac = from_tac_1 "TM.catch" TM.catch   (to_tac_0 (t ()))
let recover (t: unit -> 'a __tac): ((exn, 'a) either) __tac = from_tac_1 "TM.recover" TM.recover (to_tac_0 (t ()))

let ctrl_rewrite
    (d : direction)
    (t1 : RT.term -> (bool * ctrl_flag) __tac)
    (t2 : unit -> unit __tac)
  : unit __tac
  = from_tac_3 "ctrl_rewrite" CTRW.ctrl_rewrite d (to_tac_1 t1) (to_tac_0 (t2 ()))

let call_subtac g (t : unit -> unit __tac) u ty =
  let t = to_tac_1 t () in
  from_tac_4 "B.call_subtac" B.call_subtac g t u ty

let call_subtac_tm               = from_tac_4 "B.call_subtac_tm" B.call_subtac_tm
