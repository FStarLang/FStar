open Fstarcompiler
open Prims
open FStar_Pervasives_Native
open FStar_Pervasives
open FStarC_Tactics_Result
open FStarC_Tactics_Types

module B        = FStarC_Tactics_V1_Basic
module TM       = FStarC_Tactics_Monad
module CTRW     = FStarC_Tactics_CtrlRewrite

type 'a __tac = 'a TM.tac

let to_tac_0 (t: 'a __tac): 'a TM.tac =
  t

let to_tac_1 (t: 'b -> 'a __tac): 'b -> 'a TM.tac =
  t

let from_tac_1 (t: 'a -> 'b TM.tac): 'a  -> 'b __tac =
  t

let from_tac_2 (t: 'a -> 'b -> 'c TM.tac): 'a  -> 'b -> 'c __tac =
  t

let from_tac_3 (t: 'a -> 'b -> 'c -> 'd TM.tac): 'a  -> 'b -> 'c -> 'd __tac =
  t

let from_tac_4 (t: 'a -> 'b -> 'c -> 'd -> 'e TM.tac): 'a  -> 'b -> 'c -> 'd -> 'e __tac =
  t

let get () : proofstate __tac = TM.get

(* Pointing to the internal primitives *)
let set_goals               = from_tac_1 TM.set_goals
let set_smt_goals           = from_tac_1 TM.set_smt_goals
let top_env                 = from_tac_1 B.top_env
let fresh                   = from_tac_1 B.fresh
let refine_intro            = from_tac_1 B.refine_intro
let tc                      = from_tac_2 B.tc
let tcc                     = from_tac_2 B.tcc
let unshelve                = from_tac_1 B.unshelve
let unquote                 = fun t -> failwith "Sorry, unquote does not work in compiled tactics"
let norm                    = fun s ->   from_tac_1 B.norm s
let norm_term_env           = fun e s -> from_tac_3 B.norm_term_env e s
let norm_binder_type        = fun s ->   from_tac_2 B.norm_binder_type s
let intro                   = from_tac_1 B.intro
let intro_rec               = from_tac_1 B.intro_rec
let rename_to               = from_tac_2 B.rename_to
let revert                  = from_tac_1 B.revert
let binder_retype           = from_tac_1 B.binder_retype
let clear_top               = from_tac_1 B.clear_top
let clear                   = from_tac_1 B.clear
let rewrite                 = from_tac_1 B.rewrite
let t_exact                 = from_tac_3 B.t_exact
let t_apply                 = from_tac_4 B.t_apply
let t_apply_lemma           = from_tac_3 B.t_apply_lemma
let print                   = from_tac_1 B.print
let debugging               = from_tac_1 B.debugging
let dump                    = from_tac_1 B.dump
let dump_all                = from_tac_2 B.dump_all
let dump_uvars_of           = from_tac_2 B.dump_uvars_of
let t_trefl                 = from_tac_1 B.t_trefl
let dup                     = from_tac_1 B.dup
let prune                   = from_tac_1 B.prune
let addns                   = from_tac_1 B.addns
let t_destruct              = from_tac_1 B.t_destruct
let set_options             = from_tac_1 B.set_options
let uvar_env                = from_tac_2 B.uvar_env
let ghost_uvar_env          = from_tac_2 B.ghost_uvar_env
let unify_env               = from_tac_3 B.unify_env
let unify_guard_env         = from_tac_3 B.unify_guard_env
let match_env               = from_tac_3 B.match_env
let launch_process          = from_tac_3 B.launch_process
let fresh_bv_named          = from_tac_1 B.fresh_bv_named
let change                  = from_tac_1 B.change
let get_guard_policy        = from_tac_1 B.get_guard_policy
let set_guard_policy        = from_tac_1 B.set_guard_policy
let lax_on                  = from_tac_1 B.lax_on
let tadmit_t                = from_tac_1 B.tadmit_t
let join                    = from_tac_1 B.join
let inspect                 = from_tac_1 B.inspect
let pack                    = from_tac_1 B.pack
let pack_curried            = from_tac_1 B.pack_curried
let curms                   = from_tac_1 B.curms
let set_urgency             = from_tac_1 B.set_urgency
let t_commute_applied_match = from_tac_1 B.t_commute_applied_match
let gather_or_solve_explicit_guards_for_resolved_goals = from_tac_1 B.gather_explicit_guards_for_resolved_goals
let string_to_term          = from_tac_2 B.string_to_term
let push_bv_dsenv           = from_tac_2 B.push_bv_dsenv
let term_to_string          = from_tac_1 B.term_to_string
let comp_to_string          = from_tac_1 B.comp_to_string
let range_to_string         = from_tac_1 B.range_to_string

let with_compat_pre_core (n:Prims.int) (f: unit -> 'a __tac) : 'a __tac =
  from_tac_2 B.with_compat_pre_core n (to_tac_0 (f ()))

let get_vconfig             = from_tac_1 B.get_vconfig
let set_vconfig             = from_tac_1 B.set_vconfig
let t_smt_sync              = from_tac_1 B.t_smt_sync
let free_uvars              = from_tac_1 B.free_uvars

(* The handlers need to "embed" their argument. *)
let catch   (t: unit -> 'a __tac): ((exn, 'a) either) __tac = from_tac_1 TM.catch   (to_tac_0 (t ()))
let raise_core = from_tac_1 TM.traise

let ctrl_rewrite
    (d : direction)
    (t1 : FStarC_Syntax_Syntax.term -> (bool * ctrl_flag) __tac)
    (t2 : unit -> unit __tac)
  : unit __tac
  = from_tac_3 CTRW.ctrl_rewrite d (to_tac_1 t1) (to_tac_0 (t2 ()))
