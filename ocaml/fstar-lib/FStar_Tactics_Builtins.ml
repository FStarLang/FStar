open Prims
open FStar_Pervasives_Native
open FStar_Pervasives
open FStar_Tactics_Result
open FStar_Tactics_Types
open FStar_Tactics_Effect

module N    = FStar_TypeChecker_Normalize
module E    = FStar_Tactics_Effect
module B    = FStar_Tactics_Basic
module TM   = FStar_Tactics_Monad
module CTRW = FStar_Tactics_CtrlRewrite
module RT   = FStar_Reflection_Types
module RD   = FStar_Reflection_Data
module EMB  = FStar_Syntax_Embeddings
module NBET = FStar_TypeChecker_NBETerm

type 'a __tac = ('a, unit) E.tac_repr

let interpret_tac (t: 'a TM.tac) (ps: proofstate): 'a __result =
  TM.run t ps

let uninterpret_tac (t: 'a __tac) (ps: proofstate): 'a __result =
  t ps

let tr1 = function
          | Simpl          -> EMB.Simpl
          | Weak           -> EMB.Weak
          | HNF            -> EMB.HNF
          | Primops        -> EMB.Primops
          | Delta          -> EMB.Delta
          | Zeta           -> EMB.Zeta
          | ZetaFull       -> EMB.ZetaFull
          | Iota           -> EMB.Iota
          | Unascribe      -> EMB.Unascribe
          | NBE            -> EMB.NBE
          | Unmeta         -> EMB.Unmeta
          | Reify          -> EMB.Reify
          | UnfoldOnly  ss -> EMB.UnfoldOnly ss
          | UnfoldFully ss -> EMB.UnfoldFully ss
          | UnfoldAttr  ss -> EMB.UnfoldAttr  ss
          | UnfoldQual  ss -> EMB.UnfoldQual  ss
          | UnfoldNamespace  ss -> EMB.UnfoldNamespace  ss
let rt1 = function
          | EMB.Simpl          -> Simpl
          | EMB.Weak           -> Weak
          | EMB.HNF            -> HNF
          | EMB.Primops        -> Primops
          | EMB.Delta          -> Delta
          | EMB.Zeta           -> Zeta
          | EMB.ZetaFull       -> ZetaFull
          | EMB.Iota           -> Iota
          | EMB.Unascribe      -> Unascribe
          | EMB.NBE            -> NBE
          | EMB.Unmeta         -> Unmeta
          | EMB.Reify          -> Reify
          | EMB.UnfoldOnly  ss -> UnfoldOnly ss
          | EMB.UnfoldFully ss -> UnfoldFully ss
          | EMB.UnfoldAttr  ss -> UnfoldAttr  ss
          | EMB.UnfoldQual  ss -> UnfoldQual  ss
          | EMB.UnfoldNamespace  ss -> UnfoldNamespace  ss

(* the one plugins actually use *)
let e_norm_step' : norm_step EMB.embedding =
    EMB.embed_as EMB.e_norm_step rt1 tr1 None

let e_norm_step_nbe' : norm_step NBET.embedding =
    NBET.embed_as NBET.e_norm_step rt1 tr1 None

let tr_repr_steps =
    List.map tr1

let to_tac_0 (t: 'a __tac): 'a TM.tac =
  (fun (ps: proofstate) ->
    uninterpret_tac t ps) |> TM.mk_tac

let to_tac_1 (t: 'b -> 'a __tac): 'b -> 'a TM.tac = fun x ->
  (fun (ps: proofstate) ->
    uninterpret_tac (t x) ps) |> TM.mk_tac

let from_tac_1 (t: 'a -> 'b TM.tac): 'a  -> 'b __tac =
  fun (x: 'a) ->
    fun (ps: proofstate) ->
      let m = t x in
      interpret_tac m ps

let from_tac_2 (t: 'a -> 'b -> 'c TM.tac): 'a  -> 'b -> 'c __tac =
  fun (x: 'a) ->
    fun (y: 'b) ->
      fun (ps: proofstate) ->
        let m = t x y in
        interpret_tac m ps

let from_tac_3 (t: 'a -> 'b -> 'c -> 'd TM.tac): 'a  -> 'b -> 'c -> 'd __tac =
  fun (x: 'a) ->
    fun (y: 'b) ->
      fun (z: 'c) ->
        fun (ps: proofstate) ->
          let m = t x y z in
          interpret_tac m ps

let from_tac_4 (t: 'a -> 'b -> 'c -> 'd -> 'e TM.tac): 'a  -> 'b -> 'c -> 'd -> 'e __tac =
  fun (x: 'a) ->
  fun (y: 'b) ->
  fun (z: 'c) ->
  fun (w: 'd) ->
  fun (ps: proofstate) ->
  let m = t x y z w in
  interpret_tac m ps

let unseal x = E.tac_return x

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
let norm                    = fun s ->   from_tac_1 B.norm (tr_repr_steps s) (* TODO: somehow avoid translating steps? *)
let norm_term_env           = fun e s -> from_tac_3 B.norm_term_env e (tr_repr_steps s)
let norm_binder_type        = fun s ->   from_tac_2 B.norm_binder_type (tr_repr_steps s)
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
let term_eq_old             = from_tac_2 B.term_eq_old

let with_compat_pre_core (n:Prims.int) (f: unit -> 'a __tac) : 'a __tac =
  from_tac_2 B.with_compat_pre_core n (to_tac_0 (f ()))

let get_vconfig             = from_tac_1 B.get_vconfig
let set_vconfig             = from_tac_1 B.set_vconfig
let t_smt_sync              = from_tac_1 B.t_smt_sync
let free_uvars              = from_tac_1 B.free_uvars


type ('env, 't0, 't1) subtyping_token = unit
type ('env, 't0, 't1) equiv_token = unit
type ('env, 'e, 't) typing_token = unit
type ('env, 't) prop_validity_token = unit

let check_subtyping              = from_tac_3 B.refl_check_subtyping
let check_equiv                  = from_tac_3 B.refl_check_equiv
let core_check_term              = from_tac_3 B.refl_core_check_term
let tc_term                      = from_tac_3 B.refl_tc_term
let universe_of                  = from_tac_2 B.refl_universe_of
let check_prop_validity          = from_tac_2 B.refl_check_prop_validity
let instantiate_implicits        = from_tac_2 B.refl_instantiate_implicits
let maybe_relate_after_unfolding = from_tac_3 B.refl_maybe_relate_after_unfolding
let maybe_unfold_head            = from_tac_2 B.refl_maybe_unfold_head

(* The handlers need to "embed" their argument. *)
let catch   (t: unit -> 'a __tac): ((exn, 'a) either) __tac = from_tac_1 TM.catch   (to_tac_0 (t ()))
let recover (t: unit -> 'a __tac): ((exn, 'a) either) __tac = from_tac_1 TM.recover (to_tac_0 (t ()))

let ctrl_rewrite
    (d : direction)
    (t1 : RT.term -> (bool * ctrl_flag) __tac)
    (t2 : unit -> unit __tac)
  : unit __tac
  = from_tac_3 CTRW.ctrl_rewrite d (to_tac_1 t1) (to_tac_0 (t2 ()))
