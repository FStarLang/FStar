#light "off"
module FStar.Tactics.Embedding
open FStar
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module SC = FStar.Syntax.Const
module Env = FStar.TypeChecker.Env
module BU = FStar.Util
module C = FStar.Const
module U = FStar.Syntax.Util
module Rel = FStar.TypeChecker.Rel
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util
module N = FStar.TypeChecker.Normalize
open FStar.Tactics.Basic
module Core = FStar.Tactics.Basic

open FStar.Reflection.Basic
open FStar.Reflection.Data

type name = bv

let fstar_tactics_lid' s = SC.fstar_tactics_lid' s
let fstar_tactics_lid s = SC.fstar_tactics_lid s
let by_tactic_lid = SC.by_tactic_lid
let lid_as_tm l = S.lid_as_fv l Delta_constant None |> S.fv_to_tm
let mk_tactic_lid_as_term (s:string) = lid_as_tm (fstar_tactics_lid' ["Effect"; s])
let fstar_tactics_goal   = mk_tactic_lid_as_term "goal"
let fstar_tactics_goals  = mk_tactic_lid_as_term "goals"

let lid_as_data_tm l = S.fv_to_tm (S.lid_as_fv l Delta_constant (Some Data_ctor))
let fstar_tactics_lid_as_data_tm s = lid_as_data_tm (fstar_tactics_lid' ["Effect";s])

let fstar_tactics_Failed = fstar_tactics_lid_as_data_tm "Failed"
let fstar_tactics_Success= fstar_tactics_lid_as_data_tm "Success"

let t_bool = FStar.TypeChecker.Common.t_bool
let t_string = FStar.TypeChecker.Common.t_string

let fstar_tac_prefix_typ = S.mk_Tm_app (S.mk_Tm_uinst (lid_as_tm SC.list_lid) [U_zero])
                                       [S.as_arg t_string]
                                       None
                                       Range.dummyRange

let pair_typ t s = S.mk_Tm_app (S.mk_Tm_uinst (lid_as_tm lid_tuple2) [U_zero;U_zero])
                                      [S.as_arg t;
                                       S.as_arg s]
                                      None
                                      Range.dummyRange

let fstar_tac_nselt_typ = pair_typ fstar_tac_prefix_typ t_bool
let fstar_tac_ns_typ = pair_typ fstar_tac_nselt_typ t_bool

// TODO: for now, we just embed the head of the list. Tactics cannot
// push/pop proof namespaces
let embed_proof_namespace (ps:proofstate) (ns:Env.proof_namespace) : term =
    let embed_prefix prf = embed_list embed_string t_string prf in
    let embed_elt e = embed_pair embed_prefix fstar_tac_prefix_typ embed_bool t_bool e in
    embed_list embed_elt fstar_tac_nselt_typ (List.hd ns)

let unembed_proof_namespace (ps:proofstate) (t:term) : Env.proof_namespace =
    let orig_ns = Env.get_proof_ns ps.main_context in
    let hd = unembed_list (unembed_pair (unembed_list unembed_string) unembed_bool) t in
    hd::orig_ns

// Unsure we need to thunk these, they are normal forms already.
// They also cannot be `eliminated` because the abstract types we give them.
let embed_env (ps:proofstate) (env:Env.env) : term =
    protect_embedded_term
        fstar_refl_env
        (embed_pair
            (embed_list embed_binder fstar_refl_binder)
            fstar_refl_binders
            (embed_proof_namespace ps)
            fstar_tac_ns_typ
            (Env.all_binders env, Env.get_proof_ns env))

let unembed_env (ps:proofstate) (protected_embedded_env:term) : Env.env =
    let embedded_env = un_protect_embedded_term protected_embedded_env in
    let binders, ns = unembed_pair (unembed_list unembed_binder) (unembed_proof_namespace ps) embedded_env in
    let env = ps.main_context in
    let env = Env.set_proof_ns ns env in
    // TODO: This needs to "try" because of `visit`. Try to remove this behaviour.
    let env = FStar.List.fold_left (fun env b ->
                    match Env.try_lookup_bv env (fst b) with
                    | None -> Env.push_binders env [b]
                    | _ -> env) env binders in
    env

let embed_witness (ps:proofstate) w =
    embed_option embed_term fstar_refl_term w

let unembed_witness (ps:proofstate) t =
    unembed_option unembed_term t

let embed_goal (ps:proofstate) (g:goal) : term =
    embed_pair
        (embed_pair (embed_env ps) fstar_refl_env
                     embed_term fstar_refl_term)
        (pair_typ fstar_refl_env fstar_refl_term)
        (embed_witness ps)
        fstar_refl_term
               ((g.context, g.goal_ty), g.witness)

let unembed_goal (ps:proofstate) (t:term) : goal =
    let (env, goal_ty), witness = unembed_pair (unembed_pair (unembed_env ps) unembed_term) (unembed_witness ps) t in
    {
      context = env;
      goal_ty = goal_ty;
      witness = witness
    }

let embed_goals (ps:proofstate) (l:list<goal>) : term =
    embed_list (embed_goal ps) fstar_tactics_goal l

let unembed_goals (ps:proofstate) (egs:term) : list<goal> =
    unembed_list (unembed_goal ps) egs

type state = list<goal> * list<goal>

let embed_state (ps:proofstate) (s:state) : term =
    embed_pair (embed_goals ps) fstar_tactics_goals (embed_goals ps) fstar_tactics_goals s

let unembed_state (ps:proofstate) (s:term) : state =
    let s = U.unascribe s in
    unembed_pair (unembed_goals ps) (unembed_goals ps) s

let embed_result (ps:proofstate) (res:result<'a>) (embed_a:'a -> term) (t_a:typ) : term =
    match res with
    | Failed (msg, ps) ->
      S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Failed [U_zero])
                  [S.iarg t_a;
                   S.as_arg (embed_string msg);
                   S.as_arg (embed_state ps (ps.goals, ps.smt_goals))]
                  None
                  Range.dummyRange
    | Success (a, ps) ->
      S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Success [U_zero])
                  [S.iarg t_a;
                   S.as_arg (embed_a a);
                   S.as_arg (embed_state ps (ps.goals, ps.smt_goals))]
                  None
                  Range.dummyRange

let unembed_result (ps:proofstate) (res:term) (unembed_a:term -> 'a) : either<('a * state), (string * state)> =
    let res = U.unascribe res in
    let hd, args = U.head_and_args res in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [_t; (a, _); (embedded_state, _)]
        when S.fv_eq_lid fv (fstar_tactics_lid' ["Effect";"Success"]) ->
      Inl (unembed_a a, unembed_state ps embedded_state)

    | Tm_fvar fv, [_t; (embedded_string, _); (embedded_state, _)]
        when S.fv_eq_lid fv (fstar_tactics_lid' ["Effect";"Failed"]) ->
      Inr (unembed_string embedded_string, unembed_state ps embedded_state)

    | _ -> failwith (BU.format1 "Not an embedded result: %s" (Print.term_to_string res))
