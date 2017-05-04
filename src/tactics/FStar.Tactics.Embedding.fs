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
module Env = FStar.TypeChecker.Env
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util
module N = FStar.TypeChecker.Normalize
open FStar.Tactics.Basic
module Core = FStar.Tactics.Basic

open FStar.Reflection.Basic
open FStar.Reflection.Data

type name = bv

let fstar_tactics_lid s = Ident.lid_of_path (["FStar"; "Tactics"]@[s]) Range.dummyRange
let by_tactic_lid = fstar_tactics_lid "by_tactic"
let lid_as_tm l = S.lid_as_fv l Delta_constant None |> S.fv_to_tm
let mk_tactic_lid_as_term (s:string) = lid_as_tm (fstar_tactics_lid s)
let fstar_tactics_goal   = mk_tactic_lid_as_term "goal"
let fstar_tactics_goals  = mk_tactic_lid_as_term "goals"
let fstar_tactics_term_view = mk_tactic_lid_as_term "term_view"

let lid_as_data_tm l = S.fv_to_tm (S.lid_as_fv l Delta_constant (Some Data_ctor))
let fstar_tactics_lid_as_data_tm s = lid_as_data_tm (fstar_tactics_lid s)

let fstar_tactics_Failed = fstar_tactics_lid_as_data_tm "Failed"
let fstar_tactics_Success= fstar_tactics_lid_as_data_tm "Success"

let embed_env (env:Env.env) : term =
    protect_embedded_term
        fstar_refl_env
        (embed_list embed_binder fstar_refl_binder (Env.all_binders env))

let unembed_env (env:Env.env) (protected_embedded_env:term) : Env.env =
    let embedded_env = un_protect_embedded_term protected_embedded_env in
    let binders = unembed_list unembed_binder embedded_env in
    // TODO: Why try????
    FStar.List.fold_left (fun env b ->
        match Env.try_lookup_bv env (fst b) with
        | None -> Env.push_binders env [b]
        | _ -> env) env binders

let embed_goal (g:goal) : term =
    embed_pair (g.context, g.goal_ty)
                embed_env fstar_refl_env
                embed_term fstar_refl_term

let unembed_goal (env:Env.env) (t:term) : goal =
    let env, goal_ty = unembed_pair t (unembed_env env) unembed_term in
    {
      context = env;
      goal_ty = goal_ty;
      witness = None //TODO: sort this out for proof-relevant goals
    }

let embed_goals (l:list<goal>) : term = embed_list embed_goal fstar_tactics_goal l
let unembed_goals (env:Env.env) (egs:term) : list<goal> = unembed_list (unembed_goal env) egs

type state = list<goal> * list<goal>

let embed_state (s:state) : term =
    embed_pair s embed_goals fstar_tactics_goals embed_goals fstar_tactics_goals

let unembed_state (env:Env.env) (s:term) : state =
    let s = U.unascribe s in
    unembed_pair s (unembed_goals env) (unembed_goals env)

let embed_result (res:result<'a>) (embed_a:'a -> term) (t_a:typ) : term =
    match res with
    | Failed (msg, ps) ->
      S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Failed [U_zero])
                  [S.iarg t_a;
                   S.as_arg (embed_string msg);
                   S.as_arg (embed_state (ps.goals, ps.smt_goals))]
                  None
                  Range.dummyRange
    | Success (a, ps) ->
      S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Success [U_zero])
                  [S.iarg t_a;
                   S.as_arg (embed_a a);
                   S.as_arg (embed_state (ps.goals, ps.smt_goals))]
                  None
                  Range.dummyRange

let unembed_result (env:Env.env) (res:term) (unembed_a:term -> 'a) : either<('a * state), (string * state)> =
    let res = U.unascribe res in
    let hd, args = U.head_and_args res in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [_t; (a, _); (embedded_state, _)]
        when S.fv_eq_lid fv (fstar_tactics_lid "Success") ->
      Inl (unembed_a a, unembed_state env embedded_state)

    | Tm_fvar fv, [_t; (embedded_string, _); (embedded_state, _)]
        when S.fv_eq_lid fv (fstar_tactics_lid "Failed") ->
      Inr (unembed_string embedded_string, unembed_state env embedded_state)

    | _ -> failwith (BU.format1 "Not an embedded result: %s" (Print.term_to_string res))
