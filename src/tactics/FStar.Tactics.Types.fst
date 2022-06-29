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
module FStar.Tactics.Types

open FStar open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common

module Env     = FStar.TypeChecker.Env
module O       = FStar.Options
module SS      = FStar.Syntax.Subst
module Cfg     = FStar.TypeChecker.Cfg
module N       = FStar.TypeChecker.Normalize
module Range   = FStar.Compiler.Range
module BU      = FStar.Compiler.Util
module S       = FStar.Syntax.Syntax
module U       = FStar.Syntax.Util

let goal_env g = g.goal_main_env
let goal_witness g =
    FStar.Syntax.Syntax.mk (Tm_uvar (g.goal_ctx_uvar, ([], NoUseRange))) Range.dummyRange
let goal_type g = g.goal_ctx_uvar.ctx_uvar_typ

let goal_with_type_pure g t : goal =
    let c = g.goal_ctx_uvar in
    let c' = {c with ctx_uvar_typ = t} in
    { g with goal_ctx_uvar = c' }

let goal_with_env g env : goal =
    let c = g.goal_ctx_uvar in
    let c' = {c with ctx_uvar_gamma = env.gamma ; ctx_uvar_binders = Env.all_binders env } in
    { g with goal_main_env=env; goal_ctx_uvar = c' }

(* Unsafe? *)
let goal_of_ctx_uvar (g:goal) (ctx_u : ctx_uvar) : goal =
    { g with goal_ctx_uvar = ctx_u }

let mk_goal env u o b l = {
    goal_main_env=env;
    goal_ctx_uvar=u;
    opts=o;
    is_guard=b;
    label=l;
}

let goal_of_goal_ty env typ : goal * guard_t =
    let u, ctx_uvars, g_u =
        Env.new_implicit_var_aux "proofstate_of_goal_ty" typ.pos env typ Allow_untyped None
    in
    let ctx_uvar, _ = List.hd ctx_uvars in
    let g = mk_goal env ctx_uvar (FStar.Options.peek()) false "" in
    g, g_u

let goal_of_implicit env (i:Env.implicit) : goal =
  mk_goal ({env with gamma=i.imp_uvar.ctx_uvar_gamma}) i.imp_uvar (FStar.Options.peek()) false i.imp_reason

let rename_binders subst bs =
    bs |> List.map (function b ->
        let x = b.binder_bv in
        let y = SS.subst subst (S.bv_to_name x) in
        match (SS.compress y).n with
        | Tm_name y ->
            // We don't want to change the type
            { b with binder_bv = { b.binder_bv with sort = SS.subst subst x.sort } }
        | _ -> failwith "Not a renaming")

(* This is only for show: this goal becomes ill-formed since it does
 * not satisfy the invariant on gamma *)
let subst_goal subst goal =
    let g = goal.goal_ctx_uvar in
    let ctx_uvar = {
        g with ctx_uvar_gamma=Env.rename_gamma subst g.ctx_uvar_gamma;
               ctx_uvar_binders=rename_binders subst g.ctx_uvar_binders;
               ctx_uvar_typ=SS.subst subst g.ctx_uvar_typ;
    } in
    { goal with goal_ctx_uvar = ctx_uvar }

let subst_proof_state subst ps =
    if O.tactic_raw_binders ()
    then ps
    else { ps with goals = List.map (subst_goal subst) ps.goals
    }

let decr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth - 1 }

let incr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth + 1 }

let set_ps_psc psc ps = { ps with psc = psc }

let tracepoint_with_psc psc ps : bool =
    if O.tactic_trace () || (ps.depth <= O.tactic_trace_d ()) then begin
        let ps = set_ps_psc psc ps in
        let subst = Cfg.psc_subst ps.psc in
        ps.__dump (subst_proof_state subst ps) "TRACE"
    end;
    true

let tracepoint ps : bool =
    if O.tactic_trace () || (ps.depth <= O.tactic_trace_d ()) then begin
        let subst = Cfg.psc_subst ps.psc in
        ps.__dump (subst_proof_state subst ps) "TRACE"
    end;
    true

let set_proofstate_range ps r =
    { ps with entry_range = Range.set_def_range ps.entry_range (Range.def_range r) }

let goals_of     ps : list goal = ps.goals
let smt_goals_of ps : list goal = ps.smt_goals

let is_guard g = g.is_guard

let get_label g = g.label
let set_label l g = { g with label = l }

let check_goal_solved' goal =
  match FStar.Syntax.Unionfind.find goal.goal_ctx_uvar.ctx_uvar_head with
  | Some t -> Some t
  | None   -> None

let check_goal_solved goal =
  Option.isSome (check_goal_solved' goal)

let get_phi (g:goal) : option term =
    U.un_squash (N.unfold_whnf (goal_env g) (goal_type g))

let is_irrelevant (g:goal) : bool =
    Option.isSome (get_phi g)
