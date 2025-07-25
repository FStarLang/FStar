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
module FStarC.Tactics.Types

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common

module Env     = FStarC.TypeChecker.Env
module O       = FStarC.Options
module Range   = FStarC.Range
module U       = FStarC.Syntax.Util

instance showable_guard_policy : showable guard_policy = {
  show = (function | Goal -> "Goal"
                   | SMT -> "SMT"
                   | SMTSync -> "SMTSync"
                   | Force -> "Force"
                   | ForceSMT -> "ForceSMT"
                   | Drop -> "Drop");
}

instance pretty_guard_policy : pretty guard_policy = pretty_from_showable

let goal_env g = g.goal_main_env
let goal_range g = g.goal_main_env.range
let goal_witness g =
    FStarC.Syntax.Syntax.mk (Tm_uvar (g.goal_ctx_uvar, ([], NoUseRange))) Range.dummyRange
let goal_type g = U.ctx_uvar_typ g.goal_ctx_uvar
let goal_opts g = g.opts

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

let goal_of_goal_ty env typ : goal & guard_t =
  let u, (ctx_uvar, _) , g_u =
    Env.new_implicit_var_aux "proofstate_of_goal_ty" typ.pos env typ Strict None false
  in
  let g = mk_goal env ctx_uvar (FStarC.Options.peek()) false "" in
  g, g_u

let goal_of_implicit env (i:Env.implicit) : goal =
  mk_goal ({env with gamma=i.imp_uvar.ctx_uvar_gamma}) i.imp_uvar (FStarC.Options.peek()) false i.imp_reason

let decr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth - 1 }

let incr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth + 1 }

let set_ps_psc psc ps = { ps with psc = psc }

let tracepoint_with_psc psc ps : bool =
    if O.tactic_trace () || (ps.depth <= O.tactic_trace_d ()) then begin
        let ps = set_ps_psc psc ps in
        ps.__dump ps "TRACE"
    end;
    true

let tracepoint ps : bool =
    if O.tactic_trace () || (ps.depth <= O.tactic_trace_d ()) then begin
        ps.__dump ps "TRACE"
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
  match FStarC.Syntax.Unionfind.find goal.goal_ctx_uvar.ctx_uvar_head with
  | Some t -> Some t
  | None   -> None

let check_goal_solved goal =
  Some? (check_goal_solved' goal)
