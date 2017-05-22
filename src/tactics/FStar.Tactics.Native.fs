#light "off"
module FStar.Tactics.Native

open FStar.Tactics.Basic
open FStar.Tactics.Interpreter
module Core = FStar.Tactics.Basic

// open FStar.Syntax.Syntax
// open FStar.TypeChecker.Env

module BU = FStar.Util

(* super ugly hack: copying these over from the extracted FStar.Tactics.fst
   because inside the compiler the default efect is ML, breaking FStar.Tactics *)
type ps_result = FStar.Tactics.Basic.result
type env = FStar.TypeChecker.Env.env
type term = FStar.Syntax.Syntax.term
type goal = env * term
type goals = list<goal>
type state = goals * goals
type __result<'a> =
  | Success_r of 'a * state
  | Failed_r of string * state
// should be type _dm4f_TAC_repr<'a, 'b>
type _dm4f_TAC_repr<'a> = state -> __result<'a>
type tactic<'a> = unit -> _dm4f_TAC_repr<'a>

let register_tactic_dumb (s: string) =
    BU.print1 "Registered tactic %s\n" s

let register_tactic (s: string) (f: 'a) =
    BU.print1 "Registered tactic %s\n" s

let find_tactic (s: string) = ()

let interpret_goal (g: goal): Core.goal =
    {context=(fst g); witness=None; goal_ty=(snd g)}

let from_tactic_1 (t: 'a -> tactic<'b>): ('a -> tac<'b>) =
    let rtac =
        (fun (x: 'a) ->
            (fun (ps: proofstate) ->
                let m = t x in
                let m2 = m () in //m2: state -> __result<'a>
                let (ps_goals: goals) = List.map (fun s -> (s.context, s.goal_ty)) ps.goals in
                let (ps_smt_goals: goals) = List.map (fun s -> (s.context, s.goal_ty)) ps.smt_goals in
                let res = m2 (ps_goals, ps_smt_goals) in
                match res with
                | Success_r (a, s2) -> Success (a, {ps with goals=(List.map interpret_goal (fst s2)); smt_goals=(List.map interpret_goal (fst s2))})
                | Failed_r (str, s2) -> Failed (str, {ps with goals=(List.map interpret_goal (fst s2)); smt_goals=(List.map interpret_goal (fst s2))})
                )) in
    rtac