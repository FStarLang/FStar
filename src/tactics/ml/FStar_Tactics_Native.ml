open FStar_Tactics_Types
open FStar_Tactics
open FStar_Tactics_Basic
open FStar_Tactics_Interpreter

open FStar_Syntax_Syntax
module Core = FStar_Tactics_Basic
module S = FStar_Syntax_Syntax
module BU = FStar_Util

type itac = proofstate -> args -> term option

let n: itac list = []
let compiled_tactics = BU.mk_ref n

let register_tactic (s: string) (t: itac) =
    (*compiled_tactics := (t::!compiled_tactics);*)
    BU.print1 "Registered tactic %s\n" s

let interpret_goal (g: FStar_Tactics.goal): Core.goal =
    {context=(fst g); witness=None; goal_ty=(snd g)}

let from_tactic_1 (t: 'a -> 'b tactic): ('a -> 'b tac) =
    let rtac =
        (fun (x: 'a) ->
            mk_tac (fun (ps: proofstate) ->
                let m = t x in
                let (m2: state -> 'b __result) = m () in
                let (ps_goals: goals) = List.map (fun s -> (s.context, s.goal_ty)) ps.goals in
                let (ps_smt_goals: goals) = List.map (fun s -> (s.context, s.goal_ty)) ps.smt_goals in
                let res = m2 (ps_goals, ps_smt_goals) in
                match res with
                | Success (a, s2) -> Success (a, {ps with goals=(List.map interpret_goal (fst s2)); smt_goals=(List.map interpret_goal (fst s2))})
                | Failed (str, s2) -> Failed (str, {ps with goals=(List.map interpret_goal (fst s2)); smt_goals=(List.map interpret_goal (fst s2))})
                )) in
    rtac