(*open FStar_Tactics_Effect*)
open FStar_Tactics_Basic
open FStar_Syntax_Syntax
open FStar_Range

open FStar_Tactics
open FStar_Tactics_Logic


module E = FStar_Tactics_Effect
module Core = FStar_Tactics_Basic
module BU = FStar_Util

let r = dummyRange

type itac = proofstate -> args -> term option
type native_primitive_step =
    { name: FStar_Ident.lid;
      arity: Prims.int;
      strong_reduction_ok: bool;
      tactic: itac}

let compiled_tactics: native_primitive_step list ref = ref []

let list_all () = !compiled_tactics

let is_native_tactic lid =
    BU.is_some (BU.try_find (fun x -> FStar_Ident.lid_equals lid x.name) !compiled_tactics)

let register_tactic (s: string) (arity: int) (t: itac)=
    let step =
        { name=FStar_Ident.lid_of_str s;
          arity = Z.of_int arity;
          strong_reduction_ok=false;
          tactic=t } in
    compiled_tactics := step :: !compiled_tactics;
    BU.print1 "Registered tactic %s\n" s

(*let interpret_goal (g: FStar_Tactics_Effect.goal): Core.goal =
    {context=(fst g); witness=None; goal_ty=(snd g)}*)

(*let interpret_state (s: FStar_Tactics_Effect.state): FStar_Tactics_Embedding.state =
    (List.map interpret_goal (fst s), List.map interpret_goal (snd s))*)

(*let state_to_proofstate (s: FStar_Tactics_Effect.state): proofstate =
    match (fst s) with
    | hd::tl ->
        {
            main_context=fst hd;
            main_goal=interpret_goal hd;
            all_implicits=[];
            goals=List.map interpret_goal (fst s);
            smt_goals=List.map interpret_goal (snd s);
            transaction=FStar_Unionfind.new_transaction()
        }*)

(*let unembed_res (ps:proofstate) (res:term) (unembed_a:term -> 'a): 'a E.__result =
    match (FStar_Tactics_Embedding.unembed_result ps res unembed_a) with
    | BU.Inl (u, state) -> Success(u, uninterpret_state state)
    | BU.Inr (s, state) -> Failed(s, uninterpret_state state)*)

(*let interpret_tactic (ps: proofstate) (t: proofstate -> 'b E.__result) =
    (*let (ps_goals: goals) = List.map (fun s -> (s.context, s.goal_ty)) ps.goals in*)
    (*let (ps_smt_goals: goals) = List.map (fun s -> (s.context, s.goal_ty)) ps.smt_goals in*)
    (*let res = t (ps_goals, ps_smt_goals) in*)
    let res = t ps in
    match res with
    | Success (a, s2) -> Success (a, s2)
    | Failed (str, s2) -> Failed (str, s2)*)

(*let interpret_tactic (ps: proofstate) (t: state -> 'b __result) =
    let (ps_goals: goals) = List.map (fun s -> (s.context, s.goal_ty)) ps.goals in
    let (ps_smt_goals: goals) = List.map (fun s -> (s.context, s.goal_ty)) ps.smt_goals in
    let res = t (ps_goals, ps_smt_goals) in
    match res with
    | Success (a, s2) -> Success (a, {ps with goals=(List.map interpret_goal (fst s2)); smt_goals=(List.map interpret_goal (fst s2))})
    | Failed (str, s2) -> Failed (str, {ps with goals=(List.map interpret_goal (fst s2)); smt_goals=(List.map interpret_goal (fst s2))})*)

(*let from_tactic_0 (t: 'b E.tactic): ('b tac) =
    let rtac =
        (mk_tac (fun (ps: proofstate) ->
            let (m2: proofstate -> 'b E.__result) = t () in
            interpret_tactic ps m2
        )) in rtac

let from_tactic_1 (t: 'a -> 'b E.tactic): ('a -> 'b tac) =
    let rtac =
        (fun (x: 'a) ->
            mk_tac (fun (ps: proofstate) ->
                let m = t x in
                let (m2: proofstate -> 'b E.__result) = m () in
                interpret_tactic ps m2
        )) in rtac

let from_tactic_2 (t: 'a -> 'b -> 'c E.tactic): ('a -> 'b -> 'c tac) =
    let rtac =
        (fun (x: 'a) ->
            (fun (y: 'b) ->
                mk_tac (fun (ps: proofstate) ->
                    let m = t x y in
                    let (m2: proofstate -> 'c E.__result) = m () in
                    interpret_tactic ps m2
        ))) in rtac

let from_tac_0 (t: 'b tac): ('b E.tactic) =
    failwith "wip"*)