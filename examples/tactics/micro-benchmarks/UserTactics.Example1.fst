module UserTactics.Example1 
open FStar.Tactics

#set-options "--lax"
(* -------------------------------------------------------------------------------- *)
let cur_goal () : Tac goal = 
  let goals = TAC?.get () in 
  match fst goals with 
  | [] -> fail #goal "No more goals"
  | hd::_ -> hd

let destruct_equality_implication (t:term) : option (formula * term) = 
  match term_as_formula t with 
  | Some (Implies lhs rhs) -> 
    let lhs = term_as_formula lhs in
    (match lhs with 
     | Some (Eq _ _ _) -> Some (Some?.v lhs, rhs)
     | _ -> None)
  | _ -> None
    
let rec simplify_eq_implication : tactic
  = fun () -> 
    let context, goal_t = cur_goal () in 
    match destruct_equality_implication goal_t with
    | None -> fail "Not an equality implication"
    | Some (_, rhs) ->
      let eq_h = implies_intro () in 
      let _ = rewrite eq_h in
      let _ = clear () in
      visit simplify_eq_implication

////////////////////////////////////////////////////////////////////////////////

let rec just_do_intros : tactic = fun () ->
  let _ = forall_intros () in
  (* let _ = implies_intro () in *)
  (* let _ = smt () in *)
  (* let _ = revert () in *)
  (* revert *) ()

#reset-options // "--debug UserTactics.Example1 --debug_level Norm"
let test_1 =
  assert_by_tactic just_do_intros (forall (y:int). y==0 ==> 0==y)

  (* assert false; *)
  (* assert_by_tactic just_do_intros *)
  (*                  (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y)); *)


(* let test_2 =  *)
(*   assert_by_tactic simplify_eq_implication *)
(*                    (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y)) *)

