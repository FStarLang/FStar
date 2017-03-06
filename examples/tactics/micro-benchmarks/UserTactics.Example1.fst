module UserTactics.Example1 
open FStar.Tactics
   
(* -------------------------------------------------------------------------------- *)
let cur_goal () : Tac goal = 
  let goals = TAC?.get () in 
  match goals with 
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
    
let rec simplify_eq_implication () 
  : Tac unit
  = let context, goal_t = cur_goal () in 
    match destruct_equality_implication goal_t with
    | None -> fail "Not an equality implication"
    | Some (_, rhs) ->
      let eq_h = implies_intro () in 
      rewrite eq_h;
      clear eq_h;
      visit simplify_eq_implication

////////////////////////////////////////////////////////////////////////////////


let test_1 = assert_by_tactic simplify_eq_implication 
                             (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y))

