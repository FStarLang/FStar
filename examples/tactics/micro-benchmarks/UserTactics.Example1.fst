module UserTactics.Example1 
open FStar.Tactics

#set-options "--lax"
(* -------------------------------------------------------------------------------- *)
let rec revert_all (bs:binders) : Tac unit =
  match bs with 
  | [] -> ()
  | _::tl -> let _ = revert () in revert_all tl
  
let cur_goal () : Tac goal = 
  let goals = TAC?.get () in 
  match goals with 
  | [], _ -> fail "No more goals"
  | hd::_, _ -> hd

let destruct_equality_implication (t:term) : option (formula * term) = 
  match term_as_formula t with 
  | Some (Implies lhs rhs) -> 
    let lhs = term_as_formula lhs in
    (match lhs with 
     | Some (Eq _ _ _) -> Some (Some?.v lhs, rhs)
     | _ -> None)
  | _ -> None
    
let rec simplify_eq_implication : tactic unit
  = fun () -> 
    let context, goal_t = cur_goal () in 
    match destruct_equality_implication goal_t with
    | None -> fail "Not an equality implication"
    | Some (_, rhs) ->
      let eq_h = implies_intro () in 
      let _ = rewrite eq_h in
      let _ = clear () in
      visit simplify_eq_implication

let rec user_visit (callback:tactic unit)
    : tactic unit
    = fun () -> 
         let aux : tactic unit = fun () -> 
           let context, goal_t = cur_goal () in
           match term_as_formula goal_t with
           | None -> smt ()
           | Some (Exists _ _) -> //not yet handled
             ()
           | Some (Forall xs body) ->
             let binders = forall_intros () in
             user_visit callback ();
             revert_all binders

           | Some (And t1 t2) -> 
             seq split (user_visit callback);
             merge ()

           | Some (Implies t1 t2) -> 
             let h = implies_intro () in
             user_visit callback ();
             revert ()

           | _ -> 
             or_else trivial smt
         in
         or_else callback (user_visit callback)

////////////////////////////////////////////////////////////////////////////////

let rec just_do_intros : tactic unit = fun () ->
    focus (fun () -> 
       let _ = forall_intros () in
       let _ = implies_intro () in
       let _ = smt () in
       let _ = revert () in
       revert ())


let rec rewrite_all_equalities : tactic unit = fun () -> 
  visit simplify_eq_implication

let rec test : tactic unit = fun () -> 
  let goal = cur_goal () in 
  ()
  
#reset-options // "--debug UserTactics.Example1 --debug_level Norm"
let test_1 =
  assert_by_tactic test (forall (y:int). y==0 ==> 0==y)
//  assert_by_tactic rewrite_all_equalities (forall (y:int). y==0 ==> 0==y)
  (* assert_by_tactic just_do_intros *)
  (*                  (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y)) *)


(* let test_2 =  *)
(*   assert_by_tactic simplify_eq_implication *)
(*                    (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y)) *)

