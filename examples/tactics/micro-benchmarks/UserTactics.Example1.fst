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
      rewrite eq_h;
      clear ();
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
             let _ = user_visit callback () in
             revert_all binders

           | Some (And t1 t2) -> 
             let _ = seq split (user_visit callback) () in
             merge ()

           | Some (Implies t1 t2) -> 
             let h = implies_intro () in
             let _ = user_visit callback () in
             revert ()

           | _ -> 
             or_else trivial smt
         in
         or_else callback (user_visit callback)

let rec try_rewrite_equality (x:term) 
                             (bs:binders)
  : tactic unit 
  = fun () -> 
    match bs with 
    | [] -> ()
    | x_t::bs -> begin
      match term_as_formula (type_of_binder x_t) with 
      | Some (Eq _ y _) -> 
        if term_eq x y 
        then rewrite x_t
        else try_rewrite_equality x bs ()
      | _ -> try_rewrite_equality x bs ()
      end

let rec rewrite_all_context_equalities (bs:binders)
  : tactic unit 
  = fun () -> 
    match bs with 
    | [] -> ()
    | x_t::bs -> begin
      match term_as_formula (type_of_binder x_t) with 
      | Some (Eq _ _ _) -> 
        rewrite x_t;
        rewrite_all_context_equalities bs ()
      | _ -> 
        rewrite_all_context_equalities bs ()
      end

let rec rewrite_eqs_from_context : tactic unit 
  = fun () -> 
       let context, _ = cur_goal () in
       rewrite_all_context_equalities (binders_of_env context) ()
       
let rewrite_equality (x:term) : tactic unit 
  = fun () -> 
     let context, _ = cur_goal () in
     try_rewrite_equality x (binders_of_env context) ()

let solved : tactic unit = fun () -> 
  let _, goal = cur_goal () in 
  match term_as_formula goal with 
  | Some True_ -> ()
  | _ -> fail "Not solved"
  
////////////////////////////////////////////////////////////////////////////////

let rec just_do_intros : tactic unit = fun () ->
    focus (fun () -> 
       let _ = forall_intros () in
       let _ = implies_intro () in
       smt ();
       revert ();
       revert ())

let rec rewrite_all_equalities : tactic unit = fun () -> 
  visit simplify_eq_implication

let rec trivial' : tactic unit = trivial //horrible workaround

#reset-options
let simple_equality_assertions =
  assert_by_tactic rewrite_all_equalities
                   (forall (y:int). y==0 ==> 0==y);
  assert_by_tactic rewrite_all_equalities
                   (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y));
  assert_by_tactic rewrite_all_equalities
                   (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z))

let visible_boolean (x:int) = true
unfold let unfoldable_predicate (x:int) = True
let simple_equality_assertions_within_a_function () =
  assert_by_tactic rewrite_all_equalities
                   (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z)); //identical to one of the queries above, but now inside a function, which produces a slightly different VC
  assert_by_tactic rewrite_all_equalities
                   (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ visible_boolean x); (* gets solved before it even reaches the tactic, although it should not *)
  assert_by_tactic rewrite_all_equalities
                   (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ unfoldable_predicate x)

  
let local_let_bindings =
  assert_by_tactic trivial (let x = 10 in x + 0 == 10)

assume type pred_1 : int -> Type0
assume Pred1_saturated: forall x. pred_1 x
let partially_solved_using_smt =
  assert_by_tactic rewrite_all_equalities
                   ((forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y)) /\ //proven by tactic
                     pred_1 0 /\ //by 1 smt sub-goal
                     pred_1 1)  //by another smt sub-goal

assume val return_ten : unit -> Pure int (requires True) (ensures (fun x -> x == 10))
let scanning_environment =
  let x = return_ten () in
  assert_by_tactic (seq (rewrite_equality (quote x))
                        (seq rewrite_eqs_from_context trivial))
                   (x + 0 == 10)
  
