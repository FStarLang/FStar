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

let destruct_equality_implication (t:term) : Tac (option (formula * term)) =
  match term_as_formula t with
  | Some (Implies lhs rhs) ->
    let lhs = term_as_formula lhs in
    (match lhs with
     | Some (Eq _ _ _) -> Some (Some?.v lhs, rhs)
     | _ -> None)
  | _ -> None

let rec simplify_eq_implication : tactic unit
  = fun () ->
    let context, goal_t = cur_goal () in  // G |- x=e ==> P
    match destruct_equality_implication goal_t with
    | None -> fail "Not an equality implication"
    | Some (_, rhs) ->
      let eq_h = implies_intro () in  // G, eq_h:x=e |- P
      rewrite eq_h; // G, eq_h:x=e |- P[e/x]
      clear ();     // G |- P[e/x]
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

let rewrite_equality (x:tactic term) : tactic unit
  = fun () ->
     let context, _ = cur_goal () in
     try_rewrite_equality (x()) (binders_of_env context) ()

let solved : tactic unit = fun () ->
  let _, goal = cur_goal () in
  match term_as_formula goal with
  | Some True_ -> ()
  | _ -> fail "Not solved"

let rec just_do_intros : tactic unit = fun () ->
    focus (fun () ->
       let _ = forall_intros () in
       let _ = implies_intro () in
       smt ();
       revert ();
       revert ())

let rec rewrite_all_equalities : tactic unit = fun () ->
  visit simplify_eq_implication


assume val lemma_mul_comm : x:nat -> y:nat -> Lemma (op_Multiply x y == op_Multiply y x)
let mul_commute_ascription : tactic unit
  = fun () ->
    let _, goal_t = cur_goal () in  // G |- x=e ==> P
    match term_as_formula goal_t with
    | Some (Eq _ _ _) ->
      apply_lemma (quote lemma_mul_comm ())
    | _ -> fail "Not an equality"

let rec unfold_definition_and_simplify_eq' (tm:term)
  : tactic unit
  = fun () ->
      let _, goal_t = cur_goal () in  // G |- x=e ==> P
      match term_as_formula goal_t with
      | Some (App hd arg) ->
        if term_eq hd tm then trivial ()
      | _ -> begin
        match destruct_equality_implication goal_t with
        | None -> fail "Not an equality implication"
        | Some (_, rhs) ->
          let eq_h = implies_intro () in  // G, eq_h:x=e |- P
          rewrite eq_h; // G, eq_h:x=e |- P[e/x]
          clear ();     // G |- P[e/x]
          visit (unfold_definition_and_simplify_eq' tm)
       end

let unfold_definition_and_simplify_eq (tm:tactic term) 
  : tactic unit 
  = fun () -> unfold_definition_and_simplify_eq' (tm ()) ()

let exact (t:tactic term) 
  : tactic unit
  = fun () -> FStar.Tactics.exact (t ())

let apply_lemma (t:tactic term)
  : tactic unit
  = fun () -> FStar.Tactics.apply_lemma (t ())
  
////////////////////////////////////////////////////////////////////////////////
// End of tactic code
////////////////////////////////////////////////////////////////////////////////
#reset-options "--use_tactics"

let test_print_goal =
  assert_by_tactic (fun () -> print "User print:") //Some auto-thunking or at least some light notation for it
                   (forall (y:int). y==0 ==> 0==y)


let simple_equality_assertions =
  assert_by_tactic rewrite_all_equalities
                   (forall (y:int). y==0 ==> 0==y);
  assert_by_tactic rewrite_all_equalities
                   (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y));
  assert_by_tactic rewrite_all_equalities
                   (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z))


let visible_boolean (x:int) = true
let explicitly_trigger_normalizer =
  assert_by_tactic (seq split trivial) (visible_boolean 0 /\ visible_boolean 1) //without the "trivial", the visible_boolean will go to Z3

unfold let unfoldable_predicate (x:int) = True
let implicitly_unfolfed_before_preprocessing =
  assert_by_tactic smt
                   (unfoldable_predicate 0 /\ visible_boolean 2) //only "b2t (visible_boolean 2)" goes to SMT

let visible_predicate (x:int) = True
let simple_equality_assertions_within_a_function () =
  assert_by_tactic rewrite_all_equalities
                   (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z)); //identical to one of the queries above, but now inside a function, which produces a slightly different VC
  assert_by_tactic rewrite_all_equalities
                   (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ visible_boolean x); //we're left with (b2t (visible_boolean 0)), since we didn't ask for it to be normalized
  assert_by_tactic (fun () -> visit (unfold_definition_and_simplify_eq (quote visible_predicate)))
                   (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ visible_predicate x) //we're left with True, since it is explicit unfolded away

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

assume val mul_comm : x:nat -> y:nat -> Tot (op_Multiply x y == op_Multiply y x)
let test_exact (x:nat) (y:nat) =
  assert_by_tactic (exact (quote (mul_comm x y)))
                   (op_Multiply x y == op_Multiply y x)


let test_apply (x:nat) (y:nat) =
  assert_by_tactic (apply_lemma (quote lemma_mul_comm))
                   (op_Multiply x y == op_Multiply y x)


let test_apply_ascription (x:nat) (y:nat) =
  assert (op_Multiply x y == op_Multiply y x)
  <: Tot unit
  by (fun () -> visit mul_commute_ascription)

(* this fails, rightfully, since the top-level goal is not *)
(* let test_apply_ascription_fail (x:nat) (y:nat) = *)
(*   assert (op_Multiply x y == op_Multiply y x) *)
(*   <: Tot unit *)
(*   by (fun () -> apply_lemma (quote lemma_mul_comm)) *)
