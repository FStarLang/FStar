module UserTactics
open FStar.Tactics

let test_print_goal =
  assert_by_tactic (print "User print:") //Some auto-thunking or at least some light notation for it
                   (forall (y:int). y==0 ==> 0==y)

let test_or_else =
    assert_by_tactic (or_else (fail "failed")
                              (return ())) True

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
  assert_by_tactic (visit (unfold_definition_and_simplify_eq (quote visible_predicate)))
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
  assert_by_tactic (rewrite_equality (quote x);;
                    rewrite_eqs_from_context;;
                    trivial)
                   (x + 0 == 10)

assume val mul_comm : x:nat -> y:nat -> Tot (op_Multiply x y == op_Multiply y x)
val lemma_mul_comm : x:nat -> y:nat -> Lemma (op_Multiply x y == op_Multiply y x)
let lemma_mul_comm x y = ()

let test_exact (x:nat) (y:nat) =
  assert_by_tactic (m <-- quote (mul_comm x y);
                    exact m)
                   (op_Multiply x y == op_Multiply y x)

let test_apply (x:nat) (y:nat) =
  assert_by_tactic (apply_lemma (quote lemma_mul_comm))
                   (op_Multiply x y == op_Multiply y x)

let mul_commute_ascription : tactic unit =
    g <-- cur_goal;
    let (_, t) = g in
    f <-- term_as_formula t;
    match f with
    | Some (Eq _ _ _) ->
        apply_lemma (quote lemma_mul_comm)
    | _ ->
        fail "Not an equality"

let test_apply_ascription' (x:nat) (y:nat) =
  assert_by_tactic (visit (return ())) (op_Multiply x y == op_Multiply y x)

//TODO: doesn't work. "missing universe instantiation on reify_tactic" (??)
// let test_apply_ascription (x:nat) (y:nat) =
//   assert (op_Multiply x y == op_Multiply y x)
//   <: Tot unit
//   by (visit (return ()))

(* this fails, rightfully, since the top-level goal is not *)
(* let test_apply_ascription_fail (x:nat) (y:nat) = *)
(*   assert (op_Multiply x y == op_Multiply y x) *)
(*   <: Tot unit *)
(*   by (fun () -> apply_lemma (quote lemma_mul_comm)) *)

// TODO: if patterns are incomplete, it appears as if the tactic runs anyway
// and only afterwards is the error raised. Doesn't sound like good behaviour
let test_inspect =
  assert_by_tactic (x <-- quote 8;
                    y <-- inspect x;
                    match y with
                    | Tv_App hd a -> print "application"
                    | Tv_Abs bv t -> print "abstraction"
                    | Tv_Arrow bv t -> print "arrow"
                    | Tv_Type _ -> print "type"
                    | Tv_Var _ -> print "var"
                    | Tv_FVar _ -> print "fvar"
                    | Tv_Refine _ _ -> print "refinement"
                    | Tv_Const C_Unit -> print "unit"
                    | Tv_Const (C_Int i) -> print ("int: " ^ string_of_int i)
                    | _ -> fail "unknown"
                   ) (True)
