module UserTactics.Example1
open FStar.Tactics

let test_print_goal =
  assert_by_tactic (fun () -> print "User print:") //Some auto-thunking or at least some light notation for it
                   (forall (y:int). y==0 ==> 0==y)

let test_grewrite =
assert_by_tactic (fun () -> grewrite (quote (1 + 2) ()) (quote 3 ())) (1 + 2 == 2 + 1)

let test_grewrite2 (w x y z:int) =
assert_by_tactic (fun () -> grewrite (quote (z + y) ()) (quote (y + z) ());
                            grewrite (quote (x + (y + z)) ()) (quote ((y + z) + x) ());
                            grewrite (quote (w + ((y + z) + x)) ()) (quote (((y + z) + x) + w) ())
                 ) (w + (x + (z + y)) == (y + z) + (x + w))

let test_grewrite3 (w x y z : int) =
assert_by_tactic (fun () -> grewrite (quote (1 + 2) ()) (quote 3 ());
                            grewrite (quote (3, 3+4) ()) (quote (3,7) ())
                 )
                 ( (1+2, 3+4) == (5-2, 7+0) )

// Should rewrite all at once, and does, but we get a weird hard query
let test_grewrite4 (f : int -> int -> int) (w : int) =
assert_by_tactic (fun () -> let _ = implies_intro () in
                            grewrite (quote (f w w) ()) (quote w ());
                            revert ())
                 ( f w w == w ==> f (f w w) (f w w) == w)

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
