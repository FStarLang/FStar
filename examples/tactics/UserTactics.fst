(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module UserTactics
open FStar.Tactics

let test_print_goal =
  assert (forall (y:int). y==0 ==> 0==y)
      by (debug "User debug:") //Some auto-thunking or at least some light notation for it

let test_or_else =
    assert True
        by (or_else (fun () -> fail "failed") idtac)

type t = | A | B | C | D
let f x = match x with | A -> 0 | B -> 1 | C -> 2 | D -> 3

let test_trivial =
    assert ((f A == 0) /\ (f B == 1) /\ (f C == 2) /\ (f D == 3))
        by trivial ()

(* let simple_equality_assertions = *)
  (* assert (forall (y:int). y==0 ==> 0==y) *)
  (*     by rewrite_all_equalities (); *)
  (* assert(forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y)) *)
  (*     by rewrite_all_equalities (); *)
  (* assert(forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z)) *)
  (*     by rewrite_all_equalities () *)

let visible_boolean (x:int) = true
let explicitly_trigger_normalizer =
  assert (visible_boolean 0 /\ visible_boolean 1)
      by (seq split trivial) //without the "trivial", the visible_boolean will go to Z3

unfold let unfoldable_predicate (x:int) = True
let implicitly_unfolfed_before_preprocessing =
  assert (unfoldable_predicate 0 /\ visible_boolean 2)
      by smt () //only "b2t (visible_boolean 2)" goes to SMT

let visible_predicate (x:int) = True
(* let simple_equality_assertions_within_a_function () = *)
(*   assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z)) *)
(*       by rewrite_all_equalities (); //identical to one of the queries above, but now inside a function, which produces a slightly different VC *)
(*   assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ visible_boolean x) *)
(*       by rewrite_all_equalities (); //we're left with (b2t (visible_boolean 0)), since we didn't ask for it to be normalized *)
(*   assert (forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y) /\ (forall (z:int). z==0 ==> x==z) /\ visible_predicate x) //we're left with True, since it is explicit unfolded away *)
(*       by (visit (unfold_definition_and_simplify_eq (quote visible_predicate)) ()) *)

let local_let_bindings =
  assert (let x = 10 in x + 0 == 10) by trivial ()

assume type pred_1 : int -> Type0
assume Pred1_saturated: forall x. pred_1 x
(* let partially_solved_using_smt = *)
(*   assert ((forall (x:int). x==0 ==> (forall (y:int). y==0 ==> x==y)) /\ //proven by tactic *)
(*            pred_1 0 /\ //by 1 smt sub-goal *)
(*            pred_1 1)  //by another smt sub-goal *)
(*       by rewrite_all_equalities () *)

assume val return_ten : unit -> Pure int (requires True) (ensures (fun x -> x == 10))

(* let scanning_environment = *)
(*   let x = return_ten () in *)
(*   assert (x + 0 == 10) *)
(*       by (rewrite_equality (quote x);; *)
(*           rewrite_eqs_from_context;; *)
(*           trivial) *)

assume val mul_comm : x:nat -> y:nat -> Tot (op_Multiply x y == op_Multiply y x)
val lemma_mul_comm : x:nat -> y:nat -> Lemma (op_Multiply x y == op_Multiply y x)
let lemma_mul_comm x y = ()

let sqintro (x:'a) : squash 'a = ()

let test_exact (x:nat) (y:nat) =
  assert (op_Multiply x y == op_Multiply y x)
      by (exact (quote (sqintro (mul_comm x y))))

let test_apply (x:nat) (y:nat) =
  assert (op_Multiply x y == op_Multiply y x)
      by (apply_lemma (quote lemma_mul_comm))

let mul_commute_ascription () : Tac unit =
    let g = cur_goal () in
    match term_as_formula g with
    | Comp (Eq _) _ _ ->
        apply_lemma (quote lemma_mul_comm)
    | _ ->
        fail "Not an equality"

let test_apply_ascription' (x:nat) (y:nat) =
  assert (op_Multiply x y == op_Multiply y x) by (visit idtac)

let test_apply_ascription (x:nat) (y:nat) =
  (assert (op_Multiply x y == op_Multiply y x))
  <: Tot unit
  by ()

(* this fails, rightfully, since the top-level goal is not *)
(* let test_apply_ascription_fail (x:nat) (y:nat) = *)
(*   assert (op_Multiply x y == op_Multiply y x) *)
(*   <: Tot unit *)
(*   by (apply_lemma (quote lemma_mul_comm)) *)

let test_inspect =
  assert True
      by (let x = `8 in
          match inspect x with
          | Tv_App hd a -> debug "application"
          | Tv_Abs bv t -> debug "abstraction"
          | Tv_Arrow bv t -> debug "arrow"
          | Tv_Type _ -> debug "type"
          | Tv_Var _ -> debug "var"
          | Tv_FVar _ -> debug "fvar"
          | Tv_Refine _ _ -> debug "refinement"
          | Tv_Const C_Unit -> debug "unit"
          | Tv_Const (C_Int i) -> debug ("int: " ^ string_of_int i)
          | _ -> fail "unknown")

let test_simpl =
    assert (True /\ 1 == 1)
        by (let g = cur_goal () in
            (match term_as_formula g with
            | And _ _ -> ()
            | _ -> dump "not a conjunction?");
            simpl ();
            let g = cur_goal () in
            (match term_as_formula g with
            | True_ -> ()
            | _ -> dump ("not true after simpl? " ^ term_to_string g)))
