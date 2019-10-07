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

module RST.Effect.Test

open Steel.Resource
open Steel.RST

open RST.Effect

/// Tests for RST as a layered effect

#set-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2 --using_facts_from '* \
  -FStar.Seq \
  -FStar.ST \
  -FStar.HyperStack \
  -FStar.Monotonic.HyperStack
  -FStar.Heap
  -FStar.Monotonic.Heap \
  -FStar.Tactics \
  -FStar.Reflection \
  -LowStar \
  -FStar.ModifiesGen'"


assume val rst_get (r:resource)
: RST (rmem r)
  r (fun _ -> r)
  (fun _ -> True)
  (fun h0 r h1 -> r == h0 /\ h1 == h0)

let test1 ()
: RST nat emp (fun _ -> emp) (fun _ -> True) (fun _ r _ -> r == 2)
= 2

assume val r1 : r:resource{r.t == nat}
assume val r2 : r:resource{r.t == nat}
assume val r3 : r:resource{r.t == nat}

assume val f1
: x:nat ->
  RST unit r1 (fun _ -> r2)
  (fun (rm:rmem r1) -> rm r1 == 2)
  (fun (rm_in:rmem r1) _ (rm_out:rmem r2) -> rm_out r2 == rm_in r1 + x)

assume val f2
: x:nat ->
  RST unit r2 (fun _ -> r3)
  (fun rm -> rm r2 == 2)
  (fun rm_in _ rm_out -> rm_out r3 == rm_in r2 + x)

assume val f3
: x:nat ->
  RST unit r3 (fun _ -> r3)
  (fun rm -> rm r3 == 2)
  (fun rm_in _ rm_out -> rm_out r3 == rm_in r3 + x)

let test2 ()
: RST unit r1 (fun _ -> r3)
  (fun rm -> rm r1 == 2)
  (fun rm_in x rm_out -> rm_out r3 > 2)
= f1 0; f2 0; f3 3

assume Can_be_split_into_emp:
  forall (r:resource). r `can_be_split_into` (r, emp) /\ r `can_be_split_into` (emp, r)

let test3 ()
: RST nat r1 (fun _ -> r3)
  (fun rm -> rm r1 == 2)
  (fun rm_in x rm_out -> x == 2 /\ rm_out r3 > 2)
= f1 0; f2 0; f3 3;
  let x = rst_frame r3 (fun _ -> r3) r3 test1 in
  let _ = rst_frame r3 (fun _ -> r3) r3 test1 in
  admit ()  //this fails to prove the postcondition because of focus_rmem not working well I think

let test4 ()
: RST unit r1 (fun _ -> r2)
  (fun rm -> rm r1 == 2)
  (fun rm_in x rm_out -> True)
= f1 0; ()  //this works because the lift is parametric in the resource, else () would need to be wrapped in rst_frame

// open FStar.Tactics

// module T = FStar.Tactics

// [@resolve_implicits]
// let resolve_all_implicits () : Tac unit =
//   T.dump "Remaining problems:"

// assume val f_imp
// : unit -> RST unit r1 (fun _ -> r1) (fun _ -> True) (fun _ _ _ -> True)
// assume val g_imp
// : unit -> RST unit r2 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True)

// let test_imp ()
// : RST unit (r1 <*> r2) (fun _ -> r1 <*> r2)
//   (fun _ -> True) (fun _ _ _ -> True)
// = rst_frame _ #r1 #(fun _ -> r1) _ _ #(fun _ -> True) #(fun _ _ _ -> True) f_imp;
//   rst_frame _ #r2 #(fun _ -> r2) _ _ #(fun _ -> True) #(fun _ _ _ -> True) g_imp


/// Testing basic pattern matching

assume val test5 (x:int)
: RST unit r1 (fun _ -> r1)
  (fun _ -> x > 0)
  (fun _ _ _ -> True)

let test6 (l:list int)
: RST unit r1 (fun _ -> r1)
  (fun _ -> Cons? l /\ Cons?.hd l > 0)
  (fun _ _ _ -> True)
= match l with
  | hd::_ -> test5 hd

let test7 (l:list (option int))
: RST unit r1 (fun _ -> r1)
  (fun _ -> Cons? l /\ Some? (Cons?.hd l))
  (fun _ _ _ -> True)
= match l with
  | (Some hd)::_ ->
    if hd > 0 then test5 (Some?.v (Cons?.hd l)) else ()


(*** chacha20 ***)

/// The effect definitions and `rst_frame` are as defined in `examples/layered_effect/RST.Effect.fst`

module U32 = FStar.UInt32

assume val array (a:Type0) : Type0
assume val length (#a:Type0) (b:array a) : pos
assume val array_resource (#a:Type0) (b:array a) : resource
assume val as_rseq (#a:Type0) (b:array a) (#r:resource{array_resource b `is_subresource_of` r}) (h:rmem r)
: GTot (s:Seq.seq a{Seq.length s == length b})

assume val index (#a:Type0) (b:array a) (i:U32.t{U32.v i < length b})
: unit ->
  RST a
  (array_resource b)
  (fun _ -> array_resource b)
  (fun _ -> True)
  (fun h0 x h1 ->
    x == Seq.index (as_rseq b h0) (U32.v i) /\
    h0 == h1)

assume val upd (#a:Type0) (b:array a) (i:U32.t{U32.v i < length b}) (v:a)
: unit ->
  RST unit
  (array_resource b)
  (fun _ -> array_resource b)
  (fun _ -> True)
  (fun h0 _ h1 ->
    let s0 = as_rseq b h0 in
    let s1 = as_rseq b h1 in
    Seq.index s1 (U32.v i) == v /\
    (forall (j:nat).{:pattern Seq.index s1 j} (j < Seq.length s1 /\ j =!= (U32.v i)) ==>
              (Seq.index s1 j == Seq.index s0 j)))


type state = b:array U32.t{length b == 16}


/// `focus_rmem` doesn't work well for me, so adding lemmas that I need for chacha20 function below

assume val as_rseq_focus_rmem1 (#a:Type0)
  (b1 b2:array a) (h:rmem (array_resource b1 <*> array_resource b2))
: Lemma (as_rseq b1 h == as_rseq b1 (focus_rmem h (array_resource b1)))
        [SMTPat (as_rseq b1 h)]

assume val as_rseq_focus_rmem2 (#a:Type0)
  (b1 b2:array a) (h:rmem (array_resource b1 <*> array_resource b2))
: Lemma (as_rseq b2 h == as_rseq b2 (focus_rmem h (array_resource b2)))
        [SMTPat (as_rseq b2 h)]

assume val as_rseq_focus_rmem_inv1 (#a:Type0)
  (b1 b2:array a) (h0 h1:rmem (array_resource b1 <*> array_resource b2))
: Lemma
  (requires focus_rmem h0 (array_resource b1) == focus_rmem h1 (array_resource b1))
  (ensures as_rseq b1 h0 == as_rseq b1 h1)
  [SMTPat (focus_rmem h0 (array_resource b1)); SMTPat (focus_rmem h1 (array_resource b1))]

assume val as_rseq_focus_rmem_inv2 (#a:Type0)
  (b1 b2:array a) (h0 h1:rmem (array_resource b1 <*> array_resource b2))
: Lemma
  (requires focus_rmem h0 (array_resource b2) == focus_rmem h1 (array_resource b2))
  (ensures as_rseq b2 h0 == as_rseq b2 h1)
  [SMTPat (focus_rmem h0 (array_resource b2)); SMTPat (focus_rmem h1 (array_resource b2))]


/// `copy_state`

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

let copy_state
  (st:state)
  (ost:state)
: RST unit
  (array_resource st <*> array_resource ost)
  (fun _ -> array_resource st <*> array_resource ost)
  (fun _ -> True)
  (fun h0 _ h1 ->
    focus_rmem h0 (array_resource ost) == focus_rmem h1 (array_resource ost) /\
    as_rseq st h1 `Seq.equal` as_rseq ost h0)
= let both_st = array_resource st <*> array_resource ost in
  let h0 = rst_get both_st in
  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 0ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 0ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 1ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 1ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 2ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 2ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 3ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 3ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 4ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 4ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 5ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 5ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 6ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 6ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 7ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 7ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 8ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 8ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 9ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 9ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 10ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 10ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 11ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 11ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 12ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 12ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 13ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 13ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 14ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 14ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 15ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 15ul v);

  let h1 = rst_get both_st in

  //assert False;
  Seq.lemma_eq_intro (as_rseq st h1) (as_rseq ost h0)

module T = FStar.Tactics
module Tac = Steel.Tactics

[@resolve_implicits]
let resolve_frames () : T.Tac unit =
  T.admit_all ()

assume val rst_frame_auto (#a:Type)
  (#r_in_outer:resource)
  (#r_in_inner:resource)
  (#r_out_inner:a -> resource)
  (#r_out_outer:a -> resource)
  (#delta:resource)
  (#pre:rprop r_in_inner)
  (#post:rmem r_in_inner -> (x:a) -> rprop (r_out_inner x))
  ($f:unit -> RST a r_in_inner r_out_inner pre post)
: RST a r_in_outer r_out_outer
  (fun rm_in ->
    r_in_outer `can_be_split_into` (r_in_inner, delta) /\
    pre (focus_rmem rm_in r_in_inner))
  (fun rm_in x rm_out ->
    r_in_outer `can_be_split_into` (r_in_inner, delta) /\
    (r_out_outer x) `can_be_split_into` (r_out_inner x, delta) /\
    // (forall (r:resource).
    //    (r `is_subresource_of` delta /\
    //     r `is_subresource_of` r_in_outer /\
    //     r `is_subresource_of` (r_out_outer x)) ==> rm_in r == rm_out r) /\
    focus_rmem rm_in delta == focus_rmem rm_out delta /\  //-- this doesn't work (see test4 in RST.Effect.Test.fst)
    post (focus_rmem rm_in r_in_inner) x (focus_rmem rm_out (r_out_inner x)))

open FStar.Tactics
module T = Steel.Tactics

let split_to_canon_monoid_problem
  (a: Type)
  (outer0 inner0 : resource)
  (outer1 inner1: a -> resource)
  (delta: resource)
  (_ : squash ((inner0 <*> delta) `equal` outer0))
  (post : squash(forall (x:a). (inner1 x <*> delta) `equal` outer1 x))
  : Lemma (
    outer0 `can_be_split_into` (inner0, delta) /\
    (forall (x: a). (outer1 x) `can_be_split_into` (inner1 x, delta))
  )
  =
  can_be_split_into_star outer0 inner0 delta;
  let aux (x:a) : Lemma ((outer1 x) `can_be_split_into` (inner1 x, delta)) =
    can_be_split_into_star (outer1 x) (inner1 x) delta
  in
  Classical.forall_intro aux


unfold let delta_spec
  (#a: Type)
  (inner0 outer0: resource)
  (inner1 outer1: a -> resource)
  (delta: resource)
  : Type =
  squash (outer0 `can_be_split_into` (inner0, delta) /\
         (forall (x: a). (outer1 x) `can_be_split_into` (inner1 x, delta))
  )

let typecheck_delta () : Tac unit =
  norm [delta_only [`%delta_spec]];
  apply_lemma (normalize_term (`split_to_canon_monoid_problem));
  let open Steel.Tactics in
  let open FStar.Algebra.CommMonoid.Equiv in
  let open FStar.Tactics.CanonCommMonoidSimple.Equiv in
  norm [delta];
  canon_monoid req rm;
  let _ = forall_intro () in
  norm [delta];
  canon_monoid req rm


#push-options "--no_tactics"

let frame (#a: Type)
  (#inner1 #outer1 : a -> resource)
  (#inner0 #outer0: resource)
  (#delta: resource{with_tactic typecheck_delta (delta_spec inner0 outer0 inner1 outer1 delta)})
  (#pre:rprop inner0)
  (#post:rmem inner0 -> (x:a) -> rprop (inner1 x))
  ($f: unit -> RST a inner0 inner1 pre post)
  : RST a outer0 outer1 (fun h0 ->
    by_tactic_seman typecheck_delta (delta_spec inner0 outer0 inner1 outer1 delta);
    pre (focus_rmem h0 inner0)
  )
  (fun h0 x h1 ->
    by_tactic_seman typecheck_delta (delta_spec inner0 outer0 inner1 outer1 delta);
    focus_rmem h0 delta == focus_rmem h1 delta /\
    post (focus_rmem h0 inner0) x (focus_rmem h1 (inner1 x))
  )
  =
  by_tactic_seman typecheck_delta (delta_spec inner0 outer0 inner1 outer1 delta);
  rst_frame
    outer0
    #inner0
    #inner1
    outer1
    delta
    #pre
    #post
    (fun _ -> f ())

#pop-options

let f (b: array U32.t) : RST unit (array_resource b) (fun _ -> array_resource b) (fun _ -> True) (fun _ _ _ -> True) =
  (ignore (index b 0ul ()))

[@expect_failure]
let test_frame_inference0 (b1: array U32.t) (b2: array U32.t)
  : RST unit (array_resource b1 <*> array_resource b2) (fun _ -> array_resource b1 <*> array_resource b2) (fun _ -> True) (fun _ _ _ -> True)
 =
  frame #(array_resource b2) #(array_resource b1) #(array_resource b1) (fun _ -> f b1);
  frame #(array_resource b1) #(array_resource b2) #(array_resource b2) (fun _ -> f b2)

#reset-options

type doable_unification_goal =
  | ForwardInference
  | FinalCheck
  | ResourceTyping

let inspect_resource_typing_goal (goal: goal) : Tac (option doable_unification_goal) =
  try
  let type_name, resource_name  =
    match inspect (goal_type goal), inspect (`resource) with
    | Tv_FVar type_name, Tv_FVar resource_name ->
      type_name, resource_name
    | _ -> fail "Not a valid goal"
  in
  if FStar.Order.eq (compare_fv type_name resource_name) then begin
    Some (ResourceTyping)
  end else begin
    None
  end with
  | _ -> None

let inspect_goal (goal: goal) : Tac (option doable_unification_goal) =
  try
  let delta, refinement = match inspect (goal_type goal) with
    | Tv_Refine delta refinement -> delta, refinement
    | _ -> fail "Not a valid goal"
  in
  let delta_type_name, resource_name =
    match (inspect (inspect_bv delta).bv_sort, inspect (`resource)) with
    | (Tv_FVar delta_type_name, Tv_FVar resource_name) ->
      delta_type_name, resource_name
    | _ -> fail "Not a valid goal"
  in
  let _ = if FStar.Order.eq (compare_fv delta_type_name resource_name) then () else
    fail "Not a valid goal"
  in
  let with_tactic_and_typecheck, delta_spec_expr =
    match inspect refinement with
    | Tv_App with_tactic_and_typecheck delta_spec_expr ->
      with_tactic_and_typecheck, delta_spec_expr
    | _ -> fail "Not a valid goal"
  in
  let delta_spec_expr, _ = delta_spec_expr in
  let with_tactic_op, typecheck_op =
    match inspect with_tactic_and_typecheck with
    | Tv_App with_tactic_op typecheck_op ->
      with_tactic_op, typecheck_op
    | _ -> fail "Not a valid goal"
  in
  let typecheck_op, _ = typecheck_op in
  let with_tactic_name, with_tactic_real_name, typecheck_name, typecheck_real_name =
    match
      inspect with_tactic_op, inspect (`with_tactic),
      inspect typecheck_op, inspect (`typecheck_delta)
    with
    | Tv_FVar with_tactic_name, Tv_FVar with_tactic_real_name,
      Tv_FVar typecheck_name, Tv_FVar typecheck_real_name ->
      with_tactic_name, with_tactic_real_name, typecheck_name, typecheck_real_name
    | _ -> fail "Not a valid goal"
  in
  let _ = if FStar.Order.eq (compare_fv with_tactic_name with_tactic_real_name) then () else
    fail "Not a valid goal"
  in
  let _ = if FStar.Order.eq (compare_fv typecheck_name typecheck_real_name) then () else
    fail "Not a valid goal"
  in
  let refinement_rest, delta_arg  =
    match inspect delta_spec_expr with
    | Tv_App refinement_rest delta_arg ->
      refinement_rest, delta_arg
    | _ -> fail "Not a valid goal"
  in
  let delta_arg, _ = delta_arg in
  let refinement_rest, outer1_arg  =
    match inspect refinement_rest with
    | Tv_App refinement_rest outer1_arg ->
      refinement_rest, outer1_arg
    | _ -> fail "Not a valid goal"
  in
  let outer1_arg, _ = outer1_arg in
  let refinement_rest, inner1_arg  =
    match inspect refinement_rest with
    | Tv_App refinement_rest inner1_arg ->
      refinement_rest, inner1_arg
    | _ -> fail "Not a valid goal"
  in
  let inner1_arg, _ = inner1_arg in
  let refinement_rest, outer0_arg  =
    match inspect refinement_rest with
    | Tv_App refinement_rest outer0_arg ->
      refinement_rest, outer0_arg
    | _ -> fail "Not a valid goal"
  in
  let outer0_arg, _ = outer0_arg in
  let delta_refinement_rest, inner0_arg  =
    match inspect refinement_rest with
    | Tv_App delta_refinement inner0_arg ->
      delta_refinement, inner0_arg
    | _ -> fail "Not a valid goal"
  in
  let inner0_arg, _ = inner0_arg in
  let delta_refinement_op, return_type =
    match inspect delta_refinement_rest with
    | Tv_App delta_refinement_op return_type ->
      delta_refinement_op, return_type
    | _ -> fail "Not a valid goal"
  in
  let return_type, _ = return_type in
  let (delta_refinement_name, real_delta_refinement_name) =
    match inspect delta_refinement_op , inspect (`delta_spec) with
    | Tv_FVar delta_refinement_name, Tv_FVar real_delta_refinement_name ->
      delta_refinement_name, real_delta_refinement_name
    | _ -> fail "Not a valid goal"
  in
  let _ = if FStar.Order.eq (compare_fv delta_refinement_name real_delta_refinement_name)
    then () else fail "Not a valid goal"
  in
  let inner1_arg, outer1_arg =
    match inspect inner1_arg, inspect outer1_arg with
    | Tv_Abs _ inner1_arg, Tv_Abs _ outer1_arg ->
      inner1_arg, outer1_arg
    | _ -> fail "Not a valid goal"
  in
  begin match inspect outer0_arg, inspect outer1_arg with
  | Tv_Uvar _ _, Tv_Uvar _ _ ->
    (* Both outers are unknown, we are in the middle of the function *)
    None
  | Tv_Uvar _ _, _ ->
    (* The last outer is known by unification *)
    None
  | _, Tv_Uvar _ _ ->
    (* The first outer is known by unification, we can solve this! *)
    Some ForwardInference
  | _ ->
    (* Both outer and inner are here, we just have to compute delta *)
    Some FinalCheck
  end with
  | _ ->
    inspect_resource_typing_goal goal

let rec inspect_goals (goals:list goal) : Tac (option (doable_unification_goal & goal)) =
  match goals with
  | [] -> None
  | goal::rest -> begin
    match inspect_goal goal with
    | Some ForwardInference -> Some (ForwardInference, goal)
    | Some FinalCheck -> begin match inspect_goals rest with
      | Some (ForwardInference, goal') -> Some (ForwardInference, goal')
      | _ -> Some (FinalCheck, goal)
    end
    | Some ResourceTyping -> begin match inspect_goals rest with
      | Some (ForwardInference, goal') -> Some (ForwardInference, goal')
      | Some (FinalCheck, goal') -> Some (FinalCheck, goal')
      | _ -> Some (ResourceTyping, goal)
    end
    | _ -> inspect_goals rest
  end

let rec remove_goal_from_list (g: goal) (goals: list goal) : list goal =
  match goals with
  | [] -> []
  | g'::rest ->
    if FStar.Order.eq (compare_term (goal_type g') (goal_type g)) then rest else
      g'::(remove_goal_from_list g rest)

let focus_and_solve_goal (goal: goal) (t: unit -> Tac 'a) : Tac 'a =
  let rest_of_goals = remove_goal_from_list goal (goals ()) in
  set_goals [goal];
  let result = t () in
  match goals () with
  | [] -> set_goals rest_of_goals; result
  | _ -> fail "Focused goal not solved !"

let solve_forward_inference_goal () : Tac unit =
  refine_intro ();
  flip ();
  apply_lemma (`unfold_with_tactic);
  apply_lemma (`FStar.Classical.give_witness);
  norm [delta_only [`%delta_spec]];
  apply_lemma (`split_to_canon_monoid_problem);
  let open Steel.Tactics in
  let open FStar.Algebra.CommMonoid.Equiv in
  let open FStar.Tactics.CanonCommMonoidSimple.Equiv in
  norm [delta];
  canon_monoid req rm;
  norm [delta];
  let _ = forall_intro () in
  canon_monoid req rm

let solve_resource_witness_goal () : Tac unit =
  exact (cur_witness ())

let one_inference_step () : Tac unit =
  let cur_goals = goals () in
  match inspect_goals cur_goals with
  | Some (goal_typ, goal) -> begin
    if (goal_typ = ForwardInference || goal_typ = FinalCheck) then
      focus_and_solve_goal goal (fun _ ->
       solve_forward_inference_goal ()
      )
    else
     focus_and_solve_goal goal (fun _ ->
       solve_resource_witness_goal ()
     )
  end
  | _ -> fail "No solvable goals found!"

[@resolve_implicits]
let rec resolve_tac () : Tac unit =
  let cur_goals = goals () in
  let n = ngoals () in
  match cur_goals with
  | [] -> ()
  | _ ->
   one_inference_step ();
   let n' = ngoals () in
   if n' < n then
     resolve_tac ()
   else
     fail "The tactic is not making progress!"

let test_frame_inference2
  (b1: array U32.t)
  (b2: array U32.t)
  (b3: array U32.t)
  (b4: array U32.t)
  (b5: array U32.t)
  : RST unit
    (array_resource b1 <*>
     array_resource b2 <*>
     array_resource b3 <*>
     array_resource b4 <*>
     array_resource b5)
    (fun _ -> array_resource b1 <*>
     array_resource b2 <*>
     array_resource b3 <*>
     array_resource b4 <*>
     array_resource b5)
    (fun _ -> True)
    (fun _ _ _ -> True)
  =
  frame (fun _ -> f b1);
  frame (fun _ -> f b2);
  frame (fun _ -> f b3);
  frame (fun _ -> f b4);
  frame (fun _ -> f b5)

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

let copy_state_with_frame_inference
  (st:state)
  (ost:state)
: RST unit
  (array_resource st <*> array_resource ost)
  (fun _ -> array_resource st <*> array_resource ost)
  (fun _ -> True)
  (fun h0 _ h1 ->
    focus_rmem h0 (array_resource ost) == focus_rmem h1 (array_resource ost) /\
    as_rseq st h1 `Seq.equal` as_rseq ost h0)
  =
  let h0 = rst_get (array_resource st <*> array_resource ost) in
  let v = frame (index ost 0ul) in
  frame (upd st 0ul v);
  let v = frame (index ost 1ul) in
  frame (upd st 1ul v);
  let v = frame  (index ost 2ul) in
  frame (upd st 2ul v);
  let v = frame  (index ost 3ul) in
  frame (upd st 3ul v);
  let v = frame (index ost 4ul) in
  frame (upd st 4ul v);
  let v = frame (index ost 5ul) in
  frame (upd st 5ul v);
  let v = frame (index ost 6ul) in
  frame (upd st 6ul v);
  let v = frame (index ost 7ul) in
  frame (upd st 7ul v);
  let v = frame (index ost 8ul) in
  frame (upd st 8ul v);
  let v = frame (index ost 9ul) in
  frame (upd st 9ul v);
  let v = frame (index ost 10ul) in
  frame (upd st 10ul v);
  let v = frame (index ost 11ul) in
  frame (upd st 11ul v);
  let v = frame (index ost 12ul) in
  frame (upd st 12ul v);
  let v = frame (index ost 13ul) in
  frame (upd st 13ul v);
  let v = frame (index ost 14ul) in
  frame (upd st 14ul v);
  let v = frame (index ost 15ul) in
  frame (upd st 15ul v);
  let h1 = rst_get (array_resource st <*> array_resource ost) in
  //assert False;
  Seq.lemma_eq_intro (as_rseq st h1) (as_rseq ost h0)
