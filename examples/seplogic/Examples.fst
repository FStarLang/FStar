module Examples

open Lang
open FStar.Heap

open FStar.Tactics

#reset-options "--log_queries --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let unfold_fns :list string = [
  "wp_command";
  "wpsep_command";
  "lift_wpsep";
  "uu___is_Return";
  "uu___is_Bind";
  "uu___is_Read";
  "uu___is_Write";
  "uu___is_Alloc";
  "__proj__Return__item__v";
  "__proj__Bind__item__c1";
  "__proj__Bind__item__c2";
  "__proj__Read__item__id";
  "__proj__Write__item__id";
  "__proj__Write__item__v"
]

unfold let unfold_steps =
  List.Tot.map (fun s -> "Lang." ^ s) unfold_fns

let step_alloc_return :tactic unit =
  dump "In step_alloc_return";;
  apply_lemma (quote lemma_alloc_return);; norm [];;
  dump "After step_alloc_return"

let step_bind :tactic unit = 
  dump "In step_bind";;
  apply_lemma (quote lemma_bind);; norm [];;
  dump "After step_bind"

let step_eq_implies_intro :tactic unit =
  dump "In step_eq_implies_intro";;
  apply_lemma (quote lemma_eq_implies_intro);; norm [];;
  dump "After step_eq_implies_intro"

let step_extract_disjoint :tactic unit =
  dump "In step_extract_disjoint";;
  apply_lemma (quote lemma_extract_disjoint);; norm [];;
  dump "After lemma_extract_disjoint";;
  split;;
  dump "After split";;
  // TODO - Replace "smt" with "simplify_disjoint"
  smt

let assumption'  :tactic unit = 
  apply_raw (quote FStar.Squash.return_squash);; assumption

let assumption'' :tactic unit = 
  or_else assumption' (apply_lemma (quote lemma_addr_not_eq_refl);; norm [];; assumption')

let step_read_write       :tactic unit = 
  dump "In step_read_write";;
  apply_lemma (quote lemma_read_write);; norm [];;
  dump "After lemma_read_write";;
  split;;
  dump "After split";;
  // TODO - Replace "smt" with "simplify_contains"
  smt

let step_restrict :tactic unit =
  dump "In step_restrict";;
  or_else (apply_lemma (quote lemma_restrict_r_join_restrict_minus);;
           // TODO - Replace "smt" with "simplify_contains"
           smt)
          (apply_lemma (quote lemma_restrict_r1_join_restrict_minus);;
	   repeat (split);; 
	   // TODO - Replace "smt" with "simplify_contains"
	   smt;; 
	   smt;; 
	   assumption'')

let simplify_restrict :tactic unit =
  apply_lemma (quote lemma_eq_l_cong);;
  step_restrict;;
  trytac trefl;;
  return ()

let simplify_join_emp :tactic unit =
  dump "In simplify_join_emp";;
  pointwise (or_else (or_else (apply_lemma (quote lemma_join_h_emp);; qed) 
                              (apply_lemma (quote lemma_join_emp_h);; qed))
		     (fail "SKIP"))

let simplify_join_minus :tactic unit =
  dump "In simplify_join_minus";;
  pointwise (or_else (apply_lemma (quote lemma_join_restrict_minus);;
                      // TODO - Replace "smt" with "simplify_contains"
		      smt)
		     (fail "SKIP"))

let step_disjoint :tactic unit =
  dump "In step_disjoint";;
  split;;
  dump "After split";;
  // TODO - Replace "smt" with "step_disjoint"
  smt

let simplify_join :tactic unit =
  dump "In simplify_join";;
  apply_lemma (quote lemma_impl_l_cong);;
  simplify_join_emp;;
  simplify_join_minus;;
  dump "After simplify_join_minus";;
  apply_lemma (quote lemma_refl)

let step_intros :tactic unit =
  dump "In step_intros";;
  forall_intros;;
  simplify_join;;
  repeat simplify_restrict;;
  implies_intro;;
  return ()

let step :tactic unit =
  dump "In step";;
  step_bind                   `or_else`
  step_read_write             `or_else`
  step_alloc_return           `or_else`
  step_eq_implies_intro       `or_else`
  step_intros                 `or_else`
  step_extract_disjoint       `or_else`
  step_disjoint               `or_else`
  fail "step: failed"

let step_sel :tactic unit =
  dump "In step_sel";;
  (apply_lemma (quote lemma_sel_r_join_points_to_minus);; 
   // TODO - Replace "smt" with "simplify_contains"
   smt)           `or_else`
  (apply_lemma (quote lemma_sel_join_h_emp))                                       `or_else`
  // (apply_lemma (quote lemma_sel_r_update);; dump "ss1")                         `or_else`
  // (apply_lemma (quote lemma_sel_r1_update);; dump "ss2";; assumption'')         `or_else`
  // (apply_lemma (quote lemma_sel_r1_from_restrict);; dump "ss3";;  assumption'') `or_else`
  // (apply_lemma (quote lemma_sel_r_from_minus);; dump "ss4";; assumption'')      `or_else`
  fail "step_sel: failed"

let simplify_sel :tactic unit =
  dump "In simplify_sel";;
  trytac (apply_lemma (quote lemma_eq_cong);; norm []);;
  step_sel;;
  dump "After step_sel";;
  trytac trefl;;
  return ()

let and_elim' :tactic unit =
  h <-- implies_intro;
  and_elim (pack (Tv_Var h));;
  clear h

let implies_intros' :tactic unit =
  repeat and_elim';;
  implies_intros;;
  return ()

let rec repeat_simplify_sel () :Tac unit =
  (g <-- trytac cur_goal;
  begin match g with
  | None -> return ()
  | Some _ -> repeat simplify_sel;;
              dump "After repeat simplify_sel";;
              trytac (trivial `or_else` (trefl;; qed) `or_else` smt);;
              repeat_simplify_sel
  end
  ) ()

let simplify_goals :tactic unit =
  dump "In simplify_goals";;
  simplify_join_emp;;
  dump "After simplify_join_emp";;
  simplify_join_minus;;
  dump "After simplify_join_minus";;
  trytac (repeat split);;
  dump "After trytac (repeat split)";;
  repeat_simplify_sel;;
  dump "After repeat_simplify_sel";;
  return ()

let solve :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  dump "Initial goal";;
  trytac implies_intros';;
  e <-- cur_env;
  rewrite_all_context_equalities (binders_of_env e);;
  dump "After trytac implies_intros'";;
  repeat step;;
  dump "After repeat step";;
  simplify_goals;;
  dump "After simplify_goals";;
  dump "Final goal"

let norm_step: tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  return ()
  
(***** Examples *****)
open FStar.UInt
open FStar.UInt64

type t = UInt64.t

// let write_ok (h:heap) (r:addr) (n:t) =
//   let c = (Write r n) in
//   let p = fun _ h -> sel h r == n in
//   let post = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (h `contains` r ==> post) (
//     norm [delta; delta_only unfold_steps; primops];;
//     implies_intros';;
//     apply_lemma (quote lemma_read_write);;
//     norm [];;
//     split;;
//     assumption'';;
//     apply_lemma (quote lemma_eq_implies_intro);;
//     norm [];;
//     split;;
//     apply_lemma (quote lemma_disjoint_points_to_minus);;
//     norm [];;
//     assumption'';;
//     apply_lemma (quote lemma_sel_r_join_points_to_minus);;
//     norm [];;
//     assumption''
//   )

// let write_ok (h:heap) (r:addr) (n:t) =
//   let c = (Write r n) in
//   let p = fun _ h -> sel h r == n in
//   let post = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (h `contains` r ==> post) solve

// let increment_ok (h:heap) (r:addr) (n:t) =
//   let c = Bind (Read r) (fun n -> Write r (n +?^ 1uL)) in
//   let p = fun _ h -> (sel h r == n +?^ 1uL) in
//   let post = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (h `contains` r /\ sel h r == n ==> post) (
//     norm [delta; delta_only unfold_steps; primops];;
//     implies_intros';;
//     apply_lemma (quote lemma_bind);;
//     norm [];;
//     apply_lemma (quote lemma_read_write);;
//     norm [];;
//     split;;
//     assumption'';;
//     forall_intro;;
//     implies_intro;;
//     apply_lemma (quote lemma_extract_disjoint);;
//     norm [];;
//     split;;
//     apply_lemma (quote lemma_disjoint_restrict_minus);;
//     norm [];;
//     assumption'';;
//     apply_lemma (quote lemma_read_write);;
//     norm [];;
//     split;;
//     smt;;
//     apply_lemma (quote lemma_eq_implies_intro);;
//     norm [];;
//     split;;
//     apply_lemma (quote lemma_disjoint_points_to_minus);;
//     norm [];;
//     smt;;
//     split;;
//     apply_lemma (quote lemma_emp_disjoint);;
//     norm [];;
//     apply_lemma (quote lemma_eq_cong);;
//     norm [];;
//     apply_lemma (quote lemma_sel_join_h_emp);;
//     norm [];;
//     apply_lemma (quote lemma_eq_cong);;
//     norm [];;
//     apply_lemma (quote lemma_sel_r_join_points_to_minus);;
//     norm [];;
//     smt
//   )

// let increment_ok (h:heap) (r:addr) (n:t) =
//   let c = Bind (Read r) (fun n -> Write r (n +?^ 1uL)) in
//   let p = fun _ h -> (sel h r == n +?^ 1uL) in
//   let post = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (h `contains` r /\ sel h r == n ==> post) solve
 
// let swap_ok (r1:addr) (r2:addr) (h:heap) (a:t) (b:t) =
//   let c = Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1))) in
//   let p = fun _ h -> (sel h r1 == b /\ sel h r2 == a) in
//   let post = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (h `contains` r1 /\  h `contains` r2 /\ addr_of r1 <> addr_of r2 /\ sel h r1 == a /\ sel h r2 == b ==> post) (
//     norm [delta; delta_only unfold_steps; primops];;
//     implies_intros';;
//     apply_lemma (quote lemma_bind);;
//     norm [];;
//     apply_lemma (quote lemma_read_write);;
//     norm [];;
//     split;;
//     assumption'';;
//     forall_intro;;
//     implies_intro;;
//     apply_lemma (quote lemma_extract_disjoint);;
//     norm [];;
//     split;;
//     smt;;
//     apply_lemma (quote lemma_bind);;
//     norm [];;
//     apply_lemma (quote lemma_read_write);;
//     norm [];;
//     split;;
//     smt;;
//     forall_intro;;
//     apply_lemma (quote lemma_eq_l_cong);;
//     norm [];;
//     apply_lemma (quote lemma_restrict_r1_join_restrict_minus);;
//     norm [];;
//     repeat (split);;
//     assumption'';;
//     assumption'';;
//     assumption'';;
//     implies_intro;;
//     apply_lemma (quote lemma_extract_disjoint);;
//     norm [];;
//     apply_lemma (quote lemma_read_write);;
//     norm [];;
//     fail "here"
//   )

// let swap_ok (r1:addr) (r2:addr) (h:heap) (a:t) (b:t) =
//   let c = Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1))) in
//   let p = fun _ h -> (sel h r1 == b /\ sel h r2 == a) in
//   let post = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (h `contains` r1 /\  h `contains` r2 /\ addr_of r1 <> addr_of r2 /\ sel h r1 == a /\ sel h r2 == b ==> post) solve

let double_increment_ok (r:addr) (h:heap) (n:t{size (v n + 2) FStar.UInt64.n}) =
  let c = Bind (Bind (Read r) (fun y -> Write r (y +?^ 1uL))) (fun _ -> (Bind (Read r) (fun y -> Write r (y +?^ 1uL))))  in
  let p = fun _ h -> sel h r == (n +?^ 2uL) in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (h `contains` r /\ sel h r == n ==> t) solve

let rotate_ok (r1:addr) (r2:addr) (r3:addr) (h:heap) (i:t) (j:t) (k:t) =
  let c = Bind (Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1)))) (fun _ -> Bind (Read r2) (fun n3 -> Bind (Read r3) (fun n4 -> Bind (Write r2 n4) (fun _ -> Write r3 n3)))) in
  let p = fun _ h -> (sel h r1 == j /\ sel h r2 == k /\ sel h r3 == i) in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (h `contains` r1 /\ h `contains` r2 /\ h `contains` r3 /\ 
                    addr_of r1 <> addr_of r2 /\ addr_of r2 <> addr_of r3 /\ addr_of r1 <> addr_of r3 /\
		    sel h r1 == i /\ sel h r2 == j /\ sel h r3 == k ==> t) solve

let init_ok (h:heap) =
  let c = Bind (Alloc) (fun (r1:addr) -> Bind (Write r1 7uL) (fun _ -> Return r1)) in
  let p = fun r h -> sel h r == 7uL in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic t solve 

let copy_ok (r1:addr) (r2:addr) (r3:addr) (h:heap) (i:t) (j:t) (k:t) =
  let c = Bind (Read r1) (fun n1 -> Write r2 (n1)) in
  let p = fun _ h -> (sel h r1 == i /\ sel h r2 == i /\ sel h r3 == k) in
  let post = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (addr_of r1 <> addr_of r2 /\ addr_of r2 <> addr_of r3 /\ addr_of r1 <> addr_of r3 /\ sel h r1 == i /\ sel h r2 == j /\ sel h r3 == k ==> post) solve //here how can we apply a binder?
