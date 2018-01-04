module Test

open Lang

open FStar.SL.Heap

open FStar.Tactics

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"

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

let and_elim' :tactic unit =
  h <-- implies_intro;
  and_elim (pack (Tv_Var h));;
  clear h

let implies_intros' :tactic unit =
  repeat and_elim';;
  implies_intros;;
  return ()

let assumption'  :tactic unit = 
  apply_raw (quote FStar.Squash.return_squash);; assumption

let assumption'' :tactic unit = 
  or_else assumption' (apply_lemma (quote lemma_addr_not_eq_refl);; norm [];; assumption')

let rec split_all () :Tac unit =
  ( g <-- cur_goal;
    match (term_as_formula g) with
    | And _ _ -> split;; iseq [split_all; split_all]
    | _       -> return ()
  ) ()

(***** Tactics *****)

let simplify_contains_aux :tactic unit =
  dump "In simplify_contains_aux";;
  or_else assumption''
          ((apply_lemma (quote lemma_contains_r_join_tot_restrict_minus);; norm [])   `or_else`
	   (apply_lemma (quote lemma_contains_r_join_tot_points_to_minus);; norm [])  `or_else`
	   (apply_lemma (quote lemma_contains_r1_join_tot_restrict_minus);; norm [])  `or_else`
	   (apply_lemma (quote lemma_contains_r1_join_tot_points_to_minus);; norm []) `or_else`
           (apply_lemma (quote lemma_contains_join_tot_h_emp_with_next_addr);; norm []) `or_else`
	   (apply_lemma (quote lemma_contains_r_points_to_unused_h);; 
	    dump "heeee";;
	    apply_lemma (quote lemma_r_unused_in_h);; smt;;  norm []))

let simplify_contains :tactic unit =
  repeat simplify_contains_aux;;
  return ()

let simplify_restrict_aux :tactic unit =
  (apply_lemma (quote lemma_eq_l_cong);; norm []);;
  dump "gp";;
  (apply_lemma (quote lemma_restrict_r_join_tot_points_to_minus);; norm [])  `or_else`
  (apply_lemma (quote lemma_restrict_r_join_tot_restrict_minus);; norm [])   `or_else`
  (apply_lemma (quote lemma_restrict_r1_join_tot_restrict_minus);; norm [])  `or_else`
  (apply_lemma (quote lemma_restrict_r1_join_tot_points_to_minus);; norm []) `or_else`
  (apply_lemma (quote lemma_restrict_join_tot_h_emp_with_next_addr);; dump "A";; norm []);;
  simplify_contains

let simplify_restrict :tactic unit =
  repeat simplify_restrict_aux;;
  trytac trefl;;
  return ()

let step_bind :tactic unit = 
  dump "In step_bind";;
  apply_lemma (quote lemma_bind);;
  norm []

let step_read_write :tactic unit = 
  dump "In step_read_write";;
  apply_lemma (quote lemma_read_write);;
  dump "A";;
  norm [];;
  simplify_contains

let step_alloc_return :tactic unit =
  dump "In step_alloc_return";;
  apply_lemma (quote lemma_alloc_return);;
  norm [];;
  simplify_contains

let step_eq_implies_intro :tactic unit =
  dump "In step_eq_implies_intro";;
  apply_lemma (quote lemma_eq_implies_intro);;
  norm [];;
  dump "A"

let step_eq_implies_intro' :tactic unit =
  dump "In step_eq_implies_intro'";;
  forall_intro;;
  dump "111";;
  apply_lemma (quote lemma_eq_implies_intro');;
  dump "122";;
  norm [];;
  dump "133";;
  implies_intro;;
  dump "144"
 
let step_intro :tactic unit =
  dump "In step_intro";;
  norm [];;
  forall_intro;;
  simplify_restrict;;
  implies_intro;;
  return ()

let step :tactic unit =
  dump "step";;
  step_bind              `or_else`
  step_read_write        `or_else`
  step_alloc_return      `or_else`
  step_eq_implies_intro  `or_else`
  step_eq_implies_intro' `or_else`
  step_intro             `or_else`
  fail "step: failed"

let simplify_select :tactic unit =
 dump "In simplify_select";;
 (apply_lemma (quote lemma_sel_r_join_tot_restrict_minus);; norm [])   `or_else`
 (apply_lemma (quote lemma_sel_r_join_tot_points_to_minus);; norm [])  `or_else`
 (apply_lemma (quote lemma_sel_r1_join_tot_restrict_minus);; norm [])  `or_else`
 (apply_lemma (quote lemma_sel_r1_join_tot_points_to_minus);; norm []) `or_else`
 (apply_lemma (quote lemma_sel_join_tot_h_emp_with_next_addr);; norm [])              `or_else`
 (apply_lemma (quote lemma_sel_join_tot_emp_with_next_addr_h);; norm []);;
 simplify_contains

let step_select :tactic unit =
 apply_lemma (quote lemma_eq_cong);; 
 norm [];;
 simplify_select;;
 trytac trefl;;
 return ()

let rec repeat_step_select () :Tac unit =
  (g <-- trytac cur_goal;
  begin match g with
  | None -> return ()
  | Some _ -> repeat step_select;;
              dump "After repeat simplify_sel";;
              trytac ((trefl;; qed) `or_else` smt);;
              repeat_step_select
  end
  ) ()

let simplify :tactic unit =
 split_all;;
 repeat_step_select;;
 return ()

let solve :tactic unit =
 norm [delta; delta_only unfold_steps; primops];;
 trytac implies_intros';;
 dump "Initial goal";;
 repeat step;;
 simplify;;
 dump "End"

(***** Examples *****)
open FStar.UInt
open FStar.UInt64

type t = UInt64.t

let write_ok (h:heap) (r:addr) (n:t) =
  let c = (Write r n) in
  let p = fun _ h -> sel h r == n in
  let post = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (h `contains` r ==> post) solve

let increment_ok (h:heap) (r:addr) (n:t) =
  let c = Bind (Read r) (fun n -> Write r (n +?^ 1uL)) in
  let p = fun _ h -> (sel h r == n +?^ 1uL) in
  let post = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (h `contains` r /\ sel h r == n ==> post) solve

let swap_ok (r1:addr) (r2:addr) (h:heap) (a:t) (b:t) =
  let c = Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1))) in
  let p = fun _ h -> (sel h r1 == b /\ sel h r2 == a) in
  let post = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (h `contains` r1 /\  h `contains` r2 /\ addr_of r1 <> addr_of r2 /\ sel h r1 == a /\ sel h r2 == b ==> post) solve

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
  assert_by_tactic (h `contains` r1 /\ h `contains` r2 /\ h `contains` r3 /\ addr_of r1 <> addr_of r2 /\ addr_of r2 <> addr_of r3 /\ addr_of r1 <> addr_of r3 /\ sel h r1 == i /\ sel h r2 == j /\ sel h r3 == k ==> post) solve
