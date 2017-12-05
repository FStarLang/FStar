module Test

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
  or_else assumption''
          ((apply_lemma (quote lemma_contains_r_join_restrict_minus);; norm []) `or_else`
	   (apply_lemma (quote lemma_contains_join_h_emp);; norm [])            `or_else`
	   (apply_lemma (quote lemma_contains_r_join_points_to_minus);; norm []))

let simplify_contains :tactic unit =
  repeat simplify_contains_aux;;
  return ()

let simplify_disjoint :tactic unit =
  norm [];;
  (apply_lemma (quote lemma_disjoint_restrict_minus);; norm [])  `or_else`
  (apply_lemma (quote lemma_disjoint_points_to_minus);; norm []) `or_else`
  (apply_lemma (quote lemma_emp_disjoint);; norm []);;
  simplify_contains

let simplify_restrict_aux :tactic unit =
  (apply_lemma (quote lemma_eq_l_cong);; norm []);;
  (apply_lemma (quote lemma_restrict_join_h_emp);; norm []) `or_else`
  (apply_lemma (quote lemma_restrict_r_join_points_to_minus);; norm []);;
  simplify_contains

let simplify_restrict :tactic unit =
  repeat simplify_restrict_aux;;
  trytac trefl;;
  return ()

let step_bind :tactic unit = 
  apply_lemma (quote lemma_bind);;
  norm []

let step_read_write :tactic unit = 
  apply_lemma (quote lemma_read_write);; 
  norm [];;
  simplify_contains

let step_extract_disjoint :tactic unit =
  apply_lemma (quote lemma_extract_disjoint);;
  norm [];;
  simplify_disjoint

let step_eq_implies_intro :tactic unit =
  dump "In step_eq_implies_intro";;
  apply_lemma (quote lemma_eq_implies_intro);;
  dump "After lemma_eq_implies_intro";;
  norm [];;
  dump "After norm";;
  g <-- cur_goal;
  print (formula_to_string (term_as_formula g));;
  split;;
  dump "After split";;
  print "After split";;
  g <-- cur_goal;
  print (formula_to_string (term_as_formula g));;
  simplify_disjoint;;
  dump "After simplify_disjoint"

let step_intro :tactic unit =
  norm [];;
  forall_intro;;
  simplify_restrict;;
  implies_intro;;
  return ()

(***** Examples *****)
open FStar.UInt
open FStar.UInt64

type t = UInt64.t


let double_increment_ok (r:addr) (h:heap) (n:t{size (v n + 2) FStar.UInt64.n}) =
  let c = Bind (Bind (Read r) (fun y -> Write r (y +?^ 1uL))) (fun _ -> (Bind (Read r) (fun y -> Write r (y +?^ 1uL))))  in
  let p = fun _ h -> sel h r == (n +?^ 2uL) in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (h `contains` r /\ sel h r == n ==> t) (
    norm [delta; delta_only unfold_steps; primops];;
    trytac implies_intros';;
    dump "Initial goal";;
    step_bind;;
    step_bind;;
    step_read_write;;
    step_intro;;
    step_extract_disjoint;;
    step_read_write;;
    step_eq_implies_intro;;
    step_extract_disjoint;;
    step_bind;;
    step_read_write;;
    step_intro;;
    step_extract_disjoint;;
    step_read_write;;
    dump "See from here";;
    step_eq_implies_intro;;
    fail "End: double_increment_ok"
  )
