module SL.Tactics

open FStar.SL.Heap
open Lang
open FStar.Tactics

(*
 * Separation logic tactics for manipulating wps of the deeply embedded languages of Lang
 *)

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

unfold let unfold_steps :list string =
  List.Tot.map (fun s -> "Lang." ^ s) unfold_fns

(*
 * If we have (p /\ q) ==> r, this tactic will push p and q, separately, into the context
 *)
private let and_elim' :tactic unit =
  h <-- implies_intro;  //introduce p /\ q in the context
  and_elim (pack (Tv_Var h));;  //split them into p and q
  clear h  //remove h from the context

(*
 * wrapper over implies_intros to split the hypotheses of the form (p /\ q)
 *)
private let implies_intros' :tactic unit =
  repeat and_elim';;
  implies_intros;;
  return ()

(*
 * To prove (squash p) from p in the context
 *)
private let assumption'  :tactic unit = 
  apply_raw (quote FStar.Squash.return_squash);; assumption

(*
 * If we have (p = q) in the context, and we want to prove the goal (q = p)
 * This is specifically for addrs
 *)
private let assumption'' :tactic unit = 
  or_else assumption' (apply_lemma (quote lemma_addr_not_eq_refl);; norm [];; assumption')

(*
 * Split a goal p1 /\ p2 ... /\ pn into n goals
 *)
private let rec split_all () :Tac unit =
  ( g <-- cur_goal;
    match (term_as_formula g) with
    | And _ _ -> split;; iseq [split_all; split_all]
    | _       -> return ()
  ) ()

(***** Tactics *****)

private let simplify_unused_in :tactic unit =
  apply_lemma (quote lemma_r_unused_in_minus) `or_else`
  apply_lemma (quote lemma_r_unused_in_h)     `or_else`
  return ()

private let simplify_contains_aux :tactic unit =
  assumption'' `or_else`
  apply_lemma (quote lemma_contains_r_join_tot_restrict_minus)     `or_else`
  apply_lemma (quote lemma_contains_r_join_tot_points_to_minus)    `or_else`
  apply_lemma (quote lemma_contains_r1_join_tot_restrict_minus)    `or_else`
  apply_lemma (quote lemma_contains_r1_join_tot_points_to_minus)   `or_else`
  apply_lemma (quote lemma_contains_join_tot_h_emp_with_next_addr) `or_else`
  apply_lemma (quote lemma_contains_r_points_to_unused_h);;
  split_all;;
  simplify_unused_in;;
  norm []

private let simplify_contains :tactic unit =
  repeat simplify_contains_aux;;
  return ()

private let simplify_restrict_aux :tactic unit =
  apply_lemma (quote lemma_eq_l_cong);; 
  norm [];;
  apply_lemma (quote lemma_restrict_r_join_tot_points_to_minus)  `or_else`
  apply_lemma (quote lemma_restrict_r_join_tot_restrict_minus)   `or_else`
  apply_lemma (quote lemma_restrict_r1_join_tot_restrict_minus)  `or_else`
  apply_lemma (quote lemma_restrict_r1_join_tot_points_to_minus) `or_else`
  apply_lemma (quote lemma_restrict_join_tot_h_emp_with_next_addr);;
  norm [];;
  simplify_contains

private let simplify_restrict :tactic unit =
  repeat simplify_restrict_aux;;
  trytac trefl;;
  return ()

(*
 * Command specific tactics to solve the frames
 *)
private let step_bind :tactic unit = 
  apply_lemma (quote lemma_bind);;
  norm []

(*
 * simplify_contains takes care of the contains clauses in the goals
 *)
private let step_read_write :tactic unit = 
  apply_lemma (quote lemma_read_write);;  //lemma_read_write is the one that solves the frame
  norm [];;
  simplify_contains

private let step_alloc_return :tactic unit =
  apply_lemma (quote lemma_alloc_return);;
  norm [];;
  simplify_contains

(*
 * Following tactics are not command specific
 *
 * They do some heap rewriting of the goal by looking up heap expressions in the context
 *)
private let step_eq_implies_intro :tactic unit =
  apply_lemma (quote lemma_eq_implies_intro);;
  norm []

private let step_eq_implies_intro' :tactic unit =
  forall_intro;;
  apply_lemma (quote lemma_eq_implies_intro');;
  norm [];;
  implies_intro;;
  return ()

private let step_intro :tactic unit =
  norm [];;
  forall_intro;;
  simplify_restrict;;
  implies_intro;;
  return ()

private let step :tactic unit =
  step_bind              `or_else`
  step_read_write        `or_else`
  step_alloc_return      `or_else`
  step_eq_implies_intro  `or_else`
  step_eq_implies_intro' `or_else`
  step_intro             `or_else`
  fail "step: failed"

(*
 * Given one sel goal, try to simplify the goal by applying a bunch of lemmas
 *)
private let simplify_select :tactic unit =
 apply_lemma (quote lemma_sel_r_join_tot_restrict_minus)     `or_else`
 apply_lemma (quote lemma_sel_r_join_tot_points_to_minus)    `or_else`
 apply_lemma (quote lemma_sel_r1_join_tot_restrict_minus)    `or_else`
 apply_lemma (quote lemma_sel_r1_join_tot_points_to_minus)   `or_else`
 apply_lemma (quote lemma_sel_join_tot_h_emp_with_next_addr) `or_else`
 apply_lemma (quote lemma_sel_join_tot_emp_with_next_addr_h);;
 simplify_contains

(*
 * Splits the sel goal into two subgoals, do simplify_select on the first subgoal
 *)
private let step_select :tactic unit =
 apply_lemma (quote lemma_eq_cong);; 
 norm [];;
 simplify_select;;
 trytac trefl;;
 return ()

private let rec repeat_step_select () :Tac unit =
  (g <-- trytac cur_goal;
  begin match g with
  | None -> return ()
  | Some _ -> repeat step_select;;
              trytac ((trefl;; qed) `or_else` smt);;
              repeat_step_select
  end
  ) ()

(*
 * Simplification is in the end, when we have solved all the frames, and are left with a sel goal
 *)
private let simplify :tactic unit =
 split_all;;
 repeat_step_select;;
 return ()

(*
 * This is the main tactic
 * Our strategy is to solve one command at a time, relying on the shape of wp
 * step tactic steps through the wp and tries each command specific tactic
 *)
let solve :tactic unit =
 norm [delta; delta_only unfold_steps; primops];;
 trytac implies_intros';;
 repeat step;;
 simplify
