module SL.Tactics

open FStar.SL.Heap
open Lang
open FStar.Tactics

(*
 * Separation logic tactics for manipulating wps of the deeply embedded languages of Lang
 *)

#reset-options "--using_facts_from '* -FStar.Tactics +FStar.Tactics.Result +FStar.Tactics.Types'"

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
private let and_elim' () : Tac unit =
  let h = implies_intro () in  //introduce p /\ q in the context
  and_elim (pack (Tv_Var (bv_of_binder h)));  //split them into p and q
  clear h  //remove h from the context

(*
 * wrapper over implies_intros to split the hypotheses of the form (p /\ q)
 *)
private let implies_intros' () : Tac unit =
  let _ = repeat and_elim' in
  let _ = implies_intros () in
  ()

(*
 * To prove (squash p) from p in the context
 *)
private let assumption' () : Tac unit =
  apply_raw (`FStar.Squash.return_squash);
  assumption ()

(*
 * If we have (p = q) in the context, and we want to prove the goal (q = p)
 * This is specifically for addrs
 *)
private let assumption'' () : Tac unit =
  or_else assumption'
          (fun () -> apply_lemma (`lemma_addr_not_eq_refl); norm []; assumption' ())

(*
 * Split a goal p1 /\ p2 ... /\ pn into n goals
 *)
private let rec split_all () : Tac unit =
  let g = cur_goal () in
  match (term_as_formula g) with
  | And _ _ -> split (); iseq [split_all; split_all]
  | _       -> ()

(***** Tactics *****)

private let simplify_unused_in () : Tac unit =
  first [(fun () -> apply_lemma (`lemma_r_unused_in_minus));
         (fun () -> apply_lemma (`lemma_r_unused_in_h));
         idtac]

private let simplify_contains_aux () :Tac unit =
  first [assumption'';
         (fun () -> apply_lemma (`lemma_contains_r_join_tot_restrict_minus));
         (fun () -> apply_lemma (`lemma_contains_r_join_tot_points_to_minus));
         (fun () -> apply_lemma (`lemma_contains_r1_join_tot_restrict_minus));
         (fun () -> apply_lemma (`lemma_contains_r1_join_tot_points_to_minus));
         (fun () -> apply_lemma (`lemma_contains_join_tot_h_emp_with_next_addr));
         (fun () -> apply_lemma (`lemma_contains_r_points_to_unused_h))];
  split_all ();
  simplify_unused_in ();
  norm []

private let simplify_contains () : Tac unit =
  let _ = repeat simplify_contains_aux in
  ()

private let simplify_restrict_aux () : Tac unit =
  apply_lemma (`lemma_eq_l_cong);
  norm [];
  first [(fun () -> apply_lemma (`lemma_restrict_r_join_tot_points_to_minus));
         (fun () -> apply_lemma (`lemma_restrict_r_join_tot_restrict_minus));
         (fun () -> apply_lemma (`lemma_restrict_r1_join_tot_restrict_minus));
         (fun () -> apply_lemma (`lemma_restrict_r1_join_tot_points_to_minus));
         (fun () -> apply_lemma (`lemma_restrict_join_tot_h_emp_with_next_addr))];
  norm [];
  simplify_contains ()

private let simplify_restrict () : Tac unit =
  let _ = repeat simplify_restrict_aux in
  let _ = trytac trefl in
  ()

(*
 * Command specific tactics to solve the frames
 *)
private let step_bind () : Tac unit =
  apply_lemma (`lemma_bind);
  norm []

(*
 * simplify_contains takes care of the contains clauses in the goals
 *)
private let step_read_write () : Tac unit =
  apply_lemma (`lemma_read_write);  //lemma_read_write is the one that solves the frame
  norm [];
  simplify_contains ()

private let step_alloc_return () : Tac unit =
  apply_lemma (`lemma_alloc_return);
  norm [];
  simplify_contains ()

(*
 * Following tactics are not command specific
 *
 * They do some heap rewriting of the goal by looking up heap expressions in the context
 *)
private let step_eq_implies_intro () : Tac unit =
  apply_lemma (`lemma_eq_implies_intro);
  norm []

private let step_eq_implies_intro' () : Tac unit =
  let _ = forall_intro () in
  apply_lemma (`lemma_eq_implies_intro');
  norm [];
  let _ = implies_intro () in
  ()

private let step_intro () : Tac unit =
  norm [];
  let _ = forall_intro () in
  simplify_restrict ();
  let _ = implies_intro () in
  ()

private let step () : Tac unit =
  first [step_bind;
         step_read_write;
         step_alloc_return;
         step_eq_implies_intro;
         step_eq_implies_intro';
         step_intro;
         fun () -> fail "step: failed"]

(*
 * Given one sel goal, try to simplify the goal by applying a bunch of lemmas
 *)
private let simplify_select () : Tac unit =
  first [(fun () -> apply_lemma (`lemma_sel_r_join_tot_restrict_minus));
         (fun () -> apply_lemma (`lemma_sel_r_join_tot_points_to_minus));
         (fun () -> apply_lemma (`lemma_sel_r1_join_tot_restrict_minus));
         (fun () -> apply_lemma (`lemma_sel_r1_join_tot_points_to_minus));
         (fun () -> apply_lemma (`lemma_sel_join_tot_h_emp_with_next_addr));
         (fun () -> apply_lemma (`lemma_sel_join_tot_emp_with_next_addr_h))];
  simplify_contains ()

(*
 * Splits the sel goal into two subgoals, do simplify_select on the first subgoal
 *)
private let step_select () : Tac unit =
 apply_lemma (`lemma_eq_cong);
 norm [];
 simplify_select ();
 let _ = trytac trefl in
 ()

private let rec repeat_step_select () :Tac unit =
  let g = trytac cur_goal in
  begin match g with
  | None -> ()
  | Some _ -> let _ = repeat step_select in
              let _ = trytac (fun () -> (fun () -> trefl (); qed ()) `or_else` smt) in
              repeat_step_select ()
  end

(*
 * Simplification is in the end, when we have solved all the frames, and are left with a sel goal
 *)
private let simplify () : Tac unit =
 split_all ();
 repeat_step_select ();
 ()

(*
 * This is the main tactic
 * Our strategy is to solve one command at a time, relying on the shape of wp
 * step tactic steps through the wp and tries each command specific tactic
 *)
let solve () : Tac unit =
 norm [delta; delta_only unfold_steps; primops];
 let _ = trytac implies_intros' in
 let _ = repeat step in
 simplify ()
