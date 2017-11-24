module Examples

open Lang
open FStar.SepLogic.Heap

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

let step_read_write       :tactic unit = apply_lemma (quote lemma_read_write);; norm []

let step_alloc_return     :tactic unit = apply_lemma (quote lemma_alloc_return);; norm []

let step_bind             :tactic unit = apply_lemma (quote lemma_bind);; norm []

let step_eq_implies_intro :tactic unit = apply_lemma (quote lemma_eq_implies_intro);; norm []

let assumption'  :tactic unit = 
  apply_raw (quote FStar.Squash.return_squash);;
  assumption

let assumption'' :tactic unit = 
  or_else assumption' 
          (apply_lemma (quote lemma_addr_not_eq_refl);; norm [];; assumption')

let step_restrict :tactic unit =
  or_else (apply_lemma (quote lemma_restrict_r_update))
          (apply_lemma (quote lemma_restrict_r1_update);; assumption'') 

let simplify_restrict :tactic unit =
  apply_lemma (quote lemma_eq_l_cong);;
  step_restrict;;
  trytac trefl;;
  return ()

let simplify_join_emp :tactic unit =
  pointwise (or_else (or_else (apply_lemma (quote lemma_join_h_emp);; qed) 
                              (apply_lemma (quote lemma_join_emp_h);; qed))
		     (fail "SKIP"))

let simplify_join_minus :tactic unit =
  pointwise (or_else (or_else (apply_lemma (quote lemma_join_points_to_minus);; qed)
                              (apply_lemma (quote lemma_join_restrict_minus);; qed))
		     (fail "SKIP"))

let simplify_join :tactic unit =
  apply_lemma (quote lemma_impl_l_cong);;
  simplify_join_emp;;
  simplify_join_minus;;
  apply_lemma (quote lemma_refl)


let step_intros :tactic unit =
  forall_intros;;
  simplify_join;;
  repeat simplify_restrict;;
  implies_intro;;
  return ()

let step :tactic unit =
  step_bind                   `or_else`
  step_read_write             `or_else`
  step_alloc_return           `or_else`
  step_eq_implies_intro       `or_else`
  step_intros                 `or_else`
  fail "step: failed"

let step_sel :tactic unit =
  (apply_lemma (quote lemma_sel_r_update))                        `or_else`
  (apply_lemma (quote lemma_sel_r1_update);; assumption'')        `or_else`
  (apply_lemma (quote lemma_sel_r1_from_restrict);; assumption'') `or_else`
  (apply_lemma (quote lemma_sel_r_from_minus);; assumption'')

let simplify_sel :tactic unit =
  apply_lemma (quote lemma_eq_cong);;
  step_sel;;
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
              trytac ((trefl;; qed) `or_else` smt);;
              repeat_simplify_sel
  end
  ) ()

let simplify_goals :tactic unit =
  simplify_join_emp;;
  simplify_join_minus;;
  trytac (repeat split);;
  repeat_simplify_sel;;
  return ()

let solve :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  dump "Initial goal";;
  trytac implies_intros';;
  repeat step;;
  simplify_goals;;
  dump "Final goal"

(***** Examples *****)

type t = FStar.SepLogic.Heap.t

open FStar.UInt
open FStar.UInt64

let write_ok (r:addr) (h:heap) (n:t) =
  let c = (Write r n) in
  let p = fun _ h -> sel h r == n in
  let post = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic post solve

let increment_ok (r:addr) (h:heap) (n:t) =
  let c = Bind (Read r) (fun n -> Write r (n +?^ 1uL)) in
  let p = fun _ h -> sel h r == (n +?^ 1uL) in
  let post = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r == n ==> post) solve

let swap_ok (r1:addr) (r2:addr) (h:heap) (a:t) (b:t) =
  let c = Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1))) in
  let p = fun _ h -> sel h r1 == b /\ sel h r2 == a in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (addr_of r1 <> addr_of r2 /\ sel h r1 == a /\ sel h r2 == b ==> t) solve

let double_increment_ok (r:addr) (h:heap) (n:t{size (v n + 2) FStar.UInt64.n}) =
  let c = Bind (Bind (Read r) (fun y -> Write r (y +?^ 1uL))) (fun _ -> (Bind (Read r) (fun y -> Write r (y +?^ 1uL))))  in
  let p = fun _ h -> sel h r == (n +?^ 2uL) in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r == n ==> t) solve

let rotate_ok (r1:addr) (r2:addr) (r3:addr) (h:heap) (i:t) (j:t) (k:t) =
  let c = Bind (Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1)))) (fun _ -> Bind (Read r2) (fun n3 -> Bind (Read r3) (fun n4 -> Bind (Write r2 n4) (fun _ -> Write r3 n3)))) in
  let p = fun _ h -> (sel h r1 == j /\ sel h r2 == k /\ sel h r3 == i) in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (addr_of r1 <> addr_of r2 /\ addr_of r2 <> addr_of r3 /\ addr_of r1 <> addr_of r3 /\ sel h r1 == i /\ sel h r2 == j /\ sel h r3 == k ==> t) solve

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
