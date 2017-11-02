module Examples

open Lang
open FStar.SepLogic.Heap

open FStar.Tactics

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

let step_read_write :tactic unit =
  apply_lemma (quote lemma_read_write);; norm []

let step_alloc_return :tactic unit =
  apply_lemma (quote lemma_alloc_return);; norm []

let step_bind :tactic unit =
  apply_lemma (quote lemma_bind);; norm []

let step_implies_intro_equality :tactic unit =
  apply_lemma (quote lemma_implies_intro_equality);; norm []

// Note - If pointwise fails when one of its subgoals fails, then update this to use trefl instead of fail
let simplify_join_h_emp :tactic unit =
  pointwise ((apply_lemma (quote lemma_join_h_emp);; qed) `or_else` fail "")

let simplify_context :tactic unit =
  pointwise ((apply_lemma (quote lemma_join_points_to_minus);; qed)
  `or_else`  (apply_lemma (quote lemma_join_restrict_minus);; qed)
  `or_else`  (apply_lemma (quote lemma_restrict_r_update);; qed)
  `or_else`  (apply_lemma (quote lemma_restrict_r1_update);; qed)
  `or_else`  (apply_lemma (quote lemma_join_emp_h);; qed)
  `or_else`   fail "simplify_context: failed")
  
let simplify_goal :tactic unit =
  pointwise ((apply_lemma (quote lemma_join_points_to_minus);; qed)
  `or_else`  (apply_lemma (quote lemma_join_restrict_minus);; qed)
  `or_else`  (apply_lemma (quote lemma_sel_r_update);; qed)
  `or_else`  (apply_lemma (quote lemma_sel_r1_update);; qed)
  `or_else`  (apply_lemma (quote lemma_restrict_r_update);; qed)
  `or_else`  (apply_lemma (quote lemma_restrict_r1_update);; qed)
  `or_else`  (apply_lemma (quote lemma_join_emp_h);; qed)
  `or_else`  (apply_lemma (quote lemma_sel_r1_from_restrict);; qed)
  `or_else`  (apply_lemma (quote lemma_sel_r_from_minus);; qed)
  `or_else`   fail "simplify_goal: failed")

let rec repeat_simplify_goal () :Tac unit =
  (g1 <-- cur_goal; simplify_goal;; g2 <-- cur_goal;
   if term_eq g1 g2 
   then return () 
   else repeat_simplify_goal
  ) ()

let repeat_simplify :tactic unit =
  simplify_join_h_emp;; repeat_simplify_goal

let rec repeat_simplify' () :Tac unit =
  (g1 <-- cur_goal; simplify_goal;; g2 <-- cur_goal;
    begin match (term_as_formula' g1, term_as_formula' g2) with
    | App _ t1, App _ t2 -> 
       begin match (term_as_formula' t1, term_as_formula' t2) with
       | (Iff l1 _, Iff l2 _) -> if term_eq l1 l2
                                 then return ()
                         	 else repeat_simplify'
       | _                    -> return ()				 
       end
    | _                  -> return ()
    end
   ) ()

let step_intros :tactic unit =
  forall_intros;;
  apply_lemma (quote lemma_impl_l_cong);;
  simplify_join_h_emp;;
  repeat_simplify';;
  apply_lemma (quote lemma_refl);;
  implies_intro;;
  return ()

let step :tactic unit =
  step_bind                   `or_else`
  step_read_write             `or_else`
  step_alloc_return           `or_else`
  step_implies_intro_equality `or_else`
  step_intros                 `or_else`
  fail "step: failed"

let solve :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  dump "Initial goal";;
  trytac implies_intro;;
  repeat step;;
  simplify_join_h_emp;;
  repeat_simplify;;
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
  assert_by_tactic (sel h r1 == a /\ sel h r2 == b ==> t) solve

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
  assert_by_tactic t (solve;; trefl;; qed)  //no need to go to smt!

let copy_ok (r1:addr) (r2:addr) (r3:addr) (h:heap) (i:t) (j:t) (k:t) =
  let c = Bind (Read r1) (fun n1 -> Write r2 (n1)) in
  let p = fun _ h -> (sel h r1 == i /\ sel h r2 == i /\ sel h r3 == k) in
  let post = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r1 == i /\ sel h r2 == j /\ sel h r3 == k ==> post) solve //here how can we apply a binder?
