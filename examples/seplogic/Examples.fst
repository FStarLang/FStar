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
  apply_lemma (quote lemma_read_write);;
  norm []

let step_alloc_return :tactic unit =
  apply_lemma (quote lemma_alloc_return);;
  norm []

let step_exists_subheaps :tactic unit =
  apply_lemma (quote lemma_destruct_exists_subheaps);;
  norm []

let step_implies_intro_equality :tactic unit =
  apply_lemma (quote lemma_implies_intro_equality);;
  norm []
  
let normalize_context :tactic unit =
  e <-- cur_env;
  mapM (fun b ->
    let typ_b = type_of_binder b in
    begin match term_as_formula' typ_b with
    | App _ _ ->
        norm_binder_type [] b;;
	idtac
    | _       ->
        idtac
    end
  ) (binders_of_env e);;
  return ()

let simplify :tactic unit =
  pointwise ((apply_lemma (quote lemma_join_h_emp);; qed)
  `or_else`  (apply_lemma (quote lemma_join_points_to_minus);; qed)
  `or_else`  (apply_lemma (quote lemma_join_restrict_minus);; qed)
  `or_else`  (apply_lemma (quote lemma_sel_r_update);; qed)
  `or_else`  (apply_lemma (quote lemma_sel_r1_update);; qed)
  `or_else`  (apply_lemma (quote lemma_restrict_r_update);; qed)
  `or_else`  (apply_lemma (quote lemma_restrict_r1_update);; qed)
  `or_else`  (apply_lemma (quote lemma_join_emp_h);; qed)
  `or_else`  (apply_lemma (quote lemma_implies_intro_equality);; qed)
  `or_else`   fail "")

let rec repeat_simplify () :Tac unit =
 ( g1 <-- cur_goal;
   simplify;;
   g2 <-- cur_goal;
   if term_eq g1 g2
   then return ()
   else repeat_simplify
 ) ()

let implies_intro' :tactic unit =
  b <-- implies_intro;
  binder_retype b;;
  simplify;;
  trefl;;
  normalize_context

let step_intros :tactic unit =
  forall_intros;;
  implies_intro';;
  idtac

let step :tactic unit =
  step_exists_subheaps              `or_else`
  (step_read_write;; step_implies_intro_equality) `or_else`
  (step_alloc_return;; step_implies_intro_equality) `or_else`
  (step_read_write;; step_intros)   `or_else`
  (step_alloc_return;; step_intros) `or_else`
  step_read_write                   `or_else`
  step_alloc_return                 `or_else`
  fail "step: failed"

let solve :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  dump "Initial goal";;
  trytac implies_intro;;
  repeat step;;
  //repeat_simplify;;
  dump "Final goal"
  

(***** Examples *****)

type t = FStar.SepLogic.Heap.t

open FStar.UInt
open FStar.UInt64

open FStar.Tactics.BV

let write_ok (r:addr) (h:heap) (n:t) =
  let c = (Write r n) in
  let p = fun _ h -> v (sel h r) == v n in
  let post = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic post (solve;; (* to_bv_tac ();; *) simplify;; apply_lemma (quote lemma_sel_r_update);; qed)  //Question for Monal: when we do a second simplify, it doesn't reduce ... why? the lemma_sel_r_update should apply as part of simplify. Second question, the (repeat_simplify) tactic loops :(.

// let increment_ok (r:addr) (h:heap) (n:t) =
//   let c = Bind (Read r) (fun n -> Write r (n +?^ 1uL)) in
//   let p = fun _ h -> sel h r == (n +?^ 1uL) in
//   let post = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (sel h r == n ==> post) solve

// let swap_ok (r1:addr) (r2:addr) (h:heap) (a:t) (b:t) =
//   let c = Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1))) in
//   let p = fun _ h -> sel h r1 == b /\ sel h r2 == a in
//   let t = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (sel h r1 == a /\ sel h r2 == b ==> t) solve

// let double_increment_ok (r:addr) (h:heap) (n:t{size (v n + 2) FStar.UInt64.n}) =
//   let c = Bind (Bind (Read r) (fun y -> Write r (y +?^ 1uL))) (fun _ -> (Bind (Read r) (fun y -> Write r (y +?^ 1uL))))  in
//   let p = fun _ h -> sel h r == (n +?^ 2uL) in
//   let t = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (sel h r == n ==> t) solve

// let rotate_ok (r1:addr) (r2:addr) (r3:addr) (h:heap) (i:t) (j:t) (k:t) =
//   let c = Bind (Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1)))) (fun _ -> Bind (Read r2) (fun n3 -> Bind (Read r3) (fun n4 -> Bind (Write r2 n4) (fun _ -> Write r3 n3)))) in
//   let p = fun _ h -> (sel h r1 == j /\ sel h r2 == k /\ sel h r3 == i) in
//   let t = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (addr_of r1 <> addr_of r2 /\ addr_of r2 <> addr_of r3 /\ addr_of r1 <> addr_of r3 /\ sel h r1 == i /\ sel h r2 == j /\ sel h r3 == k ==> t) solve

// let init_ok (h:heap) =
//   let c = Bind (Alloc) (fun (r1:addr) -> Bind (Write r1 7uL) (fun _ -> Return r1)) in
//   let p = fun r h -> sel h r == 7uL in
//   let t = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic t (solve;; trefl;; qed)  //no need to go to smt!

// let copy_ok (r1:addr) (r2:addr) (r3:addr) (h:heap) (i:t) (j:t) (k:t) =
//   let c = Bind (Read r1) (fun n1 -> Write r2 (n1)) in
//   let p = fun _ h -> (sel h r1 == i /\ sel h r2 == i /\ sel h r3 == k) in
//   let post = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (sel h r1 == i /\ sel h r2 == j /\ sel h r3 == k ==> post) solve //here how can we apply a binder?

// (* Writing to a pointer *)
// let write_tau :tactic unit =
//   norm [delta; delta_only unfold_steps; primops];;
//   step;;
//   //repeat_simplify_context;;
//   repeat_simplify;;
//   dump "Write"

// (* Incrementing a pointer *)
// let increment_tau :tactic unit =
//   norm [delta; delta_only unfold_steps; primops];;
//   implies_intro;;
//   repeat step;;
//   //repeat_simplify_context;;
//   repeat_simplify;;
//   dump "Increment"

// (* Swapping two pointers *)
// let swap_tau :tactic unit =
//   norm [delta; delta_only unfold_steps; primops];;
//   implies_intro;;
//   repeat step;;
//   //repeat_simplify_context;;
//   repeat_simplify;;
//   dump "Swap"

// (* Double increment a pointer *)
// let double_increment_tau :tactic unit =
//   norm [delta; delta_only unfold_steps; primops];;
//   implies_intro;;
//   repeat step;;
//   //repeat_simplify_context;;
//   repeat_simplify;;
//   dump "Double Increment"

// (* Rotate three pointers *)
// let rotate_tau :tactic unit =
//   norm [delta; delta_only unfold_steps; primops];;
//   implies_intro;;
//   repeat step;;
//   //repeat_simplify_context;;
//   repeat_simplify;;
//   dump "Rotate"

// let swap_ok (r1:addr) (r2:addr) (h:heap) (a:int) (b:int) =
//   let c = Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1))) in
//   let p = fun _ h -> sel h r1 == b /\ sel h r2 == a in
//   let t = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (sel h r1 == a /\ sel h r2 == b ==> t) (
//     norm [delta; delta_only unfold_steps; primops];;
//     implies_intro;;
//     apply_lemma (quote lemma_destruct_exists_subheaps);;
//     norm [];;
//     apply_lemma (quote lemma_read_write);;
//     norm [];;
//     forall_intro;;
//     implies_intro;;
//     apply_lemma (quote lemma_destruct_exists_subheaps);;
//     norm [];;
//     apply_lemma (quote lemma_read_write);;
//     norm [];;
//     forall_intro;;
//     b <-- implies_intro;
//     binder_retype b;;
//     simplify;;
//     trefl;;
//     normalize_context;;
//     apply_lemma (quote lemma_destruct_exists_subheaps);;
//     norm [];;
//     apply_lemma (quote lemma_read_write);;
//     norm [];;
//     apply_lemma (quote lemma_implies_intro_equality);;
//     norm [];;
//     apply_lemma (quote lemma_read_write);;
//     norm [];;
//     apply_lemma (quote lemma_implies_intro_equality);;
//     norm [];;
//     repeat_simplify
// )

// let context_rewrites :tactic unit =
//   e <-- cur_env;
//   mapM (fun b ->
//     let typ_b = type_of_binder b in
//     match term_as_formula' typ_b with
//     | Comp Eq _ l r ->
//        begin match inspect l with
//        | Tv_Var _  -> rewrite b
//        | _         -> idtac
//        end
//     | _            -> idtac
//   ) (binders_of_env e);;
//   idtac

// let simplify_context :tactic unit =
//   e <-- cur_env;
//   mapM (fun b ->
//     let typ_b = type_of_binder b in
//     begin match term_as_formula' typ_b with
//     | Comp Eq _ _ _ ->
//         binder_retype b;;
//         simplify;;
//         trefl
//     | _             ->
//         idtac
//     end
//   ) (binders_of_env e);;
//   idtac

// let reduce_context :tactic unit =
//   simplify_context;;
//   normalize_context;;
//   context_rewrites

// let rec repeat_simplify_context () :Tac unit =
//  (e1 <-- cur_env;
//   reduce_context;;
//   e2 <-- cur_env;
//   let binders_of_e1 = binders_of_env e1 in
//   let binders_of_e2 = binders_of_env e2 in
//   if List.Tot.length binders_of_e1 = List.Tot.length binders_of_e2
//   then (if List.Tot.fold_left2 (fun acc b1 b2 -> acc && term_eq (type_of_binder b1) (type_of_binder b2))
//                                true
// 			       (binders_of_e1)
// 			       (binders_of_e2)
//        then return ()
//        else repeat_simplify_context)
//   else fail "repeat_simplify_context: binders length vary"
//  ) ()

// (* Initializing a fresh object *)
// let init_tau :tactic unit =
//   norm [delta; delta_only unfold_steps; primops];;
//   repeat step;;
//   //repeat_simplify_context;;
//   repeat_simplify;;
//   dump "Init"

// (* Copy a pointer *)
// let copy_tau :tactic unit =
//   norm [delta; delta_only unfold_steps; primops];;
//   implies_intro;;
//   repeat step;;
//   //repeat_simplify_context;;
//   repeat_simplify;;
//   dump "Copy"

