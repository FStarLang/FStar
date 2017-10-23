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

let apply_lemma_norm (tm:tactic term) :tactic unit = 
  apply_lemma (tm);;
  norm []

let apply_lemma_qed (tm:tactic term) :tactic unit =
  apply_lemma (tm);;
  qed

let step_read_write :tactic unit =
  apply_lemma_norm (quote lemma_read_write)

let step_alloc_return :tactic unit =
  apply_lemma_norm (quote lemma_alloc_return)

let step_exists_subheaps :tactic unit =
  apply_lemma_norm (quote lemma_destruct_exists_subheaps)

let step_intros :tactic unit =
  forall_intros;;
  implies_intro;;
  idtac

let step :tactic unit =
  step_exists_subheaps              `or_else`
  (step_read_write;; step_intros)   `or_else`
  (step_alloc_return;; step_intros) `or_else`
  step_read_write                   `or_else`
  step_alloc_return                 `or_else`
  fail "step: failed"

let simplify :tactic unit =
  pointwise (
  apply_lemma_qed (quote lemma_join_h_emp)                      `or_else`
  apply_lemma_qed (quote lemma_join_restrict_minus)             `or_else`
  apply_lemma_qed (quote lemma_restrict_points_to_join_h_to_r)  `or_else`
  apply_lemma_qed (quote lemma_restrict_points_to_join_h_to_r1) `or_else`
  apply_lemma_qed (quote lemma_sel_r_from_points_to_join_h)     `or_else`
  apply_lemma_qed (quote lemma_sel_r1_from_points_to_join_h)    `or_else`
  apply_lemma_qed (quote lemma_sel_r_from_minus)                `or_else`
  trefl);;
  idtac

let simplify_context :tactic unit =
  e <-- cur_env;
  mapM (fun b ->
    let typ_b = type_of_binder b in
    begin match term_as_formula' typ_b with
    | Comp Eq _ _ _ -> 
        binder_retype b;;
        simplify;;
        trefl
    | _             -> 
        idtac
    end
  ) (binders_of_env e);;
  idtac

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
  idtac

let context_rewrites :tactic unit =
  e <-- cur_env;
  mapM (fun b ->
    let typ_b = type_of_binder b in
    match term_as_formula' typ_b with
    | Comp Eq _ l r -> 
       begin match inspect l with
       | Tv_Var _  -> rewrite b
       | _         -> idtac
       end
    | _            -> idtac
  ) (binders_of_env e);;
  idtac

let reduce_context :tactic unit =
  simplify_context;;
  normalize_context;;
  context_rewrites

let rewrite_with_lemma (tm:tactic term) :tactic unit =
  pointwise ((apply_lemma tm;; qed) `or_else` trefl);;
  idtac


(* Writing to a pointer *)
let write_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  step;;
  reduce_context;;
  rewrite_with_lemma (quote lemma_sel_r_from_points_to_join_h);;
  dump "Write";;
  smt

let write_ok (r:addr) (h:heap) (n:int) =
  let c = (Write r n) in
  let p = fun _ h -> sel h r == n in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic t write_tau

(* Incrementing a pointer *)
let increment_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  implies_intro;;
  repeat step;;
  reduce_context;;
  rewrite_with_lemma (quote lemma_sel_r_from_points_to_join_h);;
  dump "Increment";;
  smt

let increment_ok (r:addr) (h:heap) (n:int) =
  let c = Bind (Read r) (fun n -> Write r (n + 1)) in
  let p = fun _ h -> sel h r == (n + 1) in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r == n ==> t) increment_tau

(* Swapping two pointers *)
let swap_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  implies_intro;;
  repeat step;;
  reduce_context;;
  rewrite_with_lemma (quote lemma_join_h_emp);;
  rewrite_with_lemma (quote lemma_join_restrict_minus);;
  rewrite_with_lemma (quote lemma_sel_r_from_points_to_join_h);;
  rewrite_with_lemma (quote lemma_sel_r1_from_points_to_join_h);;
  rewrite_with_lemma (quote lemma_sel_r_from_minus);;
  rewrite_with_lemma (quote lemma_sel_r_from_points_to_join_h);;
  dump "Swap";;
  smt

let swap_ok (r1:addr) (r2:addr) (h:heap) (a:int) (b:int) =
  let c = Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1))) in
  let p = fun _ h -> sel h r1 == b /\ sel h r2 == a in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r1 == a /\ sel h r2 == b ==> t) swap_tau

(* Double increment a pointer *)
let double_increment_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  implies_intro;;
  repeat step;;
  reduce_context;;
  rewrite_with_lemma (quote lemma_join_h_emp);;
  rewrite_with_lemma (quote lemma_join_restrict_minus);;
  rewrite_with_lemma (quote lemma_sel_r_from_points_to_join_h);;
  dump "Double increment";;
  smt

let double_increment_ok (r:addr) (h:heap) (n:int) =
  let c = Bind (Bind (Read r) (fun y -> Write r (y + 1))) (fun _ -> (Bind (Read r) (fun y -> Write r (y + 1))))  in
  let p = fun _ h -> sel h r == (n + 2) in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r == n ==> t) double_increment_tau

(* Rotate three pointers *)
let rotate_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  implies_intro;;
  repeat step;;
  reduce_context;;
  rewrite_with_lemma (quote lemma_join_h_emp);;
  rewrite_with_lemma (quote lemma_join_restrict_minus);;
  rewrite_with_lemma (quote lemma_sel_r_from_points_to_join_h);;
  rewrite_with_lemma (quote lemma_sel_r1_from_points_to_join_h);;
  rewrite_with_lemma (quote lemma_sel_r_from_minus);;
  rewrite_with_lemma (quote lemma_sel_r_from_points_to_join_h);;
  dump "Rotate";;
  smt

let rotate_ok (r1:addr) (r2:addr) (r3:addr) (h:heap) (i:int) (j:int) (k:int) =
  let c = Bind (Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1)))) (fun _ -> Bind (Read r2) (fun n3 -> Bind (Read r3) (fun n4 -> Bind (Write r2 n4) (fun _ -> Write r3 n3)))) in
  let p = fun _ h -> (sel h r2 == k) in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (addr_of r1 <> addr_of r2 /\ addr_of r2 <> addr_of r3 /\ addr_of r1 <> addr_of r3 /\ sel h r1 == i /\ sel h r2 == j /\ sel h r3 == k ==> t) rotate_tau

(* Initializing a fresh object *)
let init_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  repeat step;;
  reduce_context;;
  rewrite_with_lemma (quote lemma_join_h_emp);;
  rewrite_with_lemma (quote lemma_join_is_comm);;
  rewrite_with_lemma (quote lemma_join_h_emp);;
  rewrite_with_lemma (quote lemma_join_is_comm);;
  rewrite_with_lemma (quote lemma_sel_r_from_points_to_join_h);;
  dump "Init";;
  smt

let init_ok (h:heap) =
  let c = Bind (Alloc) (fun (r1:addr) -> Bind (Write r1 7) (fun _ -> Return r1)) in
  let p = fun r h -> sel h r == 7 in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic t init_tau

(* Copy a pointer *)
let copy_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  implies_intro;;
  repeat step;;
  reduce_context;;
  rewrite_with_lemma (quote lemma_join_h_emp);;
  rewrite_with_lemma (quote lemma_sel_r_from_points_to_join_h);;
  rewrite_with_lemma (quote lemma_sel_r1_from_points_to_join_h);;
  rewrite_with_lemma (quote lemma_join_restrict_minus);;
  rewrite_with_lemma (quote lemma_sel_r_from_minus);;
  dump "Copy"

let copy_ok (r1:addr) (r2:addr) (r3:addr) (h:heap) (i:int) (j:int) (k:int) =
  let c = Bind (Read r1) (fun n1 -> Write r2 (n1)) in
  let p = fun _ h -> (sel h r1 == i /\ sel h r2 == i /\ sel h r3 == k) in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r1 == i /\ sel h r2 == j /\ sel h r3 == k ==> t) copy_tau
