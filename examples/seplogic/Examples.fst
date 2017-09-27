module Examples

open Lang
open FStar.SepLogic.Heap

open FStar.Tactics

#reset-options "--z3rlimit 5"

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

let step :tactic unit =
  (apply_lemma (quote lemma_destruct_exists_subheaps);; norm[])                              `or_else`
  (apply_lemma (quote lemma_read_write);; norm [];; forall_intro;; implies_intro;; idtac)    `or_else`
  (apply_lemma (quote lemma_alloc_return);; norm [];; forall_intros;; implies_intro;; idtac) `or_else`
  (apply_lemma (quote lemma_read_write);; norm [])                                           `or_else`
  (apply_lemma (quote lemma_alloc_return);; norm [])                                         `or_else`
  idtac

let context_rewrites :tactic unit =
  e <-- cur_env;
  mapM (fun b ->
    let typ_b = type_of_binder b in
    match term_as_formula' typ_b with
    | Comp Eq _ lhs _ -> 
       begin match inspect lhs with
       | Tv_Var _     -> rewrite b
       | _            -> idtac
       end
    | _               -> idtac
  ) (binders_of_env e);;
  idtac

(* Writing to a pointer *)
let write_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  step;;
  context_rewrites;;
  pointwise (or_else (apply_lemma (quote lemma4);; qed) trefl);;
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
  step;;
  step;;
  step;;
  pointwise (or_else (apply_lemma (quote lemma0);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma6);; qed) trefl);;
  context_rewrites;;
  pointwise (or_else (apply_lemma (quote lemma4);; qed) trefl);;
  dump "Increment"

#set-options "--initial_fuel 2 --initial_ifuel 2 --max_fuel 2 --max_ifuel 2" 
let increment_ok (r:addr) (h:heap) (n:int) =
  let c = Bind (Read r) (fun n -> Write r (n + 1)) in
  let p = fun _ h -> sel h r == (n + 1) in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r == n ==> t) increment_tau

(* Swapping two pointers *)
let swap_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  implies_intro;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  pointwise (or_else (apply_lemma (quote lemma0);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma6);; qed) trefl);;
  context_rewrites;;
  pointwise (or_else (apply_lemma (quote lemma4);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma5);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma9);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma4);; qed) trefl);;
  dump "Swap";;
  smt

let swap_ok (r1:addr) (r2:addr) (h:heap) (a:int) (b:int) =
  let c = Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1))) in
  let p = fun _ h -> sel h r1 == b /\ sel h r2 == a in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (addr_of r1 <> addr_of r2 /\ sel h r1 == a /\ sel h r2 == b ==> t) swap_tau

(* Double increment a pointer *)
let double_increment_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  implies_intro;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  pointwise (or_else (apply_lemma (quote lemma0);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma6);; qed) trefl);;
  context_rewrites;;
  pointwise (or_else (apply_lemma (quote lemma4);; qed) trefl);;
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
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  pointwise (or_else (apply_lemma (quote lemma0);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma6);; qed) trefl);;
  context_rewrites;;
  pointwise (or_else (apply_lemma (quote lemma4);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma5);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma9);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma4);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma5);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma9);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma5);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma9);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma4);; qed) trefl);;
  fail "Rotate"

// let rotate_ok (r1:addr) (r2:addr) (r3:addr) (h:heap) (i:int) (j:int) (k:int) =
//   let c = Bind (Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1)))) (fun _ -> Bind (Read r2) (fun n3 -> Bind (Read r3) (fun n4 -> Bind (Write r2 n4) (fun _ -> Write r3 n3)))) in
//   let p = fun _ h -> (sel h r1 == j /\ sel h r2 == k /\ sel h r3 == i) in
//   let t = (lift_wpsep (wpsep_command c)) p h in
//   assert_by_tactic (addr_of r1 <> addr_of r2 /\ addr_of r2 <> addr_of r3 /\ addr_of r1 <> addr_of r3 /\ sel h r1 == i /\ sel h r2 == j /\ sel h r3 == k ==> t) rotate_tau

(* Initializing a fresh object *)
let init_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  step;;
  step;;
  step;;
  step;;
  step;;
  pointwise (or_else (apply_lemma (quote lemma0);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma6);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma6');; qed) trefl);;
  context_rewrites;;
  pointwise (or_else (apply_lemma (quote lemma4);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma5);; qed) trefl);;
  pointwise (or_else (apply_lemma (quote lemma9);; qed) trefl);;
  dump "Init";;
  smt

let init_ok (h:heap) =
  let c = Bind (Alloc) (fun (r1:addr) -> Bind (Write r1 7) (fun _ -> Return r1)) in
  let p = fun r h -> sel h r == 7 in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic t init_tau
