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
  (apply_lemma (quote lemma_destruct_exists_subheaps);; norm[]) `or_else`
  (apply_lemma (quote lemma_read_write);; norm [])              `or_else`
  (apply_lemma (quote lemma_alloc_return);; norm [])            `or_else`
  (implies_intro;; idtac)                                       `or_else`
  (forall_intro;; idtac)                                        `or_else`
  idtac

(* Writing to a pointer *)
let write_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  step

let write_ok (r:addr) (h:heap) (x:int) =
  let c = (Write r x) in
  let p = fun _ h -> sel h r == x in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic t write_tau

(* Incrementing a pointer *)
let increment_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  step;;
  smt

let increment_ok (r:addr) (h:heap) (x:int) =
  let c = Bind (Read r) (fun n -> Write r (n + 1)) in
  let p = fun _ h -> sel h r == (x + 1) in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r == x ==> t) increment_tau

(* Swapping two pointers *)
let swap_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
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
  step;;
  smt

let swap_ok (r1:addr) (r2:addr) (h:heap) (x:int) (y:int) =
  let c = Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1))) in
  let p = fun _ h -> sel h r1 == x /\ sel h r2 == y in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r1 == y /\ sel h r2 == x ==> t) swap_tau

(* Rotate three pointers *)
let rotate_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  fail "Foo"

let rotate_ok (r1:addr) (r2:addr) (r3:addr) (h:heap) (x:int) (y:int) (z:int) =
  let swap1 = Bind (Read r1) (fun n1 -> Bind (Read r2) (fun n2 -> Bind (Write r1 n2) (fun _ -> Write r2 n1))) in
  let swap2 = Bind (Read r2) (fun n3 -> Bind (Read r3) (fun n4 -> Bind (Write r2 n4) (fun _ -> Write r1 n3))) in
  let c = Bind swap1 (fun _ -> swap2) in
  let p = fun _ h -> sel h r1 == y /\ sel h r2 == z /\ sel h r3 == x in 
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r1 == x /\ sel h r2 == y /\ sel h r2 == z ==> t) rotate_tau
