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

(* Writing to a pointer *)
let write_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  apply_lemma (quote lemma_read_write)

let write_ok (r:addr) (h:heap) =
  let c = (Write r 3) in
  let p = fun _ h -> sel h r == 3 in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic t write_tau

let increment_tau :tactic unit =
  norm [delta; delta_only unfold_steps; primops];;
  implies_intro;;
  apply_lemma (quote lemma_destruct_exists_subheaps);;
  apply_lemma (quote lemma_read_write);;
//  forall_intro;;
  fail "stop"

let increment_ok (r:addr) (h:heap) =
  let c = Bind (Read r) (fun n -> Write r (n + 1)) in
  let p = fun _ h -> sel h r == 4 in
  let t = (lift_wpsep (wpsep_command c)) p h in
  assert_by_tactic (sel h r == 3 ==> t) increment_tau


  
  
  
  

  
