module LemmaArgs

open FStar.Tactics

let lemma_example1 (a:int) (b:int{b <> a})
  :Lemma (requires True)
         (ensures b <> a)
  = ()

(* This one should work *)
let example0 x : Lemma (requires (x <> 5)) (ensures True) =
  assert_by_tactic (x <> 5) (fun () -> apply_lemma (quote lemma_example1))

[@(expect_failure [19])]
let example1 x : Lemma (requires (x == 5)) (ensures False) =
  assert_by_tactic (x <> 5) (fun () -> apply_lemma (quote lemma_example1))
