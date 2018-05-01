module LemmaArgs

open FStar.Tactics

let lemma_example1 (a:int) (b:int{b <> a})
  :Lemma (requires True)
         (ensures b <> a)
  = ()

[@(fail_errs [19])]
let example1 () : Lemma (ensures False) =
  assert_by_tactic (5 <> 5) (fun () -> apply_lemma (quote lemma_example1))
