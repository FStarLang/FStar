module LemmaArgs

open FStar.Tactics

let lemma_example1 (a:int) (b:int{b <> a})
  :Lemma (requires True)
         (ensures b <> a)
  = ()

let example1 () : Lemma (ensures False) =
  assert_by_tactic (5 <> 5) (apply_lemma (quote lemma_example1))
