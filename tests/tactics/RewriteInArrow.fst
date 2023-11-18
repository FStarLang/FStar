module RewriteInArrow

module Tac = FStar.Tactics

#push-options "--debug TestBV64x --debug_level TacVerbose"

let lemma_one_is_two (): Lemma (1 == 2) = admit ()

let lemma_revert_ok (x: nat) (some_evidence: squash (x == 1)): unit =
  assert (1 == 2) by (Tac.revert (); Tac.l_to_r [(`lemma_one_is_two)]; let _ = Tac.intro () in ())
