module RewriteInArrow

module Tac = FStar.Tactics

let lemma_one_is_two (): Lemma (1 == 2) = admit ()

let lemma_revert_ok (x: nat) (some_evidence: squash (x == 1)): unit =
  assert (1 == 2) by (Tac.revert (); Tac.l_to_r [(`lemma_one_is_two)]; let _ = Tac.intro () in ())

(* This case of dependent binders was causing issues in ctrl_rewrite *)
let dependent_binders =
  assert (let id = fun (a: Type) (x: a) -> x in id Type0 True)
    by (Tac.pointwise (fun () -> Tac.trefl ()))
