module ElimExists

open FStar.Tactics

assume val pred : nat -> Type0

let lem (h : (exists x. x > 0 /\ pred x)) : Lemma (exists x. pred x /\ x > 0) =
  assert (exists x. pred x /\ x > 0)
      by (let x, pf = elim_exists (quote h) in
          witness (binder_to_term x);
          smt ())
