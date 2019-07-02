module Instantiate

open FStar.Tactics

assume val pred : int -> Type0

let test (f : (forall x. pred x)) : Lemma (exists y. pred y) =
  assert (exists y. pred y)
      by (let _ = instantiate (quote f) (`1) in
          witness (`1))
