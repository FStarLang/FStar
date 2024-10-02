module Instantiate

open FStar.Tactics.V2

assume val pred : int -> Type0

let test_u_u (f : (forall x. pred x)) : Lemma (exists y. pred y) =
  assert (exists y. pred y)
      by (let _ = instantiate (quote f) (`1) in
          witness (`1))

let test_s_u (f : squash (forall x. pred x)) : Lemma (exists y. pred y) =
  assert (exists y. pred y)
      by (let _ = instantiate (quote f) (`1) in
          witness (`1))

let test_u_s (f : (forall x. pred x)) : Lemma (squash (exists y. pred y)) =
  assert (exists y. pred y)
      by (let _ = instantiate (quote f) (`1) in
          witness (`1))

let test_s_s (f : squash (forall x. pred x)) : Lemma (squash (exists y. pred y)) =
  assert (exists y. pred y)
      by (let _ = instantiate (quote f) (`1) in
          witness (`1))
