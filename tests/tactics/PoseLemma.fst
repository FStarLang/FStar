module PoseLemma

open FStar.Tactics

assume val pred : int -> int -> Type0
assume val lem1 : x:int -> y:int -> Lemma (requires (x < 0)) (ensures (pred x y))
assume val lem2 : x:int -> y:int -> Lemma (requires True) (ensures (pred x y))

let test1 (x:int) =
  assert (pred x 2)
      by (let _ = pose_lemma (`lem2 (`@x) 2) in
          ())

let test2 (x:int) (h : squash (x < 0)) =
  assert (pred x 2)
      by (let _ = pose_lemma (`lem1 (`@x) 2) in
          exact (quote h);
          ())
