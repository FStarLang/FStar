module PoseLemma

open FStar.Tactics.V2

assume val pred : int -> int -> prop
assume val lem1 : x:int -> y:int -> Lemma (requires (x < 0)) (ensures (pred x y))
assume val lem2 : x:int -> y:int -> Lemma (requires True) (ensures (pred x y))

let test1 (x:int) =
  assert (pred x 2)
      by (let _ = pose_lemma (`lem2 (`@x) 2) in
          ())

(* [lem1]'s precondition is a trailing implicit argument of the application, so
   [pose_lemma] no longer cuts by it up front: [pose_apply] leaves it as a goal
   behind the main one, and SMT discharges it from [h] in the context. *)
let test2 (x:int) (h : squash (x < 0)) =
  assert (pred x 2)
      by (let _ = pose_lemma (`lem1 (`@x) 2) in
          ())
