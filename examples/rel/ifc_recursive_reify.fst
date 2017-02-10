module Ifc_Recursive_Reify

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed
open Rel

reifiable val p1 (lo hi :id ): n:int -> IS unit (decreases n)
reifiable let rec p1 lo hi n  =
  if n > 0 then
    (write hi (read hi -1);
    p1 lo hi (n-1))


(*
let p1_r lo hi h = (* normalize_term *) (snd (reify (p1 lo hi) h))

val ni_p1 (lo hi : id) (env:env) (h :rel heap) :
  Lemma
  (requires (lo <> hi /\
            Low? (env lo) /\
            High? (env hi) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p1_r lo hi (R?.l h)) (p1_r lo hi (R?.r h)))))
let ni_p1 lo hi env h = ()
*)
