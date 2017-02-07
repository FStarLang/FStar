module Ifc_Reify

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed
open Rel

type label =
| Low
| High

type env = id ->  Tot label

type low_equiv (env:env) (h : rel heap)  = 
  forall (x:id). (Low? (env x) ==> sel (R?.l h) x = sel (R?.r h) x)

reifiable let p1 x y hi = 
  if read hi = 0 then 
    write x (read x + read y) 
  else 
    write x (read x + read y + read hi);
  write x (read x - read hi);
  write x (read x);
  write x (read x)
  (* adding more copies of this line causes an extreme blow-up in verification
  time and RAM usage... related to #389? *)

let p1_r x y hi h = (* normalize_term *) (snd (reify (p1 x y hi) h))

val p1_x (x y hi : id) (h:heap) : 
  Lemma 
  (requires (x <> y /\ x <> hi /\ y <> hi))
  (ensures  (fun h' -> 
    (sel h' y = sel h y) /\ 
    (sel h' x = sel h x + sel h y) /\ 
    (sel h' hi = sel h hi))
    (p1_r x y hi h))
let p1_x x y hi h = ()

val ni_p1 (x y hi : id) (env:env) (h :rel heap) : 
  Lemma 
  (requires (x <> y /\ x <> hi /\ y <> hi /\
            Low? (env x) /\
            Low? (env y) /\
            High? (env hi) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p1_r x y hi (R?.l h)) (p1_r x y hi (R?.r h)))))
let ni_p1 x y hi env h = ()
