module Ifc_Reify_Long

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed
open Rel

type label =
| Low
| High

type env = id ->  Tot label

type low_equiv (env:env) (h : rel heap)  = 
  forall (x:id). (Low? (env x) ==> sel (R?.l h) x = sel (R?.r h) x)

reifiable let p1 x = 
  write x (read x);
  write x (read x);
  write x (read x)
  (* adding more copies of this line causes an extreme blow-up in verification
  time and RAM usage... related to #389? *)

let p1_r x h = (* normalize_term *) (snd (reify (p1 x) h))

val ni_p1 (x : id) (env:env) (h :rel heap) : 
  Lemma 
  (requires (Low? (env x) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p1_r x (R?.l h)) (p1_r x (R?.r h)))))
let ni_p1 x env h = ()
