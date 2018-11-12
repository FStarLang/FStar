module IfcComposeReify

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed
open Rel

type label =
| Low
| High

type env = id ->  Tot label

type low_equiv (env:env) (h : rel heap)  =
  forall (x:id). {:pattern (Low? (env x))} (Low? (env x) ==> sel (R?.l h) x = sel (R?.r h) x)

let is_x (hi:id) (x:int) :INT_STORE bool (fun s0 p -> p ((index s0 hi = x), s0))  =
  read hi = x

 let p1 lo hi =
  if (is_x hi 0) then 
    write lo (read hi)
  else 
    write lo 0


 let p2 lo hi =
  if (is_x hi 1) then 
    write lo (read hi)
  else 
    write lo 1


 let p3 lo1 lo2 hi =
  p1 lo1 hi;
  p2 lo2 hi


let p1_r lo hi h = (* normalize_term *) (snd (reify (p1 lo hi) h))
let p2_r lo hi h = (* normalize_term *) (snd (reify (p2 lo hi) h))
let p3_r lo1 lo2 hi h = (* normalize_term *) (snd (reify (p3 lo1 lo2 hi) h))

#set-options "--z3rlimit 10"
val ni_p1 (lo hi : id) (env:env) (h :rel heap) :
  Lemma
  (requires (lo <> hi /\
            Low? (env lo) /\
            High? (env hi) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p1_r lo hi (R?.l h)) (p1_r lo hi (R?.r h)))))
let ni_p1 lo hi env h = ()


val ni_p2 (lo hi : id) (env:env) (h :rel heap) :
  Lemma
  (requires (lo <> hi /\
            Low? (env lo) /\
            High? (env hi) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p2_r lo hi (R?.l h)) (p2_r lo hi (R?.r h)))))
let ni_p2 lo hi env h = ()

val ni_p3 (lo1 lo2 hi : id) (env:env) (h :rel heap) :
  Lemma
  (requires (lo1 <> lo2 /\ lo1 <> hi /\ lo2 <> hi /\
            Low? (env lo1) /\
            Low? (env lo2) /\
            High? (env hi) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p3_r lo1 lo2 hi (R?.l h)) (p3_r lo1 lo2 hi (R?.r h)))))
let ni_p3 lo1 lo2 hi env h = ni_p1 lo1 hi env h; ni_p2 lo2 hi env h



