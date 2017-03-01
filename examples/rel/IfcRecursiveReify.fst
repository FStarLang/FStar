module IfcRecursiveReify

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed
open Rel

type label =
| Low
| High

type env = id ->  Tot label

type low_equiv (env:env) (h : rel heap)  =
  forall (x:id). {:pattern (Low? (env x))} (Low? (env x) ==> sel (R?.l h) x = sel (R?.r h) x)

 val p1 (lo hi :id ): n:int -> ISNull unit (decreases n)
 let rec p1 lo hi n  =
  if n > 0 then
    (write hi (read hi -1);
    p1 lo hi (n-1))

let p1_r lo hi n h = (* normalize_term *) (snd (reify (p1 lo hi n) h))

val ni_p1 (lo hi : id) (n:int) (env:env) (h :rel heap) :
  Lemma
  (requires (lo <> hi /\
            Low? (env lo) /\
            High? (env hi) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p1_r lo hi n (R?.l h)) (p1_r lo hi n (R?.r h)))))
let rec ni_p1 lo hi n env h =
  if n > 0 then
  begin
    let R hl hr = h in
    let hl' = (upd hl hi (sel hl hi - 1)) in
    let hr' = (upd hr hi (sel hr hi - 1)) in
    ni_p1 lo hi (n-1) env (R hl' hr')
  end


 val p2 (lo hi :id ): n:int -> ISNull unit (decreases n)
 let rec p2 lo hi n  =
  if n > 0 then
    (write hi (read hi + 1);
    p2 lo hi (n - 1))

let p2_r lo hi n h = (* normalize_term *) (snd (reify (p2 lo hi n) h))

val ni_p2 (lo hi : id) (n:int) (env:env) (h :rel heap) :
  Lemma
  (requires (lo <> hi /\
            Low? (env lo) /\
            High? (env hi) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p2_r lo hi n (R?.l h)) (p2_r lo hi n (R?.r h)))))
let rec ni_p2 lo hi n env h =
  if n > 0 then
  begin
    let R hl hr = h in
    let hl' = (upd hl hi (sel hl hi + 1)) in
    let hr' = (upd hr hi (sel hr hi + 1)) in
    ni_p2 lo hi (n-1) env (R hl' hr')
  end


 let p3 lo1 lo2 hi n =
  p1 lo1 hi n ;
  p2 lo2 hi n


let p3_r lo1 lo2 hi n h = (* normalize_term *) (snd (reify (p3 lo1 lo2 hi n) h))


val ni_p3 (lo1 lo2 hi : id) (n:int) (env:env) (h :rel heap) :
  Lemma
  (requires (lo1 <> lo2 /\ lo1 <> hi /\ lo2 <> hi /\
            Low? (env lo1) /\
            Low? (env lo2) /\
            High? (env hi) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p3_r lo1 lo2 hi n (R?.l h)) (p3_r lo1 lo2 hi n (R?.r h)))))
let ni_p3 lo1 lo2 hi n env h =
  ni_p1 lo1 hi n env h;
  let R hl hr = h in
  let hl' = p1_r lo1 hi n hl in
  let hr' = p1_r lo1 hi n hr in
  ni_p2 lo2 hi n env (R hl' hr')
