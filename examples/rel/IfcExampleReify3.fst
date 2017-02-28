module IfcExampleReify3

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed
open Rel

type label =
| Low
| High

type env = id ->  Tot label

type low_equiv (env:env) (h : rel heap)  =
  forall (x:id). {:pattern (Low? (env x))} (Low? (env x) ==> sel (R?.l h) x = sel (R?.r h) x)

reifiable let p1 x y hi =
  if read hi = 0 then
    let vx = read x in
    let vy = read y in
    write x (vx + vy)
  else
    (let vx = read x in
     let vy = read y in
     let vhi = read hi in
     write x (vx + vy + vhi));
    (* Writing explicit lets because otherwise we get this: *)
    (* (let s = *)
    (*   let vx = read x in *)
    (*   let vy = read y in *)
    (*   vx + vy *)
    (*  in *)
    (*  let vhi = read hi in *)
    (*  write x (s + vhi)); *)
  let vx = read x in
  let vhi = read hi in
  write x (vx - vhi)

let p1_r x y hi h = (* normalize_term *) (snd (reify (p1 x y hi) h))

#set-options "--z3rlimit 10"
val p1_x (x y hi : id) (h:heap) :
  Lemma (requires (x <> y /\ x <> hi /\ y <> hi))
    (ensures (let h' = p1_r x y hi h in
      (sel h' y = sel h y) /\
      (sel h' x = sel h x + sel h y) /\
      (sel h' hi = sel h hi)))
let p1_x x y hi h = ()

val ni_p1 (x y hi : id) (env:env) (h :rel heap) :
  Lemma
  (requires (x <> y /\ x <> hi /\ y <> hi /\
            Low? (env x) /\
            Low? (env y) /\
            High? (env hi) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p1_r x y hi (R?.l h)) (p1_r x y hi (R?.r h)))))
let ni_p1 x y hi env h = p1_x x y hi (R?.l h) ; p1_x x y hi (R?.r h)
