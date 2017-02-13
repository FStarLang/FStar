module Ifc_Recursive_Heap_Reify

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed
open Rel

type label =
| Low
| High

type env = id ->  Tot label

type low_equiv (env:env) (h : rel heap)  =
  forall (x:id). {:pattern (Low? (env x))} (Low? (env x) ==> sel (R?.l h) x = sel (R?.r h) x)

reifiable val p1 (lo hi :id ): gh:heap -> 
  IntStore unit
  (requires (fun h -> h == gh))
  (ensures  (fun h1 _ h2 -> True))
  (decreases (sel gh hi))
reifiable let rec p1 lo hi gh  =
  if (read hi) > 0 then 
  begin
    write hi (read hi - 1);
    p1 lo hi (IS?.get ())
  end
  else 
    write lo 0

let p1_r lo hi h = (* normalize_term *) (snd (reify (p1 lo hi h) h))

#set-options "--z3rlimit 30"

val ni_p1 (lo hi : id) (env:env) (h :rel heap) :
  Lemma
  (requires (lo <> hi /\
            Low? (env lo) /\
            High? (env hi) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p1_r lo hi (R?.l h)) (p1_r lo hi (R?.r h)))))
  (decreases (let x = sel (R?.l h) hi in let y =  sel (R?.r h) hi in 
              (if x < 0 then 0 else x) + (if y < 0 then 0 else y)))
let rec ni_p1 lo hi env h = 
  let R hl hr = h in 
  let hl' = upd hl hi (sel hl hi - 1) in 
  let hr' = upd hr hi (sel hr hi - 1) in 
  match sel hl hi <= 0, sel hr hi <= 0 with
  | true , true  -> ()
  | true , false -> ni_p1 lo hi env (R hl hr')
  | false, true  -> ni_p1 lo hi env (R hl' hr)
  | false, false -> ni_p1 lo hi env (R hl' hr')
