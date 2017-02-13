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


let op_Star = op_Multiply

reifiable val fac (a:id) (n:id{a <> n}): gh:heap -> 
  IntStore unit
  (requires (fun h -> h == gh))
  (ensures  (fun h1 _ h2 -> True))
  (decreases (let x = sel gh n in if x < 0 then 0 else x))
reifiable let rec fac a n gh =
  let vn = read n in 
  if vn <= 0 then 
    write a 1
  else
  begin
    let va = read a in 
    let an = va * vn in 
    write a an;
    let n_1 = vn - 1 in 
    write n n_1;
    let h = IS?.get () in 
    fac a n h
  end

let fac_r a n h = (snd (reify (fac a n h) h))

#set-options "--z3rlimit 30"

val fac_mon (a:id) (n:id{a<>n}) (h:rel heap) :
  Lemma
  (requires (sel (R?.l h) n <= sel (R?.r h) n /\ 
             sel (R?.l h) a <= sel (R?.r h) a /\
             sel (R?.l h) a >= 0 /\
             sel (R?.r h) a >= 0))
  (ensures  (sel (fac_r a n (R?.l h)) a <= sel (fac_r a n (R?.r h)) a))
  (decreases (let x = sel (R?.l h) n in let y =  sel (R?.r h) n in 
              (if x < 0 then 0 else x) + (if y < 0 then 0 else y)))
let rec fac_mon a n h = 
  let R hl hr = h in 
  let hl'' = upd hl a (sel hl a * sel hl n) in 
  let hl' = upd hl'' n (sel hl'' n - 1) in 
  let hr'' = upd hr a (sel hr a * sel hr n) in
  let hr' = upd hr'' n (sel hr'' n - 1) in
  match sel hl n <= 0 , sel hr n <= 0 with
  | true , true  -> ()
  | true , false -> fac_mon a n (R hl hr')
  | false, false -> fac_mon a n (R hl' hr')
