(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module IfcRecursiveHeapReify

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed
open Rel
module X = FStar.DM4F.IntStoreFixed
type label =
| Low
| High

type env = id ->  Tot label

type low_equiv (env:env) (h : rel heap)  =
  forall (x:id). {:pattern (Low? (env x))} (Low? (env x) ==> sel (R?.l h) x = sel (R?.r h) x)

 val p1 (lo hi :id ): gh:heap ->
  IntStore unit
  (requires (fun h -> h == gh /\ lo <> hi))
  (ensures  (fun h1 _ h2 -> True))
  (decreases (sel gh hi))
 let rec p1 lo hi gh  =
  if (read hi) > 0 then
  begin
    write hi (read hi - 1);
    let h = X.get () in
    p1 lo hi h;
    write lo (read lo - 1)
  end;
  write lo (read lo + 1)


let p1_r lo (hi:id{lo<>hi}) h = (* normalize_term *) (snd (reify (p1 lo hi h) h))

let nat_of (x:int) : nat = if x < 0 then 0 else x

//inlining this leads to a crash!
let dec_metric (lo:id) (hi:id{lo<>hi}) (h :rel heap) =
  nat_of (sel (R?.l h) hi) +
  nat_of (sel (R?.r h) hi)
  
#set-options "--z3rlimit 60"

let rec ni_p1 (lo:id) (hi:id{lo<>hi}) (env:env) (h :rel heap) :
  Lemma
  (requires (Low? (env lo) /\
            High? (env hi) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p1_r lo hi (R?.l h)) (p1_r lo hi (R?.r h)))))
  (decreases (dec_metric lo hi h)) =
  let R hl hr = h in
  let hl' = upd hl hi (sel hl hi - 1) in
  let hr' = upd hr hi (sel hr hi - 1) in
  
  match sel hl hi <= 0, sel hr hi <= 0 with
  | true , true  -> 
    begin
      let hl'' = upd hl lo (sel hl lo + 1) in
      let hr'' = upd hr lo (sel hr lo + 1) in
      cut (low_equiv env (R hl'' hr''))
    end
  | true , false ->
    begin
      let hl2 = p1_r lo hi hl in
      let hr2 = p1_r lo hi hr' in
      ni_p1 lo hi env (R hl hr');
      cut (low_equiv env (R hl2 hr2));
      let hr2' = upd hr2 lo (sel hr2 lo - 1) in
      let hr2'' = upd hr2' lo (sel hr2' lo + 1) in
      cut (hr2'' == p1_r lo hi  hr);
      cut (low_equiv env (R hl2 hr2''))
    end
  | false, true  -> 
    begin
      let hl2 = p1_r lo hi hl' in
      let hr2 = p1_r lo hi hr in
      ni_p1 lo hi env (R hl' hr);
      cut (low_equiv env (R hl2 hr2));
      let hl2' = upd hl2 lo (sel hl2 lo - 1) in
      let hl2'' = upd hl2' lo (sel hl2' lo + 1) in
      cut (hl2'' == p1_r lo hi hl);
      cut (low_equiv env (R hl2'' hr2))
    end
  | false, false -> 
    begin
      let hl2 = p1_r lo hi hl' in
      let hr2 = p1_r lo hi hr' in
      ni_p1 lo hi env (R hl' hr');
      cut (low_equiv env (R hl2 hr2));
      let hl2' = upd hl2 lo (sel hl2 lo - 1) in 
      let hr2' = upd hr2 lo (sel hr2 lo - 1) in
      let hl2'' = upd hl2' lo (sel hl2' lo + 1) in 
      let hr2'' = upd hr2' lo (sel hr2' lo + 1) in
      cut (hl2'' == p1_r lo hi  hl);
      cut (hr2'' == p1_r lo hi  hr);
      cut (low_equiv env (R hl2'' hr2''))
    end


let op_Star = op_Multiply

let rec fac (a:id) (n:id{a <> n}) (gh:heap)
: IntStore unit
  (requires (fun h -> h == gh))
  (ensures  (fun h1 _ h2 -> True))
  (decreases (nat_of (sel gh n)))
= let vn = read n in
  if vn <= 0 then
    write a 1
  else
  begin
    let va = read a in
    let an = va * vn in
    write a an;
    let n_1 = vn - 1 in
    write n n_1;
    let h = X.get () in
    fac a n h
  end

let fac_r a n h = (snd (reify (fac a n h) h))

#set-options "--z3rlimit 40"

let rec fac_mon (a:id) (n:id{a<>n}) (h:rel heap) :
  Lemma
  (requires (sel (R?.l h) n <= sel (R?.r h) n /\
             sel (R?.l h) a <= sel (R?.r h) a /\
             sel (R?.l h) a >= 0 /\
             sel (R?.r h) a >= 0))
  (ensures  (sel (fac_r a n (R?.l h)) a <= sel (fac_r a n (R?.r h)) a))
  (decreases (dec_metric a n h)) =
  let R hl hr = h in
  let hl'' = upd hl a (sel hl a * sel hl n) in
  let hl' = upd hl'' n (sel hl'' n - 1) in
  let hr'' = upd hr a (sel hr a * sel hr n) in
  let hr' = upd hr'' n (sel hr'' n - 1) in
  match sel hl n <= 0 , sel hr n <= 0 with
  | true , true  -> ()
  | true , false -> fac_mon a n (R hl hr')
  | false, false -> fac_mon a n (R hl' hr')
