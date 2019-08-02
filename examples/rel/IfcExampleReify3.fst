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

(* AR: need to investigate what's happening without this is_x in p1 *)
let is_x (hi:id) (x:int) :INT_STORE bool (fun s0 p -> p ((index s0 hi = x), s0))  =
  read hi = x

 let p1 x y hi =
  begin if is_x hi 0 then
    let vx = read x in
    let vy = read y in
    write x (vx + vy)
  else
    let vx = read x in
    let vy = read y in
    let vhi = read hi in
    write x (vx + vy + vhi)
  end ;
  let vx = read x in
  let vhi = read hi in
  write x (vx - vhi)

unfold
let p1_r x y hi h = (snd (reify (p1 x y hi) h))

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
