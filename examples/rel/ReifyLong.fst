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
module ReifyLong

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed
open Rel

(*
type label =
| Low
| High

type env = id ->  Tot label

type low_equiv (env:env) (h : rel heap)  =
  forall (x:id). (Low? (env x) ==> sel (R?.l h) x = sel (R?.r h) x)
 *)
let is_x (hi:id) (x:int) :INT_STORE bool (fun s0 p -> p ((index s0 hi = x), s0))  =
  read hi = x

 let p1 x =
  if is_x x 0 then write x 0 else write x 0;
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x);
  write x (read x)
  (* adding more copies of this line causes an extreme blow-up in verification
  time and ram usage ... related to #389? *)

let bidule (h:heap) (x:id) : Lemma (fst (reify (p1 x) h) = ()) = ()
(*
let p1_r x h = (* normalize_term *) (snd (reify (p1 x) h))

val p1_lemma (x:id) (h:heap) :
  Lemma
  (requires True)
  (ensures ((sel (p1_r x h) x = 0)))
let p1_lemma x h = ()
*)

(*
val ni_p1 (x : id) (env:env) (h :rel heap) :
  Lemma
  (requires (Low? (env x) /\
            low_equiv env h))
  (ensures  (low_equiv env (R (p1_r x (R?.l h)) (p1_r x (R?.r h)))))
let ni_p1 x env h = ()
*)
