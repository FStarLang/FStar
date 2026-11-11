(*
   Copyright 2026 Microsoft Research

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
module Pulse.Extrinsic.Safety

open Pulse.Extrinsic.Language

let observes (l:language) (q:l.value -> l.state -> prop) (c:config l) : prop =
  forall v. main_returns l c v ==> q v c.state

// An operational adequacy target, not a separation-logic assertion.
let rec safe_for (l:language) (n:nat) (c:config l) (q:l.value -> l.state -> prop)
  : Tot prop (decreases n)
  = safe l c /\ observes l q c /\
    (if n = 0 then True
     else forall (c':config l) (_:pool_step l c c'). safe_for l (n - 1) c' q)

let safe_forever (l:language) (c:config l) (q:l.value -> l.state -> prop) : prop =
  forall n. safe_for l n c q

let rec execution_safe
  (#l:language) (#n:nat) (#c0 #c1:config l)
  (run:execution l n c0 c1) (q:l.value -> l.state -> prop)
  : Lemma
      (requires safe_for l n c0 q)
      (ensures safe l c1 /\ observes l q c1)
      (decreases run)
  = match run with
    | Done _ -> ()
    | Step s rest ->
        execution_safe rest q

let adequate
  (#l:language) (#n:nat) (#c0 #c1:config l)
  (run:execution l n c0 c1) (q:l.value -> l.state -> prop)
  : Lemma
      (requires safe_forever l c0 q)
      (ensures safe l c1 /\ observes l q c1)
  = execution_safe run q

let rec invariant_implies_safe_for
  (l:language) (inv:config l -> prop) (q:l.value -> l.state -> prop)
  (initial:config l)
  (good:(c:config l -> Lemma
    (requires inv c)
    (ensures safe l c /\ observes l q c)))
  (preserved:(c:config l -> c':config l -> pool_step l c c' -> Lemma
    (requires inv c)
    (ensures inv c')))
  (n:nat)
  : Lemma
      (requires inv initial)
      (ensures safe_for l n initial q)
      (decreases n)
  = good initial;
    if n > 0 then (
      introduce forall (c':config l) (s:pool_step l initial c').
        safe_for l (n - 1) c' q
      with (
        preserved initial c' s;
        invariant_implies_safe_for l inv q c' good preserved (n - 1)
      )
    )
