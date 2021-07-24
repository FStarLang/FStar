(*
   Copyright 2021 Microsoft Research

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

module FStar.Classical.Lemmas

(*** Implication *)

let impl_intro_lemma #p #q h =
  let lem (x:p) : Lemma (q) = h () in
  FStar.Classical.impl_intro lem

(*** Universal quantification *)

let forall_intro_lemma #a #p #q h =
  let q' = fun (x:a) -> fun (_:unit) -> q x in
  FStar.Classical.ghost_lemma h

let forall_intro_2_lemma #a #b #p #q h =
  let p' = fun (tup: a * b) -> p (fst tup) (snd tup) in
  let q' = fun (tup: a * b) -> q (fst tup) (snd tup) in
  let h' (tup: a * b) : Lemma (requires p' tup) (ensures q' tup) =
    h (fst tup) (snd tup) in
  forall_intro_lemma h';
  assert (forall (tup: a * b). p' tup ==> q' tup);
  let lem (x: a) (y: b) : Lemma (p x y ==> q x y) =
    (let tup = (x, y) in assert (p' tup ==> q' tup)) in
  FStar.Classical.forall_intro_2 lem

(*** Existential quantification *)

let exists_elim_lemma #a #goal #property existence instance_implies_goal =
  let existence' = existence () in
  let instance_implies_goal':(x:a{property x} -> squash goal) = fun (x:a{property x}) -> instance_implies_goal x in
  FStar.Classical.exists_elim goal #a #property existence' instance_implies_goal'

(*** Disjunction *)

let or_elim_lemma #l #r #goal hl hr =
  let goal':(squash (l \/ r) -> ubool) = fun _ -> goal in
  let hl':(squash l -> Lemma (goal)) = fun _ -> hl () in
  let hr':(squash r -> Lemma (goal)) = fun _ -> hr () in
  FStar.Classical.or_elim #l #r #goal' hl' hr'

let or_elim_3_lemma #l #m #r #goal hl hm hr =
  or_elim_lemma hl hm;
  let hl' () : Lemma (requires l \/ m) (ensures goal) = () in
  or_elim_lemma hl' hr
