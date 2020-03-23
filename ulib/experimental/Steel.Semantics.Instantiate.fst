(*
   Copyright 2020 Microsoft Research

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

module Steel.Semantics.Instantiate

friend Steel.Memory

module S = Steel.Semantics.Hoare.MST

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let associative () : Lemma (S.associative equiv star)
= Classical.forall_intro_3 star_associative

let commutative () : Lemma (S.commutative equiv star)
= Classical.forall_intro_2 star_commutative

let is_unit () : Lemma (S.is_unit emp equiv star)
= let aux (y:hprop) : Lemma (star emp y `equiv` y /\ star y emp `equiv` y)
    = emp_unit y; star_commutative emp y
  in
  Classical.forall_intro aux

#push-options "--warn_error -271"
let state_obeys_st_laws _ =
  associative (); commutative (); is_unit ();
  let aux (p1 p2 p3:hprop)
    : Lemma (p1 `equiv` p2 ==> (p1 `star` p3) `equiv` (p2 `star` p3))
      [SMTPat ()]
    = equiv_extensional_on_star  p1 p2 p3
  in
  ()
#pop-options
