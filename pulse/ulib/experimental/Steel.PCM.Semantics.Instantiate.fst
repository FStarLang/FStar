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

module Steel.PCM.Semantics.Instantiate
open Steel.PCM.Memory
module S = Steel.Semantics.Hoare.MST

let is_unit ()
  : Lemma (S.is_unit emp equiv star)
  = let aux (y:slprop)
      : Lemma (star emp y `equiv` y /\ star y emp `equiv` y)
      = emp_unit y; star_commutative emp y
    in
    Classical.forall_intro aux

#push-options "--warn_error -271"
let state_obeys_st_laws uses =
  Classical.forall_intro_3 star_associative;
  Classical.forall_intro_2 star_commutative;
  is_unit ();
  FStar.Classical.forall_intro_3 disjoint_join;
  let aux (m0 m1:mem)
    : Lemma (requires disjoint m0 m1)
            (ensures join m0 m1 == join m1 m0)
            [SMTPat (disjoint m0 m1)]
    = join_commutative m0 m1
  in
  let aux (m0 m1 m2:mem)
    : Lemma
      (requires
        disjoint m1 m2 /\
        disjoint m0 (join m1 m2))
      (ensures
        (disjoint_join m0 m1 m2;
        join m0 (join m1 m2) == join (join m0 m1) m2))
      [SMTPat (disjoint m0 (join m1 m2))]
    = join_associative m0 m1 m2
  in
  let aux (p1 p2 p3:slprop)
    : Lemma (p1 `equiv` p2 ==> (p1 `star` p3) `equiv` (p2 `star` p3))
      [SMTPat ()]
    = equiv_extensional_on_star  p1 p2 p3
  in
  ()
#pop-options
