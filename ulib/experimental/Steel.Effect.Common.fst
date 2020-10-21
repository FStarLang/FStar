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

module Steel.Effect.Common

let sl_implies p q = slimp p q

let sl_implies_reflexive p = ()
let sl_implies_interp p q =
  let aux (m:mem) (f:slprop)
    : Lemma (requires interp (p `star` f) m)
            (ensures interp (q `star` f) m)
    = slimp_star p q f f
  in Classical.forall_intro_2 (Classical.move_requires_2 aux)
let sl_implies_interp_emp p q = ()

let equiv_forall #a p q = forall x. p x `equiv` q x
let equiv_forall_split #a t1 t2 = ()
let equiv_forall_elim #a t1 t2 = ()

let can_be_split_forall_frame p q frame x =
  assert (sl_implies (p x) (q x));
  slimp_star (p x) (q x) frame frame;
  star_commutative (p x) frame;
  star_commutative (q x) frame

let equiv_sl_implies p1 p2 = ()
let lemma_sl_implies_refl p = equiv_sl_implies p p
