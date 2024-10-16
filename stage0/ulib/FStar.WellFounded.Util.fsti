(*
   Copyright 2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: N. Swamy
*)

module FStar.WellFounded.Util
open FStar.WellFounded
(** Provides some utilities related to well-founded relations *)

(* 1. Given a well-founded relation `r:binrel a`
      turn it into a well-founded relation on `binrel top`,
      by construction a relation that only relates `top` elements
      in `a` by `r`

      This is useful when writing type-polymorphic recursive functions
      whose termination depends on some custom well-founded order

      See tests/micro-benchmarks/TestWellFoundedRecursion.rel_poly2
*)

let top = (b:Type & b)

let lift_binrel (#a:Type)
                (r:binrel a)
    : binrel top
    = fun (t0 t1:top) ->
        (_:(dfst t0==a /\ dfst t1==a) & r (dsnd t0) (dsnd t1))

val intro_lift_binrel (#a:Type) (r:binrel a) (y:a) (x:a)
  : Lemma
    (requires r y x)
    (ensures lift_binrel r (| a, y |) (| a, x |))

val elim_lift_binrel (#a:Type) (r:binrel a) (y:top) (x:a)
  : Lemma
    (requires lift_binrel r y (| a, x |))
    (ensures dfst y == a /\ r (dsnd y) x)

val lower_binrel (#a:Type)
                 (#r:binrel a)
                 (x y:top)
                 (p:lift_binrel r x y)
  : r (dsnd x) (dsnd y)


val lift_binrel_well_founded (#a:Type u#a)
                             (#r:binrel u#a u#r a)
                             (wf_r:well_founded r)
  : well_founded (lift_binrel r)

let lift_binrel_as_well_founded_relation (#a:Type u#a) (#r:binrel u#a u#r a) (wf_r:well_founded r)
  : well_founded_relation u#(a + 1) u#r (top u#a)
  = as_well_founded #top #(lift_binrel r) (lift_binrel_well_founded wf_r)


(* 2. Given a well-founded relation `r:binrel a`
      turn it into a *squashed* well-founded relation on `binrel top`,
      by construction a relation that only relates `top` elements
      in `a` by `r`

      This is very similar to 1, but uses squashed types,
      which leads to slightly better SMT automation at use sites.

      See tests/micro-benchmarks/TestWellFoundedRecursion.rel_poly

*)
let lift_binrel_squashed (#a:Type u#a)
                         (r:binrel u#a u#r a)
    : binrel top
    = fun (t0 t1:top) ->
        (dfst t0==a /\ dfst t1==a /\ squash (r (dsnd t0) (dsnd t1)))

val lower_binrel_squashed (#a:Type u#a)
                          (#r:binrel u#a u#r a)
                          (x y:top u#a)
                          (p:lift_binrel_squashed r x y)
  : squash (r (dsnd x) (dsnd y))


let squash_binrel (#a:Type) (r:binrel u#a u#r a) (x y:a) = squash (r x y)

val lift_binrel_squashed_well_founded (#a:Type u#a)
                                      (#r:binrel u#a u#r a)
                                      (wf_r:well_founded (squash_binrel r))
  : well_founded (lift_binrel_squashed r)


let lift_binrel_squashed_as_well_founded_relation (#a:Type u#a)
                                                  (#r:binrel u#a u#r a)
                                                  (wf_r:well_founded (squash_binrel r))
  : well_founded_relation u#(a + 1) u#0 top
  = as_well_founded #top #(lift_binrel_squashed r) (lift_binrel_squashed_well_founded wf_r)

val lift_binrel_squashed_intro (#a:Type)
                               (#r:binrel a)
                               (wf_r:well_founded (squash_binrel r))
                               (x y:a)
                               (sqr:squash (r x y))
  : Lemma
    (ensures lift_binrel_squashed r (|a, x|) (|a, y|))

(* If a squashed relation is well-founded, then so is its unsquashed counterpart.
   The converse is not true, i.e., the well-founded proof is in contravariant position here *)
val unsquash_well_founded (#a:Type u#a) (r:binrel u#a u#r a) (wf_r:well_founded (squash_binrel r))
  : well_founded u#a u#r r
