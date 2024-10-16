(*
   Copyright 2022 Jay Lorch and Nikhil Swamy, Microsoft Research

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

(* This library is intended to simplify using well-founded relations
   in decreases clauses.
*)

module FStar.WellFoundedRelation

open FStar.Universe
module WF = FStar.WellFounded
module WFU = FStar.WellFounded.Util

let rec default_decreaser (#a: Type u#a) (x: a)
  : Tot (acc_classical (default_relation #a) x) (decreases x) =
  let smaller (y: a{default_relation y x}) : acc_classical (default_relation #a) y =
    default_decreaser y
  in
  AccClassicalIntro smaller

let default_wfr (a: Type u#a) : (wfr: wfr_t a{wfr.relation == default_relation}) =
  let proof (x1: a) (x2: a)
    : Lemma (requires default_relation x1 x2)
            (ensures default_decreaser x1 << default_decreaser x2) =
    assert ((default_decreaser x2).access_smaller x1 == default_decreaser x1)
  in
  { relation = default_relation; decreaser = default_decreaser; proof = proof; }

let rec empty_decreaser (#a: Type u#a) (x: a)
  : Tot (acc_classical (empty_relation #a) x) (decreases x) =
  let smaller (y: a{empty_relation y x}) : acc_classical (empty_relation #a) y =
    empty_decreaser y
  in
  AccClassicalIntro smaller

let empty_wfr (a: Type u#a) : (wfr: wfr_t a{wfr.relation == empty_relation}) =
  let proof (x1: a) (x2: a)
    : Lemma (requires empty_relation x1 x2) (ensures empty_decreaser x1 << empty_decreaser x2) =
    assert ((empty_decreaser x2).access_smaller x1 == empty_decreaser x1)
  in
  { relation = empty_relation; decreaser = empty_decreaser; proof = proof; }

let rec acc_decreaser
  (#a: Type u#a)
  (r: a -> a -> Type0)
  (f: WF.well_founded r{forall x1 x2 (p: r x1 x2). (f x2).access_smaller x1 p == f x1})
  (x: a)
  : Tot (acc_classical (acc_relation r) x) (decreases (f x)) =
  let smaller (y: a{(acc_relation r) y x}) : (acc_classical (acc_relation r) y) = (
    eliminate exists (p: r y x). True
    returns   f y << f x
    with _.   assert ((f x).access_smaller y p == f y);
    acc_decreaser r f y
  ) in
  AccClassicalIntro smaller

let rec eta_expand_well_founded (#a: Type) (r: WF.binrel a) (wf_r: WF.well_founded r) (x: a)
  : Tot (WF.acc r x)
        (decreases {:well-founded (WFU.lift_binrel_as_well_founded_relation wf_r) (| a, x |)})
  = WF.AccIntro (let g_smaller (y: a) (u: r y x) : WF.acc r y =
                     WFU.intro_lift_binrel r y x;
                     eta_expand_well_founded r wf_r y
                 in g_smaller)

let acc_to_wfr (#a: Type u#a) (r: WF.binrel u#a u#0 a) (f: WF.well_founded r)
  : (wfr: wfr_t a{wfr.relation == acc_relation r}) =
  let f = eta_expand_well_founded r f in
  let proof (x1: a) (x2: a)
    : Lemma (requires acc_relation r x1 x2)
            (ensures acc_decreaser r f x1 << acc_decreaser r f x2) =
    assert ((acc_decreaser r f x2).access_smaller x1 == acc_decreaser r f x1)
  in
  { relation = acc_relation r; decreaser = acc_decreaser r f; proof = proof; }

let rec subrelation_decreaser (#a: Type u#a) (r: a -> a -> Type0)
                              (wfr: wfr_t a{forall x1 x2. r x1 x2 ==> wfr.relation x1 x2}) (x: a)
  : Tot (acc_classical r x) (decreases wfr.decreaser x) =
  let smaller (y: a{r y x}) : (acc_classical r y) =
    subrelation_decreaser r wfr y
  in
  AccClassicalIntro smaller

let subrelation_to_wfr (#a: Type u#a) (r: a -> a -> Type0)
                       (wfr: wfr_t a{forall x1 x2. r x1 x2 ==> wfr.relation x1 x2})
  : (wfr': wfr_t a{wfr'.relation == r}) =
  let proof (x1: a) (x2: a)
     : Lemma (requires r x1 x2)
             (ensures subrelation_decreaser r wfr x1 << subrelation_decreaser r wfr x2) =
    assert ((subrelation_decreaser r wfr x2).access_smaller x1 == subrelation_decreaser r wfr x1)
  in
  { relation = r; decreaser = subrelation_decreaser r wfr; proof = proof; }

let rec inverse_image_decreaser (#a: Type u#a) (#b: Type u#b) (r: a -> a -> Type0) (f: a -> b)
                                (wfr: wfr_t b{forall x1 x2. r x1 x2 ==> wfr.relation (f x1) (f x2)})
                                (x: a)
  : Tot (acc_classical r x) (decreases wfr.decreaser (f x)) =
  let smaller (y: a{r y x}) : (acc_classical r y) =
    inverse_image_decreaser r f wfr y
  in
  AccClassicalIntro smaller

let inverse_image_to_wfr (#a: Type u#a) (#b: Type u#b) (r: a -> a -> Type0) (f: a -> b)
                         (wfr: wfr_t b{forall x1 x2. r x1 x2 ==> wfr.relation (f x1) (f x2)})
  : (wfr': wfr_t a{wfr'.relation == r}) =
  let proof (x1: a) (x2: a)
    : Lemma (requires r x1 x2)
            (ensures inverse_image_decreaser r f wfr x1 << inverse_image_decreaser r f wfr x2) =
    assert ((inverse_image_decreaser r f wfr x2).access_smaller x1 ==
            inverse_image_decreaser r f wfr x1)
  in
  { relation = r; decreaser = inverse_image_decreaser r f wfr; proof = proof; }

let rec lex_nondep_decreaser (#a: Type u#a) (#b: Type u#b) (wfr_a: wfr_t a) (wfr_b: wfr_t b)
                             (xy: a & b)
  : Tot (acc_classical (lex_nondep_relation wfr_a wfr_b) xy)
    (decreases %[wfr_a.decreaser (fst xy); wfr_b.decreaser (snd xy)]) =
  let smaller (xy': a & b{lex_nondep_relation wfr_a wfr_b xy' xy})
    : (acc_classical (lex_nondep_relation wfr_a wfr_b) xy') =
    lex_nondep_decreaser wfr_a wfr_b xy'
  in
  AccClassicalIntro smaller

let lex_nondep_wfr (#a: Type u#a) (#b: Type u#b) (wfr_a: wfr_t a) (wfr_b: wfr_t b)
  : wfr: wfr_t (a & b){wfr.relation == lex_nondep_relation wfr_a wfr_b} =
  let proof (xy1: a & b) (xy2: a & b)
    : Lemma (requires lex_nondep_relation wfr_a wfr_b xy1 xy2)
            (ensures  lex_nondep_decreaser wfr_a wfr_b xy1 <<
                      lex_nondep_decreaser wfr_a wfr_b xy2) =
    assert ((lex_nondep_decreaser wfr_a wfr_b xy2).access_smaller xy1 ==
            lex_nondep_decreaser wfr_a wfr_b xy1)
  in
  { relation = lex_nondep_relation wfr_a wfr_b;
    decreaser = lex_nondep_decreaser wfr_a wfr_b;
    proof = proof; }

let rec lex_dep_decreaser (#a: Type u#a) (#b: a -> Type u#b) (wfr_a: wfr_t a)
                          (a_to_wfr_b: (x: a -> wfr_t (b x))) (xy: (x: a & b x))
  : Tot (acc_classical (lex_dep_relation wfr_a a_to_wfr_b) xy)
        (decreases %[wfr_a.decreaser (dfst xy); (a_to_wfr_b (dfst xy)).decreaser (dsnd xy)]) =
  let smaller (xy': (x: a & b x){lex_dep_relation wfr_a a_to_wfr_b xy' xy})
    : (acc_classical (lex_dep_relation wfr_a a_to_wfr_b) xy') =
    lex_dep_decreaser wfr_a a_to_wfr_b xy'
  in
  AccClassicalIntro smaller

let lex_dep_wfr (#a: Type u#a) (#b: a -> Type u#b) (wfr_a: wfr_t a)
                (a_to_wfr_b: (x: a -> wfr_t (b x)))
  : wfr: wfr_t (x: a & b x){wfr.relation == lex_dep_relation wfr_a a_to_wfr_b} =
  let proof (xy1: (x: a & b x)) (xy2: (x: a & b x))
    : Lemma (requires lex_dep_relation wfr_a a_to_wfr_b xy1 xy2)
            (ensures  lex_dep_decreaser wfr_a a_to_wfr_b xy1 <<
                      lex_dep_decreaser wfr_a a_to_wfr_b xy2) =
    assert ((lex_dep_decreaser wfr_a a_to_wfr_b xy2).access_smaller xy1 ==
            lex_dep_decreaser wfr_a a_to_wfr_b xy1)
  in
  { relation = lex_dep_relation wfr_a a_to_wfr_b;
    decreaser = lex_dep_decreaser wfr_a a_to_wfr_b;
    proof = proof; }

let bool_wfr: (wfr: wfr_t bool{wfr.relation == bool_relation}) =
  inverse_image_to_wfr #bool #nat bool_relation (fun b -> if b then 1 else 0) (default_wfr nat)

let option_wfr (#a: Type u#a) (wfr: wfr_t a)
  : wfr': wfr_t (option a){wfr'.relation == option_relation wfr} =
  // We'll need the unit type raised to universe u#a

  let unit_a: Type u#a = raise_t unit in

  // Step 1: Create a function f mapping an `option a` to a
  //          `(b: bool & (if b then a else unit_a))`.  It should map
  //          `Some x` to `(| true, x |)` and `None` to `(| false, () |)`.

  let f: option a -> (b: bool & (if b then a else unit_a)) =
    fun opt -> (match opt with | Some x -> (| true, x |) | None -> (| false, raise_val () |) )
  in

  // Step 2:  Create a wfr for (b: bool & (if b then a else unit_a)) using lex_dep_wfr.
  //          The precedence for the bool field should be bool_wfr (i.e., false precedes true).
  //          The precedence for the (if b then a else unit_a) field should be either wfr or
  //          empty_wfr, depending on whether b is true or false.

  let bool_to_wfr_a (b: bool) : wfr_t (if b then a else unit_a) =
    if b then wfr else empty_wfr unit_a
  in
  let wfr_bool_a: wfr_t (b: bool & (if b then a else unit_a)) =
    lex_dep_wfr bool_wfr bool_to_wfr_a
  in

  assert (forall (bx1: (b: bool & (if b then a else unit_a)))
            (bx2: (b: bool & (if b then a else unit_a))).
            wfr_bool_a.relation bx1 bx2 <==>
               (let (| b1, x1 |), (| b2, x2 |) = bx1, bx2 in
                (not b1 && b2) \/ (b1 && b2 /\ wfr.relation x1 x2)));

  // Step 3:  Create the final wfr using inverse_image_to_wfr, using `f` as the mapping
  //          function from `option a` to `(b: bool & (if b then a else unit_a))` and
  //          `wfr_bool_a` as the wfr_t for `(b: bool & (if b then a else unit_a))`.

  assert (forall opt1 opt2. (option_relation wfr) opt1 opt2 ==> wfr_bool_a.relation (f opt1) (f opt2));
  inverse_image_to_wfr (option_relation wfr) f wfr_bool_a
