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

let default_wfr (a: Type u#a) : (wfr: wfr_t a (fun _ -> a){ wfr.relation == (fun x1 x2 -> x1 << x2) }) =
  let decreaser (x: a) : a = x in
  let relation (x1: a) (x2: a) : Type0 = x1 << x2 in
  let proof (x1: a) (x2: a) : Lemma (requires relation x1 x2) (ensures decreaser x1 << decreaser x2) = () in
  { decreaser = decreaser; relation = relation; proof = proof; }

let empty_wfr (a: Type u#a) : (wfr: wfr_t a (fun _ -> unit){ wfr.relation == (fun x1 x2 -> False) }) =
  let decreaser (x: a) : unit = () in
  let relation (x1: a) (x2: a) : Type0 = False in
  let proof (x1: a) (x2: a) : Lemma (requires relation x1 x2) (ensures decreaser x1 << decreaser x2) = () in
  { decreaser = decreaser; relation = relation; proof = proof; }

let acc_to_wfr (#a: Type u#a) (r: a -> a -> Type0) (f: well_founded r{forall x1 x2 (p: r x1 x2). (f x2).access_smaller x1 p == f x1})
  : (wfr: wfr_t a (fun (x: a) -> acc r x) { wfr.relation == (fun x1 x2 -> exists (p: r x1 x2). True) }) =
  let relation (x1: a) (x2: a) : Type0 = (exists (p: r x1 x2). True) in
  let proof (x1: a) (x2: a) : Lemma (requires relation x1 x2) (ensures f x1 << f x2) = () in
  { decreaser = f; relation = relation; proof = proof; }

let subrelation_to_wfr (#a: Type u#a) (#d: a -> Type u#d) (r: a -> a -> Type0)
                       (wfr: wfr_t a d{forall x1 x2. r x1 x2 ==> wfr.relation x1 x2})
  : (wfr': wfr_t a d{wfr'.relation == r}) =
  let proof (x1: a) (x2: a) : Lemma (requires r x1 x2) (ensures wfr.decreaser x1 << wfr.decreaser x2) = () in
  { decreaser = wfr.decreaser; relation = r; proof = proof; }

let inverse_image_to_wfr (#a: Type u#a) (#b: Type u#b) (#d: b -> Type u#d) (r: a -> a -> Type0) (f: a -> b)
                         (wfr: wfr_t b d{forall x1 x2. r x1 x2 ==> wfr.relation (f x1) (f x2)})
  : (wfr': wfr_t a (fun x -> d (f x)){ wfr'.relation == r }) =
  let decreaser (x: a) : d (f x) = wfr.decreaser (f x) in
  let proof (x1: a) (x2: a) : Lemma (requires r x1 x2) (ensures decreaser x1 << decreaser x2) = () in
  { decreaser = decreaser; relation = r; proof = proof; }

let rec precedes_lex_value_nondep (#a: Type u#a) (#b: Type u#b) (xy: a * b) : Tot (lex_nondep_t xy) (decreases %[fst xy; snd xy]) =
  LexIntroNondep (fun xy' _ -> precedes_lex_value_nondep xy')

let precedes_lex_nondep_lemma (#a1: Type u#a) (#a2: Type u#a) (#b1: Type u#b) (#b2: Type u#b) (xy1: a1 * b1) (xy2: a2 * b2)
  : Lemma (requires (let (x1, y1), (x2, y2) = xy1, xy2 in x1 << x2 \/ (a1 == a2 /\ x1 == x2 /\ y1 << y2)))
          (ensures  precedes_lex_value_nondep xy1 << precedes_lex_value_nondep xy2) =
  let u = assert (let (x1, y1), (x2, y2) = xy1, xy2 in x1 << x2 \/ (a1 == a2 /\ x1 == x2 /\ y1 << y2)) in
  let lex1: lex_nondep_t #a1 #b1 xy1 = precedes_lex_value_nondep xy1 in
  let lex2: lex_nondep_t #a2 #b2 xy2 = precedes_lex_value_nondep xy2 in
  assert (lex2.access_smaller #a1 #b1 xy1 u == lex1)

let lex_nondep_d (#a: Type u#a) (#b: Type u#b) (#da: a -> Type u#da) (#db: b -> Type u#db)
                 (wfr_a: wfr_t a da) (wfr_b: wfr_t b db) (xy: a * b) : Type u#(max da db + 1) =
  lex_nondep_t (wfr_a.decreaser (fst xy), wfr_b.decreaser (snd xy))

let lex_nondep_wfr (#a: Type u#a) (#b: Type u#b) (#da: a -> Type u#da) (#db: b -> Type u#db) (wfr_a: wfr_t a da) (wfr_b: wfr_t b db)
  : wfr: wfr_t (a * b) (lex_nondep_d wfr_a wfr_b) { wfr.relation == lex_nondep_relation wfr_a wfr_b } =
  let decreaser (xy: a * b) : (lex_nondep_d wfr_a wfr_b xy) =
    precedes_lex_value_nondep (wfr_a.decreaser (fst xy), wfr_b.decreaser (snd xy)) in
  let relation = lex_nondep_relation wfr_a wfr_b in
  let proof (xy1: a * b) (xy2: a * b) : Lemma (requires relation xy1 xy2) (ensures decreaser xy1 << decreaser xy2) =
    (let (x1, y1), (x2, y2) = xy1, xy2 in
     let dxy1 = (wfr_a.decreaser x1, wfr_b.decreaser y1) in
     let dxy2 = (wfr_a.decreaser x2, wfr_b.decreaser y2) in
     precedes_lex_nondep_lemma dxy1 dxy2) in
  { decreaser = decreaser; relation = relation; proof = proof; }  

let rec precedes_lex_value_dep (#a: Type u#a) (#b: a -> Type u#b) (xy: (x: a & b x))
  : Tot (lex_dep_t xy) (decreases %[dfst xy; dsnd xy]) =
  LexIntroDep (fun xy' _ -> precedes_lex_value_dep xy')

let precedes_lex_dep_lemma (#a1: Type u#a) (#a2: Type u#a) (#b1: a1 -> Type u#b) (#b2: a2 -> Type u#b)
                           (xy1: (x: a1 & b1 x)) (xy2: (x2: a2) & b2 x2)
  : Lemma (requires (let (|x1, y1|), (|x2, y2|) = xy1, xy2 in x1 << x2 \/ (a1 == a2 /\ x1 == x2 /\ y1 << y2)))
          (ensures  precedes_lex_value_dep xy1 << precedes_lex_value_dep xy2) =
  let u = assert (let (|x1, y1|), (|x2, y2|) = xy1, xy2 in x1 << x2 \/ (a1 == a2 /\ x1 == x2 /\ y1 << y2)) in
  let lex1: lex_dep_t #a1 #b1 xy1 = precedes_lex_value_dep xy1 in
  let lex2: lex_dep_t #a2 #b2 xy2 = precedes_lex_value_dep xy2 in
  assert (lex2.access_smaller #a1 #b1 xy1 u == lex1)

let lex_dep_d (#a: Type u#a) (#b: a -> Type u#b) (#da: a -> Type u#da) (#db: (x: a) -> (y: b x) -> Type u#db)
              (wfr_a: wfr_t a da) (a_to_wfr_b: (x: a -> wfr_t (b x) (db x))) (xy: (x: a) & b x) : Type u#(max da db + 1) =
  let (| x, y |) = xy in
  lex_dep_t (| wfr_a.decreaser x, (a_to_wfr_b x).decreaser y |)

let lex_dep_wfr (#a: Type u#a) (#b: a -> Type u#b) (#da: a -> Type u#da) (#db: (x: a) -> (y: b x) -> Type u#db)
                (wfr_a: wfr_t a da) (a_to_wfr_b: (x: a -> wfr_t (b x) (db x)))
  : wfr: wfr_t (x: a & b x) (lex_dep_d wfr_a a_to_wfr_b){ wfr.relation == lex_dep_relation wfr_a a_to_wfr_b } =
  let relation = lex_dep_relation wfr_a a_to_wfr_b in
  let coerce_to_same_type (t1: Type) (t2: Type{t2 == t1}) (x: t1) : t2 = x in
  let decreaser (xy: (x: a & b x)) : lex_dep_d wfr_a a_to_wfr_b xy =
    (let (| x, y |) = xy in
     let dxy = (| wfr_a.decreaser x, (a_to_wfr_b x).decreaser y |) in
     let result: lex_dep_t dxy = precedes_lex_value_dep dxy in
     assert (lex_dep_d wfr_a a_to_wfr_b xy ==
             (let (| x, y |) = xy in lex_dep_t (| wfr_a.decreaser x, (a_to_wfr_b x).decreaser y |)));
     coerce_to_same_type (lex_dep_t dxy) (lex_dep_d wfr_a a_to_wfr_b xy) result) in
  let proof (xy1: (x1: a) & b x1) (xy2: (x2: a) & b x2)
    : Lemma (requires relation xy1 xy2) (ensures decreaser xy1 << decreaser xy2) =
    (let (| x1, y1 |), (| x2, y2 |) = xy1, xy2 in
     let dxy1 = (| wfr_a.decreaser x1, (a_to_wfr_b x1).decreaser y1 |) in
     let dxy2 = (| wfr_a.decreaser x2, (a_to_wfr_b x2).decreaser y2 |) in
     precedes_lex_dep_lemma dxy1 dxy2;
     assert (lex_dep_d wfr_a a_to_wfr_b xy1 ==
             (let (| x1, y1 |) = xy1 in lex_dep_t (| wfr_a.decreaser x1, (a_to_wfr_b x1).decreaser y1 |)));
     assert (lex_dep_d wfr_a a_to_wfr_b xy2 ==
             (let (| x2, y2 |) = xy2 in lex_dep_t (| wfr_a.decreaser x2, (a_to_wfr_b x2).decreaser y2 |)));
     assert (decreaser xy1 ==
             coerce_to_same_type (lex_dep_t dxy1) (lex_dep_d wfr_a a_to_wfr_b xy1) (precedes_lex_value_dep dxy1));
     assert (decreaser xy2 ==
             coerce_to_same_type (lex_dep_t dxy2) (lex_dep_d wfr_a a_to_wfr_b xy2) (precedes_lex_value_dep dxy2))) in
  { decreaser = decreaser; relation = relation; proof = proof; }  

let bool_wfr: (wfr: wfr_t bool (fun _ -> nat){ wfr.relation == (fun b1 b2 -> b1 == false /\ b2 == true) }) =
  inverse_image_to_wfr #bool #nat #(fun _ -> nat) (fun b1 b2 -> b1 == false /\ b2 == true) (fun b -> if b then 1 else 0) (default_wfr nat)

let option_d (#a: Type u#a) (#d: a -> Type u#d) (wfr: wfr_t a d) (x: option a) : Type u#(d + 1)=
  let unit_a: Type u#a = raise_t unit in
  let unit_d: Type u#d = raise_t unit in
  let f: option a -> (b: bool & (if b then a else unit_a)) =
    fun opt -> (match opt with | Some x -> (| true, x |) | None -> (| false, raise_val () |) ) in
  let bool_to_wfr_a (b: bool) : wfr_t (if b then a else unit_a) (fun x -> if b then d x else unit_d) =
    if b then
      { decreaser = wfr.decreaser; relation = wfr.relation; proof = wfr.proof; }
    else
      let proof (x1: unit_a) (x2: unit_d) : Lemma (requires False) (ensures raise_val () << raise_val ()) = () in
      { decreaser = (fun _ -> raise_val ()); relation = (fun x1 x2 -> False <: (related: Type0{~related})); proof = proof; } in
  (lex_dep_d bool_wfr bool_to_wfr_a) (f x)

let option_wfr (#a: Type u#a) (#d: a -> Type u#d) (wfr: wfr_t a d) :
  wfr': wfr_t (option a) (option_d wfr) { wfr'.relation == option_relation wfr } =
  // We'll need the unit types raised to universes u#a and u#d

  let unit_a: Type u#a = raise_t unit in
  let unit_d: Type u#d = raise_t unit in

  // Step 1:  Create a function f mapping an `option a` to a `(b: bool & (if b then a else unit_a))`.
  //          It should map `Some x` to `(| true, x |)` and `None` to `(| false, () |)`.

  let f: option a -> (b: bool & (if b then a else unit_a)) =
    fun opt -> (match opt with | Some x -> (| true, x |) | None -> (| false, raise_val () |) ) in

  // Step 2:  Create a wfr for (b: bool & (if b then a else unit_a)) using lex_dep_wfr.
  //          The precedence for the bool field should be bool_wfr (i.e., false precedes true).
  //          The precedence for the (if b then a else unit_a) field should be either wfr or empty_wfr,
  //          depending on whether b is true or false.
  
  let bool_to_wfr_a (b: bool) : wfr_t (if b then a else unit_a) (fun x -> if b then d x else unit_d) =
    if b then
      { decreaser = wfr.decreaser; relation = wfr.relation; proof = wfr.proof; }
    else
      let proof (x1: unit_a) (x2: unit_d) : Lemma (requires False) (ensures raise_val () << raise_val ()) = () in
      { decreaser = (fun _ -> raise_val ()); relation = (fun x1 x2 -> False <: (related: Type0{~related})); proof = proof; } in

  let wfr_bool_a: wfr_t (b: bool & (if b then a else unit_a)) (lex_dep_d bool_wfr bool_to_wfr_a) =
    lex_dep_wfr bool_wfr bool_to_wfr_a in

  assert (forall (bx1: (b: bool & (if b then a else unit_a))) (bx2: (b: bool & (if b then a else unit_a))).
            wfr_bool_a.relation bx1 bx2 <==>
               (let (| b1, x1 |), (| b2, x2 |) = bx1, bx2 in
                (not b1 && b2) \/ (b1 && b2 /\ wfr.relation x1 x2)));

  // Step 3:  Create the final wfr using inverse_image_to_wfr, using `f` as the mapping function from
  //          `option a` to `(b: bool & (if b then a else unit_a))` and `wfr_bool_a` as the wfr_t
  //          for `(b: bool & (if b then a else unit_a))`.

  assert (forall opt1 opt2. (option_relation wfr) opt1 opt2 ==> wfr_bool_a.relation (f opt1) (f opt2));
  inverse_image_to_wfr (option_relation wfr) f wfr_bool_a
