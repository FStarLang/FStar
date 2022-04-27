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

noeq type wfr_t (a: Type u#a) (d: a -> Type u#d) : Type u#(max a d + 1) =
  {
    decreaser: (x: a -> d x);
    relation: (x1: a -> x2: a -> related: Type0{related ==> decreaser x1 << decreaser x2});
  }

let decreaser_for_wfr (#a: Type u#a) (#d: a -> Type u#d) (wfr: wfr_t a d) (x: a) : d x =
  wfr.decreaser x

let precedes_by_wfr (#a: Type u#a) (#d: a -> Type u#d) (wfr: wfr_t a d) (x1: a) (x2: a)
  : (related: Type0{related ==> decreaser_for_wfr wfr x1 << decreaser_for_wfr wfr x2}) =
  wfr.relation x1 x2

let default_wfr (a: Type u#a) : (wfr: wfr_t a (fun _ -> a) {forall x1 x2. precedes_by_wfr wfr x1 x2 <==> x1 << x2}) =
  let r (x1: a) (x2: a) : related: Type0{related ==> x1 << x2} =
    x1 << x2 in
  let wfr: wfr_t a (fun _ -> a) = {
    decreaser = (fun x -> x);
    relation = r;
  } in
  wfr

let empty_wfr (a: Type u#a) : (wfr: wfr_t a (fun _ -> unit){forall x1 x2. ~(precedes_by_wfr wfr x1 x2)}) =
  let r (x1: a) (x2: a) : related: Type0{~related} =
    False in
  let wfr: wfr_t a (fun _ -> unit) = {
    decreaser = (fun _ -> ());
    relation = r;
  } in
  wfr

let acc_to_wfr (#a: Type u#a) (r: a -> a -> Type0) (f: well_founded r{forall x1 x2 (p: r x1 x2). (f x2).access_smaller x1 p == f x1})
  : (wfr: wfr_t a (fun (x: a) -> acc r x) {forall x1 x2. precedes_by_wfr wfr x1 x2 <==> (exists (p: r x1 x2). True)}) =
  let relation (x1: a) (x2: a) : related: Type0{related ==> f x1 << f x2} = (
    let related = (exists (p: r x1 x2). True) in
    introduce related ==> f x1 << f x2
    with _. (
      eliminate exists (p: r x1 x2). True
      returns f x1 << f x2
      with _. assert ((f x2).access_smaller x1 p == f x1)
    );
    related
  ) in
  let wfr: wfr_t a (fun (x: a) -> acc r x) = {
    decreaser = f;
    relation = relation;
  } in
  wfr

let subrelation_to_wfr (#a: Type u#a) (#d: a -> Type u#d) (r: a -> a -> Type0)
                       (wfr: wfr_t a d{forall x1 x2. r x1 x2 ==> precedes_by_wfr wfr x1 x2})
  : (wfr': wfr_t a d{forall x1 x2. precedes_by_wfr wfr' x1 x2 <==> r x1 x2}) =
  let relation (x1: a) (x2: a) : related: Type0{related <==> r x1 x2} =
    r x1 x2 in
  let wfr': wfr_t a d = {
    decreaser = wfr.decreaser;
    relation = relation;
  } in
  wfr'

let inverse_image_to_wfr (#a: Type u#a) (#b: Type u#b) (#d: b -> Type u#d) (r: a -> a -> Type0) (f: a -> b)
                         (wfr: wfr_t b d{forall x1 x2. r x1 x2 ==> precedes_by_wfr wfr (f x1) (f x2)})
  : (wfr': wfr_t a (fun x -> d (f x)){forall x1 x2. precedes_by_wfr wfr' x1 x2 <==> r x1 x2}) =
  let relation (x1: a) (x2: a) : related: Type0{related <==> r x1 x2} =
    r x1 x2 in
  let wfr': wfr_t a (fun x -> d (f x)) = {
    decreaser = (fun x -> wfr.decreaser (f x));
    relation = relation;
  } in
  wfr'

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
  lex_nondep_t (decreaser_for_wfr wfr_a (fst xy), decreaser_for_wfr wfr_b (snd xy))

let lex_nondep_wfr (#a: Type u#a) (#b: Type u#b) (#da: a -> Type u#da) (#db: b -> Type u#db) (wfr_a: wfr_t a da) (wfr_b: wfr_t b db)
  : wfr: wfr_t (a * b) (lex_nondep_d wfr_a wfr_b)
         {forall xy1 xy2. precedes_by_wfr wfr xy1 xy2 <==>
                     (let (x1, y1), (x2, y2) = xy1, xy2 in
                      precedes_by_wfr wfr_a x1 x2 \/ (x1 == x2 /\ precedes_by_wfr wfr_b y1 y2))} =
  let relation (xy1: a * b) (xy2: a * b) : related: Type0{related ==>
       precedes_lex_value_nondep (decreaser_for_wfr wfr_a (fst xy1), decreaser_for_wfr wfr_b (snd xy1))
    << precedes_lex_value_nondep (decreaser_for_wfr wfr_a (fst xy2), decreaser_for_wfr wfr_b (snd xy2))} =
  (
    let (x1, y1), (x2, y2) = xy1, xy2 in
    let dxy1 = (decreaser_for_wfr wfr_a x1, decreaser_for_wfr wfr_b y1) in
    let dxy2 = (decreaser_for_wfr wfr_a x2, decreaser_for_wfr wfr_b y2) in
    let related = precedes_by_wfr wfr_a x1 x2 \/ (x1 == x2 /\ precedes_by_wfr wfr_b y1 y2) in
    introduce related ==> precedes_lex_value_nondep dxy1 << precedes_lex_value_nondep dxy2
    with _. precedes_lex_nondep_lemma dxy1 dxy2;
    related
  ) in
  let wfr: wfr_t (a * b) (fun xy -> lex_nondep_t (decreaser_for_wfr wfr_a (fst xy), decreaser_for_wfr wfr_b (snd xy))) = {
    decreaser = (fun (xy: a * b) -> precedes_lex_value_nondep (decreaser_for_wfr wfr_a (fst xy), decreaser_for_wfr wfr_b (snd xy)));
    relation = relation;
  } in
  wfr

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
              (wfr_a: wfr_t a da) (wfr_b: (x: a -> wfr_t (b x) (db x))) (xy: (x: a) & b x) : Type u#(max da db + 1) =
  lex_dep_t (| decreaser_for_wfr wfr_a (dfst xy), decreaser_for_wfr (wfr_b (dfst xy)) (dsnd xy) |)

let lex_dep_wfr (#a: Type u#a) (#b: a -> Type u#b) (#da: a -> Type u#da) (#db: (x: a) -> (y: b x) -> Type u#db)
                (wfr_a: wfr_t a da) (wfr_b: (x: a -> wfr_t (b x) (db x)))
  : wfr: wfr_t (x: a & b x) (lex_dep_d wfr_a wfr_b)
         {forall xy1 xy2. precedes_by_wfr wfr xy1 xy2 <==>
                     (let (| x1, y1 |), (| x2, y2 |) = xy1, xy2 in
                      precedes_by_wfr wfr_a x1 x2 \/ (x1 == x2 /\ precedes_by_wfr (wfr_b x1) y1 y2))} =
  let relation (xy1: (x1: a) & b x1) (xy2: (x2: a) & b x2) : related: Type0{related ==>
       precedes_lex_value_dep (| decreaser_for_wfr wfr_a (dfst xy1), decreaser_for_wfr (wfr_b (dfst xy1)) (dsnd xy1) |)
    << precedes_lex_value_dep (| decreaser_for_wfr wfr_a (dfst xy2), decreaser_for_wfr (wfr_b (dfst xy2)) (dsnd xy2) |)} =
  (
    let (| x1, y1 |), (| x2, y2 |) = xy1, xy2 in
    let dxy1 = (| decreaser_for_wfr wfr_a x1, decreaser_for_wfr (wfr_b x1) y1 |) in
    let dxy2 = (| decreaser_for_wfr wfr_a x2, decreaser_for_wfr (wfr_b x2) y2 |) in
    let related = precedes_by_wfr wfr_a x1 x2 \/ (x1 == x2 /\ precedes_by_wfr (wfr_b x1) y1 y2) in
    introduce related ==>
          precedes_lex_value_dep (| decreaser_for_wfr wfr_a (dfst xy1), decreaser_for_wfr (wfr_b (dfst xy1)) (dsnd xy1) |)
       << precedes_lex_value_dep (| decreaser_for_wfr wfr_a (dfst xy2), decreaser_for_wfr (wfr_b (dfst xy2)) (dsnd xy2) |)
    with _. (
      precedes_lex_dep_lemma dxy1 dxy2;
      assert (dxy1 == (| decreaser_for_wfr wfr_a (dfst xy1), decreaser_for_wfr (wfr_b (dfst xy1)) (dsnd xy1) |));
      assert (dxy2 == (| decreaser_for_wfr wfr_a (dfst xy2), decreaser_for_wfr (wfr_b (dfst xy2)) (dsnd xy2) |))
    );
    related
  ) in
  let wfr: wfr_t (x: a & b x)
                 (fun xy -> lex_dep_t (| decreaser_for_wfr wfr_a (dfst xy), decreaser_for_wfr (wfr_b (dfst xy)) (dsnd xy) |)) = {
    decreaser = (fun (xy: (x : a) & b x) ->
                   precedes_lex_value_dep (| decreaser_for_wfr wfr_a (dfst xy), decreaser_for_wfr (wfr_b (dfst xy)) (dsnd xy) |));
    relation = relation;
  } in
  wfr

let bool_wfr: (wfr: wfr_t bool (fun _ -> nat){forall b1 b2. precedes_by_wfr wfr b1 b2 <==> b1 == false /\ b2 == true}) =
  inverse_image_to_wfr #bool #nat #(fun _ -> nat) (fun b1 b2 -> b1 == false /\ b2 == true) (fun b -> if b then 1 else 0) (default_wfr nat)

let option_d (#a: Type u#a) (#d: a -> Type u#d) (wfr: wfr_t a d) (x: option a) : Type u#(d + 1)=
  let unit_a: Type u#a = raise_t unit in
  let unit_d: Type u#d = raise_t unit in
  let f: option a -> (b: bool & (if b then a else unit_a)) =
    fun opt -> (match opt with | Some x -> (| true, x |) | None -> (| false, raise_val () |) ) in
  let bool_to_wfr_a (b: bool) : wfr_t (if b then a else unit_a) (fun x -> if b then d x else unit_d) =
    if b then
      { decreaser = wfr.decreaser; relation = wfr.relation; }
    else
      { decreaser = (fun _ -> raise_val ()); relation = (fun x1 x2 -> False <: (related: Type0{~related})); } in
  (lex_dep_d bool_wfr bool_to_wfr_a) (f x)

let option_wfr (#a: Type u#a) (#d: a -> Type u#d) (wfr: wfr_t a d) :
  wfr': wfr_t (option a) (option_d wfr)
        {forall opt1 opt2. precedes_by_wfr wfr' opt1 opt2 <==> Some? opt2 /\ (None? opt1 \/ precedes_by_wfr wfr (Some?.v opt1) (Some?.v opt2))} =
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
      { decreaser = wfr.decreaser; relation = wfr.relation; }
    else
      { decreaser = (fun _ -> raise_val ()); relation = (fun x1 x2 -> False <: (related: Type0{~related})); } in
  let wfr_bool_a: wfr_t (b: bool & (if b then a else unit_a)) (lex_dep_d bool_wfr bool_to_wfr_a) =
    lex_dep_wfr bool_wfr bool_to_wfr_a in

  assert (forall (bx1: (b: bool & (if b then a else unit_a))) (bx2: (b: bool & (if b then a else unit_a))).
            precedes_by_wfr wfr_bool_a bx1 bx2 <==>
               (let (| b1, x1 |), (| b2, x2 |) = bx1, bx2 in
                (not b1 && b2) \/ (b1 && b2 /\ precedes_by_wfr wfr x1 x2)));

  // Step 3:  Create the desired relation

  let relation (opt1: option a) (opt2: option a) : Type0 =
    Some? opt2 /\ (None? opt1 \/ precedes_by_wfr wfr (Some?.v opt1) (Some?.v opt2)) in

  // Step 4:  Create the final wfr using inverse_image_to_wfr, using `f` as the mapping function from
  //          `option a` to `(b: bool & (if b then a else unit_a))` and `wfr_bool_a` as the wfr_t
  //          for `(b: bool & (if b then a else unit_a))`.

  assert (forall opt1 opt2. relation opt1 opt2 ==> precedes_by_wfr wfr_bool_a (f opt1) (f opt2));
  inverse_image_to_wfr relation f wfr_bool_a
