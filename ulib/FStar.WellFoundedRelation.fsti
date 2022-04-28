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

   The key data structure is `wfr_t`.  A `wfr_t` encapsulates a
   well-founded relation in a way that lets one establish that a pair
   of values are related by that relation.  Specifically, the
   predicate `precedes_by_wfr wfr x1 x2` means that `x1` precedes `x2`
   in the well-founded relation described by `wfr`.

   You can then use this relatedness to show that a function is
   decreasing in a certain term.  Whenever you assert `precedes_by_wfr
   wfr x1 x2`, this implies that `decreaser_for_wfr wfr x1 <<
   decreaser_for_wfr wfr x2`.  So you can use `decreaser_for_wfr wfr x`
   in your decreases clause.  For example:

     // Define `nat_nat_wfr` to represent the lexicographically-precedes
     // relation between two elements of type `nat * nat`.  That is,
     // `(x1, y1)` is related to `(x2, y2)` if
     // `x1 < x2 \/ (x1 == x2 /\ y1 < y2)`.

     let nat_nat_wfr = lex_nondep_wfr (default_wfr nat) (default_wfr nat)

     // To show that `f` is well-defined, we use the decreases clause
     // `nat_nat_wfr.decreaser (x, y)`.  We then need to show, on each
     // recursive call, that the parameters x2 and y2 to the nested
     // call satisfy `nat_nat_wfr.relation (x2, y2) (x, y)`.  The
     // assertions below aren't necessary, but are provided for ease
     // of understanding.

     let rec f (x: nat) (y: nat)
       : Tot nat (decreases (nat_nat_wfr.decreaser (x, y))) =
       if x = 0 then
         0
       else if y = 0 then (
         assert (nat_nat_wfr.relation (x - 1, 100) (x, y));
         f (x - 1) 100
       )
       else (
         assert (nat_nat_wfr.relation (x, y - 1) (x, y));
         f x (y - 1)
       )
   
  Note that `wfr_t` isn't itself a type; `wfr_t a d` is.  But you
  don't have to really care about that.  In case you care, `a` is the
  type of things related by the well-founded relation, like `nat *
  nat` in the example above.  `d` is a function that, when applied to
  a value `x` of type `a`, produces the type of `decreaser_for_wfr wfr
  x`.

  There are a few ways to build a `wfr_t`:

    `default_wfr a`

    This is the well-founded relation built into F* for type `a`.  For
    instance, for `nat` it's the less-than relation.  For an inductive
    type it's the sub-term ordering.  For instance, `precedes_by_wfr
    (default_wfr nat) 3 4` is True.

    `empty_wfr a`

    This is the empty well-founded relation, which doesn't relate any
    pair of values.  In other words, `precedes_by_wfr (empty_wfr a) x1
    x2` is always False.

    `bool_wfr`

    This is the well-founded relation on booleans that has false
    preceding true.  So, `precedes_by_wfr bool_wfr b1 b2` is
    equivalent to `b1 == false /\ b2 == true`.

    `acc_to_wfr r f`

    This is a `wfr_t` built from a relation `r` and a function `f:
    well-founded r`.  Such a function demonstrates that `r` is
    well-founded using the accessibility type `acc` described in
    FStar.WellFounded.fst.  So, `precedes_by_wfr (acc_to_wfr r f) x1
    x2` is true whenever there exists an object of type `r x1 x2`.

    `subrelation_to_wfr r wfr`

    This is a `wfr_t` built from a relation `r` that's a subrelation
    of an existing well-founded relation `wfr`.  By "subrelation" we
    mean that any pair related by `r` is also related by `wfr`.  So,
    `precedes_by_wfr (subrelation_to_wfr r wfr) x1 x2` is equivalent
    to `r x1 x2`.

    `inverse_image_to_wfr r f wfr`

    This is a `wfr_t` built from a relation `r: a -> a -> Type0`, a
    function `f: a -> b`, and an existing well-founded relation `wfr`
    on `b`.  The relation `r` must be an "inverse image" of `wfr`
    using the mapping function `f`, meaning that
    `forall x1 x2. r x1 x2 ==> precedes_by_wfr wfr (f x1) (f x2)`.
    So, `precedes_by_wfr (inverse_image_to_wfr r f wfr) x1 x2` is
    equivalent to `r x1 x2`.

    `lex_nondep_wfr wfr_a wfr_b`

    This is a `wfr_t` describing lexicographic precedence for
    non-dependent tuples of some type `a * b`.  It's built from two
    well-founded relations: `wfr_a` on type `a` and `wfr_b` on type
    `b`.  So, `precedes_by_wfr (lex_nondep_wfr wfr_a wfr_b) xy1 xy2`
    is equivalent to `let (x1, y1), (x2, y2) = xy1, xy2 in
    precedes_by_wfr wfr_a x1 x2 \/ (x1 == x2 /\ precedes_by_wfr wfr_b
    y1 y2)`.

    `lex_dep_wfr wfr_a wfr_b`

    This is a `wfr_t` describing lexicographic precedence for
    dependent tuples of type `(x: a & b x)`.  It's built from a
    well-founded relation `wfr_a` on type `a` and a function `wfr_b`
    that maps each `x: a` to a `wfr_t` on type `(b x)`.  So,
    `precedes_by_wfr (lex_dep_wfr wfr_a wfr_b) xy1 xy2` is equivalent
    to `let (| x1, y1 |), (| x2, y2 |) = xy1, xy2 in precedes_by_wfr
    wfr_a x1 x2 \/ (x1 == x2 /\ precedes_by_wfr (wfr_b x1) y1 y2)`.

    `option_wfr wfr`

    This is a `wfr_t` describing precedence for an `option a`.  It's
    built from a well-founded relation `wfr` on `a`.  It has `None`
    precede any `Some x`, and has `Some x1` precede `Some x2` if `x1`
    precedes `x2` according to `wfr`.  In other words,
    `precedes_by_wfr (option_wfr wfr) opt1 opt2` is equivalent to
    `Some? opt2 /\ (None? opt1 \/ precedes_by_wfr wfr (Some?.v opt1)
    (Some?.v opt2)`.

*)

module FStar.WellFoundedRelation

open FStar.Universe
open FStar.WellFounded

noeq type wfr_t (a: Type u#a) (d: a -> Type u#d) : Type u#(max a d + 1) =
  {
    decreaser: (x: a -> d x);
    relation: a -> a -> Type0;
    proof: (x1: a) -> (x2: a) -> Lemma (requires relation x1 x2) (ensures decreaser x1 << decreaser x2);
  }

let ambient_wfr_lemma (#a: Type u#a) (#d: a -> Type u#d) (wfr: wfr_t a d) (x1: a) (x2: a)
  : Lemma (requires wfr.relation x1 x2)
          (ensures  wfr.decreaser x1 << wfr.decreaser x2)
          [SMTPat (wfr.decreaser x1); SMTPat (wfr.decreaser x2)] =
  wfr.proof x1 x2

val default_wfr (a: Type u#a) : (wfr: wfr_t a (fun _ -> a){ wfr.relation == (fun x1 x2 -> x1 << x2) })

val empty_wfr (a: Type u#a) : (wfr: wfr_t a (fun _ -> unit){ wfr.relation == (fun x1 x2 -> False) })

val acc_to_wfr (#a: Type u#a) (r: a -> a -> Type0) (f: well_founded r{forall x1 x2 (p: r x1 x2). (f x2).access_smaller x1 p == f x1})
  : (wfr: wfr_t a (fun (x: a) -> acc r x) { wfr.relation == (fun x1 x2 -> exists (p: r x1 x2). True) })

val subrelation_to_wfr (#a: Type u#a) (#d: a -> Type u#d) (r: a -> a -> Type0)
                       (wfr: wfr_t a d{forall x1 x2. r x1 x2 ==> wfr.relation x1 x2})
  : (wfr': wfr_t a d{wfr'.relation == r})

val inverse_image_to_wfr (#a: Type u#a) (#b: Type u#b) (#d: b -> Type u#d) (r: a -> a -> Type0) (f: a -> b)
                         (wfr: wfr_t b d{forall x1 x2. r x1 x2 ==> wfr.relation (f x1) (f x2)})
  : (wfr': wfr_t a (fun x -> d (f x)){ wfr'.relation == r })

noeq type lex_nondep_t (#a: Type u#a) (#b: Type u#b) (xy: a * b) : Type u#(max a b + 1) =
  | LexIntroNondep: access_smaller:(#a': Type u#a -> #b': Type u#b -> xy': (a' * b') ->
                                    u: squash(let (x', y'), (x, y) = xy', xy in x' << x \/ (a' == a /\ x' == x /\ y' << y)) ->
                                    lex_nondep_t xy') -> lex_nondep_t xy

val lex_nondep_d (#a: Type u#a) (#b: Type u#b) (#da: a -> Type u#da) (#db: b -> Type u#db)
                 (wfr_a: wfr_t a da) (wfr_b: wfr_t b db) : (a * b) -> Type u#(max da db + 1)

let lex_nondep_relation (#a: Type u#a) (#b: Type u#b) (#da: a -> Type u#da) (#db: b -> Type u#db)
                        (wfr_a: wfr_t a da) (wfr_b: wfr_t b db) (xy1: a * b) (xy2: a * b) : Type0 =
  let (x1, y1), (x2, y2) = xy1, xy2 in
  wfr_a.relation x1 x2 \/ (x1 == x2 /\ wfr_b.relation y1 y2)  

val lex_nondep_wfr (#a: Type u#a) (#b: Type u#b) (#da: a -> Type u#da) (#db: b -> Type u#db) (wfr_a: wfr_t a da) (wfr_b: wfr_t b db)
  : wfr: wfr_t (a * b) (lex_nondep_d wfr_a wfr_b) { wfr.relation == lex_nondep_relation wfr_a wfr_b }

noeq type lex_dep_t (#a: Type u#a) (#b: a -> Type u#b) (xy: (x: a & b x)) : Type u#(max a b + 1) =
  | LexIntroDep: access_smaller:(#a': Type u#a -> #b': (a' -> Type u#b) -> xy': (x': a' & b' x') ->
                                u: squash(let (| x', y' |), (| x, y |) = xy', xy in x' << x \/ (a' == a /\ x' == x /\ y' << y)) ->
                                lex_dep_t xy') -> lex_dep_t xy

val lex_dep_d (#a: Type u#a) (#b: a -> Type u#b) (#da: a -> Type u#da) (#db: (x: a) -> (y: b x) -> Type u#db)
              (wfr_a: wfr_t a da) (wfr_b: (x: a -> wfr_t (b x) (db x))) : (x: a) & b x -> Type u#(max da db + 1)

let lex_dep_relation (#a: Type u#a) (#b: a -> Type u#b) (#da: a -> Type u#da) (#db: (x: a) -> (y: b x) -> Type u#db)
                     (wfr_a: wfr_t a da) (wfr_b: (x: a -> wfr_t (b x) (db x)))
                     (xy1: (x: a & b x)) (xy2: (x: a & b x)) : Type0 =
  let (| x1, y1 |), (| x2, y2 |) = xy1, xy2 in
  wfr_a.relation x1 x2 \/ (x1 == x2 /\ (wfr_b x1).relation y1 y2)

val lex_dep_wfr (#a: Type u#a) (#b: a -> Type u#b) (#da: a -> Type u#da) (#db: (x: a) -> (y: b x) -> Type u#db)
                (wfr_a: wfr_t a da) (wfr_b: (x: a -> wfr_t (b x) (db x)))
  : wfr: wfr_t (x: a & b x) (lex_dep_d wfr_a wfr_b){ wfr.relation == lex_dep_relation wfr_a wfr_b }

val bool_wfr: (wfr: wfr_t bool (fun _ -> nat){ wfr.relation == (fun b1 b2 -> b1 == false /\ b2 == true) })

val option_d (#a: Type u#a) (#d: a -> Type u#d) (wfr: wfr_t a d) : option a -> Type u#(d + 1)

let option_relation (#a: Type u#a) (#d: a -> Type u#d) (wfr: wfr_t a d) (opt1: option a) (opt2: option a) : Type0 =
  Some? opt2 /\ (None? opt1 \/ wfr.relation (Some?.v opt1) (Some?.v opt2))

val option_wfr (#a: Type u#a) (#d: a -> Type u#d) (wfr: wfr_t a d) :
  wfr': wfr_t (option a) (option_d wfr) { wfr'.relation == option_relation wfr }
