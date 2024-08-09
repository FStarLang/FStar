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

   The key data structure is `wfr_t a`, which encapsulates a
   well-founded relation on `a`. Specifically, the predicate
   `wfr.relation x1 x2` means that `x1` precedes `x2` in the
   well-founded relation described by `wfr`.

   You can then use this relatedness to show that a function is
   decreasing in a certain term. Whenever `wfr.relation x1 x2` holds,
   `wfr.decreaser x1 << wfr.decreaser x2` also holds. The library has
   an ambient lemma triggered by seeing two instances of
   `wfr.decreaser`, so you can use `wfr.decreaser x` in your decreases
   clause. For example:

     // Define `nat_nat_wfr` to represent the lexicographically-precedes
     // relation between two elements of type `nat * nat`. That is,
     // `(x1, y1)` is related to `(x2, y2)` if
     // `x1 < x2 \/ (x1 == x2 /\ y1 < y2)`.

     let nat_nat_wfr = lex_nondep_wfr (default_wfr nat) (default_wfr nat)

     // To show that `f` is well-defined, we use the decreases clause
     // `nat_nat_wfr.decreaser (x, y)`. We then need to show, on each
     // recursive call, that the parameters x2 and y2 to the nested
     // call satisfy `nat_nat_wfr.relation (x2, y2) (x, y)`.

     let rec f (x: nat) (y: nat)
       : Tot nat (decreases (nat_nat_wfr.decreaser (x, y))) =
       if x = 0 then
         0
       else if y = 0 then (
         // This assertion isn't necessary; it's just for illustration
         assert (nat_nat_wfr.relation (x - 1, 100) (x, y));
         f (x - 1) 100
       )
       else (
         // This assertion isn't necessary; it's just for illustration
         assert (nat_nat_wfr.relation (x, y - 1) (x, y));
         f x (y - 1)
       )

  One way `wfr_t` can be useful is that it simplifies debugging when
  the SMT solver can't verify termination. You can assert the
  relation explicitly (as in the examples above), and if the assertion
  doesn't hold you can try to prove it. If you instead use something
  like `decreases %[x, y]`, it's harder to debug because you can't
  `assert (%[x2, y2] << %[x, y])`.

  But where `wfr_t` is most useful is in writing a function that takes
  a well-founded relation as input. Here's an illustrative example:

    let rec count_steps_to_none
      (#a: Type)
      (wfr: wfr_t a)
      (stepper: (x: a) -> (y: option a{Some? y ==> wfr.relation (Some?.v y) x}))
      (start: option a)
      : Tot nat (decreases (option_wfr wfr).decreaser start) =
      match start with
      | None -> 0
      | Some x -> 1 + count_steps_to_none wfr stepper (stepper x)

  `wfr_t` is also useful when composing a well-founded relation
  produced using `acc` (from the FStar.WellFounded library) with one
  or more other well-founded relations.

  There are a few ways to build a `wfr_t`, described in more detail in
  comments throughout this file. Those ways are:

    `default_wfr a`
    `empty_wfr a`
    `acc_to_wfr r f`
    `subrelation_to_wfr r wfr`
    `inverse_image_to_wfr r f wfr`
    `lex_nondep_wfr wfr_a wfr_b`
    `lex_dep_wfr wfr_a a_to_wfr_b`
    `bool_wfr`
    `option_wfr wfr`
*)

module FStar.WellFoundedRelation

noeq type acc_classical (#a: Type u#a) (r: a -> a -> Type0) (x: a) : Type u#a =
  | AccClassicalIntro : access_smaller:(y: a{r y x} -> acc_classical r y) -> acc_classical r x

noeq type wfr_t (a: Type u#a) : Type u#(a + 1) =
  {
    relation: a -> a -> Type0;
    decreaser: (x: a -> acc_classical relation x);
    proof: (x1: a) -> (x2: a) -> 
           Lemma (requires relation x1 x2) (ensures decreaser x1 << decreaser x2);
  }

let ambient_wfr_lemma (#a: Type u#a) (wfr: wfr_t a) (x1: a) (x2: a)
  : Lemma (requires wfr.relation x1 x2)
          (ensures  wfr.decreaser x1 << wfr.decreaser x2)
          [SMTPat (wfr.decreaser x1); SMTPat (wfr.decreaser x2)] =
  wfr.proof x1 x2

/// `default_wfr a` is the well-founded relation built into F* for
/// type `a`. For instance, for `nat` it's the less-than relation.
/// For an inductive type it's the sub-term ordering.
///
/// `(default_wfr a).relation` is `default_relation` as defined below.

let default_relation (#a: Type u#a) (x1: a) (x2: a) : Type0 = x1 << x2

val default_wfr (a: Type u#a) : (wfr: wfr_t a{wfr.relation == default_relation})

/// `empty_wfr a` is the empty well-founded relation, which doesn't relate any
/// pair of values.
///
/// `(empty_wfr a).relation` is `empty_relation` as defined below.

let empty_relation (#a: Type u#a) (x1: a) (x2: a) : Type0 = False

val empty_wfr (a: Type u#a) : (wfr: wfr_t a{wfr.relation == empty_relation})

/// `acc_to_wfr r f` is a `wfr_t` built from a relation `r` and a
/// function `f: well-founded r`. Such a function demonstrates that
/// `r` is well-founded using the accessibility type `acc` described
/// in FStar.WellFounded.fst.
///
/// `(acc_to_wfr r f).relation` is `acc_relation r` as defined below.

let acc_relation (#a: Type u#a) (r: a -> a -> Type0) (x1: a) (x2: a) : Type0 = exists (p: r x1 x2). True

val acc_to_wfr (#a: Type u#a) (r: a -> a -> Type0) (f: FStar.WellFounded.well_founded r)
  : (wfr: wfr_t a{wfr.relation == acc_relation r})

/// `subrelation_to_wfr r wfr` is a `wfr_t` built from a relation `r`
/// that's a subrelation of an existing well-founded relation `wfr`.
/// By "subrelation" we mean that any pair related by `r` is also
/// related by `wfr`.
///
/// `(subrelation_to_wfr r wfr).relation` is the parameter `r`.

val subrelation_to_wfr (#a: Type u#a) (r: a -> a -> Type0)
                       (wfr: wfr_t a{forall x1 x2. r x1 x2 ==> wfr.relation x1 x2})
  : (wfr': wfr_t a{wfr'.relation == r})

/// `inverse_image_to_wfr r f wfr` is a `wfr_t` built from a relation
/// `r: a -> a -> Type0`, a function `f: a -> b`, and an existing
/// well-founded relation `wfr` on `b`. The relation `r` must be an
/// "inverse image" of `wfr` using the mapping function `f`, meaning
/// that `forall x1 x2. r x1 x2 ==> wfr.relation (f x1) (f x2)`.
///
/// `(inverse_image_to_wfr r f wfr).relation` is the parameter `r`.

val inverse_image_to_wfr
  (#a: Type u#a)
  (#b: Type u#b)
  (r: a -> a -> Type0)
  (f: a -> b)
  (wfr: wfr_t b{forall x1 x2. r x1 x2 ==> wfr.relation (f x1) (f x2)})
  : (wfr': wfr_t a{wfr'.relation == r})

/// `lex_nondep_wfr wfr_a wfr_b` is a `wfr_t` describing lexicographic
/// precedence for non-dependent tuples of some type `a * b`. It's
/// built from two well-founded relations: a `wfr_t a` and a `wfr_t
/// b`.
///
/// `(lex_nondep_wfr wfr_a wfr_b).relation` is `lex_nondep_relation
/// wfr_a wfr_b` as defined below.

let lex_nondep_relation (#a: Type u#a) (#b: Type u#b) (wfr_a: wfr_t a) (wfr_b: wfr_t b)
                        (xy1: a & b) (xy2: a & b)
  : Type0 =
  let (x1, y1), (x2, y2) = xy1, xy2 in
  wfr_a.relation x1 x2 \/ (x1 == x2 /\ wfr_b.relation y1 y2)

val lex_nondep_wfr (#a: Type u#a) (#b: Type u#b) (wfr_a: wfr_t a) (wfr_b: wfr_t b)
  : wfr: wfr_t (a & b){wfr.relation == lex_nondep_relation wfr_a wfr_b}

/// `lex_dep_wfr wfr_a a_to_wfr_b` is a `wfr_t` describing
/// lexicographic precedence for dependent tuples of type `(x: a & b
/// x)`. It's built from a well-founded relation of type `wfr_t a`
/// and a function `a_to_wfr_b` that maps each `x: a` to a `wfr_t (b
/// x)`.
///
/// `(lex_dep_wfr wfr_a a_to_wfr_b).relation` is `lex_dep_relation
/// wfr_a a_to_wfr_b` as defined below.

let lex_dep_relation (#a: Type u#a) (#b: a -> Type u#b) (wfr_a: wfr_t a)
                     (a_to_wfr_b: (x: a -> wfr_t (b x))) (xy1: (x: a & b x)) (xy2: (x: a & b x))
  : Type0 =
  let (| x1, y1 |), (| x2, y2 |) = xy1, xy2 in
  wfr_a.relation x1 x2 \/ (x1 == x2 /\ (a_to_wfr_b x1).relation y1 y2)

val lex_dep_wfr (#a: Type u#a) (#b: a -> Type u#b) (wfr_a: wfr_t a)
                (a_to_wfr_b: (x: a -> wfr_t (b x)))
  : wfr: wfr_t (x: a & b x){wfr.relation == lex_dep_relation wfr_a a_to_wfr_b}

/// `bool_wfr` is the well-founded relation on booleans that has false
/// preceding true.
///
/// `bool_wfr.relation` is `bool_relation`, as defined below.

let bool_relation (x1: bool) (x2: bool) : Type0 = x1 == false /\ x2 == true

val bool_wfr: (wfr: wfr_t bool{wfr.relation == bool_relation})

/// `option_wfr wfr` is a `wfr_t` describing precedence for an `option
/// a`. It's built from a well-founded relation `wfr` on `a`. It has
/// `None` precede any `Some x`, and has `Some x1` precede `Some x2`
/// if `x1` precedes `x2` according to `wfr`.
///
/// `(option_wfr wfr).relation` is `option_relation wfr` as defined below.

let option_relation (#a: Type u#a) (wfr: wfr_t a) (opt1: option a) (opt2: option a) : Type0 =
  Some? opt2 /\ (None? opt1 \/ wfr.relation (Some?.v opt1) (Some?.v opt2))

val option_wfr (#a: Type u#a) (wfr: wfr_t a)
  : wfr': wfr_t (option a){wfr'.relation == option_relation wfr}
